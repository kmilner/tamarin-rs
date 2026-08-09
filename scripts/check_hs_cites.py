#!/usr/bin/env python3
"""Validate the Haskell oracle citations in Rust comments against the pin.

Comments across `crates/` cite upstream Haskell locations as `Foo.hs:12`,
`Foo.hs:150-183`, `Foo.hs:61-63,84,92` or `Foo.hs:150-183, see line 162`.  The
numbers are line numbers in the `tamarin-prover/` submodule at its pinned
commit, so they are only as good as the last bump.

Nothing else fails on a stale one.  `extend_anchor_citations.py` leaves an
anchor it cannot resolve unchanged and reports it; `remap_hs_cites.py` maps
cites across a bump but treats anything ambiguous as a report, not an error,
and `bump_submodule.sh` does not abort on that report.  A cite that ends up
pointing at a blank line, or at a file that no longer exists, therefore
survives indefinitely, and a reader who follows it to check a byte-parity
claim is silently misled.  This script is the gate for the mechanical part of
that: it exits nonzero on any finding, so it can run at the end of a bump.

Finding classes
---------------
  MISSING    the cited `.hs` basename matches no file in the pinned tree.
  AMBIGUOUS  it matches more than one.  Around twenty basenames are shared
             upstream -- `Rule.hs`, `Proof.hs`, `Term.hs`, `Dot.hs`,
             `Parser.hs`, `Signature.hs`, `Class.hs` among them -- so a bare
             `Rule.hs:97` names two or three different files and its line
             number cannot be checked against any of them.  The class is
             reported rather than resolved by preferring a candidate: a
             preference that picks the wrong sibling turns an unverifiable
             cite into a confidently wrong one.  The fix is to write enough
             of the path to disambiguate (`Theory/Model/Rule.hs:1464`).
  RANGE      the line number is past the end of the file (or below 1).
  BLANK      the cited line is empty.
  COMMENT    an ANCHOR line -- a bare `File.hs:N`, or a `see line N` target --
             holds only a Haskell comment.  Sometimes intended (an anchor may
             name the `-- |` haddock that states the fact being cited), so this
             class is separated from BLANK for triage.  Range ENDPOINTS are not
             checked this way: a declaration extent legitimately starts at its
             haddock.
  SEELINE    a `see line N` falls outside the `A-B` extent it annotates.

What this script does NOT check
-------------------------------
Read the summary line: it prints what it skipped, so a green run is not
mistaken for more coverage than it has.

  * **Whether a cite names the right declaration.**  This is the big one, and
    it is the failure the classes above cannot see.  A cite whose target
    merely drifted -- `Handler.hs:1422-1440` for a `getKillThreadR` that a
    bump moved to 1517 -- lands on a line that exists and is neither blank nor
    a comment, so every class passes.  Only a human, or a checker that knows
    which identifier the comment claims, catches that.  Zero findings here
    means "no cite is mechanically broken", never "every cite is correct".
  * **Cites inside string literals.**  Deliberately not reported; see Scope.
  * **Anything outside `crates/**/*.rs`.**  `scripts/`, `tests/`, the `*.md`
    files and the `.spthy` fixtures under `scripts/divergence_fixtures/` all
    carry cites that nothing validates.
  * **A parts list that WRAPS onto the following comment line** (see
    `remap_hs_cites.py`'s `continuation`) has its tail skipped, which
    under-reports rather than misreports.
  * **Haskell block-comment interiors.**  `is_comment_only` recognises `--`,
    an opening `{-` and a closing `-}`, but not a line in the middle of a
    `{- ... -}`; missing one costs a report, not a false one.  `{-#` pragma
    lines are code, not comments, and are not reported.

Scope
-----
Comment text only, found by lexing each file: line comments, block comments
and their doc forms.  A `//` inside a string literal does NOT open a comment.
That matters here -- this repo has about a hundred of them, because Tamarin's
own output format uses `//` and the expected-output fixtures quote it
verbatim (`"// Function signature and definition of the equational theory E"`,
`"SOLVED // trace found"`).  A scope rule that just split each line on its
first `//` would scan those literals as if they were commentary, and a cite
"corrected" inside one of them is a byte-parity regression, not a doc fix.

Two guards exist for exactly that failure:

  * A `File.hs:LINE:COL` token -- with a COLUMN -- is a GHC `HasCallStack`
    coordinate, not a citation.  The port reproduces those verbatim, so their
    numbers belong to the oracle's output and are never validated or reported
    here.  They are counted as EMITTED.
  * A comment cite whose text also occurs inside a string literal in the same
    file is reported as a MIRRORED advisory: the same token is both commentary
    and emitted bytes, so a global rewrite of it changes what the binary
    prints.  Advisories go to stderr and do not affect the exit status.

A cite may name its file as a path (`Theory/Model/Rule.hs`) or as a dotted
module (`Theory.Tools.SubtermStore.hs`); both resolve.  Modules in
`EXTERNAL_MODULES` are Haskell the port cites but the submodule does not
vendor, so their line numbers cannot be checked here and are not findings.

Usage: scripts/check_hs_cites.py [--crate NAME]... [--skip CLASS]...
                                 [--submodule PATH] [--show-emitted]
"""
import argparse
import collections
import os
import re
import subprocess
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(SCRIPT_DIR)
CRATES = os.path.join(REPO, "crates")

# `<file>.hs:<parts>[, see line <n>[,<n>...]]` where parts is a comma-joined
# list of `N` / `N-M` -- the shape `remap_hs_cites.py` writes.
CITE = re.compile(
    r"([A-Za-z][A-Za-z0-9_/.']*\.hs):"
    r"(\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*)"
    r"((?:, see line \d+(?:,\d+)*)?)")
# The same head followed by a second `:<digits>` is a GHC source coordinate
# (`src/Main/Mode/Batch.hs:163:33`), not a line citation.
EMITTED = re.compile(r"[A-Za-z][A-Za-z0-9_/.']*\.hs:\d+:\d+")
SEE = re.compile(r"\d+")

CLASSES = ("MISSING", "AMBIGUOUS", "RANGE", "BLANK", "COMMENT", "SEELINE")

# Haskell the port cites that lives outside the submodule, so its line numbers
# are not the pin's to validate: `HughesPJ.hs` is GHC's `pretty` package, whose
# layout algorithm `pretty_hpj.rs` reproduces.
EXTERNAL_MODULES = {"HughesPJ.hs"}


# --------------------------------------------------------------------------
# Rust lexing: comment spans and string spans, whole-file so that a multi-line
# literal is tracked across the lines it covers.
# --------------------------------------------------------------------------
def lex_spans(src):
    """Return (comment_spans, string_spans) as lists of (start, end) offsets."""
    comments, strings = [], []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            j = src.find("\n", i)
            j = n if j == -1 else j
            comments.append((i, j))
            i = j
            continue
        if c == "/" and i + 1 < n and src[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth += 1
                    j += 2
                elif src.startswith("*/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            comments.append((i, j))
            i = j
            continue
        # raw string: r"..." / r#"..."# / br#"..."#
        if c in "rb":
            k = i + 1
            if c == "b" and k < n and src[k] == "r":
                k += 1
            elif c == "b":
                k = i + 1
            h = 0
            while k < n and src[k] == "#":
                h += 1
                k += 1
            if k < n and src[k] == '"' and (c == "r" or src[i:k].startswith("br")
                                            or (c == "b" and h == 0)):
                close = '"' + "#" * h
                e = src.find(close, k + 1)
                e = e + len(close) if e != -1 else n
                strings.append((i, e))
                i = e
                continue
        if c == "'":
            # char literal or lifetime; only literals can hide a `//`
            if src.startswith("'\\", i):
                e = src.find("'", i + 2)
                i = e + 1 if e != -1 else i + 1
            elif i + 2 < n and src[i + 2] == "'":
                i += 3
            else:
                i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if src[j] == "\\":
                    j += 2
                    continue
                if src[j] == '"':
                    break
                j += 1
            strings.append((i, min(j + 1, n)))
            i = j + 1
            continue
        i += 1
    return comments, strings


def line_index(src):
    starts = [0]
    for m in re.finditer("\n", src):
        starts.append(m.end())
    return starts


def lineno_of(starts, off):
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= off:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


# --------------------------------------------------------------------------
# The pinned tree
# --------------------------------------------------------------------------
class Oracle:
    """The pinned submodule's `.hs` files.

    Read through `git show HEAD:` when the submodule carries git metadata, and
    straight off disk otherwise -- a git worktree does not get the submodule,
    and a source tarball has no `.git` at all.  The disk path is announced,
    because it validates whatever is checked out rather than the pin.
    """

    def __init__(self, sub, use_git):
        self.sub = sub
        self.use_git = use_git
        self._lines = {}
        if use_git:
            out = self._git(["ls-tree", "-r", "--name-only", "HEAD"]).stdout
            self.tree = [p for p in out.splitlines() if p.endswith(".hs")]
        else:
            self.tree = []
            for dp, ds, fs in os.walk(sub):
                ds[:] = [d for d in ds if d != ".git"]
                for f in fs:
                    if f.endswith(".hs"):
                        self.tree.append(
                            os.path.relpath(os.path.join(dp, f), sub))
        self.tree.sort()

    def _git(self, args):
        return subprocess.run(["git"] + args, cwd=self.sub,
                              capture_output=True, text=True)

    def candidates(self, cite):
        """Paths matching a cited name, by path suffix then by dotted module.

        `Theory/Model/Rule.hs` matches as a suffix; `Theory.Tools.SubtermStore.hs`
        only once its dots become slashes.  The dotted form is tried second so a
        real path is never re-read as a module name.
        """
        c = cite.lstrip("./")
        hits = [h for h in self.tree if h == c or h.endswith("/" + c)]
        if hits:
            return hits
        stem, _, ext = c.rpartition(".")
        dotted = stem.replace(".", "/") + "." + ext
        return [h for h in self.tree if h == dotted or h.endswith("/" + dotted)]

    def lines(self, path):
        if path not in self._lines:
            if self.use_git:
                r = self._git(["show", f"HEAD:{path}"])
                self._lines[path] = r.stdout.splitlines() if r.returncode == 0 else []
            else:
                try:
                    with open(os.path.join(self.sub, path), encoding="utf-8",
                              errors="replace") as fh:
                        self._lines[path] = fh.read().splitlines()
                except OSError:
                    self._lines[path] = []
        return self._lines[path]


def is_blank(text):
    return not text.strip()


def is_comment_only(text):
    """A Haskell line carrying nothing but a comment.

    Line comments and the one-line/opening/closing forms of a block comment.
    `{-#` opens a pragma, which is code.
    """
    s = text.strip()
    if s.startswith("{-#"):
        return False
    return s.startswith("--") or s.startswith("{-") or s == "-}"


def parse_parts(spec):
    """`"61-63,84"` -> `[(61, 63), (84, 84)]`."""
    out = []
    for p in spec.split(","):
        a, _, b = p.partition("-")
        out.append((int(a), int(b) if b else int(a)))
    return out


def rust_files(crates_filter):
    for dirpath, dirs, files in os.walk(CRATES):
        dirs[:] = [d for d in dirs if d != "target"]
        for fname in sorted(files):
            if not fname.endswith(".rs"):
                continue
            rs = os.path.join(dirpath, fname)
            crate = os.path.relpath(rs, CRATES).split(os.sep)[0]
            if crates_filter and crate not in crates_filter:
                continue
            yield crate, rs


def check_file(oracle, rs, findings, advisories, stats):
    rel = os.path.relpath(rs, REPO)
    with open(rs, encoding="utf-8", errors="replace") as fh:
        src = fh.read()
    comments, strings = lex_spans(src)
    starts = line_index(src)
    literal_text = "\n".join(src[a:b] for a, b in strings)

    # cites that sit in string literals are counted, never reported
    for a, b in strings:
        seg = src[a:b]
        for m in CITE.finditer(seg):
            if EMITTED.match(seg, m.start()):
                stats["emitted"] += 1
            else:
                stats["in_string"] += 1

    for a, b in comments:
        seg = src[a:b]
        for m in CITE.finditer(seg):
            name, spec, see_tail = m.group(1), m.group(2), m.group(3)
            cite = f"{name}:{spec}{see_tail}"
            here = f"{rel}:{lineno_of(starts, a + m.start())}"

            # A column suffix makes this an emitted GHC coordinate, not a cite.
            if EMITTED.match(seg[m.start():]):
                stats["emitted"] += 1
                if stats["show_emitted"]:
                    advisories.append(
                        (here, "EMITTED", EMITTED.match(seg[m.start():]).group(0),
                         "GHC HasCallStack coordinate; change only in lockstep "
                         "with a re-captured oracle byte"))
                continue

            if os.path.basename(name) in EXTERNAL_MODULES:
                stats["external"] += 1
                continue

            # Same token also emitted from this file?  Rewriting it edits bytes.
            if m.group(0) in literal_text:
                advisories.append(
                    (here, "MIRRORED", cite,
                     "this token also occurs in a string literal in this file; "
                     "do not rewrite it without re-capturing the oracle"))

            cands = oracle.candidates(name)
            if not cands:
                findings.append((here, "MISSING", cite,
                                 "no such file in the pinned tree"))
                continue
            if len(cands) > 1:
                findings.append((here, "AMBIGUOUS", cite,
                                 "matches " + ", ".join(sorted(cands))))
                continue
            path = cands[0]
            body = oracle.lines(path)
            parts = parse_parts(spec)
            stats["checked"] += 1
            # Range endpoints: bounds only.  A single-line part is also an
            # anchor, so it gets the blank/comment check below.
            for lo, hi in parts:
                for n in {lo, hi}:
                    if not 1 <= n <= len(body):
                        findings.append(
                            (here, "RANGE", cite,
                             f"{path} has {len(body)} lines, cite names {n}"))
            anchors = [lo for lo, hi in parts if lo == hi]
            if see_tail:
                anchors += [int(n) for n in SEE.findall(see_tail)]
                span = set()
                for lo, hi in parts:
                    span.update(range(lo, hi + 1))
                for n in (int(x) for x in SEE.findall(see_tail)):
                    if n not in span:
                        findings.append(
                            (here, "SEELINE", cite,
                             f"see line {n} is outside {spec}"))
            for n in anchors:
                if not 1 <= n <= len(body):
                    continue  # already reported as RANGE
                text = body[n - 1]
                if is_blank(text):
                    findings.append((here, "BLANK", cite, f"{path}:{n} is empty"))
                elif is_comment_only(text):
                    findings.append(
                        (here, "COMMENT", cite,
                         f"{path}:{n} is a comment: {text.strip()[:60]}"))


def resolve_pin(sub):
    """(use_git, head, note).  `head` is None when the pin cannot be read."""
    dotgit = os.path.join(sub, ".git")
    if not os.path.exists(dotgit):
        return False, None, "no git metadata: validating the checked-out tree"
    r = subprocess.run(["git", "rev-parse", "HEAD"], cwd=sub,
                       capture_output=True, text=True)
    if r.returncode != 0:
        return False, None, "git present but unreadable: validating the tree"
    head = r.stdout.strip()
    g = subprocess.run(["git", "ls-tree", "HEAD", "tamarin-prover"], cwd=REPO,
                       capture_output=True, text=True)
    recorded = g.stdout.split()[2] if len(g.stdout.split()) > 2 else None
    if recorded and recorded != head:
        return True, head, (f"submodule HEAD {head[:12]} does NOT match the "
                            f"gitlink {recorded[:12]} recorded at the "
                            f"superproject HEAD")
    return True, head, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--crate", action="append", default=[],
                    help="restrict to this crate (repeatable)")
    ap.add_argument("--skip", action="append", default=[], choices=CLASSES,
                    help="do not report this finding class (repeatable)")
    ap.add_argument("--submodule", default=os.environ.get("TAMARIN_HS_SRC"),
                    help="path to the pinned Haskell tree "
                         "(default: <repo>/tamarin-prover, or $TAMARIN_HS_SRC)")
    ap.add_argument("--show-emitted", action="store_true",
                    help="list the GHC coordinates that were skipped")
    args = ap.parse_args()

    sub = args.submodule or os.path.join(REPO, "tamarin-prover")
    if not os.path.isdir(sub):
        print(f"no Haskell tree at {sub}", file=sys.stderr)
        print("a git worktree does not get the submodule; pass --submodule "
              "PATH or set TAMARIN_HS_SRC", file=sys.stderr)
        return 2

    use_git, head, note = resolve_pin(sub)
    oracle = Oracle(sub, use_git)
    if not oracle.tree:
        print(f"no .hs files under {sub}"
              + (" at HEAD" if use_git else ""), file=sys.stderr)
        return 2

    findings, advisories = [], []
    stats = collections.Counter()
    stats["show_emitted"] = int(args.show_emitted)
    scanned = 0
    for _crate, rs in rust_files(set(args.crate)):
        scanned += 1
        check_file(oracle, rs, findings, advisories, stats)

    if not scanned:
        # "0 findings over 0 files" is the same exit status as a clean run, so
        # a misspelt --crate would gate a bump on nothing at all.
        print("no .rs files matched"
              + (f" --crate {' '.join(sorted(args.crate))}" if args.crate else "")
              + f" under {CRATES}", file=sys.stderr)
        return 2

    findings = [f for f in findings if f[1] not in set(args.skip)]
    for here, cls, cite, detail in findings:
        print(f"{here}\t{cls}\t{cite}\t{detail}")

    err = sys.stderr
    print(f"\npin: {sub}"
          + (f" @ {head[:12]}" if head else "")
          + ("" if use_git else "  [WORKING TREE, NOT A PINNED COMMIT]"), file=err)
    if note:
        print(f"WARNING: {note}", file=err)
    for here, cls, cite, detail in advisories:
        print(f"{here}\t{cls}\t{cite}\t{detail}", file=err)

    counts = collections.Counter(cls for _, cls, _, _ in findings)
    summary = ", ".join(f"{c}={counts[c]}" for c in CLASSES if counts[c])
    print(f"{scanned} .rs files scanned; {stats['checked']} cites verified; "
          f"{len(findings)} findings" + (f" ({summary})" if summary else ""),
          file=err)
    skipped = [f"{stats['emitted']} GHC coordinates",
               f"{stats['in_string']} cites inside string literals",
               f"{stats['external']} external-module cites"]
    print("not checked: " + "; ".join(skipped)
          + f"; {len(advisories)} advisories"
          + "; and whether any verified cite names the RIGHT declaration "
            "(see the module docstring)", file=err)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
