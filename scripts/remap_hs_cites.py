#!/usr/bin/env python3
"""Remap Haskell line cites in Rust comments across a submodule bump.

    scripts/remap_hs_cites.py --old <pin> --new <pin> [--apply] [file.rs ...]

Comments across crates/ cite upstream Haskell locations as `Foo.hs:12`,
`Foo.hs:150-183`, `Foo.hs:61-63,84,92`, `Foo.hs:150-183, see line 162` or,
with a symbol anchor, `Foo.hs:150-183#declName`.  The grammar is
`check_hs_cites.CITE`, imported rather than restated: this tool writes what
that gate reads.  The numbers are relative to the pinned submodule, so a bump
silently invalidates any cite into a Haskell file the bump rewrote.  This
tool maps every cite through the `git diff <old> <new>` line mapping of its
Haskell file:

  * parts that fall outside every changed hunk get the pure line shift;
  * parts that land inside a changed hunk are re-anchored semantically: the
    old top-level declaration (extend_anchor_citations' `decl_groups`) is
    located by name in the new tree, exact-extent cites are rewritten to the
    declaration's new extent, and interior lines (`see line` targets,
    sub-range endpoints) are re-found by exact line-text match within it;
  * anything ambiguous is left untouched and reported as UNRESOLVED for a
    human pass.

Which file a cite names is resolved by path suffix and then by the dotted
module spelling, the same two ways `check_hs_cites.py` resolves it, and a
basename matching two upstream files is UNRESOLVED rather than guessed at by
crate preference — remapping through the wrong sibling's diff produces
numbers that look maintained and name nothing, and the gate rejects a cite
that vague anyway.  Cites into `check_hs_cites.EXTERNAL_MODULES` (Haskell the
submodule does not vendor) and `Foo.hs:LINE:COL` GHC coordinates (emitted
output, not citations) are skipped and counted, never rewritten.

A `#declName` anchor is carried through the rewrite and does three things: it
names the declaration to re-anchor onto directly, it makes a cite that was
ALREADY stale at the old pin refuse to remap (reported, so the gate still
sees it), and it makes a rewrite whose new range no longer contains the name
refuse likewise.  Without one, a cite that both pins consider in-range but
that now spans the wrong declaration is remapped silently — that is the
failure the anchor exists for.

A cite whose parts list WRAPS onto the following comment line is joined first
and remapped as one list, then written back at the same split (see
`continuation`); the shape recognised is deliberately narrow, and
bump_submodule.sh lints for the wrapped cites it declines to join.

Dry run by default (prints every planned rewrite); `--apply` edits in
place.  Only comment text is touched, and for `.rs` files "comment" means
what `check_hs_cites.lex_spans` lexes as one, not "after the first `//`": the
expected-output fixtures quote Tamarin's own `//` lines, several of them
around an upstream cite, and a rewrite inside such a literal would change
bytes the corpus comparison pins.  Other file types keep the plain `#`/`//`
scan.  Exit status is 0 unless arguments are bad: unresolved cites are a
report, not a failure, so the bump flow never aborts on them.

Invoked automatically by scripts/bump_submodule.sh with the old and new
pins after the gitlink moves.
"""
import argparse
import collections
import importlib.util
import os
import re
import subprocess
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(SCRIPT_DIR)
SUB = os.path.join(REPO, "tamarin-prover")
CRATES = os.path.join(REPO, "crates")

def _load(name):
    spec = importlib.util.spec_from_file_location(
        name, os.path.join(SCRIPT_DIR, name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_eac = _load("extend_anchor_citations")
decl_groups, trim_extent = _eac.decl_groups, _eac.trim_extent
# The gate's own lexer, cite grammar and external-module list: what this tool
# rewrites and what check_hs_cites.py validates have to be the same language,
# or a bump hands the gate cites it never taught it to read.
_chk = _load("check_hs_cites")
CITE, EMITTED = _chk.CITE, _chk.EMITTED
EXTERNAL_MODULES, word_re = _chk.EXTERNAL_MODULES, _chk.word_re

# Wrapped-cite pieces: a line ending in `Foo.hs:61-63,` carries the rest of its
# parts list on the next comment line (`// 84,92) reads …`).
COMMENT_OPEN = re.compile(r"//+!?|#+!?")   # `//`, `///`, `//!`, `#`, `#!`
WRAP_TAIL = re.compile(r",[ \t]*$")        # what follows the cite on line i
CONT_FRAG = re.compile(r"\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*")   # tail on line i+1
# The tail must END like a parts list: at the line end or against closing
# punctuation.  `,` is excluded on purpose — `// 84, and see …` would otherwise
# read as a continuation.
CONT_END = re.compile(r"[)\]}.;:]|$")


def git(args, cwd=SUB):
    return subprocess.run(["git"] + args, cwd=cwd, capture_output=True, text=True)


def show_lines(pin, path):
    r = git(["show", f"{pin}:{path}"])
    return r.stdout.splitlines() if r.returncode == 0 else None


def hs_tree(pin):
    out = git(["ls-tree", "-r", "--name-only", pin]).stdout
    return [p for p in out.splitlines() if p.endswith(".hs")]


class LineMap:
    """Old-line -> new-line mapping from a -U0 diff's hunk headers."""

    def __init__(self, old, new, path):
        d = git(["diff", "-U0", old, new, "--", path]).stdout
        self.hunks = []  # (old_start, old_len, new_start, new_len)
        for m in re.finditer(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", d, re.M):
            os_, ol = int(m.group(1)), int(m.group(2) or "1")
            ns, nl = int(m.group(3)), int(m.group(4) or "1")
            self.hunks.append((os_, ol, ns, nl))

    def map(self, line):
        """('keep', new_line) | ('hunk', None) for lines inside a change."""
        delta = 0
        for os_, ol, _, nl in self.hunks:
            # A pure insertion (ol == 0) sits between old lines os_ and os_+1
            # and swallows nothing.
            if ol > 0 and os_ <= line < os_ + ol:
                return ("hunk", None)
            if line >= os_ + ol:
                delta += nl - ol
            else:
                break
        return ("keep", line + delta)


def parse_parts(spec):
    out = []
    for p in spec.split(","):
        a, _, b = p.partition("-")
        out.append((int(a), int(b) if b else None))
    return out


def fmt_parts(parts):
    return ",".join(f"{a}-{b}" if b is not None else f"{a}" for a, b in parts)


def group_at(groups, line):
    for s, e, name in groups:
        if s <= line <= e:
            return (s, e, name)
    return None


def resolve_cite(name, tree):
    """`(path, None)` or `(None, reason)` -- never a guess.

    Path suffix first, then the dotted-module spelling (`Theory.Tools.X.hs`),
    exactly as `check_hs_cites.Oracle.candidates` resolves them: a cite the
    gate can validate has to be a cite this tool can move, or the next bump
    leaves it behind pointing at old line numbers.

    A basename matching two upstream files is REPORTED rather than resolved by
    crate preference.  Preferring a sibling here would rewrite the cite using
    the wrong file's diff -- numbers that look freshly maintained and name
    nothing -- and the gate now rejects such a cite outright, so the only
    correct move is to leave it and say so.
    """
    c = name.lstrip("./")
    hits = [h for h in tree if h == c or h.endswith("/" + c)]
    if not hits:
        stem, _, ext = c.rpartition(".")
        dotted = stem.replace(".", "/") + "." + ext
        hits = [h for h in tree if h == dotted or h.endswith("/" + dotted)]
    if len(hits) == 1:
        return hits[0], None
    if not hits:
        return None, "no such file at the old pin"
    return None, "ambiguous basename: matches " + ", ".join(sorted(hits))


def in_span(lines, parts, sym):
    """Does `sym` occur as a whole Haskell word inside the cited parts?"""
    pat = word_re(sym)
    for a, b in parts:
        for n in range(a, (a if b is None else b) + 1):
            if 1 <= n <= len(lines) and pat.search(lines[n - 1]):
                return True
    return False


def find_text(lines, text, lo, hi):
    """1-based unique position of stripped `text` within lines[lo-1:hi]."""
    hits = [i for i in range(lo, hi + 1)
            if i <= len(lines) and lines[i - 1].strip() == text]
    return hits[0] if len(hits) == 1 else None


class Remapper:
    def __init__(self, old, new):
        self.old_pin, self.new_pin = old, new
        r = git(["diff", "--name-only", old, new]).stdout
        self.changed = {p for p in r.splitlines() if p.endswith(".hs")}
        self.old_tree = hs_tree(old)
        self.new_tree = set(hs_tree(new))
        self._maps, self._old_lines, self._new_lines, self._groups = {}, {}, {}, {}

    def linemap(self, path):
        if path not in self._maps:
            self._maps[path] = LineMap(self.old_pin, self.new_pin, path)
        return self._maps[path]

    def lines(self, pin, path, cache):
        if path not in cache:
            cache[path] = show_lines(pin, path)
        return cache[path]

    def old_lines(self, path):
        return self.lines(self.old_pin, path, self._old_lines)

    def new_lines(self, path):
        return self.lines(self.new_pin, path, self._new_lines)

    def new_groups(self, path):
        if path not in self._groups:
            nl = self.new_lines(path)
            self._groups[path] = decl_groups(nl) if nl else []
        return self._groups[path]

    def new_group_by_name(self, path, name):
        """The same-named declaration at the new pin, when it is unambiguous."""
        cands = [ng for ng in self.new_groups(path) if ng[2] == name]
        return cands[0] if len(cands) == 1 else None

    def reanchor(self, path, line, prefer_lo=None, prefer_hi=None):
        """Semantic fallback for a line inside a changed hunk: exact-text
        match, restricted to [prefer_lo, prefer_hi] when given."""
        ol, nl = self.old_lines(path), self.new_lines(path)
        if not ol or not nl or line > len(ol):
            return None
        text = ol[line - 1].strip()
        if not text:
            return None
        lo, hi = prefer_lo or 1, prefer_hi or len(nl)
        return find_text(nl, text, lo, hi)

    def remap_cite(self, path, parts, sees, sym=None):
        """-> (new_parts, new_sees) or (None, reason).

        A `#sym` anchor is both a precondition and a postcondition: the cite
        has to still name `sym` at the old pin (otherwise it was already wrong
        and remapping only launders it), and the rewritten range has to name
        it at the new pin.  Neither is repaired here -- the cite is left alone
        and reported, so check_hs_cites.py's SYMBOL class still sees it.
        """
        lm = self.linemap(path)
        old_groups = decl_groups(self.old_lines(path) or [])
        if sym and not in_span(self.old_lines(path) or [], parts, sym):
            return None, f"`{sym}` is not in the OLD range: cite was already stale"

        def target_decl():
            """New-pin extent of the declaration the whole cite anchors into.

            The anchor names it outright when the cite carries one, which
            survives a rename of the neighbouring declaration and a
            signature/equation regrouping that changes `decl_groups`' idea of
            the old name.
            """
            if sym:
                ng = self.new_group_by_name(path, sym)
                if ng:
                    return ng
            anchor = sees[0] if sees else parts[0][0]
            g = group_at(old_groups, anchor)
            return self.new_group_by_name(path, g[2]) if g else None

        decl = None

        def map_line(l):
            nonlocal decl
            kind, v = lm.map(l)
            if kind == "keep":
                return v
            if decl is None:
                decl = target_decl()
            if decl:
                return self.reanchor(path, l, decl[0], decl[1])
            return self.reanchor(path, l)

        new_parts = []
        for a, b in parts:
            # An exact old-declaration extent is rewritten to the new extent
            # even when only one endpoint sits in a hunk.
            if b is not None:
                g = group_at(old_groups, a)
                if g and (a, b) in {(g[0], g[1]),
                                    trim_extent(self.old_lines(path), g[0], g[1])}:
                    ng = self.new_group_by_name(path, g[2])
                    if ng:
                        new_parts.append(trim_extent(self.new_lines(path), ng[0], ng[1]))
                        continue
            na = map_line(a)
            nb = map_line(b) if b is not None else None
            if na is None or (b is not None and nb is None):
                return None, f"line {a}{'-%d' % b if b else ''} lost in rewrite"
            if b is not None and nb < na:
                return None, f"range {a}-{b} inverted by remap"
            new_parts.append((na, nb))
        new_sees = []
        for s in sees:
            ns = map_line(s)
            if ns is None:
                return None, f"see-line {s} lost in rewrite"
            new_sees.append(ns)
        if sym and not in_span(self.new_lines(path) or [], new_parts, sym):
            return None, (f"`{sym}` is not in the remapped range "
                          f"{fmt_parts(new_parts)}")
        return (new_parts, new_sees), None


def comment_pos(line, fname):
    markers = ["//"] if fname.endswith(".rs") else ["#", "//"]
    return min((line.find(m) for m in markers if m in line), default=-1)


def comment_starts(src, fname):
    """Per line, the column its comment text starts at, or -1 for none.

    For `.rs` this comes from the whole-file lexer `check_hs_cites.py` gates
    with, so a `//` inside a string literal does not open a comment.  That is
    not hypothetical here: Tamarin's own output format uses `//`, about a
    hundred expected-output fixtures quote it verbatim, and several of those
    literals also quote an upstream cite.  `--apply` runs unreviewed from
    `bump_submodule.sh`, so a cite "remapped" inside one would silently change
    bytes the corpus comparison pins.  Other file types keep the plain
    `#`/`//` scan.
    """
    lines = src.split("\n")
    if not fname.endswith(".rs"):
        return [comment_pos(l, fname) for l in lines]
    cols = [-1] * len(lines)
    spans, _strings = _chk.lex_spans(src)
    starts = _chk.line_index(src)
    for a, b in spans:
        first = _chk.lineno_of(starts, a)
        last = _chk.lineno_of(starts, max(a, b - 1))
        for ln in range(first, min(last, len(cols)) + 1):
            col = a - starts[ln - 1] if ln == first else 0
            if cols[ln - 1] < 0 or col < cols[ln - 1]:
                cols[ln - 1] = col
    return cols


def comment_open(line, cpos):
    """`(marker, offset just past it)` for the line's comment, or None."""
    if cpos < 0:
        return None
    m = COMMENT_OPEN.match(line, cpos)
    return (m.group(0), m.end()) if m else None


def continuation(lines, i, cols):
    """The parts fragment on line i+1 that continues the cite ending line i.

    -> `(start, end, parts)` as offsets into line i+1, or None.  Joining is
    narrow by design: the next line must open the SAME comment marker and,
    after whitespace, start with a parts fragment that ends at the line end or
    against closing punctuation.  Prose opening with a number (`// 20 lines
    below`) fails the terminator test and is left alone."""
    if i + 1 >= len(lines):
        return None
    here, nxt = comment_open(lines[i], cols[i]), comment_open(lines[i + 1],
                                                              cols[i + 1])
    if not here or not nxt or here[0] != nxt[0]:
        return None
    body = lines[i + 1]
    pos = nxt[1]
    while pos < len(body) and body[pos] in " \t":
        pos += 1
    m = CONT_FRAG.match(body, pos)
    if not m or not CONT_END.match(body, m.end()):
        return None
    return (m.start(), m.end(), parse_parts(m.group(0)))


def rs_files(args_files):
    if args_files:
        return args_files
    out = []
    for dirpath, dirs, files in os.walk(CRATES):
        dirs[:] = [d for d in dirs if d != "target"]
        out += [os.path.join(dirpath, f) for f in files if f.endswith(".rs")]
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--old", required=True)
    ap.add_argument("--new", required=True)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args()

    rm = Remapper(args.old, args.new)
    rewrites, unresolved, checked = [], [], 0
    skipped = collections.Counter()

    for rs in rs_files(args.files):
        with open(rs) as f:
            src = f.read()
        lines = src.split("\n")
        cols = comment_starts(src, rs)
        changed_any = False
        for i, line in enumerate(lines):
            cpos = cols[i]
            if cpos < 0:
                continue
            edits, cont_edit = [], None
            for m in CITE.finditer(line):
                if m.start() < cpos:
                    continue
                checked += 1
                # `Foo.hs:163:33` is a GHC HasCallStack coordinate the port
                # reproduces byte for byte; a comment quoting one documents
                # emitted output, so its numbers move with the oracle's own
                # bytes, never with this diff.
                if EMITTED.match(line, m.start()):
                    skipped["emitted"] += 1
                    continue
                name = m.group("file")
                if os.path.basename(name) in EXTERNAL_MODULES:
                    skipped["external"] += 1
                    continue
                path, why = resolve_cite(name, rm.old_tree)
                if path is None:
                    unresolved.append((rs, i + 1, m.group(0), why))
                    continue
                if path not in rm.changed:
                    skipped["unchanged"] += 1
                    continue
                if path not in rm.new_tree:
                    unresolved.append((rs, i + 1, m.group(0), "file gone at new pin"))
                    continue
                parts = parse_parts(m.group("parts"))
                sym = m.group("sym")
                sees = [int(x) for x in re.findall(r"\d+", m.group("see"))]
                # Only a cite ending the line can wrap, and a `see line` tail
                # would have to be re-emitted mid-list, so both are excluded.
                cont = None
                if not sees and WRAP_TAIL.match(line, m.end()):
                    cont = continuation(lines, i, cols)
                head_n = len(parts)
                if cont:
                    parts = parts + cont[2]
                res, why = rm.remap_cite(path, parts, sees, sym)
                if res is None:
                    unresolved.append((rs, i + 1, m.group(0), why))
                    continue
                new_parts, new_sees = res
                if new_parts == parts and new_sees == sees:
                    continue
                see_txt = ", see line " + ",".join(map(str, new_sees)) if new_sees else ""
                sym_txt = f"#{sym}" if sym else ""
                repl = (f"{name}:{fmt_parts(new_parts[:head_n])}"
                        f"{sym_txt}{see_txt}")
                edits.append((m.start(), m.end(), repl, m.group(0)))
                if cont:
                    tail = fmt_parts(new_parts[head_n:])
                    cont_edit = (cont[0], cont[1], tail,
                                 f"{name}:...,{fmt_parts(cont[2])}",
                                 f"{name}:...,{tail}")
            for start, end, repl, old_txt in reversed(edits):
                rewrites.append((rs, i + 1, old_txt, repl))
                lines[i] = lines[i][:start] + repl + lines[i][end:]
                changed_any = True
            if cont_edit:
                start, end, repl, shown_old, shown_new = cont_edit
                rewrites.append((rs, i + 2, shown_old, shown_new))
                lines[i + 1] = lines[i + 1][:start] + repl + lines[i + 1][end:]
                changed_any = True
        if changed_any and args.apply:
            with open(rs, "w") as f:
                f.write("\n".join(lines))

    for rs, ln, old_txt, repl in rewrites:
        print(f"{os.path.relpath(rs, REPO)}:{ln}: {old_txt} -> {repl}")
    if unresolved:
        print(f"\nUNRESOLVED ({len(unresolved)}) — fix by hand:", file=sys.stderr)
        for rs, ln, cite, why in unresolved:
            print(f"  {os.path.relpath(rs, REPO)}:{ln}: {cite} ({why})", file=sys.stderr)
    mode = "applied" if args.apply else "planned (dry run; use --apply)"
    print(f"\nremap_hs_cites: {checked} cites checked, {len(rewrites)} rewrites {mode}, "
          f"{len(unresolved)} unresolved", file=sys.stderr)
    print(f"not remapped: {skipped['unchanged']} in files the bump did not "
          f"touch; {skipped['emitted']} GHC coordinates; "
          f"{skipped['external']} external-module cites "
          f"({', '.join(sorted(EXTERNAL_MODULES))})", file=sys.stderr)


if __name__ == "__main__":
    main()
