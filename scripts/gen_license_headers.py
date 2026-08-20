#!/usr/bin/env python3
"""Maintain the GPL-permission headers on ported Rust sources.

Scans crates/**/*.rs for citations of upstream tamarin-prover Haskell files
(`Foo.hs`, `path/Foo.hs:123-456`, or dotted module paths like
`Theory.Constraint.Solver.AnnotatedGoals`) and resolves them against the
submodule tree.  Every file with at least one resolved citation gets the
same constant header; files with none get none, and stale headers are
stripped.  The header names no authors, so it never churns with upstream
blame drift.  Idempotent, and never runs git blame.

`--authors` answers the author question on demand for one file: it blames
that file's cited sources at the pinned submodule HEAD and prints the
upstream authors whose permission the derived content awaits, one
tab-separated `<line-count> <author>` row each (GitHub usernames where
known, most lines first), then the sources those counts came from.

Blame scope: a citation with an explicit line span (`Foo.hs:123-456`) blames
only that span; when EVERY citation of a given source in a given Rust file
carries a span, the source's author list for that file is the union of its
spans.  A bare citation (`Foo.hs`) or a single-line anchor (`Foo.hs:162`,
which conventionally marks a function's start, not its extent) blames the
whole file — anchors have no honest extent to narrow to.

Usage:
  scripts/gen_license_headers.py             # regenerate headers in place
  scripts/gen_license_headers.py --check     # exit 1 if any header is stale
  scripts/gen_license_headers.py --preview F # print the header F would get
  scripts/gen_license_headers.py --authors F # rank F's upstream authors
  scripts/gen_license_headers.py --authors F --refresh-identities
                                             # ... re-querying GitHub (gh CLI)
                                             #     for unknown emails

Identity resolution order (--authors only): committed cache
(scripts/header_identities.json) -> username embedded in
@users.noreply.github.com emails -> GitHub commits API via `gh` (only with
--refresh-identities) -> git author name verbatim.
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUB = os.path.join(REPO, "tamarin-prover")
CRATES = os.path.join(REPO, "crates")
CACHE = os.path.join(REPO, "scripts", "header_identities.json")
CACHE_OUT = os.environ.get("HEADER_CACHE_OUT", CACHE)
UPSTREAM_REPO = "tamarin-prover/tamarin-prover"

HEADER = (
    "// Currently GPL 3.0 until granted permission by the upstream authors\n"
    "// of the tamarin-prover sources this file cites; list them with:\n"
    "//   scripts/gen_license_headers.py --authors <this file>\n"
    "\n")
# Prefix common to this header and the per-author form it supersedes:
# stripping on the prefix recognises both, so a rewrite converts an old
# header into this one and re-running changes nothing.
HEADER_SENTINEL = "// Currently GPL 3.0 until"

# Contributors whose permission is not required (the porting author).
SELF_EMAILS = {
    "kamilner@kamilner.ca", "kevin.milner@cs.ox.ac.uk",
    "github@kamilner.ca", "kevinmilner@improbable.io",
}
# Cited files that are not tamarin-prover sources (external libraries).
EXTERNAL = {"HughesPJ.hs", "Text/PrettyPrint/HughesPJ.hs"}

FILE_PAT = re.compile(r"[A-Za-z][A-Za-z0-9_/.]*\.hs")
SPAN_PAT = re.compile(r"([A-Za-z][A-Za-z0-9_/.]*\.hs):(\d+)-(\d+)")
MODULE_PAT = re.compile(
    r"\b(?:Theory|Term|Sapic|Accountability|Main|Web|Items|Text|Utils)"
    r"(?:\.[A-Z][A-Za-z0-9_]*)+\b")

CRATE_PREF = {
    "tamarin-parser": lambda h: "/Text/Parser" in h,
    "tamarin-sapic": lambda h: h.startswith("lib/sapic/"),
    "tamarin-term": lambda h: h.startswith("lib/term/"),
    "tamarin-accountability": lambda h: h.startswith("lib/accountability/"),
    "tamarin-server": lambda h: h.startswith("src/Web/"),
    "tamarin-theory": lambda h: h.startswith("lib/theory/") and "/Text/Parser" not in h,
    "tamarin-utils": lambda h: h.startswith("lib/utils/"),
    "tamarin-prover": lambda h: h.startswith("src/"),
}


def die(msg):
    print(f"ERROR: {msg}", file=sys.stderr)
    sys.exit(2)


def git(args, cwd=SUB):
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                          text=True, check=False).stdout


def hs_files():
    """The upstream tree every citation resolves against.

    An empty tree would resolve nothing and strip every header, so a
    missing submodule checkout is a hard error, not a quiet no-op.  A
    non-repository SUB is one too: git run there walks up to this repo, whose
    HEAD and blame describe the port rather than the upstream sources."""
    if not os.path.isdir(SUB):
        die(f"{SUB} does not exist: check out the tamarin-prover submodule "
            "(git submodule update --init)")
    top = git(["rev-parse", "--show-toplevel"]).strip()
    if not top or os.path.realpath(top) != os.path.realpath(SUB):
        die(f"{SUB} is not a git repository of its own (git run there reports "
            f"{top or 'no repository'}): its HEAD and blame would describe "
            "something other than the pinned upstream sources "
            "(git submodule update --init)")
    tree = git(["ls-files", "*.hs"]).split()
    if not tree:
        die(f"no .hs files under {SUB}: the tamarin-prover submodule is not "
            "checked out (git submodule update --init)")
    return tree


def submodule_head():
    """The pinned submodule commit that --authors blames."""
    out = subprocess.run(["git", "rev-parse", "--verify", "HEAD"], cwd=SUB,
                         capture_output=True, text=True, check=False)
    if out.returncode != 0 or not out.stdout.strip():
        die(f"no git history at {SUB}: --authors blames the pinned submodule "
            "HEAD (git submodule update --init)")
    return out.stdout.strip()


def rust_files():
    for dirpath, dirs, files in os.walk(CRATES):
        dirs[:] = [d for d in dirs if d != "target"]
        for f in files:
            if f.endswith(".rs"):
                yield os.path.join(dirpath, f)


def module_to_candidates(dotted, tree):
    """Resolve a dotted module path, dropping trailing segments (which may be
    function names) until a file matches."""
    parts = dotted.split(".")
    for end in range(len(parts), 0, -1):
        suffix = "/".join(parts[:end]) + ".hs"
        m = [h for h in tree if h == suffix or h.endswith("/" + suffix)]
        if m:
            return m
    return []


def cite_spans(text):
    """Per citation string: the set of explicit N-M spans, and whether every
    occurrence carries one (only then may blame narrow to the spans)."""
    plain = collections.Counter(FILE_PAT.findall(text))
    spans, ranged = collections.defaultdict(set), collections.Counter()
    for m in SPAN_PAT.finditer(text):
        lo, hi = int(m.group(2)), int(m.group(3))
        if hi < lo:
            lo, hi = hi, lo
        spans[m.group(1)].add((lo, hi))
        ranged[m.group(1)] += 1
    return {c: frozenset(spans[c]) for c in spans if plain[c] <= ranged[c]}


def merge_scope(store, path, scope):
    """Union a blame scope into store[path]; None (whole file) absorbs spans."""
    if path in store and (store[path] is None or scope is None):
        store[path] = None
    elif scope is None:
        store[path] = None
    else:
        store[path] = frozenset(store.get(path, frozenset()) | scope)


def resolve_citations(text, crate, tree, global_qualified):
    """Return ({resolved path: spans|None}, ambiguous candidate tuples)."""
    resolved, ambiguous = {}, []
    cites = set(FILE_PAT.findall(text))
    narrowed = cite_spans(text)
    # Dotted module paths count as derivation citations only in an explicit
    # "port of" context — bare mentions in module-map docs are references,
    # not derivation (see the uncited-file audit: those files are independent).
    for line in text.splitlines():
        if re.search(r"\b[Pp]ort(?:ed)?\b.*\bof\b", line):
            for dotted in MODULE_PAT.findall(line):
                cites.add(dotted + ".hs")  # normalized below
    for c in cites:
        scope = narrowed.get(c)  # None = whole file
        c = c.lstrip("./")
        if c in EXTERNAL or os.path.basename(c) in EXTERNAL:
            continue
        m = [h for h in tree if h == c or h.endswith("/" + c)]
        if not m and "." in c[:-3]:
            m = module_to_candidates(c[:-3], tree)
        if not m:
            parts = c[:-3].replace(".", "/").split("/")
            for i in range(1, len(parts)):
                mm = [h for h in tree if h.endswith("/" + "/".join(parts[i:]) + ".hs")]
                if len(mm) == 1:
                    m = mm
                    break
        if len(m) == 1:
            merge_scope(resolved, m[0], scope)
            global_qualified.add(m[0])
        elif m:
            ambiguous.append((tuple(sorted(m)), scope))
    return resolved, ambiguous


def disambiguate(resolved, ambiguous, crate, global_qualified):
    basenames = {os.path.basename(h) for h in resolved}
    for cands, scope in ambiguous:
        if any(os.path.basename(c) in basenames and c in resolved for c in cands):
            continue  # covered by a qualified citation in the same file
        pref = [c for c in cands if CRATE_PREF.get(crate, lambda h: False)(c)]
        pool = pref if pref else list(cands)
        if len(pool) > 1:
            g = [c for c in pool if c in global_qualified]
            pool = g if g else pool
        for c in pool:  # conservative: keep all remaining candidates
            merge_scope(resolved, c, scope)
    return resolved


def scan_sources(tree):
    """{rust file: (current text, {upstream path: spans|None})} for crates/**.

    Two passes: the first resolves every file's unambiguous citations, which
    fills the `global_qualified` set that the second pass uses to pick among
    same-basename candidates."""
    staged, global_qualified = {}, set()
    for rs in rust_files():
        text = open(rs, encoding="utf-8", errors="replace").read()
        crate = os.path.relpath(rs, CRATES).split(os.sep)[0]
        resolved, ambiguous = resolve_citations(strip_header(text), crate, tree,
                                                global_qualified)
        staged[rs] = (text, crate, resolved, ambiguous)
    return {rs: (text, disambiguate(dict(resolved), ambiguous, crate, global_qualified))
            for rs, (text, crate, resolved, ambiguous) in staged.items()}


def load_identities():
    if os.path.exists(CACHE):
        return json.load(open(CACHE))
    return {}


def identify(email, name, identities, refresh):
    if email in identities:
        return identities[email]
    m = re.match(r"(?:\d+\+)?([^@]+)@users\.noreply\.github\.com", email)
    if m:
        identities[email] = m.group(1)
        return identities[email]
    if refresh:
        try:
            out = subprocess.run(
                ["gh", "api", f"/repos/{UPSTREAM_REPO}/commits?author={email}&per_page=1",
                 "-q", ".[0].author.login"],
                capture_output=True, text=True)
        except FileNotFoundError:
            die("--refresh-identities needs the gh CLI on PATH "
                "(https://cli.github.com); drop the flag to resolve "
                "identities from the cache alone")
        login = out.stdout.strip()
        if out.returncode == 0 and login and login != "null":
            identities[email] = login
            return login
    identities[email] = name  # fallback: git author name verbatim
    return name


def blame_lines(path):
    """(email, author name) per line of the file at the submodule HEAD.

    Move/copy-detecting blame (`-C -C -M`): a line that was RELOCATED from
    another file in the same commit (e.g. the 2022 module split of Theory.hs
    into ClosedTheory/Prover/Rule/…) is attributed to the line's ORIGINAL
    author, not the author who moved it. This is accurate provenance — moved
    code belongs to who wrote it — and it keeps a pure relocator off the
    permission ask-list without a discretionary judgement. `-C -C` catches
    same-commit cross-file moves; `-M` catches within-file moves. (A third
    `-C` also scans unrelated historical files but is ~10x slower for no
    change on this tree, so it is not used.)"""
    lines, author = [], None
    for line in git(["blame", "-C", "-C", "-M", "--line-porcelain",
                     "HEAD", "--", path]).splitlines():
        if line.startswith("author "):
            author = line[7:]
        elif line.startswith("author-mail "):
            lines.append((line[12:].strip("<>"), author))
    return lines


def merge_name_fallbacks(identities, names_by_email):
    """An author with several emails may resolve to a username on one email
    and fall back to their git name on another.  Collapse: if a fallback
    label equals the git author name behind a username-resolved email, remap
    it to that username."""
    name_to_user = {}
    for email, ident in identities.items():
        if "@" not in ident and email in names_by_email:
            if ident != names_by_email[email]:  # ident is a username
                name_to_user[names_by_email[email]] = ident
            m = re.match(r"(?:\d+\+)?([^@]+)@users\.noreply\.github\.com", email)
            if m:
                name_to_user.setdefault(names_by_email[email], ident)
    remap = {n: u for n, u in name_to_user.items() if n in
             {i for i in identities.values()}}
    for email, ident in list(identities.items()):
        if ident in remap:
            identities[email] = remap[ident]


def scope_indices(scope, n_lines):
    if scope is None:
        return range(n_lines)
    return sorted({i for lo, hi in scope
                   for i in range(max(lo - 1, 0), min(hi, n_lines))})


def format_source(path, scope):
    if scope is None:
        return path
    return path + ":" + ",".join(f"{lo}-{hi}" for lo, hi in sorted(scope))


def strip_header(src):
    """Drop a leading generated header: the run of plain `//` lines starting
    at the sentinel, plus the blank line separating it from the body.  Doc
    comments (`//!`, `///`) and code end the run, so a header whose blank
    separator has been edited away costs no body text."""
    if not src.startswith(HEADER_SENTINEL):
        return src
    lines = src.splitlines(keepends=True)
    i = 0
    while (i < len(lines) and lines[i].startswith("//")
           and not lines[i].startswith(("//!", "///"))):
        i += 1
    if i < len(lines) and not lines[i].strip():
        i += 1
    return "".join(lines[i:])


def target_sources(rs_arg, per_file):
    rs = os.path.abspath(rs_arg)
    if rs not in per_file:
        die(f"{rs_arg} is not a .rs file under {CRATES}")
    return per_file[rs][1]


def report_authors(rs_arg, per_file, refresh):
    """Print a tab-separated line count and author for every upstream author
    of one file's cited scopes, most lines first, then the sources those
    counts came from."""
    sources = target_sources(rs_arg, per_file)
    if not sources:
        print("(no upstream citations: this file carries no header and awaits "
              "no permission)")
        return
    head = submodule_head()
    identities = load_identities()
    cached = dict(identities)

    blames, names_by_email = {}, {}
    for h in sorted(sources):
        blames[h] = blame_lines(h)
        if not blames[h]:
            die(f"git blame produced no lines for {h} at {SUB} {head[:8]}: "
                "refusing to report an author list that would read as "
                "'no permission needed'")
    for lines in blames.values():
        for email, name in lines:
            if email in SELF_EMAILS:
                continue
            names_by_email[email] = name
            identify(email, name, identities, refresh)
    merge_name_fallbacks(identities, names_by_email)
    if identities != cached:
        json.dump(identities, open(CACHE_OUT, "w"), indent=1, sort_keys=True)

    agg, blamed = collections.Counter(), 0
    for h in sorted(sources):
        indices = scope_indices(sources[h], len(blames[h]))
        blamed += len(indices)
        for i in indices:
            email, name = blames[h][i]
            if email in SELF_EMAILS:
                continue
            agg[identities.get(email, name)] += 1
    if not blamed:
        cited = ", ".join(format_source(h, sources[h]) for h in sorted(sources))
        die(f"every cited span of {rs_arg} lies outside its source at "
            f"{head[:8]} ({cited}): refusing to report an author list that "
            "would read as 'no permission needed'")
    for ident, n in sorted(agg.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"{n}\t{ident}")
    if not agg:
        print("(no upstream authors: every blamed line of the cited scopes is "
              "the porting author's)")
    print("sources: " + ", ".join(format_source(h, sources[h])
                                  for h in sorted(sources)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any header is stale")
    ap.add_argument("--preview", metavar="RS_FILE",
                    help="print the header RS_FILE would get")
    ap.add_argument("--authors", metavar="RS_FILE",
                    help="rank the upstream authors of RS_FILE's cited sources")
    ap.add_argument("--refresh-identities", action="store_true",
                    help="with --authors: re-query GitHub for unknown emails")
    args = ap.parse_args()

    # `is not None`, not truthiness: an empty --preview/--authors argument is
    # a mode selection too, and must not fall through to the rewrite.
    modes = [args.check, args.preview is not None, args.authors is not None]
    if sum(modes) > 1:
        ap.error("--check, --preview and --authors are mutually exclusive")
    if args.refresh_identities and args.authors is None:
        ap.error("--refresh-identities is only meaningful with --authors: no "
                 "other mode resolves author identities")

    per_file = scan_sources(hs_files())

    if args.authors is not None:
        report_authors(args.authors, per_file, args.refresh_identities)
        return
    if args.preview is not None:
        sources = target_sources(args.preview, per_file)
        sys.stdout.write(HEADER if sources else "(no header: no upstream citations)\n")
        return

    changed, stale = 0, []
    for rs, (text, sources) in sorted(per_file.items()):
        body = strip_header(text)
        new = (HEADER + body) if sources else body
        if new != text:
            stale.append(os.path.relpath(rs, REPO))
            if not args.check:
                open(rs, "w", encoding="utf-8").write(new)
                changed += 1

    if args.check:
        for f in stale:
            print(f"STALE: {f}")
        print(f"{len(stale)} stale header(s)")
        sys.exit(1 if stale else 0)
    print(f"updated {changed} file(s)")


if __name__ == "__main__":
    main()
