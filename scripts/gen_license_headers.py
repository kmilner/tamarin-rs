#!/usr/bin/env python3
"""Regenerate the per-file GPL-permission headers on ported Rust sources.

Scans crates/**/*.rs for citations of upstream tamarin-prover Haskell files
(`Foo.hs`, `path/Foo.hs:123-456`, or dotted module paths like
`Theory.Constraint.Solver.AnnotatedGoals`), resolves them against the
submodule tree, blames the cited files at the pinned submodule HEAD, and
writes a header naming the upstream authors (GitHub usernames where known)
whose permission the file's derived content awaits.  Files with no upstream
citations get no header; stale headers are stripped.  Idempotent.

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
  scripts/gen_license_headers.py --refresh-identities   # re-query GitHub
                                             # (gh CLI) for unknown emails

Identity resolution order: committed cache (scripts/header_identities.json)
-> username embedded in @users.noreply.github.com emails -> GitHub commits
API via `gh` (only with --refresh-identities) -> git author name verbatim.
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

HEADER1 = "// Currently GPL 3.0 until granted permission by the following authors:"
SOURCES_LINE = "// Ported from upstream tamarin-prover sources:"
MIN_LINES = 10          # authors below this per-file line count fold into the tail note
WRAP = 72

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


def git(args, cwd=SUB):
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                          text=True, check=False).stdout


def hs_files():
    return git(["ls-files", "*.hs"]).split()


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
        out = subprocess.run(
            ["gh", "api", f"/repos/{UPSTREAM_REPO}/commits?author={email}&per_page=1",
             "-q", ".[0].author.login"],
            capture_output=True, text=True)
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
    return sorted({i for lo, hi in scope for i in range(lo - 1, min(hi, n_lines))})


def wrap_comment(text):
    words, lines, cur = text.split(" "), [], "//  "
    for w in words:
        if len(cur) + len(w) + 1 > WRAP and cur.strip("/ "):
            lines.append(cur)
            cur = "//  "
        cur += " " + w
    lines.append(cur)
    return lines


def build_header(authors, sources):
    ranked = sorted(authors.items(), key=lambda kv: (-kv[1], kv[0]))
    major = [a for a, n in ranked if n >= MIN_LINES]
    minor = any(n < MIN_LINES for _, n in authors.items())
    names = ", ".join(major)
    if minor:
        names += ", and other minor contributors (see upstream git history)"
    if not major and minor:
        names = ("only minor contributions per cited ranges "
                 "(see upstream git history)")
    out = [HEADER1, *wrap_comment(names), SOURCES_LINE,
           *wrap_comment(", ".join(sorted(sources)))]
    return "\n".join(out) + "\n\n"


def strip_header(src):
    if src.startswith(HEADER1):
        return src.split("\n\n", 1)[1] if "\n\n" in src else ""
    return src


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--preview", metavar="RS_FILE")
    ap.add_argument("--refresh-identities", action="store_true")
    args = ap.parse_args()

    tree = hs_files()
    identities = load_identities()
    global_qualified = set()
    per_file = {}

    for rs in rust_files():
        body = strip_header(open(rs, encoding="utf-8", errors="replace").read())
        crate = os.path.relpath(rs, CRATES).split(os.sep)[0]
        resolved, ambiguous = resolve_citations(body, crate, tree, global_qualified)
        per_file[rs] = (body, crate, resolved, ambiguous)

    blame_cache, names_by_email = {}, {}
    file_sources = {}
    for rs, (body, crate, resolved, ambiguous) in per_file.items():
        sources = disambiguate(dict(resolved), ambiguous, crate, global_qualified)
        file_sources[rs] = sources
        for h in sources:
            if h not in blame_cache:
                blame_cache[h] = blame_lines(h)
    for lines in blame_cache.values():
        for email, name in lines:
            if email in SELF_EMAILS:
                continue
            names_by_email[email] = name
            identify(email, name, identities, args.refresh_identities)
    merge_name_fallbacks(identities, names_by_email)

    changed, stale = 0, []
    for rs, (body, crate, resolved, ambiguous) in sorted(per_file.items()):
        sources = file_sources[rs]
        agg = collections.Counter()
        for h in sorted(sources):
            lines = blame_cache[h]
            for i in scope_indices(sources[h], len(lines)):
                email, name = lines[i]
                if email in SELF_EMAILS:
                    continue
                agg[identities.get(email, name)] += 1
        new = (build_header(agg, sources) + body) if sources and agg else body
        if args.preview and os.path.abspath(args.preview) == rs:
            print(new[:len(new) - len(body)] if sources and agg
                  else "(no header: no cited-author lines)")
            return
        cur = open(rs, encoding="utf-8", errors="replace").read()
        if new != cur:
            stale.append(os.path.relpath(rs, REPO))
            if not args.check:
                open(rs, "w", encoding="utf-8").write(new)
                changed += 1

    json.dump(identities, open(CACHE_OUT, "w"), indent=1, sort_keys=True)
    if args.preview:
        print(f"preview: {args.preview} not found under crates/", file=sys.stderr)
        sys.exit(2)
    if args.check:
        for f in stale:
            print(f"STALE: {f}")
        print(f"{len(stale)} stale header(s)")
        sys.exit(1 if stale else 0)
    print(f"updated {changed} file(s); identities cached: {len(identities)}")


if __name__ == "__main__":
    main()
