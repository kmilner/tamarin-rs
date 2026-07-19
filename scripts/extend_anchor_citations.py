#!/usr/bin/env python3
"""Extend single-line Haskell anchor citations to declaration ranges.

Rewrites `Foo.hs:162` (an anchor at a function) in Rust comment lines to
`Foo.hs:150-183, see line 162` where 150-183 is the extent of the top-level
Haskell declaration containing line 162, computed at the pinned submodule
HEAD (so extents line up with `git blame HEAD`).  If the anchor IS the
declaration's first line, the `, see line N` suffix is dropped.

Only comment lines are touched (string literals reproducing GHC CallStack
paths etc. are left alone).  Anchors that land in the module header/import
region, or in files that cannot be resolved uniquely, are left unchanged
and reported.

Usage: anchor_extend.py [--apply] [--exclude-crate NAME]...
Default is a dry run printing every planned rewrite.
"""
import argparse
import bisect
import collections
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUB = os.path.join(REPO, "tamarin-prover")
CRATES = os.path.join(REPO, "crates")

ANCHOR = re.compile(r"([A-Za-z][A-Za-z0-9_/.]*\.hs):(\d+)(?![-\d:])")
KEYWORDS = ("data ", "type ", "newtype ", "class ", "instance ", "foreign ",
            "deriving ", "infixl", "infixr", "infix ")
HEADERISH = ("module ", "import ", "{-# LANGUAGE", "{-# OPTIONS")

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


def git_show(path):
    r = subprocess.run(["git", "show", f"HEAD:{path}"], cwd=SUB,
                       capture_output=True, text=True)
    return r.stdout.splitlines() if r.returncode == 0 else None


def hs_tree():
    out = subprocess.run(["git", "ls-files", "*.hs"], cwd=SUB,
                         capture_output=True, text=True).stdout
    return out.split()


def decl_name(line):
    s = line.rstrip()
    for kw in KEYWORDS:
        if s.startswith(kw):
            return s  # keyword decls never merge: identity is the whole head
    m = re.match(r"([A-Za-z_][A-Za-z0-9_']*|\([^)]+\))", s)
    return m.group(1) if m else s


def decl_groups(lines):
    """[(start_line, end_line, name)] 1-based, covering the whole file.
    Consecutive groups with the same value-level name (signature + equations)
    are merged."""
    starts = []
    for i, line in enumerate(lines, 1):
        if not line or line[0] in " \t":
            continue
        if line.startswith(("--", "{-", "#", "}")):
            continue
        if any(line.startswith(h) for h in HEADERISH):
            starts.append((i, "<header>"))
            continue
        starts.append((i, decl_name(line)))
    if not starts:
        return []
    groups = []
    for j, (s, name) in enumerate(starts):
        e = (starts[j + 1][0] - 1) if j + 1 < len(starts) else len(lines)
        if groups and groups[-1][2] == name and name != "<header>":
            groups[-1] = (groups[-1][0], e, name)
        elif groups and name == "<header>" and groups[-1][2] == "<header>":
            groups[-1] = (groups[-1][0], e, name)
        else:
            groups.append((s, e, name))
    return groups


def trim_extent(lines, s, e):
    while e > s and (not lines[e - 1].strip()
                     or lines[e - 1].lstrip().startswith("--")):
        e -= 1
    return s, e


def resolve(cite, crate, tree, local_hint):
    c = cite.lstrip("./")
    m = [h for h in tree if h == c or h.endswith("/" + c)]
    if len(m) > 1:
        hinted = [h for h in m if h in local_hint]
        if len(hinted) == 1:
            return hinted[0]
        pref = [h for h in m if CRATE_PREF.get(crate, lambda x: False)(h)]
        if len(pref) == 1:
            return pref[0]
        return None
    return m[0] if m else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--exclude-crate", action="append", default=[])
    args = ap.parse_args()

    tree = hs_tree()
    file_lines, file_groups = {}, {}
    stats = collections.Counter()
    unresolved = []

    def groups_for(path):
        if path not in file_groups:
            lines = git_show(path)
            file_lines[path] = lines
            file_groups[path] = decl_groups(lines) if lines else []
        return file_groups[path]

    for dirpath, dirs, files in os.walk(CRATES):
        dirs[:] = [d for d in dirs if d != "target"]
        for fname in files:
            if not fname.endswith(".rs"):
                continue
            rs = os.path.join(dirpath, fname)
            crate = os.path.relpath(rs, CRATES).split(os.sep)[0]
            if crate in args.exclude_crate:
                stats["files_excluded"] += 1
                continue
            src = open(rs, encoding="utf-8", errors="replace").read()
            if not ANCHOR.search(src):
                continue
            # local hint: full paths already cited in this file disambiguate
            local_hint = set(re.findall(r"(?:lib|src)/[A-Za-z0-9_/.]*\.hs", src))
            local_hint = {h for c in local_hint for h in tree
                          if h == c or h.endswith("/" + c)}
            out, changed = [], False
            for line in src.splitlines(keepends=True):
                if not line.lstrip().startswith("//"):
                    out.append(line)
                    continue

                def sub(m):
                    cite, n = m.group(1), int(m.group(2))
                    path = resolve(cite, crate, tree, local_hint)
                    if path is None:
                        # tiebreak ambiguity: the anchor line must land in a
                        # real (non-header) declaration; if that holds in
                        # exactly one candidate, it is the cited file
                        c = cite.lstrip("./")
                        cands = [h for h in tree if h == c or h.endswith("/" + c)]
                        valid = []
                        for h in cands:
                            gs = groups_for(h)
                            if gs and n <= len(file_lines[h]):
                                idx = bisect.bisect_right([g[0] for g in gs], n) - 1
                                if idx >= 0 and gs[idx][2] != "<header>":
                                    valid.append(h)
                        if len(valid) == 1:
                            path = valid[0]
                    if path is None:
                        stats["anchor_unresolvable_file"] += 1
                        unresolved.append((rs, m.group(0), "ambiguous/missing file"))
                        return m.group(0)
                    groups = groups_for(path)
                    if not groups or n > len(file_lines[path]):
                        stats["anchor_bad_line"] += 1
                        unresolved.append((rs, m.group(0), "line out of range"))
                        return m.group(0)
                    idx = bisect.bisect_right([g[0] for g in groups], n) - 1
                    if idx < 0:
                        idx = 0
                    s, e, name = groups[idx]
                    if name == "<header>":
                        stats["anchor_in_header"] += 1
                        unresolved.append((rs, m.group(0), "module header region"))
                        return m.group(0)
                    s, e = trim_extent(file_lines[path], s, e)
                    stats["anchor_rewritten"] += 1
                    if n == s:
                        return f"{cite}:{s}-{e}"
                    return f"{cite}:{s}-{e}, see line {n}"

                new_line = ANCHOR.sub(sub, line)
                if new_line != line:
                    changed = True
                out.append(new_line)
            if changed:
                stats["files_changed"] += 1
                if args.apply:
                    open(rs, "w", encoding="utf-8").write("".join(out))
                else:
                    for old, new in zip(src.splitlines(), "".join(out).splitlines()):
                        if old != new:
                            print(f"{os.path.relpath(rs, REPO)}:")
                            print(f"  - {old.strip()[:130]}")
                            print(f"  + {new.strip()[:130]}")

    for k, v in sorted(stats.items()):
        print(f"{k}: {v}", file=sys.stderr)
    if unresolved:
        print(f"\nUNRESOLVED ({len(unresolved)}):", file=sys.stderr)
        for rs, cite, why in unresolved[:40]:
            print(f"  {os.path.relpath(rs, REPO)}: {cite} ({why})", file=sys.stderr)


if __name__ == "__main__":
    main()
