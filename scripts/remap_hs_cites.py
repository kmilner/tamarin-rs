#!/usr/bin/env python3
"""Remap Haskell line cites in Rust comments across a submodule bump.

    scripts/remap_hs_cites.py --old <pin> --new <pin> [--apply] [file.rs ...]

Comments across crates/ cite upstream Haskell locations as `Foo.hs:12`,
`Foo.hs:150-183`, `Foo.hs:61-63,84,92` or `Foo.hs:150-183, see line 162`.
The numbers are relative to the pinned submodule, so a bump silently
invalidates any cite into a Haskell file the bump rewrote.  This tool maps
every cite through the `git diff <old> <new>` line mapping of its Haskell
file:

  * parts that fall outside every changed hunk get the pure line shift;
  * parts that land inside a changed hunk are re-anchored semantically: the
    old top-level declaration (extend_anchor_citations' `decl_groups`) is
    located by name in the new tree, exact-extent cites are rewritten to the
    declaration's new extent, and interior lines (`see line` targets,
    sub-range endpoints) are re-found by exact line-text match within it;
  * anything ambiguous is left untouched and reported as UNRESOLVED for a
    human pass.

Dry run by default (prints every planned rewrite); `--apply` edits in
place.  Only comment lines are touched — a cite is processed only when it
sits after `//` (or `#` in scripts) on its line.  Exit status is 0 unless
arguments are bad: unresolved cites are a report, not a failure, so the
bump flow never aborts on them.

Invoked automatically by scripts/bump_submodule.sh with the old and new
pins after the gitlink moves.
"""
import argparse
import importlib.util
import os
import re
import subprocess
import sys

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(SCRIPT_DIR)
SUB = os.path.join(REPO, "tamarin-prover")
CRATES = os.path.join(REPO, "crates")

_spec = importlib.util.spec_from_file_location(
    "extend_anchor_citations", os.path.join(SCRIPT_DIR, "extend_anchor_citations.py"))
_eac = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_eac)
decl_groups, trim_extent, resolve = _eac.decl_groups, _eac.trim_extent, _eac.resolve

# `<file>.hs:<parts>[, see line <n>[,<n>...]]` where parts is a comma-joined
# list of `N` / `N-M`.  A following `, Other.hs:...` cite never matches the
# parts tail (it does not start with a digit).
CITE = re.compile(
    r"([A-Za-z][A-Za-z0-9_/.']*\.hs):"
    r"(\d+(?:-\d+)?(?:,\d+(?:-\d+)?)*)"
    r"((?:, see line \d+(?:,\d+)*)?)")


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

    def remap_cite(self, path, parts, sees):
        """-> (new_parts, new_sees) or (None, reason)."""
        lm = self.linemap(path)
        old_groups = decl_groups(self.old_lines(path) or [])

        def target_decl():
            anchor = sees[0] if sees else parts[0][0]
            g = group_at(old_groups, anchor)
            if not g:
                return None
            cands = [ng for ng in self.new_groups(path) if ng[2] == g[2]]
            return (g, cands[0]) if len(cands) == 1 else None

        decl = None

        def map_line(l):
            nonlocal decl
            kind, v = lm.map(l)
            if kind == "keep":
                return v
            if decl is None:
                decl = target_decl()
            if decl:
                (_, _, _), (ns, ne, _) = decl[0], decl[1]
                return self.reanchor(path, l, ns, ne)
            return self.reanchor(path, l)

        new_parts = []
        for a, b in parts:
            # An exact old-declaration extent is rewritten to the new extent
            # even when only one endpoint sits in a hunk.
            if b is not None:
                g = group_at(old_groups, a)
                if g and (a, b) in {(g[0], g[1]),
                                    trim_extent(self.old_lines(path), g[0], g[1])}:
                    cands = [ng for ng in self.new_groups(path) if ng[2] == g[2]]
                    if len(cands) == 1:
                        ns, ne = trim_extent(self.new_lines(path), cands[0][0], cands[0][1])
                        new_parts.append((ns, ne))
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
        return (new_parts, new_sees), None


def comment_pos(line, fname):
    markers = ["//"] if fname.endswith(".rs") else ["#", "//"]
    return min((line.find(m) for m in markers if m in line), default=-1)


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

    for rs in rs_files(args.files):
        with open(rs) as f:
            src = f.read()
        crate = os.path.relpath(rs, CRATES).split(os.sep)[0]
        hint = {m for m in re.findall(r"[A-Za-z0-9_/.']+\.hs", src) if "/" in m}
        lines = src.split("\n")
        changed_any = False
        for i, line in enumerate(lines):
            cpos = comment_pos(line, rs)
            if cpos < 0:
                continue
            edits = []
            for m in CITE.finditer(line):
                if m.start() < cpos:
                    continue
                checked += 1
                path = resolve(m.group(1), crate, rm.old_tree, hint)
                if path is None or path not in rm.changed:
                    continue
                if path not in rm.new_tree:
                    unresolved.append((rs, i + 1, m.group(0), "file gone at new pin"))
                    continue
                parts = parse_parts(m.group(2))
                sees = [int(x) for x in re.findall(r"\d+", m.group(3))]
                res, why = rm.remap_cite(path, parts, sees)
                if res is None:
                    unresolved.append((rs, i + 1, m.group(0), why))
                    continue
                new_parts, new_sees = res
                if new_parts == parts and new_sees == sees:
                    continue
                see_txt = ", see line " + ",".join(map(str, new_sees)) if new_sees else ""
                repl = f"{m.group(1)}:{fmt_parts(new_parts)}{see_txt}"
                edits.append((m.start(), m.end(), repl, m.group(0)))
            for start, end, repl, old_txt in reversed(edits):
                rewrites.append((rs, i + 1, old_txt, repl))
                lines[i] = lines[i][:start] + repl + lines[i][end:]
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


if __name__ == "__main__":
    main()
