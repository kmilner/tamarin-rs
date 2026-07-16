#!/usr/bin/env python3
"""Compare two web-crawl manifests (HS oracle vs RS) at the semantic level.

For each idx-normalized URL in the union of both manifests:
  - only in HS  -> MISSING_RS  (RS never produced/visited this URL)
  - only in RS  -> MISSING_HS  (RS produced an extra URL)
  - in both     -> canonicalize both bodies (by the HS/oracle kind) and
                   compare: MATCH | DIFF (also flags status/kind mismatch)

Emits a TSV (url<TAB>status<TAB>hs_http<TAB>rs_http<TAB>kind) and, per DIFF,
a unified diff of the two canonical forms under <diffdir>/ for inspection.

Usage: web_diff.py HS.json RS.json OUT.tsv [DIFFDIR]
"""
import difflib
import json
import os
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from web_normalize import canon  # noqa: E402


def load(p):
    with open(p, encoding="utf-8") as f:
        return json.load(f)


def safe_name(url):
    return url.replace("://", "_").replace("/", "_").replace("?", "_")[:180]


def main():
    if len(sys.argv) < 4:
        print("usage: web_diff.py HS.json RS.json OUT.tsv [DIFFDIR]", file=sys.stderr)
        sys.exit(2)
    hs = load(sys.argv[1])["manifest"]
    rs = load(sys.argv[2])["manifest"]
    out_tsv = sys.argv[3]
    diffdir = sys.argv[4] if len(sys.argv) > 4 else None
    if diffdir:
        os.makedirs(diffdir, exist_ok=True)

    urls = sorted(set(hs) | set(rs))
    rows = []
    counts = {}
    for u in urls:
        h = hs.get(u)
        r = rs.get(u)
        if h and not r:
            status = "MISSING_RS"
            rows.append((u, status, str(h["status"]), "-", h["kind"]))
            counts[status] = counts.get(status, 0) + 1
            continue
        if r and not h:
            status = "MISSING_HS"
            rows.append((u, status, "-", str(r["status"]), r["kind"]))
            counts[status] = counts.get(status, 0) + 1
            continue
        kind = h["kind"]  # oracle kind
        ch = canon(kind, h["body"])
        cr = canon(kind, r["body"])
        kind_mismatch = h["kind"] != r["kind"]
        status_mismatch = h["status"] != r["status"]
        if ch == cr and not kind_mismatch and not status_mismatch:
            status = "MATCH"
        else:
            status = "DIFF"
            if diffdir:
                extra = ""
                if kind_mismatch:
                    extra += f"# KIND MISMATCH hs={h['kind']} rs={r['kind']}\n"
                if status_mismatch:
                    extra += f"# HTTP MISMATCH hs={h['status']} rs={r['status']}\n"
                ud = difflib.unified_diff(
                    ch.splitlines(), cr.splitlines(),
                    fromfile="HS", tofile="RS", lineterm="")
                with open(os.path.join(diffdir, safe_name(u) + ".diff"), "w",
                          encoding="utf-8") as f:
                    f.write(f"# URL {u}\n{extra}" + "\n".join(ud) + "\n")
        rows.append((u, status, str(h["status"]), str(r["status"]), kind))
        counts[status] = counts.get(status, 0) + 1

    rows.sort()
    with open(out_tsv, "w", encoding="utf-8") as f:
        for row in rows:
            f.write("\t".join(row) + "\n")

    total = len(rows)
    print("=== web-parity summary ===")
    for k in ("MATCH", "DIFF", "MISSING_RS", "MISSING_HS"):
        if k in counts:
            print(f"  {k:12s} {counts[k]:5d}")
    print(f"  {'TOTAL':12s} {total:5d}")
    print(f"  tsv: {out_tsv}" + (f"  diffs: {diffdir}" if diffdir else ""))


if __name__ == "__main__":
    main()
