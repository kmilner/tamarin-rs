#!/usr/bin/env python3
"""Compare two web-crawl manifests (HS oracle vs RS) at the semantic level.

For each idx-normalized URL in the union of both manifests:
  - only in HS  -> MISSING_RS  (RS never produced/visited this URL)
  - only in RS  -> MISSING_HS  (RS produced an extra URL)
  - in both     -> canonicalize both bodies (by the HS/oracle kind) and
                   compare: MATCH | DIFF (also flags status/kind mismatch)

Emits a TSV (url<TAB>status<TAB>hs_http<TAB>rs_http<TAB>kind) and, per DIFF,
a unified diff of the two canonical forms under <diffdir>/ for inspection.

A side whose crawl hit web_crawl.py's --max-nodes cap gets its own
`CAPPED_HS` / `CAPPED_RS` row: the pages past the cap were never fetched, so
the URL rows below cover only part of the theory and a truncated crawl must
not read as a complete one.

Usage: web_diff.py HS.json RS.json OUT.tsv [DIFFDIR]
"""
import difflib
import hashlib
import json
import os
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from web_normalize import canon  # noqa: E402


def load(p):
    with open(p, encoding="utf-8") as f:
        return json.load(f)


def safe_name(url):
    readable = url.replace("://", "_").replace("/", "_").replace("?", "_")
    # URLs routinely share a long proof-path prefix. Truncation alone made
    # distinct rows overwrite the same artifact; retain a readable prefix and
    # append identity from the complete URL.
    digest = hashlib.sha256(url.encode("utf-8")).hexdigest()[:16]
    return f"{readable[:150]}__{digest}"


def main():
    if len(sys.argv) < 4:
        print("usage: web_diff.py HS.json RS.json OUT.tsv [DIFFDIR]", file=sys.stderr)
        sys.exit(2)
    # `manifest` holds URL rows only: web_crawl.py's `__plan_version__` stamp
    # is a TOP-LEVEL sibling of it (beside base/lemmas/log/capped), so the URL
    # union below never sees it and cannot report it as a MISSING_* row.
    hs_doc = load(sys.argv[1])
    rs_doc = load(sys.argv[2])
    hs = hs_doc["manifest"]
    rs = rs_doc["manifest"]
    out_tsv = sys.argv[3]
    diffdir = sys.argv[4] if len(sys.argv) > 4 else None
    if diffdir:
        os.makedirs(diffdir, exist_ok=True)

    # Unpaired probe family: the three graph routes at case index 0/0.  The
    # backends deliberately disagree there (upstream's unchecked `!!` answers
    # a 500 exception page, the port answers Not Found — see the divergence
    # notes in tamarin-server handlers/theory.rs), so the rows pair as
    # neither MATCH nor a defect.  web_crawl.py does not probe them; cached
    # HS manifests can still carry the rows, which are dropped here rather
    # than surfacing as MISSING_RS.
    unpaired_case_routes = ("/json/cases/", "/graph/cases/",
                            "/interactive-graph-def/cases/")
    urls = [u for u in sorted(set(hs) | set(rs))
            if not (u.endswith("/0/0")
                    and any(r in u for r in unpaired_case_routes))]
    rows = []
    counts = {}
    # Truncation gets rows of its own, kept apart from the comparison rows so
    # they cannot pad the TOTAL.  web_crawl.py stamps `capped` when it dropped
    # proof-node visits at --max-nodes; until now that flag reached nobody, and
    # a theory crawled down to the cap produced a page of MATCHes for the part
    # that was visited and silence for the part that was not.
    # A manifest predating the flag carries no `capped` key: absent means
    # unknown, and claiming "not truncated" for it is exactly what these rows
    # exist to prevent — telling the two apart is the crawl-plan stamp's job
    # (web_parity.sh re-crawls a manifest from an older plan).
    capped_rows = []
    for side, doc in (("HS", hs_doc), ("RS", rs_doc)):
        if doc.get("capped"):
            status = f"CAPPED_{side}"
            capped_rows.append(("-", status, "-", "-", "-"))
            counts[status] = counts.get(status, 0) + 1
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
                # keepends: the graph and text routes are compared byte for
                # byte, and `splitlines()` throws away the line terminators —
                # a body that differs only by a trailing newline then produced
                # an EMPTY diff beside a DIFF row, which reads as the differ
                # having failed rather than as the divergence it is.
                ud = difflib.unified_diff(
                    ch.splitlines(keepends=True), cr.splitlines(keepends=True),
                    fromfile="HS", tofile="RS")
                with open(os.path.join(diffdir, safe_name(u) + ".diff"), "w",
                          encoding="utf-8") as f:
                    f.write(f"# URL {u}\n{extra}" + "".join(ud) + "\n")
        rows.append((u, status, str(h["status"]), str(r["status"]), kind))
        counts[status] = counts.get(status, 0) + 1

    rows.sort()
    with open(out_tsv, "w", encoding="utf-8") as f:
        for row in capped_rows + rows:
            f.write("\t".join(row) + "\n")

    total = len(rows)
    print("=== web-parity summary ===")
    for k in ("MATCH", "DIFF", "MISSING_RS", "MISSING_HS",
              "CAPPED_HS", "CAPPED_RS"):
        if k in counts:
            print(f"  {k:12s} {counts[k]:5d}")
    print(f"  {'TOTAL':12s} {total:5d}"
          + ("   (TRUNCATED CRAWL — the rows below the cap were never fetched)"
             if capped_rows else ""))
    print(f"  tsv: {out_tsv}" + (f"  diffs: {diffdir}" if diffdir else ""))


if __name__ == "__main__":
    main()
