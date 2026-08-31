#!/usr/bin/env python3
"""Drive one running Tamarin interactive server and capture a response manifest.

Deterministic click-through crawl:
  1. discover lemmas from the theory-1 overview
  2. hit the static routes (overview/source/message/rules/tactic/cases/help)
  3. autoprove every lemma (tracking the incrementing theory idx via each
     autoprove's JSON `redirect`)
  4. harvest the fully-proved theory's per-lemma overview left-pane as the
     site map (every `main/*` link — proof nodes, methods, add/edit/delete,
     cases, …)
  5. GET every site-map URL; for each `main/proof/...` node also GET the
     `interactive-graph-def/...` (DOT), `json/...` (JSON graph) and
     `intdot/...` (HTML shell) variants
  6. also exercise next/prev on the lemma roots

Writes a JSON manifest {norm_url: {kind, status, body}} keyed by
idx-normalized URL, for web_diff.py to compare across HS and RS, stamped with
the `PLAN_VERSION` of the crawl plan that produced it.

Pure stdlib (urllib, json, re).  Usage:
  web_crawl.py BASE_URL OUT_MANIFEST.json [--max-nodes N]
"""
import json
import os
import re
import sys
import time
import urllib.request
import urllib.error

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from web_normalize import norm_url_key  # noqa: E402

# Per-request timeout.  60s was too small for legitimately-slow autoproves
# (Yubikey slightly_weaker_invariant, eccDAA, opc_ua) — a capped autoprove
# freezes the lemma at its replayed skeleton and poisons the comparison.
# web_parity.sh's FILE_TIMEOUT (300s default) still caps the WHOLE crawl,
# so a genuinely-hung page is bounded regardless.
TIMEOUT = int(os.environ.get("WEB_CRAWL_TIMEOUT", "120"))
MAX_NODES_DEFAULT = int(os.environ.get("WEB_CRAWL_MAX_NODES", "400"))

# Version of the URL PLAN below, stamped into every manifest under
# PLAN_VERSION_KEY (a top-level sibling of "manifest", never a URL row).
# v2 = statics + source cases + per-lemma roots/next/prev + autoprove + sitemap ×4 variants.
# web_parity.sh includes this value in its HS cache profile. Bump it whenever
# the plan adds URLs; the new plan then selects a distinct profile instead of
# mistaking an old manifest's unvisited URL families for MISSING_HS rows.
# Dropping URLs from the plan needs no bump: a cached manifest is then a
# superset, and web_diff.py drops the unpaired rows (the graph-route 0/0
# probes) before pairing.
PLAN_VERSION = 2
PLAN_VERSION_KEY = "__plan_version__"


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None  # don't follow; we want to see the 3xx


_OPENER = urllib.request.build_opener(NoRedirect)


def http_get(base, path):
    """Return (status, content_type, body_text)."""
    url = base + path
    req = urllib.request.Request(url, method="GET")
    try:
        with _OPENER.open(req, timeout=TIMEOUT) as r:
            ct = r.headers.get("Content-Type", "")
            body = r.read().decode("utf-8", "replace")
            return r.status, ct, body
    except urllib.error.HTTPError as e:
        ct = e.headers.get("Content-Type", "") if e.headers else ""
        body = ""
        try:
            body = e.read().decode("utf-8", "replace")
        except Exception:
            pass
        return e.code, ct, body
    except Exception as e:  # noqa: BLE001
        return 0, "", f"REQUEST_ERROR: {e!r}"


def http_get_retry(base, path, attempts=3, backoff=2.0):
    """`http_get` with retries on transient failures (timeout / 5xx / conn
    err).  Used for the step-1 lemma-discovery fetch, where a transient
    failure would otherwise cache an empty-lemma stub manifest."""
    status, ct, body = 0, "", ""
    for i in range(attempts):
        status, ct, body = http_get(base, path)
        if status and status < 500 and not body.startswith("REQUEST_ERROR"):
            return status, ct, body
        time.sleep(backoff * (i + 1))
    return status, ct, body


def kind_of(path, ct):
    if "/interactive-graph-def/" in path or "/graph/" in path:
        # graph route is DOT text (or, on the img route, an svg — treat as dot)
        return "dot"
    if "application/json" in ct:
        return "json"
    if "text/html" in ct:
        return "html"
    return "text"


def idx_of(url_or_path, default):
    m = re.search(r"/thy/trace/(\d+)/", url_or_path)
    return int(m.group(1)) if m else default


def hrefs(body):
    return re.findall(r'href="([^"]*)"', body)


def main():
    if len(sys.argv) < 3:
        print("usage: web_crawl.py BASE OUT.json [--max-nodes N] [--allow-no-lemmas]",
              file=sys.stderr)
        sys.exit(2)
    base = sys.argv[1].rstrip("/")
    out_path = sys.argv[2]
    allow_no_lemmas = "--allow-no-lemmas" in sys.argv
    max_nodes = MAX_NODES_DEFAULT
    if "--max-nodes" in sys.argv:
        max_nodes = int(sys.argv[sys.argv.index("--max-nodes") + 1])

    manifest = {}   # norm_url -> {kind,status,body}
    log = []

    def record(path):
        status, ct, body = http_get(base, path)
        k = kind_of(path, ct)
        manifest[norm_url_key(path)] = {"kind": k, "status": status, "body": body}
        return status, ct, body

    idx = 1
    # 1. discover lemmas from the RECORDED theory-1 overview (retry on
    # transient failure; a silent empty discovery poisons the whole crawl).
    status, ct, ov = http_get_retry(base, f"/thy/trace/{idx}/overview/help")
    manifest[norm_url_key(f"/thy/trace/{idx}/overview/help")] = {
        "kind": kind_of("overview/help", ct), "status": status, "body": ov}
    lemmas = []
    for h in hrefs(ov):
        m = re.match(r"/thy/trace/\d+/main/proof/([^/\"]+)$", h)
        if m and m.group(1) not in lemmas:
            lemmas.append(m.group(1))
    log.append(f"lemmas={lemmas}")
    if not lemmas and not allow_no_lemmas:
        print(f"ERROR: discovered 0 lemmas at {base} "
              f"(overview/help status={status}); refusing to write a stub manifest",
              file=sys.stderr)
        sys.exit(3)

    # 2. static routes (overview/help already recorded in step 1)
    for r in ["source", "message", "main/rules", "main/help",
              "main/message", "main/tactic"]:
        record(f"/thy/trace/{idx}/{r}")

    # Source cases, on every route that renders them: the sources pane, the
    # JSON graph and the two dot routes.  `0/0` is the index the left-pane nav
    # link carries; the sources pane renders it (both backends index off the
    # front of the case list there) so it stays crawled on `main`.  On the
    # three graph routes the backends deliberately disagree about it —
    # upstream's unchecked `!!` raises a 500 exception page, the port answers
    # Not Found (see the divergence notes in tamarin-server
    # handlers/theory.rs) — so it is not probed there; the port's behaviour is
    # pinned by the server's own route tests.  `1/1` is the first real case,
    # which every route draws.
    for route in ["main", "json", "graph", "interactive-graph-def"]:
        cases = ["0/0", "1/1"] if route == "main" else ["1/1"]
        for kind in ["raw", "refined"]:
            for case in cases:
                record(f"/thy/trace/{idx}/{route}/cases/{kind}/{case}")

    # per-lemma root main + lemma views + graph at root
    for L in lemmas:
        record(f"/thy/trace/{idx}/main/lemma/{L}")
        record(f"/thy/trace/{idx}/main/proof/{L}")
        record(f"/thy/trace/{idx}/interactive-graph-def/proof/{L}")
        record(f"/thy/trace/{idx}/json/proof/{L}")
        record(f"/thy/trace/{idx}/intdot/proof/{L}")
        # next/prev on the lemma root
        record(f"/thy/trace/{idx}/next/normal/proof/{L}")
        record(f"/thy/trace/{idx}/prev/normal/proof/{L}")

    # 3. autoprove each lemma, tracking idx
    for L in lemmas:
        status, ct, body = record(f"/thy/trace/{idx}/autoprove/idfs/0/False/proof/{L}")
        try:
            j = json.loads(body)
        except Exception:
            j = {}
        if isinstance(j, dict) and "redirect" in j:
            idx = idx_of(j["redirect"], idx)
    log.append(f"final_idx_after_autoprove={idx}")

    # 4. build sitemap from each lemma's fully-proved overview
    sitemap = []
    seen = set()
    for L in lemmas:
        # Through record(), so the page lands in the manifest with the status
        # and content-type the server actually answered.  Hand-writing the row
        # with a hardcoded 200 made web_diff's HTTP comparison inert on exactly
        # the pages that drive the rest of the crawl: one side could 500 here
        # and, as long as its error page canonicalized like the other's, the row
        # still read MATCH.
        _, _, ov = record(f"/thy/trace/{idx}/overview/proof/{L}")
        for h in hrefs(ov):
            if "/main/" not in h:
                continue
            # strip the idx to a canonical relative path with current idx
            rel = re.sub(r"^/thy/trace/\d+/", f"/thy/trace/{idx}/", h)
            key = norm_url_key(rel)
            if key in seen:
                continue
            seen.add(key)
            sitemap.append(rel)

    # 5. visit sitemap
    proof_nodes = [p for p in sitemap if "/main/proof/" in p]
    others = [p for p in sitemap if "/main/proof/" not in p]
    capped = False
    if len(proof_nodes) > max_nodes:
        capped = True
        log.append(f"CAPPED proof-node visits {len(proof_nodes)} -> {max_nodes}")
        proof_nodes = proof_nodes[:max_nodes]
    for p in others:
        record(p)
    for p in proof_nodes:
        record(p)
        # same node under the DOT, JSON-graph and HTML-shell routes
        for route in ("interactive-graph-def", "json", "intdot"):
            record(p.replace("/main/proof/", f"/{route}/proof/"))

    # A dead or dying server (OOM-guard kill, per-request heap exhaustion)
    # yields REQUEST_ERROR bodies; a manifest containing them would be cached
    # as valid and poison every later comparison against this theory.
    errored = [u for u, e in manifest.items()
               if e["body"].startswith("REQUEST_ERROR")]
    if errored:
        print(f"ERROR: {len(errored)} REQUEST_ERROR pages (first: {errored[0]}); "
              f"refusing to write a poisoned manifest", file=sys.stderr)
        sys.exit(3)

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump({"base": base, "lemmas": lemmas, "log": log,
                   "capped": capped, PLAN_VERSION_KEY: PLAN_VERSION,
                   "manifest": manifest}, f)
    print(f"crawled {len(manifest)} urls, {len(proof_nodes)} proof nodes"
          f"{' (CAPPED)' if capped else ''}; lemmas={len(lemmas)}", file=sys.stderr)


if __name__ == "__main__":
    main()
