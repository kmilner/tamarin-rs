#!/usr/bin/env python3
"""Semantic normalizers for the web-parity gate (RS interactive UI vs HS).

The parity bar is *structural / semantic* equivalence, NOT byte-identity:
we canonicalize away whitespace, attribute order, JSON key order, DOT
serialization form, highlight `<span class="hl_*">` wrappers, `<br/>`/`<pre>`
cosmetic markup, and the genuinely nondeterministic env fields (theory idx,
timestamps, temp/cache-dir prefixes, absolute load paths).  What survives the
canonicalization must match: element structure, visible text, link hrefs +
text, form actions, embedded resource URLs, JSON values, and the DOT graph
(nodes/edges/clusters compared by label, not by serialization bytes).

Used by web_diff.py.  Pure stdlib (html.parser, json, re).
"""
import html
import json
import re
from html.parser import HTMLParser

# ---------------------------------------------------------------------------
# Env-field normalization (applied to every raw body + to URL keys)
# ---------------------------------------------------------------------------

# The theory idx increments on every server-side mutation (HS modifyTheory /
# RS clone) and is embedded in every link.  It is a server-internal handle,
# not user-meaningful, so we canonicalize it everywhere.
_IDX_RE = re.compile(r"/thy/trace/\d+/")
# Same for diff theories, for completeness.
_EQUIV_IDX_RE = re.compile(r"/thy/equiv/\d+/")
# Wall-clock timestamps rendered on the theory-list / overview pages
# (formatTime "%T" -> HH:MM:SS).  Also full date stamps if present.
_TIME_RE = re.compile(r"\b\d{2}:\d{2}:\d{2}\b")
_DATE_RE = re.compile(r"\b\d{1,2}/[A-Z][a-z]{2}/\d{4}(:\d{2}:\d{2}:\d{2})?( [+-]\d{4})?")


# Volatile build/version lines emitted in the `Generated from:` footer of the
# pretty-printed theory (source/message routes) and in page headers — the RS
# and HS binaries differ here.  Mirrors corpus_file_diff.sh's strip_env.
_VOLATILE = [
    (re.compile(r"Tamarin version[^\n<]*"), "Tamarin version #"),
    (re.compile(r"Maude version[^\n<]*"), "Maude version #"),
    (re.compile(r"Git revision:[^\n<]*"), "Git revision: #"),
    (re.compile(r"Compiled at:[^\n<]*"), "Compiled at: #"),
    (re.compile(r"processing time:[^\n<]*"), "processing time: #"),
    # The Rust port advertises its identity in the `Running Tamarin <version>
    # (Rust port)` header (a deliberate, plan-approved divergence from HS's
    # bare `<version>`); normalize it away so the shared page frame compares
    # equal.  HS never emits this suffix, so the rule is a no-op on HS.
    (re.compile(r" \(Rust port\)"), ""),
    # The help page's env line — HS `helpHtml` renders `Theory: NAME (Loaded at
    # <formatTime %T> from <show origin>) ...` (`src/Web/Theory.hs:1187-1194`).
    # The wall-clock time and the temp/cache-dir load path both differ between
    # the two backends (and run-to-run), so strip the whole `Loaded at …`
    # parenthetical to a placeholder on BOTH sides.  The load path never
    # contains a `)`, so `[^)]*` stops at the closing paren.
    (re.compile(r"Loaded at [^)]*"), "Loaded at #"),
    # web_parity.sh stages each theory in a fresh `mktemp -d` workdir, and the
    # cached HS manifest generally comes from a DIFFERENT run (different
    # tmpdir) than the live RS crawl.  Absolute paths under it leak into the
    # sequent pane's oracle banner ("Goals sorted according to an oracle …
    # located at /tmp/tmp.XXXX/thy/oracle-…"), so canonicalise the random
    # tmpdir component on both sides.
    (re.compile(r"/tmp/tmp\.[A-Za-z0-9]+/"), "/tmp/tmp.#/"),
]


def norm_env(s: str) -> str:
    s = _IDX_RE.sub("/thy/trace/#/", s)
    s = _EQUIV_IDX_RE.sub("/thy/equiv/#/", s)
    for rx, rep in _VOLATILE:
        s = rx.sub(rep, s)
    return s


def norm_url_key(url: str) -> str:
    """Normalize a URL for use as a manifest key (idx-agnostic)."""
    return norm_env(url)


# ---------------------------------------------------------------------------
# HTML canonicalization
# ---------------------------------------------------------------------------

# Tags whose open/close markup is dropped entirely (children kept) — purely
# cosmetic layout that the two backends emit differently.  The structural
# container tags `html`/`head`/`body` are unwrapped because HS emits malformed
# doubled `</script></script>` closes that shift the parser's head/body
# boundary; their children (title/links/scripts, then page content) appear in
# the same document order on both sides, so dropping the boundary markers keeps
# real content diffs visible while eliminating the serialization artifact.
_UNWRAP_TAGS = {"pre", "html", "head", "body"}
# Void/among tags treated as a whitespace break (dropped, contribute a space).
_BREAK_TAGS = {"br"}
# Attributes ignored during comparison (volatile / cosmetic only).
_IGNORE_ATTRS = {"style"}


def _is_hl_span(tag, attrs_dict):
    if tag != "span":
        return False
    cls = attrs_dict.get("class", "")
    toks = cls.split()
    return bool(toks) and all(t.startswith("hl_") for t in toks)


class _Canon(HTMLParser):
    """Build a canonical token stream from an HTML fragment/page.

    - highlight `<span class="hl_*">` wrappers are unwrapped (text kept)
    - <pre> unwrapped, <br> -> space
    - attributes sorted, values idx-normalized, `class` tokens sorted,
      `style` and empty attrs dropped
    - runs of whitespace (incl. &nbsp;, already unescaped by the parser)
      collapse to a single space; whitespace-only text between tags dropped
    """

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.tokens = []          # list of ('t', text) | ('o', tag, attrs) | ('c', tag)
        self._stack = []          # (tag, emitted_bool)
        self._pending_text = []

    def _flush_text(self):
        if not self._pending_text:
            return
        text = "".join(self._pending_text)
        self._pending_text = []
        # &nbsp; -> normal space (parser gives us \xa0), collapse runs
        text = text.replace("\xa0", " ")
        text = re.sub(r"\s+", " ", text)
        if text.strip() == "":
            # keep a single separating space token so adjacent inline text
            # doesn't get glued, but only if the previous token is text.
            if self.tokens and self.tokens[-1][0] == "t" and not self.tokens[-1][1].endswith(" "):
                self.tokens[-1] = ("t", self.tokens[-1][1] + " ")
            return
        # merge with a preceding text token
        if self.tokens and self.tokens[-1][0] == "t":
            self.tokens[-1] = ("t", (self.tokens[-1][1] + text))
        else:
            self.tokens.append(("t", text))

    def _canon_attrs(self, attrs):
        out = []
        for k, v in attrs:
            if k in _IGNORE_ATTRS:
                continue
            if v is None:
                v = ""
            v = norm_env(v)
            if k == "class":
                v = " ".join(sorted(v.split()))
            out.append((k, v))
        out.sort()
        return tuple(out)

    def handle_starttag(self, tag, attrs):
        self._flush_text()
        ad = {k: (v or "") for k, v in attrs}
        if tag in _BREAK_TAGS:
            # treat as whitespace
            self._pending_text.append(" ")
            return
        if tag in _UNWRAP_TAGS or _is_hl_span(tag, ad):
            self._stack.append((tag, False))
            return
        self.tokens.append(("o", tag, self._canon_attrs(attrs)))
        self._stack.append((tag, True))

    def handle_startendtag(self, tag, attrs):
        self._flush_text()
        if tag in _BREAK_TAGS:
            self._pending_text.append(" ")
            return
        ad = {k: (v or "") for k, v in attrs}
        if tag in _UNWRAP_TAGS or _is_hl_span(tag, ad):
            return
        self.tokens.append(("o", tag, self._canon_attrs(attrs)))
        self.tokens.append(("c", tag))

    def handle_endtag(self, tag):
        self._flush_text()
        if tag in _BREAK_TAGS:
            return
        # Find the nearest matching open tag WITHOUT mutating the stack.
        idx = None
        for i in range(len(self._stack) - 1, -1, -1):
            if self._stack[i][0] == tag:
                idx = i
                break
        if idx is None:
            # Stray close with no matching open (e.g. HS's malformed doubled
            # `</script></script>`) — ignore it, leaving the stack intact.
            return
        # Pop down to and including the match.  Intermediate emitted tags that
        # were left open (improper nesting / omitted closes, e.g. HS's Hamlet
        # leaving the contextMenu `<ul><li>` unclosed before `</body>`) are
        # implicitly closed by this ancestor, so emit their close tokens too —
        # matching a backend that closes them explicitly.
        while len(self._stack) > idx:
            t, e = self._stack.pop()
            if e:
                self.tokens.append(("c", t))

    def handle_data(self, data):
        self._pending_text.append(data)

    def result(self):
        self._flush_text()
        # Close any tags still open at EOF (implicit end-of-document close), so
        # a document that omits trailing closes compares equal to one that
        # spells them out.
        while self._stack:
            t, e = self._stack.pop()
            if e:
                self.tokens.append(("c", t))
        parts = []
        for tok in self.tokens:
            if tok[0] == "t":
                # Collapse any multi-space runs that arose from merging text
                # across break/whitespace boundaries.  HS renders the sequent
                # with `<br/><br/>` blank lines between goals (each break
                # contributes a space, so a blank line leaks a double space at
                # the join); RS renders the same block as `<pre>` text with
                # `\n\n`, which collapses to a single space.  Both are the same
                # block text semantically — canonicalize the whitespace so the
                # `<pre>`+`\n` and `<br/>`-postprocessed forms compare equal
                # (see the parity-definition "canonicalize … to the same block
                # text").
                s = re.sub(r"\s+", " ", tok[1]).strip()
                if s:
                    parts.append("T:" + s)
            elif tok[0] == "o":
                a = ",".join(f"{k}={v}" for k, v in tok[2])
                parts.append(f"<{tok[1]} {a}>")
            else:
                parts.append(f"</{tok[1]}>")
        return "\n".join(parts)


def canon_html(body: str) -> str:
    # Normalize volatile/env tokens (theory idx, version strings, the RS
    # `(Rust port)` identity suffix) across the WHOLE document — including
    # text nodes, which the per-attribute `norm_env` pass does not reach.
    body = norm_env(body)
    p = _Canon()
    try:
        p.feed(body)
        p.close()
    except Exception as e:
        return "HTML_PARSE_ERROR: " + repr(e) + "\n" + norm_env(body)
    return p.result()


# ---------------------------------------------------------------------------
# JSON canonicalization (the {title,html} / {alert} / {redirect} envelopes)
# ---------------------------------------------------------------------------

_HTMLISH = re.compile(r"<[a-zA-Z/!]")


def _canon_json_val(v, key=None):
    if isinstance(v, str):
        # The `html` and `title` fields are ALWAYS canonicalized as HTML
        # (even when the fragment happens to be tag-free, e.g.
        # "this is a mistake" or "Lemma: X"), otherwise a tag-free value
        # would canon differently from a `<br/>`-postprocessed / highlighted
        # one and diverge spuriously.  HS builds the `title` for a proof
        # method via `renderHtmlDoc . prettyProofMethod` — it carries `hl_*`
        # operator spans — whereas the Rust server emits the same title as
        # plain text; forcing both through `canon_html` makes them compare
        # equal (the spans unwrap to the same text).
        if key in ("html", "title") or _HTMLISH.search(v):
            return canon_html(v)
        return norm_env(v)
    if isinstance(v, dict):
        return {k: _canon_json_val(x, k) for k, x in sorted(v.items())}
    if isinstance(v, list):
        return [_canon_json_val(x) for x in v]
    return v


def canon_json(body: str) -> str:
    try:
        v = json.loads(body)
    except Exception:
        # not valid JSON — fall back to text
        return canon_text(body)
    return json.dumps(_canon_json_val(v), sort_keys=True, ensure_ascii=False, indent=1)


# ---------------------------------------------------------------------------
# DOT graph canonicalization (compare as a graph, not as serialization bytes)
# ---------------------------------------------------------------------------

_DOT_STMT = re.compile(r"""\s*(.*?)\s*;""", re.S)


def _parse_dot_attrs(s):
    """Parse an `[a=b,c="d"]` attr list into a sorted dict-ish tuple."""
    s = s.strip()
    if not (s.startswith("[") and s.endswith("]")):
        return ()
    inner = s[1:-1]
    attrs = {}
    # split on commas not inside quotes
    for m in re.finditer(r'([A-Za-z_]+)\s*=\s*("(?:[^"\\]|\\.)*"|[^,]*)', inner):
        k = m.group(1)
        v = m.group(2).strip()
        if len(v) >= 2 and v[0] == '"' and v[-1] == '"':
            v = v[1:-1]
        v = norm_env(v)
        # Canonicalize numeric attr values to a single float form — HS and RS
        # serialize the same edge weight / size differently (`weight=10.0` vs
        # `weight=10`), which is a serialization diff the graph comparator is
        # meant to ignore.
        if re.fullmatch(r"-?\d+(?:\.\d+)?", v):
            v = repr(float(v))
        attrs[k] = v
    return tuple(sorted(attrs.items()))


def _norm_record_label(lbl):
    """Port/bracket-agnostic canonical form of a DOT node label.

    HS and RS both emit graphviz RECORD labels for protocol-rule nodes —
    `{ premises } | id : rule[acts] | { conclusions }` — but with DIFFERENT
    field-port ids (HS a graph-global `<nK>` counter, RS local `<p0>`/`<c0>`)
    and different record bracketing/serialization.  The parity bar explicitly
    "ignores node-id scheme, quoting, and attribute order" and compares the
    graph structurally, so we strip the record scaffolding down to the field
    TEXT: drop `<portid>` prefixes and record braces, split into fields on
    `|`, collapse whitespace (incl. HS's vertical multi-action `\\l` / `&nbsp;`
    rendering, which RS joins horizontally), and drop empty fields.  A plain
    (ellipse) label has no ports/braces/`|` → a single-field tuple.  Returns a
    tuple of field strings so it doubles as a stable node key for resolving
    edge endpoints.
    """
    if lbl is None:
        return None
    s = re.sub(r"<[A-Za-z0-9_]+>\s*", "", lbl)          # strip record port ids
    s = s.replace("{", " ").replace("}", " ")            # drop record braces
    s = s.replace("\\l", " ").replace("&nbsp;", " ").replace("\xa0", " ")
    fields = [re.sub(r"\s+", " ", f).strip() for f in s.split("|")]
    return tuple(f for f in fields if f)


def canon_dot(body: str) -> str:
    """Canonicalize a DOT graph to a label-keyed structural form.

    HS uses counter node-ids (`nX`), RS uses semantic ids; we key nodes by
    their `label` attribute (in the port/bracket-agnostic `_norm_record_label`
    form) so the two are comparable.  Node/edge *default* attribute blocks
    (`node[...]` / `edge[...]`) are merged into each node's / edge's effective
    attrs before comparison, because the two backends split attrs between
    per-node and default statements differently (e.g. HS sets `shape=record`
    per-node via genRecord, RS as a `node[]` default) yet render identically.
    We compare: graph-level kv (nodesep/ranksep/graph[]), the set of effective
    node labels (normalized) + attrs, and the set of effective edges
    (endpoints resolved to normalized labels) + attrs.
    """
    body = norm_env(body)
    # collect id -> label and node attrs, and edges by id
    node_label = {}
    node_attrs = {}
    edges = []
    node_defaults = {}   # merged into every node's effective attrs
    edge_defaults = {}   # merged into every edge's effective attrs
    graph_kv = {}        # graph-level scalar attrs (nodesep, ranksep, ...)
    # crude statement scan (DOT here is machine-generated, line/`;`-delimited)
    text = body
    # normalize newlines to spaces inside the body except keep statement ';'
    # iterate statements
    stmts = []
    cur = []
    inq = False  # inside a double-quoted string?
    for ch in text:
        if ch == '"':
            inq = not inq
            cur.append(ch)
        elif inq:
            # Do NOT treat `;` (or braces) inside a quoted label as a
            # statement break — HS record labels embed `&nbsp;` (which
            # contains `;`) and `{...}` record braces, so a quote-blind
            # splitter fragments the node statement mid-label and the node
            # loses its `label` attr.
            cur.append(ch)
        elif ch == ";":
            stmts.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        stmts.append("".join(cur).strip())

    # Endpoint id captures MUST exclude `:` so the trailing `(?::port)?` can
    # strip the graphviz record port (`node:port`) — otherwise a greedy
    # `[\w.\-:]+` swallows `n3:n1` whole and the endpoint never resolves to its
    # node label.  Node ids themselves never contain `:`.
    edge_re = re.compile(r'^\s*"?([\w\.\-]+)"?(?::[\w\.\-<>]+)?\s*->\s*"?([\w\.\-]+)"?(?::[\w\.\-<>]+)?\s*(\[.*\])?\s*$', re.S)
    node_re = re.compile(r'^\s*"?([\w\.\-:]+)"?\s*(\[.*\])\s*$', re.S)
    default_re = re.compile(r'^\s*(graph|node|edge)\s*(\[.*\])\s*$', re.S)
    kv_re = re.compile(r'^\s*(\w+)\s*=\s*("?.*?"?)\s*$', re.S)

    def label_of(attrs):
        for k, v in attrs:
            if k == "label":
                return v
        return None

    for st in stmts:
        st = st.strip()
        if not st or st.startswith("//") or st.startswith("subgraph") or st in ("{", "}") or st.startswith("digraph"):
            continue
        m = default_re.match(st)
        if m:
            kind = m.group(1)
            at = dict(_parse_dot_attrs(m.group(2)))
            if kind == "node":
                node_defaults.update(at)
            elif kind == "edge":
                edge_defaults.update(at)
            else:  # graph[...]
                graph_kv.update(at)
            continue
        m = edge_re.match(st)
        if m:
            edges.append((m.group(1), m.group(2), dict(_parse_dot_attrs(m.group(3) or ""))))
            continue
        m = node_re.match(st)
        if m:
            nid = m.group(1)
            at = dict(_parse_dot_attrs(m.group(2)))
            node_attrs[nid] = at
            lbl = label_of(tuple(at.items()))
            node_label[nid] = lbl if lbl is not None else nid
            continue
        m = kv_re.match(st)
        if m:
            graph_kv[m.group(1)] = norm_env(m.group(2).strip('"'))
            continue

    def key(nid):
        # Node identity = its normalized (port/bracket-agnostic) label; falls
        # back to the id for anything unlabelled.  Edge endpoints resolve
        # through the same map so `node:port` references compare by label.
        return _norm_record_label(node_label.get(nid, nid))

    def eff_dict(defaults, own):
        d = dict(defaults)
        d.update(own)
        return d

    def eff(defaults, own):
        d = eff_dict(defaults, own)
        # The label is the node identity (compared via `key` in normalized
        # form) — drop the RAW label from the attr set so record port-ids /
        # bracketing don't resurface as a spurious attr diff.
        d.pop("label", None)
        return tuple(sorted(d.items()))

    nodes_canon = sorted(
        (key(nid), eff(node_defaults, own)) for nid, own in node_attrs.items()
    )
    # Drop `style=invis` edges: HS's `generateLegend` (Dot.hs:426-433) emits
    # invisible sink→legend-anchor edges purely to POSITION the legend box;
    # they render nothing and carry no semantic graph structure (the visible
    # legend node itself compares as a normal node).  RS omits them.  Under the
    # semantic/layout-agnostic parity bar these are ignored, not a divergence.
    edges_canon = sorted(
        (key(a), key(b), eff(edge_defaults, own))
        for (a, b, own) in edges
        if eff_dict(edge_defaults, own).get("style") != "invis"
    )
    out = {
        "graph_kv": sorted(graph_kv.items()),
        "nodes": nodes_canon,
        "edges": edges_canon,
    }
    return json.dumps(out, sort_keys=True, ensure_ascii=False, indent=1, default=list)


# ---------------------------------------------------------------------------
# Plain text canonicalization (source / message / next/prev URL / robots)
# ---------------------------------------------------------------------------

def canon_text(body: str) -> str:
    body = norm_env(body)
    lines = [ln.rstrip() for ln in body.splitlines()]
    while lines and lines[-1] == "":
        lines.pop()
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------

def canon(kind: str, body: str) -> str:
    if kind == "html":
        return canon_html(body)
    if kind == "json":
        return canon_json(body)
    if kind == "dot":
        return canon_dot(body)
    return canon_text(body)


if __name__ == "__main__":
    import sys
    k = sys.argv[1] if len(sys.argv) > 1 else "text"
    print(canon(k, sys.stdin.read()))
