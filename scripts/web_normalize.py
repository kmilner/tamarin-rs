#!/usr/bin/env python3
"""Semantic normalizers for the web-parity gate (RS interactive UI vs HS).

The parity bar is *structural / semantic* equivalence for the markup routes,
NOT byte-identity: we canonicalize away whitespace, attribute order, JSON key
order, highlight `<span class="hl_*">` wrappers, `<br/>`/`<pre>` cosmetic
markup, and the genuinely nondeterministic env fields (theory idx, timestamps,
temp/cache-dir prefixes, absolute load paths).  What survives must match:
element structure, visible text, link hrefs + text, form actions, embedded
resource URLs and JSON values.

The graph routes and the text/plain routes are held to byte-identity — the port
emits `Text.Dot`'s bytes through the same `showDot` upstream uses, and serves
the pretty-printed theory verbatim on `source`/`message` — bar the env fields
above and graphviz's own version stamp in a rendered SVG.  Whitespace is
content on both: a trailing space inside a DOT label, and the pretty printer's
own trailing spaces in the theory echo, are divergences the gate must see.

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
# The only wall-clock stamp the crawled routes carry is the help page's
# `Loaded at <%T> from <origin>` parenthetical, handled as one unit in
# _VOLATILE below.  There is deliberately no blanket HH:MM:SS rule: it would
# also rewrite times inside trace and constraint-system text, which is content.


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
    # contains a `)`, so the match stops at the closing paren; `\n` is excluded
    # too, so a side that somehow omits the paren erases the rest of one line
    # instead of running on through the markup to whatever `)` comes next.
    (re.compile(r"Loaded at [^)\n]*"), "Loaded at #"),
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
# Graph-route canonicalization
# ---------------------------------------------------------------------------

# graphviz stamps its own version and build date into an XML comment at the top
# of every SVG it renders.  Both backends shell out to the SAME local binary, so
# within one run the two stamps agree and this substitution is a no-op; it earns
# its keep only when a cached HS manifest was crawled under a different
# graphviz.  It does NOT make such a manifest comparable — a version change
# generally moves the layout coordinates too — it just keeps the resulting DIFF
# about the graph rather than about the stamp.  `[^\n]*` stops at the end of the
# comment's first line, which is where graphviz breaks it.
_SVG_GENERATOR = re.compile(r"Generated by graphviz version [^\n]*")


def canon_dot(body: str) -> str:
    """Canonicalize a graph-route response.

    The port serialises through the same `Text.Dot` `showDot` upstream does
    (see `constraint/system/dot.rs`), so the DOT is compared BYTE FOR BYTE —
    node ids, record ports, attribute quoting and all.  Anything weaker was
    hiding a real dialect divergence here for as long as the port had a
    second serializer.

    `/graph/*` answers the RENDERED SVG when graphviz is on PATH and falls
    back to the DOT source when it is not, so the two shapes are told apart
    by the body rather than by the route.

    "Byte for byte" is meant literally: a trailing space inside a DOT label is
    a divergence, and it is the exact class of dialect difference this route
    exists to catch.  Only the env-volatile tokens `norm_env` handles (and
    graphviz's version stamp) are normalized; nothing else about the body is
    touched.
    """
    if body.lstrip().startswith(("<?xml", "<svg")):
        body = _SVG_GENERATOR.sub("Generated by graphviz version X", body)
    return norm_env(body)


# ---------------------------------------------------------------------------
# Plain text canonicalization (source / message / next/prev URL / robots)
# ---------------------------------------------------------------------------

def canon_text(body: str) -> str:
    """Canonicalize a text/plain response.

    The `source` and `message` routes serve the pretty-printed theory verbatim,
    so this is a BYTE comparison bar the env-volatile tokens `norm_env` handles
    — the same bar `canon_dot` holds the graph routes to, and for the same
    reason.  The pretty printer's own trailing whitespace is content here: the
    oracle emits `Rule inrsignmk_0_11: ` with a trailing space and blank lines
    spelled as four spaces, and a per-line rstrip would make reproducing them
    optional.
    """
    return norm_env(body)


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
