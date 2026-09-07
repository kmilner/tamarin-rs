#!/usr/bin/env python3
"""Semantic normalizers for the web-parity gate (RS interactive UI vs HS).

The parity bar is *structural / semantic* equivalence for the markup routes,
NOT byte-identity: we canonicalize away whitespace, attribute order, JSON key
order, and the genuinely nondeterministic env fields (theory idx, timestamps,
temp/cache-dir prefixes, absolute load paths).  What survives must match:
element structure (including syntax/status highlighting), attributes (including
inline styles), visible text, link hrefs + text, form actions, embedded resource
URLs and JSON values.

The graph routes and the text/plain routes are held to byte-identity — the port
emits `Text.Dot`'s bytes through the same `showDot` upstream uses, and serves
the pretty-printed theory verbatim on `source`/`message` — bar the env fields
above and graphviz's own version stamp in a rendered SVG.  Whitespace is
content on both: a trailing space inside a DOT label, and the pretty printer's
own trailing spaces in the theory echo, are divergences the gate must see.

Used by web_diff.py.  Pure stdlib (html.parser, json, re).
"""
import json
import re
from functools import lru_cache
from html.parser import HTMLParser

from web_url_key import norm_indices

# ---------------------------------------------------------------------------
# Env-field normalization (applied to every raw body + to URL keys)
# ---------------------------------------------------------------------------

# The theory idx increments on every server-side mutation (HS modifyTheory /
# RS clone) and is embedded in every link.  It is a server-internal handle,
# not user-meaningful, so we canonicalize it everywhere.
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
]

# Most HTML text/attributes contain none of these fields. One search avoids
# running every substitution on each of those small strings. Keep the ordered
# substitutions below for values that do need normalization. Large bodies
# bypass the search: another full scan costs more than it saves there.
_HAS_VOLATILE = re.compile("|".join(rx.pattern for rx, _ in _VOLATILE))


@lru_cache(maxsize=16)
def prepare_workdirs(workdirs):
    """Resolve the two immutable roots once, longest first for nested paths."""
    return tuple(sorted(set(filter(None, workdirs)), key=len, reverse=True))


def norm_env(s: str, workdirs=()) -> str:
    # Callers pass prepare_workdirs() output, not arbitrary path prefixes.
    for workdir in workdirs:
        s = s.replace(workdir, "/WEB-WORKDIR")
    s = norm_indices(s)
    if len(s) > 512 or _HAS_VOLATILE.search(s):
        for rx, rep in _VOLATILE:
            s = rx.sub(rep, s)
    return s

# ---------------------------------------------------------------------------
# HTML canonicalization
# ---------------------------------------------------------------------------

# HTML void elements have no closing tag, regardless of whether the serializer
# spells their opening tag as <br> or <br/>.
_VOID_TAGS = {"area", "base", "br", "col", "embed", "hr", "img", "input",
              "link", "meta", "param", "source", "track", "wbr"}


class _Canon(HTMLParser):
    """Build a canonical token stream from an HTML fragment/page.

    - element structure retained, with HTML void tags represented once
    - attributes sorted, values idx-normalized, `class` tokens sorted,
      boolean attrs represented by empty values
    - runs of whitespace (incl. &nbsp;, already unescaped by the parser)
      collapse to a single space; whitespace-only text between tags dropped
    """

    def __init__(self, workdirs=()):
        super().__init__(convert_charrefs=True)
        self.workdirs = prepare_workdirs(tuple(workdirs))
        self.parts = []
        self._stack = []          # open non-void tags
        self._pending_text = []

    def _flush_text(self):
        if not self._pending_text:
            return
        text = "".join(self._pending_text)
        self._pending_text = []
        text = " ".join(norm_env(text, self.workdirs).split())
        if text:
            self.parts.append("T:" + text)

    def _canon_attrs(self, attrs):
        out = []
        for k, v in attrs:
            if v is None:
                v = ""
            v = norm_env(v, self.workdirs)
            if k == "class":
                v = " ".join(sorted(v.split()))
            out.append((k, v))
        out.sort()
        return out

    def handle_starttag(self, tag, attrs):
        self._flush_text()
        attrs = ",".join(f"{k}={v}" for k, v in self._canon_attrs(attrs))
        self.parts.append(f"<{tag} {attrs}>")
        if tag not in _VOID_TAGS:
            self._stack.append(tag)

    def handle_endtag(self, tag):
        if tag in _VOID_TAGS:
            return
        # Find the nearest matching open tag WITHOUT mutating the stack.
        idx = None
        for i in range(len(self._stack) - 1, -1, -1):
            if self._stack[i] == tag:
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
        self._flush_text()
        while len(self._stack) > idx:
            self.parts.append(f"</{self._stack.pop()}>")

    def handle_data(self, data):
        self._pending_text.append(data)

    def result(self):
        self._flush_text()
        # Close any tags still open at EOF (implicit end-of-document close), so
        # a document that omits trailing closes compares equal to one that
        # spells them out.
        while self._stack:
            self.parts.append(f"</{self._stack.pop()}>")
        return "\n".join(self.parts)


def canon_html(body: str, workdirs=()) -> str:
    # HTMLParser decodes character references before handing us text and
    # attributes. Normalize those semantic values instead of trying to predict
    # whether a serializer chose &apos;, &#39;, &#x27;, or another legal spelling.
    p = _Canon(workdirs)
    try:
        p.feed(body)
        p.close()
    except Exception as e:
        return "HTML_PARSE_ERROR: " + repr(e) + "\n" + norm_env(body, workdirs)
    return p.result()


# ---------------------------------------------------------------------------
# JSON canonicalization (the {title,html} / {alert} / {redirect} envelopes)
# ---------------------------------------------------------------------------

def _canon_json_val(v, key=None, workdirs=()):
    if isinstance(v, str):
        # The `html` and `title` fields are ALWAYS canonicalized as HTML
        # (even when the fragment happens to be tag-free, e.g.
        # "this is a mistake" or "Lemma: X"). Both servers render proof-method
        # titles as HTML, including syntax highlighting and line breaks.
        if key in ("html", "title"):
            return canon_html(v, workdirs)
        if key == "alert":
            # The UI's showDialog inserts HTML after turning newlines into br.
            return canon_html(v.replace("\n", "<br>"), workdirs)
        return norm_env(v, workdirs)
    if isinstance(v, dict):
        return {k: _canon_json_val(x, k, workdirs) for k, x in v.items()}
    if isinstance(v, list):
        return [_canon_json_val(x, workdirs=workdirs) for x in v]
    return v


def canon_json(body: str, workdirs=()) -> str:
    try:
        v = json.loads(body)
    except Exception:
        # not valid JSON — fall back to text
        return canon_text(body, workdirs)
    return json.dumps(
        _canon_json_val(v, workdirs=workdirs),
        sort_keys=True,
        ensure_ascii=False,
        indent=1,
    )


def canon_json_pair(left, right, workdirs=()):
    """Normalize differing fields once; identical strings need no HTML parse."""
    try:
        left, right = json.loads(left), json.loads(right)
    except ValueError:
        return canon_json(left, workdirs), canon_json(right, workdirs)
    workdirs = prepare_workdirs(tuple(workdirs))

    def pair(a, b, key=None):
        if isinstance(a, str) and isinstance(b, str) and a == b:
            return a, b
        if isinstance(a, dict) and isinstance(b, dict) and a.keys() == b.keys():
            fields = {k: pair(v, b[k], k) for k, v in a.items()}
            return ({k: v[0] for k, v in fields.items()},
                    {k: v[1] for k, v in fields.items()})
        if isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
            items = [pair(x, y) for x, y in zip(a, b)]
            return [x for x, _ in items], [y for _, y in items]
        return _canon_json_val(a, key, workdirs), _canon_json_val(b, key, workdirs)

    left, right = pair(left, right)
    # Serialization retains the existing distinction between true, 1, 1.0,
    # and -0.0, which Python object equality would lose.
    return tuple(json.dumps(v, sort_keys=True, ensure_ascii=False, indent=1)
                 for v in (left, right))


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


def canon_dot(body: str, workdirs=()) -> str:
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
    return norm_env(body, workdirs)


# ---------------------------------------------------------------------------
# Plain text canonicalization (source / message / next/prev URL / robots)
# ---------------------------------------------------------------------------

def canon_text(body: str, workdirs=()) -> str:
    """Canonicalize a text/plain response.

    The `source` and `message` routes serve the pretty-printed theory verbatim,
    so this is a BYTE comparison bar the env-volatile tokens `norm_env` handles
    — the same bar `canon_dot` holds the graph routes to, and for the same
    reason.  The pretty printer's own trailing whitespace is content here: the
    oracle emits `Rule inrsignmk_0_11: ` with a trailing space and blank lines
    spelled as four spaces, and a per-line rstrip would make reproducing them
    optional.
    """
    return norm_env(body, workdirs)


# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------

def canon(kind: str, body: str, workdirs=()) -> str:
    # A cached HS manifest and the live RS crawl normally come from different
    # mktemp directories. The crawler records those exact configurable roots;
    # replace them before parsing so paths in text, HTML attributes and JSON
    # strings all receive the same treatment without guessing their prefix.
    workdirs = prepare_workdirs(tuple(workdirs))
    if kind == "html":
        return canon_html(body, workdirs)
    if kind == "json":
        return canon_json(body, workdirs)
    if kind == "dot":
        return canon_dot(body, workdirs)
    return canon_text(body, workdirs)


if __name__ == "__main__":
    import sys
    k = sys.argv[1] if len(sys.argv) > 1 else "text"
    print(canon(k, sys.stdin.read()))
