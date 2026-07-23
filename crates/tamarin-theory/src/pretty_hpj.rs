// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, arcz, ValentinYuri, felixlinker, jdreier, Nynko, and other
//   minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/Substitution/SubstVFresh.hs,
//   lib/term/src/Term/Term.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/System/Dot.hs,
//   lib/theory/src/Theory/Text/Pretty.hs,
//   lib/utils/src/Control/Monad/Disj/Class.hs,
//   lib/utils/src/Text/PrettyPrint/Class.hs,
//   lib/utils/src/Text/PrettyPrint/Highlight.hs,
//   lib/utils/src/Text/PrettyPrint/Html.hs, src/Main/Console.hs,
//   src/Web/Handler.hs

//! HughesPJ-faithful pretty-printer Doc engine.
//!
//! Port of the layout algorithm from
//! `Text.PrettyPrint.HughesPJ` (pretty-1.1.3.6) — the non-annotated
//! module used in production (HS `Class.hs:64-67, see line 67`/`:72`).
//!
//! The HS `Doc` is reduced to an RDoc with five constructors —
//! `Empty`, `NilAbove`, `TextBeside`, `Nest`, `Union`, plus the
//! failure constructor `NoDoc`.  Combinators (`<>`, `<+>`, `$$`, `$+$`,
//! `sep`, `cat`, `fsep`, `fcat`, `nest`) build a `Doc`; `render` walks
//! the doc using HughesPJ's `best` / `get` / `get1` choosing between
//! Union alternatives via `nicest1` /`fits`.  We track per-line `w`
//! shrinkage at each `NilAbove` (HS `get1` line 1011 of pretty-1.1.3.6:
//! `get1 w sl (NilAbove p) = nilAbove_ (get (w - sl) p)`).
//!
//! Defaults: `lineWidth = 110` (HS src/Main/Console.hs), threaded into
//! HughesPJ's `lineLength` field, `ribbonsPerLine = 1.5` (HS HughesPJ.hs),
//! giving `ribbon = round(110/1.5) = 73` (HS HughesPJ.hs).
//!
//! Subset choice: we omit `Above`/`Beside` lazy constructors and the
//! `g` (with-space) tracking around fillNB's special "Empty after
//! Nest" handling — our concrete callers always emit explicit
//! `TextBeside " "` between items.  We also omit annotations
//! (`AnnotStart`/`AnnotEnd`) — text output only.

use std::rc::Rc;

/// HS `lineWidth` from `src/Main/Console.hs`, threaded into HughesPJ's
/// `lineLength` field.
pub const LINE_LENGTH: usize = 110;
/// HS `ribbonLen = round(lineLength / ribbonsPerLine)` =
/// `round(110/1.5) = 73` (`pretty-1.1.3.6/Text/PrettyPrint/HughesPJ.hs`).
pub const RIBBON: usize = 73;

use std::sync::atomic::{AtomicUsize, Ordering};

/// Process-wide DISPLAY width used by the bare [`Doc::render`] path.
///
/// The two output modes render at different widths in HS, and it is a
/// property of the whole process (you invoke either `--prove` OR
/// `interactive`, never both in one process):
///   - the CLI (`--prove`) renders at the *console* width
///     `LINE_LENGTH`/`RIBBON` = 110/73 (`src/Main/Console.hs`
///     `renderDoc`);
///   - the interactive web server renders every HTTP response at HS's
///     *web* width 100/67 — HughesPJ's default `style` used by `render`
///     (`getTheorySourceR` = `render . prettyClosedTheory`,
///     `src/Web/Handler.hs:950-957, see line 956`) and by `renderHtmlDoc`
///     (`Text/PrettyPrint/Html.hs:140-149, see line 151`).
///
/// Defaults to 110/73 so the CLI path is unchanged; the server calls
/// [`set_display_width`] once at startup, before any rendering.  This is
/// presentation-only — it can never affect proof search or verdicts —
/// and the explicit `render_with`/`render_at` widths (WF/oracle/goal
/// rendering) are unaffected.
static DISPLAY_LINE_LENGTH: AtomicUsize = AtomicUsize::new(LINE_LENGTH);
static DISPLAY_RIBBON: AtomicUsize = AtomicUsize::new(RIBBON);

/// HS web display width: HughesPJ default `style` (100) with
/// `round(100/1.5) = 67` ribbon.
pub const WEB_LINE_LENGTH: usize = 100;
pub const WEB_RIBBON: usize = 67;

/// Override the bare-`render()` display width process-wide (see
/// [`DISPLAY_LINE_LENGTH`]).  Called once by the interactive server with
/// `(WEB_LINE_LENGTH, WEB_RIBBON)`.
pub fn set_display_width(line_length: usize, ribbon: usize) {
    DISPLAY_LINE_LENGTH.store(line_length, Ordering::Relaxed);
    DISPLAY_RIBBON.store(ribbon, Ordering::Relaxed);
}

thread_local! {
    /// When set, [`Doc::text`]/[`Doc::char`] measure each token's *fill* width
    /// as its HTML-entity-escaped column count instead of its visible column
    /// count.  This mirrors HS's web render path, which builds every document
    /// through the `HtmlDoc Doc` transformer: its `Document (HtmlDoc d)`
    /// instance (`Text/PrettyPrint/Html.hs:105-107`) runs `escapeHtmlEntities`
    /// on every `text`/`char` token BEFORE the HughesPJ fill measures it, so a
    /// `<`/`>` costs 4 columns (`&lt;`/`&gt;`) and a `'` costs 5 (`&#39;`) when
    /// deciding line breaks.  The interactive server escapes AFTER rendering
    /// (`html_escape`), so without matching this accounting its `fsep`/`fcat`
    /// wraps a pair-tuple `<…>` at a different column than HS (task #17 family
    /// D — a space appears/disappears before a tuple's closing `>`).
    ///
    /// This is presentation-only: it never affects proof search or verdicts,
    /// and it is scoped (via [`HtmlEntityWidthGuard`]) to the web
    /// constraint-system pane only, so the `--prove` byte-identity corpus is
    /// untouched (the flag defaults to `false`).
    static HTML_ENTITY_WIDTH: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Column width of `s` after HTML-entity escaping, matching HS
/// `escapeHtmlEntities` (`Text/PrettyPrint/Html.hs:130-138`) and the server's
/// `html_escape`: `<`/`>` → `&lt;`/`&gt;` (4), `&` → `&amp;` (5), `'` →
/// `&#39;` (5), `"` → `&quot;` (6); every other codepoint counts as 1 column.
fn html_entity_col_width(s: &str) -> usize {
    s.chars()
        .map(|c| match c {
            '<' | '>' => 4,
            '&' | '\'' => 5,
            '"' => 6,
            _ => 1,
        })
        .sum()
}

/// RAII guard enabling HTML-entity fill-width accounting on the current thread
/// until dropped (see [`HTML_ENTITY_WIDTH`]).  Restores the previous value on
/// drop, so nested/re-entrant use is safe.
#[must_use = "dropping this guard immediately ends the scope it protects"]
pub struct HtmlEntityWidthGuard(bool);

impl HtmlEntityWidthGuard {
    /// Enable entity-width accounting for the current thread; the previous
    /// value is restored when the returned guard is dropped.
    pub fn enable() -> Self {
        HtmlEntityWidthGuard(HTML_ENTITY_WIDTH.with(|c| c.replace(true)))
    }
}

impl Drop for HtmlEntityWidthGuard {
    fn drop(&mut self) {
        HTML_ENTITY_WIDTH.with(|c| c.set(self.0));
    }
}

thread_local! {
    /// The full "HtmlDoc" render mode: a faithful port of HS building every
    /// web pane through the `HtmlDoc Doc` transformer (`Text/PrettyPrint/Html.hs`).
    /// When enabled:
    ///   * [`Doc::text`]/[`Doc::char`] run `escapeHtmlEntities` on their content
    ///     BEFORE it enters the layout, exactly as the `Document (HtmlDoc d)`
    ///     instance (`Html.hs:102-105`) — so the stored bytes are already escaped
    ///     and the HughesPJ fill measures each token at its escaped-entity width
    ///     (`<`/`>` = 4, `&`/`'` = 5, `"` = 6).  This is a superset of the
    ///     width-only [`HtmlEntityWidthGuard`].
    ///   * the highlight combinators ([`keyword`]/[`operator`]/[`comment`] via
    ///     [`Doc::highlight`]) wrap their argument in a `<span class="hl_*">…</span>`
    ///     emitted as ZERO-WIDTH text (HS `withTag`, `Html.hs:59-64`,
    ///     `highlight`, `Html.hs:129-135`), so markup never perturbs line breaks.
    ///     In plain mode they are the identity (HS plain `Doc` instance,
    ///     `Highlight.hs:41-42`), so the `--prove` byte-identity corpus is
    ///     untouched (the flag defaults to `false`).
    ///
    /// Scoped via [`HtmlDocGuard`]; presentation-only, never affects verdicts.
    static HTML_MODE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// RAII guard enabling the full HtmlDoc render mode on the current thread until
/// dropped (see [`HTML_MODE`]).  Restores the previous value on drop.
#[must_use = "dropping this guard immediately ends the scope it protects"]
pub struct HtmlDocGuard(bool);

impl HtmlDocGuard {
    /// Enable HtmlDoc mode for the current thread; the previous value is
    /// restored when the returned guard is dropped.
    pub fn enable() -> Self {
        HtmlDocGuard(HTML_MODE.with(|c| c.replace(true)))
    }

    /// Force PLAIN mode for the current thread (previous value restored on
    /// drop).  For plain-text side channels rendered while an enclosing
    /// page render holds an `enable()` guard — e.g. the oracle/tactic
    /// goal strings, which HS produces with the plain `render $
    /// prettyGoal` regardless of the surrounding widget (ProofMethod.hs:598-623, see line 607):
    /// HTML spans/entities in oracle stdin break the oracle's regexes.
    pub fn disable() -> Self {
        HtmlDocGuard(HTML_MODE.with(|c| c.replace(false)))
    }
}

impl Drop for HtmlDocGuard {
    fn drop(&mut self) {
        HTML_MODE.with(|c| c.set(self.0));
    }
}

/// Whether the full HtmlDoc render mode is active on this thread.
#[inline]
pub fn html_mode() -> bool {
    HTML_MODE.with(|c| c.get())
}

/// HS `escapeHtmlEntities` (`Text/PrettyPrint/Html.hs:140-149`, copied there
/// from blaze-html) — escape the five HTML metacharacters in the exact HS
/// order/mapping so escaped column widths and output bytes match.
pub use tamarin_utils::pretty_html::escape_html_entities;

/// The fill width of a text run `s`: its visible column count, or — under an
/// active [`HtmlEntityWidthGuard`] or [`HtmlDocGuard`] — its HTML-entity-escaped
/// column count.
#[inline]
fn fill_width(s: &str) -> usize {
    if HTML_MODE.with(|c| c.get()) || HTML_ENTITY_WIDTH.with(|c| c.get()) {
        html_entity_col_width(s)
    } else {
        s.chars().count()
    }
}

// ============================================================================
// Doc tree
// ============================================================================

/// HS `Doc` from `pretty-1.1.3.6/Text/PrettyPrint/HughesPJ.hs` (the
/// non-annotated module used in production, HS `Class.hs:64-67, see line 67`/`:72`)
/// — minus the `Above`/`Beside` lazy constructors (we eagerly reduce on
/// build).
#[derive(Clone)]
pub enum Doc {
    /// Empty doc, length 0.
    Empty,
    /// `NilAbove p` — emit a newline, then `p` on the next line.
    NilAbove(Rc<Doc>),
    /// `TextBeside s p` — emit `s` (a text run of `width` cols) then
    /// continue with `p` on the same line.  `width` is decoupled from
    /// `s.len()` to support multi-byte chars (e.g. `∧` = 1 col).
    TextBeside(Rc<str>, usize, Rc<Doc>),
    /// `Nest n p` — add `n` to the current indent for the rest of `p`.
    Nest(isize, Rc<Doc>),
    /// `Union p q` — try `p` first; if it doesn't fit, use `q`.
    Union(Rc<Doc>, Rc<Doc>),
    /// Lazy variant of `Union`: the left (flat) branch `p` is materialised,
    /// but the right branch is a memoised thunk forced only when `p` does
    /// not fit.  HughesPJ relies on Haskell's laziness so that the `q`
    /// branch of a `Union` (which, in `fill1`/`fillNBE`/`sep1`, recursively
    /// re-lays the remaining items) is never built unless a line actually
    /// breaks there.  An eager Rust port materialises both branches at
    /// construction time, making the reduced tree O(2^depth) for deeply
    /// nested terms (e.g. TLS `Out( <senc(<..>, h(<..>)), ..> )`).  This
    /// thunk restores HS's laziness: construction stays linear, and only
    /// the layout path that is actually chosen forces its right branches.
    LazyUnion(Rc<Doc>, Rc<LazyRight>),
    /// Deferred reduction continuation: a memoised thunk holding the
    /// `get`/`get1` reduction of some sub-doc.  `get`/`get1` wrap each
    /// recursive position in a `Deferred` so that — exactly as in HS's
    /// call-by-need `best` — the reduced doc past the first line break is
    /// NOT built until `fits` (which stops at the first `NilAbove`) or
    /// `lay` actually walks into it.  This is what keeps reduction linear
    /// in the output size instead of eagerly materialising every layout
    /// alternative (the 56 s / 64 GB blowup on `arpki`'s `ILS_Reg_ILS`).
    Deferred(Rc<LazyRight>),
    /// `NoDoc` — failure marker (only appears inside reduced Unions).
    NoDoc,
}

/// Memoised thunk for the right branch of a `LazyUnion`.
pub struct LazyRight {
    thunk: std::cell::RefCell<Option<Box<dyn FnOnce() -> Doc>>>,
    value: std::cell::RefCell<Option<Rc<Doc>>>,
}

impl LazyRight {
    fn new(f: impl FnOnce() -> Doc + 'static) -> Rc<LazyRight> {
        Rc::new(LazyRight {
            thunk: std::cell::RefCell::new(Some(Box::new(f))),
            value: std::cell::RefCell::new(None),
        })
    }
    /// Force the thunk, memoising the result.
    fn force(&self) -> Rc<Doc> {
        if let Some(v) = self.value.borrow().as_ref() {
            return v.clone();
        }
        let f = self
            .thunk
            .borrow_mut()
            .take()
            .expect("LazyRight forced while already forcing (cycle)");
        let d = Rc::new(f());
        *self.value.borrow_mut() = Some(d.clone());
        d
    }
}

// `LazyRight` deliberately does NOT implement `Clone`.  It is only ever
// shared via `Rc<LazyRight>` inside `Doc`, and `#[derive(Clone)] for Doc`
// only requires the *fields* (`Rc<LazyRight>`) to be `Clone`, which they
// always are — the `Rc` clone bumps the refcount without touching the inner
// thunk.  Omitting the impl turns any stray direct deep-clone of a
// `LazyRight` value into a compile error rather than a runtime panic.

// There is deliberately no whole-`Doc` `force()` helper: forcing a
// `LazyUnion`'s right branch eagerly runs the deferred `aboveNest`/`fill`
// reconstruction even for layouts that never break, degenerating
// reduction to O(n²) on large docs.  Every consumer must force the
// memoised thunk only on the path that actually needs it, matching HS's
// call-by-need `best`.

/// Wrap a `get`/`get1` reduction step as a memoised `Deferred` node, so
/// it is only run when `fits`/`lay` walks into it.
fn defer(f: impl FnOnce() -> Doc + 'static) -> Doc {
    Doc::Deferred(LazyRight::new(f))
}

/// HS `mkUnion` with a lazy right branch.
fn lazy_union(p: Doc, q: impl FnOnce() -> Doc + 'static) -> Doc {
    if matches!(p, Doc::Empty) {
        return Doc::Empty;
    }
    Doc::LazyUnion(rc(p), LazyRight::new(q))
}

impl Doc {
    pub fn empty() -> Doc {
        Doc::Empty
    }

    /// `text s` with `width = s.chars().count()` — the number of
    /// codepoints, exactly matching HS `P.text`'s `length s` (HS
    /// likewise counts codepoints, not terminal columns, so wide glyphs
    /// like CJK count as 1 in both).
    pub fn text<S: AsRef<str>>(s: S) -> Doc {
        let s = s.as_ref();
        // HS `Document (HtmlDoc d)` (`Html.hs:102-123, see line 104`): `text = HtmlDoc . text .
        // escapeHtmlEntities`.  In HtmlDoc mode we escape the content up front so
        // the stored bytes AND the layout width are the escaped form (a `<`
        // costs 4 columns, matching HS).  In plain mode this is the byte-faithful
        // `--prove` path — no escaping, visible-column width.
        if html_mode() {
            let esc = escape_html_entities(s);
            let w = esc.chars().count();
            Doc::text_w(&esc, w)
        } else {
            let w = fill_width(s);
            Doc::text_w(s, w)
        }
    }

    /// `text` with explicit width.  Use when `chars().count()` doesn't
    /// match the rendered column count (e.g. zero-width markers).
    pub fn text_w(s: &str, width: usize) -> Doc {
        if s.is_empty() && width == 0 {
            Doc::Empty
        } else {
            Doc::TextBeside(Rc::from(s), width, Rc::new(Doc::Empty))
        }
    }

    pub fn char(c: char) -> Doc {
        let mut buf = [0u8; 4];
        let s = c.encode_utf8(&mut buf);
        // HS `Document (HtmlDoc d)` (`Html.hs:102-123, see line 103`): `char = HtmlDoc . text .
        // escapeHtmlEntities . return`.  Escape in HtmlDoc mode (a bare `<`
        // becomes `&lt;`, width 4); plain mode is unchanged.
        if html_mode() {
            let esc = escape_html_entities(s);
            let w = esc.chars().count();
            Doc::text_w(&esc, w)
        } else {
            let w = fill_width(s);
            Doc::text_w(s, w)
        }
    }

    /// HS `<>` (beside without space).
    pub fn beside(self, other: Doc) -> Doc {
        beside_text(self, other)
    }

    /// HS `<+>` (beside with one space).
    pub fn beside_sp(self, other: Doc) -> Doc {
        if matches!(self, Doc::Empty) {
            return other;
        }
        if matches!(other, Doc::Empty) {
            return self;
        }
        self.beside(Doc::char(' ')).beside(other)
    }

    /// HS `$$` (above, no overlap-guard).  Concretely: emit self, then
    /// `NilAbove` (line break), then other.
    pub fn above(self, other: Doc) -> Doc {
        above_g(self, false, other)
    }

    /// HS `$+$` (above with single-line padding between).
    pub fn above_g(self, other: Doc) -> Doc {
        above_g(self, true, other)
    }

    /// HS `nest n p`.
    pub fn nest(self, n: isize) -> Doc {
        mk_nest(n, reduce_doc(self))
    }

    /// Render at the process-wide display width (see
    /// [`set_display_width`]): 110/73 for the CLI, 100/67 for the
    /// interactive web server.
    pub fn render(self) -> String {
        self.render_with(
            DISPLAY_LINE_LENGTH.load(Ordering::Relaxed),
            DISPLAY_RIBBON.load(Ordering::Relaxed),
        )
    }

    pub fn render_with(self, line_length: usize, ribbon: usize) -> String {
        let reduced = reduce_doc(self);
        let r = ribbon as isize;
        let best = get_doc(line_length as isize, r, &reduced);
        let mut out = String::new();
        lay(0, &best, &mut out);
        out
    }

    /// Render assuming `sl_initial` chars have already been emitted on
    /// the current line (e.g. when this Doc is laid out mid-line after
    /// a leading prefix).  Mirrors HS's `get1 w r sl_initial d`.
    /// The returned string is the Doc's rendering with continuation
    /// lines indented to start at column 0 (caller must pad as needed).
    pub fn render_at(self, line_length: usize, ribbon: usize, sl_initial: usize) -> String {
        let reduced = reduce_doc(self);
        let r = ribbon as isize;
        let best = get1(line_length as isize, r, sl_initial as isize, reduced);
        let mut out = String::new();
        // sl_initial doesn't appear in `out` (it's just budget bookkeeping);
        // continuation lines come from `lay`'s nest tracking.
        lay2(sl_initial as isize, &best, &mut out);
        out
    }

    /// HS `renderStyle (defaultStyle { mode = OneLineMode })` —
    /// `fullRender OneLineMode … = easyDisplay spaceText (\_ y -> y) …
    /// (reduceDoc doc)` (pretty-1.1.3.6 `Text.PrettyPrint.HughesPJ`,
    /// `fullRender`/`easyDisplay`): every `Union` takes its SECOND
    /// (fully-laid-out) branch — the one guaranteed free of `NoDoc` —
    /// every `Nest` is dropped, and every `NilAbove` (line break) becomes
    /// exactly ONE space.  Used by HS `Dot.hs:371-373`'s `oneLineRender`
    /// to measure each record field's used width for `renderBalanced`.
    pub fn one_line_render(&self) -> String {
        // Iterative for the same stack-depth reason as `lay_loop`.
        let mut out = String::new();
        let mut cur: Doc = self.clone();
        loop {
            cur = match cur {
                Doc::Empty => return out,
                Doc::NoDoc => panic!("one_line_render: NoDoc"),
                Doc::NilAbove(p) => {
                    out.push(' ');
                    (*p).clone()
                }
                Doc::TextBeside(s, _w, p) => {
                    out.push_str(&s);
                    (*p).clone()
                }
                Doc::Nest(_, p) => (*p).clone(),
                // `easyDisplay`'s chooser for OneLineMode is `\_ y -> y`.
                Doc::Union(_, q) => (*q).clone(),
                Doc::LazyUnion(_, r) => (*r.force()).clone(),
                Doc::Deferred(c) => (*c.force()).clone(),
            };
        }
    }
}

// ============================================================================
// Highlighting + HTML markup (port of Text.PrettyPrint.Highlight / .Html and
// Theory.Text.Pretty).  All markup is emitted as ZERO-WIDTH text so it never
// perturbs the layout the plain `--prove` path already produces byte-for-byte.
// The highlight combinators are the identity in plain mode; the `with_tag`/
// `closed_tag` helpers are web-pane-only (never reached from `--prove`) and
// always emit their tags, mirroring HS's `HtmlDoc`/`NoHtmlDoc` split.
// ============================================================================

/// HS `HighlightStyle` (`Text/PrettyPrint/Highlight.hs:33-34`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Hl {
    Keyword,
    Comment,
    Operator,
}

/// HS `hlClass` (`Text/PrettyPrint/Html.hs:133-135`).
fn hl_class(h: Hl) -> &'static str {
    match h {
        Hl::Comment => "hl_comment",
        Hl::Keyword => "hl_keyword",
        Hl::Operator => "hl_operator",
    }
}

impl Doc {
    /// HS `highlight` — `withTag "span" [("class", hlClass style)]` in the
    /// `HtmlDoc` instance (`Html.hs:129-135`), the identity in the plain `Doc`
    /// instance (`Highlight.hs:41-42`).
    pub fn highlight(self, style: Hl) -> Doc {
        if html_mode() {
            with_tag("span", &[("class", hl_class(style))], self)
        } else {
            self
        }
    }
}

/// HS `attribute` (`Html.hs:82-83, see line 83`): ` key="escaped-value"`.
fn push_attribute(buf: &mut String, key: &str, value: &str) {
    buf.push(' ');
    buf.push_str(key);
    buf.push_str("=\"");
    buf.push_str(&escape_html_entities(value));
    buf.push('"');
}

/// HS `withTag tag attrs inner` (`Html.hs:59-64`):
/// `unescapedZeroWidthText open <> inner <> unescapedZeroWidthText close`.
/// The open/close tags are ZERO-WIDTH (they don't move any line break), and the
/// inner document is laid out normally.  Used only when building web panes.
pub fn with_tag(tag: &str, attrs: &[(&str, &str)], inner: Doc) -> Doc {
    let mut open = String::from("<");
    open.push_str(tag);
    for (k, v) in attrs {
        push_attribute(&mut open, k, v);
    }
    open.push('>');
    let close = format!("</{tag}>");
    Doc::text_w(&open, 0)
        .beside(inner)
        .beside(Doc::text_w(&close, 0))
}

/// HS `closedTag tag attrs` (`Html.hs:71-73`): `<tag …/>` as zero-width text.
pub fn closed_tag(tag: &str, attrs: &[(&str, &str)]) -> Doc {
    let mut s = String::from("<");
    s.push_str(tag);
    for (k, v) in attrs {
        push_attribute(&mut s, k, v);
    }
    s.push_str("/>");
    Doc::text_w(&s, 0)
}

/// The opening `<span class="hl_*">` tag for a highlight style, or the empty
/// string in plain mode.  Together with [`hl_close`] this is the exact markup
/// HS `withTag "span"`/`highlight` emits (zero-width), exposed for the few
/// String-based printers that wrap an already-rendered MULTI-LINE block (e.g.
/// a `multiComment` around an expanded-formula block); injecting these at the
/// block's start/end is the same mechanism, and it leaves the plain-mode bytes
/// unchanged (both tags are the empty string in plain mode).
pub fn hl_open(style: Hl) -> String {
    if html_mode() {
        format!("<span class=\"{}\">", hl_class(style))
    } else {
        String::new()
    }
}

/// The closing `</span>` tag for a highlight style, or the empty string in
/// plain mode.  See [`hl_open`].  The style is accepted for call-site symmetry
/// with [`hl_open`] (every `</span>` is identical regardless of class).
pub fn hl_close(_style: Hl) -> String {
    if html_mode() {
        "</span>".to_string()
    } else {
        String::new()
    }
}

// -- General highlighters (HS Highlight.hs:48-59) -----------------------------

pub fn comment(d: Doc) -> Doc {
    d.highlight(Hl::Comment)
}
pub fn keyword(d: Doc) -> Doc {
    d.highlight(Hl::Keyword)
}
pub fn operator(d: Doc) -> Doc {
    d.highlight(Hl::Operator)
}

pub fn comment_(s: &str) -> Doc {
    comment(Doc::text(s))
}
pub fn keyword_(s: &str) -> Doc {
    keyword(Doc::text(s))
}
pub fn operator_(s: &str) -> Doc {
    operator(Doc::text(s))
}

/// HS `opParens d = operator_ "(" <> d <> operator_ ")"` (`Highlight.hs:58-59`).
pub fn op_parens(d: Doc) -> Doc {
    operator_("(").beside(d).beside(operator_(")"))
}

/// HS `parens p = char '(' <> p <> char ')'` (`Class.hs:149-149`) — PLAIN parens
/// (no highlight), used e.g. around `(modulo AC)`.
pub fn parens(d: Doc) -> Doc {
    Doc::char('(').beside(d).beside(Doc::char(')'))
}

// -- Comments (HS Theory.Text.Pretty.hs:96-112) -------------------------------

/// HS `lineComment_ s = comment $ text "//" <-> text s` (`Pretty.hs:96-100`).
pub fn line_comment_(s: &str) -> Doc {
    comment(Doc::text("//").beside_sp(Doc::text(s)))
}

/// HS `multiComment_ ls = comment $ fsep [text "/*", vcat (map text ls),
/// text "*/"]` (`Pretty.hs:105-106`).
pub fn multi_comment_(lines: &[&str]) -> Doc {
    let body = vcat(lines.iter().map(|l| Doc::text(*l)).collect());
    comment(fsep(vec![Doc::text("/*"), body, Doc::text("*/")]))
}

/// HS `closedComment_ s = comment $ fsep [text "/*", text s, text "*/"]`
/// (`Pretty.hs:111-112`).
pub fn closed_comment_(s: &str) -> Doc {
    comment(fsep(vec![Doc::text("/*"), Doc::text(s), Doc::text("*/")]))
}

// -- Keyword composites (HS Theory.Text.Pretty.hs:148-159) --------------------

/// HS `kwModulo what thy = keyword_ what <-> parens (keyword_ "modulo" <->
/// text thy)` (`Pretty.hs:148-152`).
pub fn kw_modulo(what: &str, thy: &str) -> Doc {
    keyword_(what).beside_sp(parens(keyword_("modulo").beside_sp(Doc::text(thy))))
}

/// HS `kwRuleModulo = kwModulo "rule"` (`Pretty.hs:154-156, see line 156`).
pub fn kw_rule_modulo(thy: &str) -> Doc {
    kw_modulo("rule", thy)
}

// -- Postprocessing (HS Html.hs:155-162) --------------------------------------

/// HS `postprocessHtmlDoc = unlines . map (addBreak . indent) . lines`
/// (`Html.hs:157-162`): every line's leading spaces become `&nbsp;` runs, a
/// `<br/>` is appended to every line, and lines are re-joined with `\n` (with a
/// trailing `\n`, matching `unlines`).  `lines` treats `\n` as a terminator, so
/// a trailing `\n` in the input does NOT create an extra empty line.
pub fn postprocess_html(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + s.len() / 4);
    let mut rest = s;
    loop {
        let (line, tail, more) = match rest.find('\n') {
            Some(idx) => (&rest[..idx], &rest[idx + 1..], true),
            None => {
                if rest.is_empty() {
                    break;
                }
                (rest, "", false)
            }
        };
        let mut suffix_offset = 0;
        for c in line.chars() {
            if c != ' ' {
                break;
            }
            out.push_str("&nbsp;");
            suffix_offset += c.len_utf8();
        }
        out.push_str(&line[suffix_offset..]);
        out.push_str("<br/>");
        out.push('\n');
        if !more {
            break;
        }
        rest = tail;
    }
    out
}

// ============================================================================
// Smart constructors (internal)
// ============================================================================

fn rc(d: Doc) -> Rc<Doc> {
    Rc::new(d)
}

/// HS `nilAbove_`.
fn nil_above_(d: Doc) -> Doc {
    Doc::NilAbove(rc(d))
}

/// HS `textBeside_ s p`.
fn text_beside_(s: Rc<str>, w: usize, p: Doc) -> Doc {
    Doc::TextBeside(s, w, rc(p))
}

/// HS `nest_ k p`.
fn nest_(k: isize, p: Doc) -> Doc {
    Doc::Nest(k, rc(p))
}

/// HS `union_ p q`.
fn union_(p: Doc, q: Doc) -> Doc {
    Doc::Union(rc(p), rc(q))
}

/// HS `mkUnion`: drop union if left is Empty.
fn mk_union(p: Doc, q: Doc) -> Doc {
    if matches!(p, Doc::Empty) {
        Doc::Empty
    } else {
        union_(p, q)
    }
}

/// HS `mkNest`.
fn mk_nest(k: isize, p: Doc) -> Doc {
    match p {
        Doc::Nest(k1, inner) => mk_nest(k + k1, (*inner).clone()),
        Doc::NoDoc => Doc::NoDoc,
        Doc::Empty => Doc::Empty,
        _ if k == 0 => p,
        _ => nest_(k, p),
    }
}

/// HS `elideNest`.
fn elide_nest(d: Doc) -> Doc {
    match d {
        Doc::Nest(_, inner) => (*inner).clone(),
        other => other,
    }
}

/// HS `reduceDoc` — our Doc has no `Above`/`Beside` lazy nodes so
/// reduceDoc is the identity.  Kept for parity.
fn reduce_doc(d: Doc) -> Doc {
    d
}

// ============================================================================
// Beside (HS `beside` — eager, RDoc->RDoc)
// ============================================================================

/// HS `beside p g q`.  Concats `p` followed by `q` (with optional space
/// `g` = True for `<+>`).  We eagerly walk and avoid storing lazy
/// `Beside` nodes.
fn beside_text(p: Doc, q: Doc) -> Doc {
    let q = reduce_doc(q);
    beside_inner(reduce_doc(p), false, q)
}

fn beside_inner(p: Doc, g: bool, q: Doc) -> Doc {
    match p {
        // HS `beside NoDoc _ _ = NoDoc`.
        Doc::NoDoc => Doc::NoDoc,
        // HS `beside Empty _ q = q`.
        Doc::Empty => q,
        // HS `beside (Nest k p) g q = nest_ k $! beside p g q`.
        Doc::Nest(k, inner) => nest_(k, beside_inner((*inner).clone(), g, q)),
        // HS `beside (p1 Union p2) g q = beside p1 g q union beside p2 g q`.
        // CRITICAL: HS's `union` is lazy in its right argument (a GHC thunk),
        // and `best`/`fits` only forces the right branch when the left fails to
        // fit.  Distributing `beside` over BOTH branches eagerly duplicates `q`
        // into each branch at CONSTRUCTION time; for a doc with nested `sep`s
        // (e.g. a large conjunction `A & B & C & …`) that builds a 2^depth tree
        // before reduction even starts, OOMing the renderer.  Mirror HS by
        // deferring the right branch exactly as the `LazyUnion` arm below does.
        Doc::Union(a, b) => {
            let q2 = q.clone();
            lazy_union(beside_inner((*a).clone(), g, q), move || {
                beside_inner((*b).clone(), g, q2)
            })
        }
        // Lazy distribution of `beside` over a LazyUnion (keep right lazy).
        Doc::LazyUnion(a, r) => {
            let q2 = q.clone();
            lazy_union(beside_inner((*a).clone(), g, q), move || {
                beside_inner((*r.force()).clone(), g, q2)
            })
        }
        // HS `beside (NilAbove p) g q = nilAbove_ $! beside p g q`.
        Doc::NilAbove(p1) => nil_above_(beside_inner((*p1).clone(), g, q)),
        // HS `beside (TextBeside t p) g q = TextBeside t rest
        //       where rest = case p of { Empty -> nilBeside g q
        //                               ; _     -> beside p g q }`.
        // CRITICAL: when the inner doc ends (rest = Empty), HS routes the
        // tail `q` through `nilBeside g`, which ELIDES q's leading `Nest`
        // (`nilBeside g (Nest _ p) = nilBeside g p`).  Recursing through
        // `beside_inner(Empty, g, q)` instead would RETAIN that leading
        // Nest, shifting later wrap columns by the nest amount (the NSPK3
        // GGuarded inner-sep drift).
        Doc::TextBeside(s, w, rest) => {
            let rest_inner = match &*rest {
                Doc::Empty => nil_beside(g, q),
                _ => beside_inner((*rest).clone(), g, q),
            };
            text_beside_(s, w, rest_inner)
        }
        // `Deferred` is produced only by `get`/`get1` during reduction,
        // never by the construction combinators that feed `beside`.
        Doc::Deferred(_) => unreachable!("Deferred only appears in reduced docs"),
    }
}

// ============================================================================
// Above (HS `above`)
// ============================================================================

fn above_g(p: Doc, g: bool, q: Doc) -> Doc {
    if matches!(p, Doc::Empty) {
        return q;
    }
    if matches!(q, Doc::Empty) {
        return p;
    }
    let p = reduce_doc(p);
    let q = reduce_doc(q);
    above_nest(p, g, 0, q)
}

/// HS `aboveNest` — combine `p $$ nest k q`.  The boolean `g` carries
/// the `$+$` flag (insert single-space line filler when one side is
/// effectively empty).
fn above_nest(p: Doc, g: bool, k: isize, q: Doc) -> Doc {
    match p {
        Doc::NoDoc => Doc::NoDoc,
        // HS `aboveNest (p Union q) g k r = aboveNest p g k r `union_`
        // aboveNest q g k r` (pretty-1.1.3.6 HughesPJ.hs:585).  CRITICAL:
        // under GHC's call-by-need both distributed branches are thunks —
        // `best`/`fits` forces the right one only when the left overflows.
        // Distributing eagerly into BOTH branches rebuilds `q` under every
        // Union alternative at construction time; for a union-rich doc (a
        // vcat of 18 ∃-substs over bilinear eCK terms, each a nest of
        // sep/fsep unions) that is O(2^depth) — the task-#19 web OOM
        // (8 GB, source-cases page, Chen_Kudla `Init_2`).  Mirror HS's
        // laziness exactly as `beside_inner`'s Union arm does: keep the
        // right branch a memoised thunk.
        Doc::Union(p1, p2) => {
            let q2 = q.clone();
            lazy_union(above_nest((*p1).clone(), g, k, q), move || {
                above_nest((*p2).clone(), g, k, q2)
            })
        }
        // Lazy distribution: keep the right branch a thunk.
        Doc::LazyUnion(p1, r) => {
            let q2 = q.clone();
            lazy_union(above_nest((*p1).clone(), g, k, q), move || {
                above_nest((*r.force()).clone(), g, k, q2)
            })
        }
        Doc::Empty => mk_nest(k, q),
        Doc::Nest(k1, inner) => nest_(k1, above_nest((*inner).clone(), g, k - k1, q)),
        Doc::NilAbove(p1) => nil_above_(above_nest((*p1).clone(), g, k, q)),
        Doc::TextBeside(s, w, rest) => {
            let k1 = k - w as isize;
            let rest_inner: Doc = (*rest).clone();
            let rest_q = match rest_inner {
                Doc::Empty => nil_above_nest(g, k1, q),
                other => above_nest(other, g, k1, q),
            };
            text_beside_(s, w, rest_q)
        }
        Doc::Deferred(_) => unreachable!("Deferred only appears in reduced docs"),
    }
}

/// HS `nilAboveNest`.
fn nil_above_nest(g: bool, k: isize, q: Doc) -> Doc {
    match q {
        Doc::Empty => Doc::Empty,
        Doc::Nest(k1, inner) => nil_above_nest(g, k + k1, (*inner).clone()),
        Doc::LazyUnion(p1, r) => lazy_union(nil_above_nest(g, k, (*p1).clone()), move || {
            nil_above_nest(g, k, (*r.force()).clone())
        }),
        other => {
            if !g && k > 0 {
                // HS: `textBeside_ (NoAnnot (Str (indent k)) k) q` —
                // emit `k` spaces inline.  We don't see this on the
                // sep/fsep path we care about but include for parity.
                let spaces: String = " ".repeat(k as usize);
                text_beside_(Rc::from(spaces.as_str()), k as usize, other)
            } else {
                nil_above_(mk_nest(k, other))
            }
        }
    }
}

// ============================================================================
// oneLiner
// ============================================================================

fn one_liner(d: Doc) -> Doc {
    match d {
        Doc::NoDoc | Doc::NilAbove(_) => Doc::NoDoc,
        Doc::Empty => Doc::Empty,
        Doc::TextBeside(s, w, p) => text_beside_(s, w, one_liner((*p).clone())),
        Doc::Nest(k, p) => nest_(k, one_liner((*p).clone())),
        Doc::Union(p, _) => one_liner((*p).clone()),
        // oneLiner takes only the left (flat) branch — never force `q`.
        Doc::LazyUnion(p, _) => one_liner((*p).clone()),
        Doc::Deferred(_) => unreachable!("Deferred only appears in reduced docs"),
    }
}

// ============================================================================
// sep / cat / fsep / fcat
// ============================================================================

/// HS `sep` — try one line (separated by spaces); else vertical.
pub fn sep(ds: Vec<Doc>) -> Doc {
    sep_x(true, ds)
}

/// HS `cat` — try one line (no separator); else vertical.
pub fn cat(ds: Vec<Doc>) -> Doc {
    sep_x(false, ds)
}

/// HS `fsep` — fill-style paragraph (greedy wrap), space-separated.
pub fn fsep(ds: Vec<Doc>) -> Doc {
    fill(true, ds)
}

/// HS `fcat` — fill-style paragraph, no separator.
pub fn fcat(ds: Vec<Doc>) -> Doc {
    fill(false, ds)
}

/// HS `ppTerms sepa n lead finish ts` (Term/Term.hs:288-290): an `fcat` of
/// `text lead`, each element rendered and `nest(1)`'d (all but the last
/// `sep`-suffixed), and `text finish`.  Shared by the pair (`<`/`, `/`>`)
/// and AC-op (`(`/op/`)`) builders across the parser-AST, GTerm and SAPIC
/// term renderers — they differ only in these three strings and the
/// per-element `render` fn, so every caller stays byte-identical.
pub fn fcat_bracketed<T>(
    lead: &str,
    sep: &str,
    finish: &str,
    items: &[&T],
    render: impl Fn(&T) -> Doc,
) -> Doc {
    let n = items.len();
    let mut parts: Vec<Doc> = Vec::with_capacity(n + 2);
    parts.push(Doc::text(lead));
    for (i, t) in items.iter().enumerate() {
        let mut d = render(t);
        if i + 1 < n {
            d = d.beside(Doc::text(sep));
        }
        parts.push(d.nest(1));
    }
    parts.push(Doc::text(finish));
    fcat(parts)
}

/// HS `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts))
/// <> text ")"` (Term/Term.hs:295-296).  Shared by the parser-AST, GTerm and
/// SAPIC function-application renderers — they differ only in the per-element
/// `render` fn, so the common `text(name++"(") <> fsep(punctuate ',' …) <>
/// text ")"` Doc shape lives here (HS `comma = char ','`).
pub fn fun_app_doc<T>(name: &str, args: &[&T], render: impl Fn(&T) -> Doc) -> Doc {
    let arg_docs: Vec<Doc> = args.iter().map(|a| render(a)).collect();
    let body = fsep(punctuate(Doc::char(','), arg_docs));
    Doc::text(format!("{}(", name))
        .beside(body)
        .beside(Doc::text(")"))
}

/// HS `nestShort' lead finish body =
///   nestShort (length lead + 1) (text lead) (text finish) body
///   = sep [ text lead $$ nest n body, text finish ]`
/// where `$$` is HughesPJ `above` and `n = length lead + 1`
/// (Class.hs:218-223).  Shared by the formula, fact and SAPIC renderers.
pub fn nest_short_doc(lead: &str, finish: &str, body: Doc) -> Doc {
    let n = lead.chars().count() as isize + 1;
    let above = Doc::text(lead).above(body.nest(n));
    sep(vec![above, Doc::text(finish)])
}

/// HS `hsep = foldr (\p q -> Beside p True q) empty` then reduce
/// (HughesPJ.hs:500).  RIGHT fold, no Empty-filtering — the `beside_`
/// smart constructor handles Empty.  Using a LEFT fold (or pre-filtering
/// Empty) builds a structurally different RDoc whose `Nest`/`Union`
/// accumulation diverges from HS for 3+ items (NSPK3 GGuarded inner sep).
pub fn hsep(ds: Vec<Doc>) -> Doc {
    foldr_beside(true, ds)
}

/// HS `hcat = foldr (\p q -> Beside p False q) empty` (HughesPJ.hs:496).
pub fn hcat(ds: Vec<Doc>) -> Doc {
    foldr_beside(false, ds)
}

/// HS `vcat = foldr (\p q -> Above p False q) empty` (HughesPJ.hs:504).
/// RIGHT fold.
pub fn vcat(ds: Vec<Doc>) -> Doc {
    // foldr Above empty ds  →  d0 $$ (d1 $$ (... $$ empty))
    let mut acc = Doc::Empty;
    for d in ds.into_iter().rev() {
        acc = above_g(d, false, acc);
    }
    acc
}

/// HS `foldr (\p q -> Beside p g q) empty` (the hsep/hcat shape).
fn foldr_beside(g: bool, ds: Vec<Doc>) -> Doc {
    let mut acc = Doc::Empty;
    for d in ds.into_iter().rev() {
        // `beside_ d g acc`: Empty operands collapse (Class/HughesPJ
        // `beside_ p _ Empty = p; beside_ Empty _ q = q`).
        acc = if matches!(d, Doc::Empty) {
            acc
        } else if matches!(acc, Doc::Empty) {
            d
        } else if g {
            d.beside_sp(acc)
        } else {
            d.beside(acc)
        };
    }
    acc
}

fn sep_x(x: bool, mut ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::Empty;
    }
    let first = ds.remove(0);
    sep1(x, reduce_doc(first), 0, ds)
}

/// HS `sep1`.
fn sep1(g: bool, p: Doc, k: isize, ys: Vec<Doc>) -> Doc {
    match p {
        Doc::NoDoc => Doc::NoDoc,
        Doc::Union(p, q) => {
            let left = sep1(g, (*p).clone(), k, ys.clone());
            lazy_union(left, move || {
                above_nest((*q).clone(), false, k, reduce_doc(vcat(ys)))
            })
        }
        // Keep the right branch a thunk: forcing it eagerly here would run its
        // `aboveNest`/`beside` reconstruction even for layouts that never break —
        // see `get`'s LazyUnion arm.
        Doc::LazyUnion(p, rt) => {
            let left = sep1(g, (*p).clone(), k, ys.clone());
            lazy_union(left, move || {
                above_nest((*rt.force()).clone(), false, k, reduce_doc(vcat(ys)))
            })
        }
        Doc::Deferred(c) => sep1(g, (*c.force()).clone(), k, ys),
        Doc::Empty => mk_nest(k, sep_x(g, ys)),
        Doc::Nest(n, inner) => nest_(n, sep1(g, (*inner).clone(), k - n, ys)),
        Doc::NilAbove(p) => nil_above_(above_nest((*p).clone(), false, k, reduce_doc(vcat(ys)))),
        Doc::TextBeside(s, w, p) => text_beside_(s, w, sep_nb(g, (*p).clone(), k - w as isize, ys)),
    }
}

/// HS `sepNB`.
fn sep_nb(g: bool, p: Doc, k: isize, ys: Vec<Doc>) -> Doc {
    match p {
        Doc::Nest(_, inner) => sep_nb(g, (*inner).clone(), k, ys),
        Doc::Empty => {
            // HS `sepNB g Empty k ys` (pretty-1.1.3.6 HughesPJ.hs:760-766):
            //   = oneLiner (nilBeside g (reduceDoc rest)) `mkUnion`
            //     nilAboveNest False k (reduceDoc (vcat ys))
            //   where rest | g = hsep ys | otherwise = hcat ys
            // The flag is `False` (see the XXX comment in pretty-1.1.3.6
            // — GHC's bundled pretty settled on False).
            let rest = if g {
                hsep(ys.clone())
            } else {
                hcat(ys.clone())
            };
            let left = one_liner(nil_beside(g, reduce_doc(rest)));
            let right = nil_above_nest(false, k, reduce_doc(vcat(ys)));
            mk_union(left, right)
        }
        _ => sep1(g, p, k, ys),
    }
}

/// HS `nilBeside`.
fn nil_beside(g: bool, p: Doc) -> Doc {
    match p {
        Doc::Empty => Doc::Empty,
        Doc::Nest(_, inner) => nil_beside(g, (*inner).clone()),
        Doc::LazyUnion(p1, r) => lazy_union(nil_beside(g, (*p1).clone()), move || {
            nil_beside(g, (*r.force()).clone())
        }),
        other => {
            if g {
                text_beside_(Rc::from(" "), 1, other)
            } else {
                other
            }
        }
    }
}

/// HS `fill` — paragraph-fill greedy wrap.
fn fill(g: bool, mut ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::Empty;
    }
    let first = ds.remove(0);
    fill1(g, reduce_doc(first), 0, ds)
}

/// HS `fill1`.
fn fill1(g: bool, p: Doc, k: isize, ys: Vec<Doc>) -> Doc {
    match p {
        Doc::NoDoc => Doc::NoDoc,
        Doc::Union(p, q) => {
            // Keep the right (line-breaking) branch lazy — it re-fills the
            // remaining items and is only needed if the flat layout fails.
            let left = fill1(g, (*p).clone(), k, ys.clone());
            lazy_union(left, move || {
                above_nest((*q).clone(), false, k, fill(g, ys))
            })
        }
        // Keep the right branch a thunk (see `sep1`/`get`): forcing it eagerly
        // here degenerates fill reduction to O(n²) on large docs.
        Doc::LazyUnion(p, rt) => {
            let left = fill1(g, (*p).clone(), k, ys.clone());
            lazy_union(left, move || {
                above_nest((*rt.force()).clone(), false, k, fill(g, ys))
            })
        }
        Doc::Deferred(c) => fill1(g, (*c.force()).clone(), k, ys),
        Doc::Empty => mk_nest(k, fill(g, ys)),
        Doc::Nest(n, inner) => nest_(n, fill1(g, (*inner).clone(), k - n, ys)),
        Doc::NilAbove(p) => nil_above_(above_nest((*p).clone(), false, k, fill(g, ys))),
        Doc::TextBeside(s, w, p) => {
            text_beside_(s, w, fill_nb(g, (*p).clone(), k - w as isize, ys))
        }
    }
}

/// HS `fillNB`.
fn fill_nb(g: bool, p: Doc, k: isize, ys: Vec<Doc>) -> Doc {
    match p {
        Doc::Nest(_, inner) => fill_nb(g, (*inner).clone(), k, ys),
        Doc::Empty => {
            if ys.is_empty() {
                return Doc::Empty;
            }
            // Skip leading Empty ys.
            let mut iter = ys.into_iter();
            let y_first = loop {
                match iter.next() {
                    None => return Doc::Empty,
                    Some(Doc::Empty) => continue,
                    Some(d) => break d,
                }
            };
            let rest: Vec<Doc> = iter.collect();
            fill_nbe(g, k, y_first, rest)
        }
        other => fill1(g, other, k, ys),
    }
}

/// HS `fillNBE` (pretty-1.1.3.6 HughesPJ.hs:824+):
///   fillNBE g k y ys
///     = nilBeside g (fill1 g ((elideNest . oneLiner . reduceDoc) y) k1 ys)
///         `mkUnion` nilAboveNest False k (fill g (y:ys))
///     where k1 | g = k - 1 | otherwise = k
fn fill_nbe(g: bool, k: isize, y: Doc, ys: Vec<Doc>) -> Doc {
    let k1 = if g { k - 1 } else { k };
    let inner_y = elide_nest(one_liner(reduce_doc(y.clone())));
    let left = nil_beside(g, fill1(g, inner_y, k1, ys.clone()));
    // Right branch (`fill g (y:ys)`) re-fills the whole remaining list —
    // keep it lazy so it is only built when the flat layout doesn't fit.
    lazy_union(left, move || {
        let mut y_and_ys = vec![y];
        y_and_ys.extend(ys);
        nil_above_nest(false, k, fill(g, y_and_ys))
    })
}

// ============================================================================
// best / get / get1 / nicest1 / fits
// ============================================================================

/// HS `best w r doc = get w doc`.
fn get_doc(w: isize, r: isize, d: &Doc) -> Doc {
    get(w, r, d.clone())
}

/// HS `get w doc` (line-start case).
///
/// LAZINESS (the whole point — see `Doc::Deferred`): every recursive
/// reduction is wrapped in `defer`, so this returns only the HEAD
/// constructor of the reduced doc; the tail is a memoised thunk forced on
/// demand.  `fits` (which stops at the first `NilAbove`) therefore forces
/// only the first line of a `Union`'s left branch before deciding, and the
/// unchosen alternatives are never materialised.  This mirrors HS's
/// call-by-need `best` and keeps reduction O(output) instead of O(2^depth).
fn get(w: isize, r: isize, d: Doc) -> Doc {
    match d {
        Doc::Empty => Doc::Empty,
        Doc::NoDoc => Doc::NoDoc,
        Doc::NilAbove(p) => nil_above_(defer(move || get(w, r, (*p).clone()))),
        Doc::TextBeside(s, sw, p) => {
            let len = sw as isize;
            text_beside_(s, sw, defer(move || get1(w, r, len, (*p).clone())))
        }
        Doc::Nest(k, p) => nest_(k, defer(move || get(w - k, r, (*p).clone()))),
        Doc::Union(p, q) => {
            // nicest1 w r 0 (get w p) (get w q): only `get` the flat branch
            // `p` (returns its head + deferred tail); `fits` forces just its
            // first line.  The line-breaking branch `q` is reduced ONLY when
            // `p` overflows.
            let p1 = get(w, r, (*p).clone());
            let budget = std::cmp::min(w, r); // sl = 0 here
            if fits(budget, &p1) {
                p1
            } else {
                get(w, r, (*q).clone())
            }
        }
        // CRITICAL (task #20 perf): a `LazyUnion` must NOT be `force()`d at
        // the match head — that RUNS the right-branch thunk (an
        // `aboveNest`/`fill` reconstruction over the remaining doc) even
        // when the flat branch fits, degenerating reduction to O(n²) on
        // large docs (the one-Doc web constraint-system pane).  HS's
        // call-by-need `best` evaluates `q` only when `p` overflows;
        // mirror that by forcing the thunk exclusively on the failure path.
        Doc::LazyUnion(p, rt) => {
            let p1 = get(w, r, (*p).clone());
            let budget = std::cmp::min(w, r); // sl = 0 here
            if fits(budget, &p1) {
                p1
            } else {
                get(w, r, (*rt.force()).clone())
            }
        }
        Doc::Deferred(c) => get(w, r, (*c.force()).clone()),
    }
}

/// HS `get1 w sl doc` (in-line, after `sl` cols of text).
fn get1(w: isize, r: isize, sl: isize, d: Doc) -> Doc {
    match d {
        Doc::Empty => Doc::Empty,
        Doc::NoDoc => Doc::NoDoc,
        Doc::NilAbove(p) => {
            // After a line break the next line's budget shrinks by `sl`.
            nil_above_(defer(move || get(w - sl, r, (*p).clone())))
        }
        Doc::TextBeside(s, sw, p) => {
            let len = sw as isize;
            text_beside_(s, sw, defer(move || get1(w, r, sl + len, (*p).clone())))
        }
        // Nest is a no-op while we're already mid-line.
        Doc::Nest(_k, p) => get1(w, r, sl, (*p).clone()),
        Doc::Union(p, q) => {
            let p1 = get1(w, r, sl, (*p).clone());
            let budget = std::cmp::min(w, r) - sl;
            if fits(budget, &p1) {
                p1
            } else {
                get1(w, r, sl, (*q).clone())
            }
        }
        // See `get`'s LazyUnion arm: force the right branch ONLY when the
        // flat branch overflows (HS call-by-need).
        Doc::LazyUnion(p, rt) => {
            let p1 = get1(w, r, sl, (*p).clone());
            let budget = std::cmp::min(w, r) - sl;
            if fits(budget, &p1) {
                p1
            } else {
                get1(w, r, sl, (*rt.force()).clone())
            }
        }
        Doc::Deferred(c) => get1(w, r, sl, (*c.force()).clone()),
    }
}

/// HS `fits`.
fn fits(n: isize, d: &Doc) -> bool {
    if n < 0 {
        return false;
    }
    match d {
        Doc::NoDoc => false,
        Doc::Empty => true,
        Doc::NilAbove(_) => true,
        Doc::TextBeside(_, w, p) => fits(n - *w as isize, p),
        Doc::Nest(_, p) => fits(n, p),
        Doc::Union(p, _) => fits(n, p), // pre-reduced, but be defensive
        // Only the left (flat) branch matters for fits; never force `q`.
        Doc::LazyUnion(p, _) => fits(n, p),
        // A deferred reduction tail: force it (memoised) and continue.
        // `fits` stops at the first `NilAbove`, so this only ever forces
        // the first line of a reduced branch.
        Doc::Deferred(c) => fits(n, &c.force()),
    }
}

// ============================================================================
// lay (render an RDoc to String)
// ============================================================================

/// HS `lay` — walk the reduced doc, accumulating output.
///
/// ITERATIVE (task #20): the walk is a pure state machine — `lay` (at
/// line start, where `Nest` bumps the column and the first text emits the
/// indent) vs `lay2` (mid-line, `Nest` inert) — so it is driven by a loop
/// with a `line_start` flag instead of mutual recursion.  The recursive
/// form's depth is the doc's total token count, which overflows the 2 MiB
/// tokio worker stacks now that the web constraint-system pane is one
/// single Doc (HS `prettyNonGraphSystem = vsep …`).  Semantics are
/// byte-identical to the recursive HS `lay`/`lay2` pair.
fn lay(k: isize, d: &Doc, out: &mut String) {
    lay_loop(k, d, out, true)
}

/// HS `lay2` — continuation on the SAME line (no indent emission until
/// NilAbove).  See `lay` for the loop rationale.
fn lay2(k: isize, d: &Doc, out: &mut String) {
    lay_loop(k, d, out, false)
}

fn lay_loop(k0: isize, d: &Doc, out: &mut String, line_start0: bool) {
    let mut k = k0;
    let mut line_start = line_start0;
    let mut cur: Doc = d.clone();
    loop {
        cur = match cur {
            Doc::Empty => return,
            Doc::NoDoc => panic!(
                "pretty_hpj::lay: NoDoc reached — best should have picked a fitting alternative"
            ),
            // `lay (k + k1)` at line start; `lay2` ignores Nest mid-line.
            Doc::Nest(k1, p) => {
                if line_start {
                    k += k1;
                }
                (*p).clone()
            }
            // Both `lay` and `lay2` continue at column `k` on the next
            // line (HS `lay2 k (NilAbove p) = nlText <> lay k p`).
            Doc::NilAbove(p) => {
                out.push('\n');
                line_start = true;
                (*p).clone()
            }
            Doc::TextBeside(s, w, p) => {
                // First char of this line: emit indent if buffer is empty
                // OR the last char was '\n'.  `'\n'` is ASCII, so the
                // trailing-byte check is O(1) (no full-output scan).
                if line_start && (out.is_empty() || out.ends_with('\n')) {
                    for _ in 0..k.max(0) {
                        out.push(' ');
                    }
                }
                out.push_str(&s);
                k += w as isize;
                line_start = false;
                (*p).clone()
            }
            Doc::Deferred(c) => (*c.force()).clone(),
            Doc::Union(_, _) => panic!("pretty_hpj::lay: Union — best did not reduce"),
            Doc::LazyUnion(_, _) => panic!("pretty_hpj::lay: LazyUnion — best did not reduce"),
        };
    }
}

// ============================================================================
// Punctuation helpers (HS `punctuate`).
// ============================================================================

/// `punctuate sep docs` — interleave `sep` after each non-last doc.
/// E.g. `punctuate "," [a;b;c]` → `[a<>"," ; b<>"," ; c]`.
pub fn punctuate(sep: Doc, ds: Vec<Doc>) -> Vec<Doc> {
    let n = ds.len();
    if n == 0 {
        return Vec::new();
    }
    let mut out = Vec::with_capacity(n);
    for (i, d) in ds.into_iter().enumerate() {
        if i + 1 == n {
            out.push(d);
        } else {
            out.push(d.beside(sep.clone()));
        }
    }
    out
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_renders_verbatim() {
        assert_eq!(Doc::text("hello").render(), "hello");
        assert_eq!(Doc::empty().render(), "");
    }

    #[test]
    fn beside_concats() {
        assert_eq!(Doc::text("a").beside(Doc::text("b")).render(), "ab");
    }

    #[test]
    fn beside_sp_inserts_space() {
        assert_eq!(Doc::text("a").beside_sp(Doc::text("b")).render(), "a b");
    }

    #[test]
    fn above_inserts_newline() {
        let d = Doc::text("a").above(Doc::text("b"));
        assert_eq!(d.render(), "a\nb");
    }

    #[test]
    fn nest_indents_continuation() {
        // HS `$$` (above_g=false) ALLOWS the second line's first text
        // to overlap onto p's last line when nest gap permits.
        // `text "a" $$ nest 2 (text "b")` becomes "a b" (overlap with
        // 1 inline space, since `a` took col 0 and `nest 2` shifts to
        // col 2 = 1 space after `a`).  HS `nilAboveNest g=False k=1 q`
        // line: `textBeside_ (Str " ") q`.
        let d = Doc::text("a").above(Doc::text("b").nest(2));
        assert_eq!(d.render(), "a b");
        // Forcing a newline requires `$+$` (above_g=true) or `sep` of
        // multi-line content.
        let d = sep(vec![Doc::text("aaaaaa"), Doc::text("bbbbbb")]);
        let out = d.render_with(5, 5);
        assert!(out.contains('\n'), "got: {out}");
    }

    #[test]
    fn sep_fits_horizontal() {
        let d = sep(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]);
        assert_eq!(d.render(), "a b c");
    }

    #[test]
    fn sep_breaks_when_too_wide() {
        // Force the sep to wrap by exceeding ribbon width.
        let long = "x".repeat(40);
        let d = sep(vec![Doc::text(&long), Doc::text(&long)]).nest(0);
        let out = d.render_with(50, 50);
        assert!(out.contains('\n'), "expected wrap: {out}");
    }

    #[test]
    fn fsep_packs_greedy() {
        let words: Vec<Doc> = (0..10).map(|i| Doc::text(format!("w{}", i))).collect();
        let d = fsep(words);
        let out = d.render_with(20, 20);
        assert!(out.contains('\n'));
        // First line should hold several words.
        let first_line = out.split('\n').next().unwrap();
        assert!(first_line.starts_with("w0 w1"), "got: {out}");
    }

    #[test]
    fn nicest1_w_shrinks_at_nilabove() {
        // Verify that w shrinks at NilAbove: a sep where the LEFT fits
        // but the right would need a shrunk budget to choose vertical.
        //
        // sep [aaa, sep [bbb, ccc]] at width 6: outer sep tries flat
        // "aaa bbb ccc" (11 chars) — doesn't fit width 6, wraps.
        // Result: "aaa\nbbb ccc" or "aaa\nbbb\nccc"?
        // Per HS algorithm, after the outer NilAbove, inner sep gets
        // w = 6 - 0 = 6 (sl=0 since text started at start-of-line).
        // Inner flat "bbb ccc" = 7 chars > 6, so wraps to "bbb\nccc".
        let d = sep(vec![
            Doc::text("aaa"),
            sep(vec![Doc::text("bbb"), Doc::text("ccc")]),
        ]);
        let out = d.render_with(6, 6);
        assert_eq!(out, "aaa\nbbb\nccc", "got: {out:?}");
    }

    #[test]
    fn punctuate_separates() {
        let docs = vec![Doc::text("a"), Doc::text("b"), Doc::text("c")];
        let p = punctuate(Doc::text(","), docs);
        let d = hcat(p);
        assert_eq!(d.render(), "a,b,c");
    }

    #[test]
    fn nested_binop_w_shrinks_with_depth() {
        // Mirror the wireguard "5-deep And" case (pattern 2 from
        // commit 681224a7 follow-up).  Build a deep `(A ∧ B)` sep
        // where each level is `sep [opParens(left) <+> "∧", opParens(right)]`.
        //
        // With ribbon=73 measured from line start (sl=0 first line),
        // after the outermost sep wraps to vertical, the inner sep
        // gets `w` shrunk by `sl` (col where prior text started) and
        // should wrap too.
        let conn = |l: Doc, r: Doc| sep(vec![l.beside_sp(Doc::text("\u{2227}")), r]);
        // Simpler test: sep deep nesting at width 40 should wrap.
        let mut d = Doc::text("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"); // 36 chars
        for _ in 0..3 {
            d = conn(
                Doc::text("[").beside(d).beside(Doc::text("]")),
                Doc::text("y"),
            );
        }
        let out = d.render_with(50, 50);
        // Verify SOMETHING wrapped (we'd be at >50 cols otherwise).
        assert!(out.contains('\n'));
    }

    #[test]
    fn wireguard_5_deep_and_layout() {
        // Mirror wireguard UKS_resistance lemma's deep And exactly.
        // Goal: produce HS's wrap shape (break at the inner And) for:
        //   (((((pki1 = pki2) ∧ (pkr1 = pkr2)) ∧ (peki1 = peki2)) ∧
        //     (pekr1 = pekr2)) ∧
        //    (psk1 = psk2))
        // The top-level Doc has 4 chars of leading indent (from
        // lemma-body), then opParens cascading.
        let op_parens = |d: Doc| Doc::text("(").beside(d).beside(Doc::text(")"));
        let eq = |a: &str, b: &str| Doc::text(format!("{} = {}", a, b));
        let and = "\u{2227}";
        let conn = |l: Doc, r: Doc| {
            // HS: sep [opParens(l) <+> op, opParens(r)]
            sep(vec![op_parens(l).beside_sp(Doc::text(and)), op_parens(r)])
        };
        let a = eq("pki1", "pki2");
        let b = eq("pkr1", "pkr2");
        let c = eq("peki1", "peki2");
        let d_eq = eq("pekr1", "pekr2");
        let e = eq("psk1", "psk2");
        // ((((A ∧ B) ∧ C) ∧ D) ∧ E)
        let ab = conn(a, b);
        let abc = conn(ab, c);
        let abcd = conn(abc, d_eq);
        let abcde = conn(abcd, e);
        // Wrap in outer opParens (from Implies's right opParens).
        let full = op_parens(abcde);
        // Lay out at 4-space indent.
        let indented = Doc::text("    ").beside(full);
        let out = indented.render();
        // HS produces (we want):
        //     (((((pki1 = pki2) ∧ (pkr1 = pkr2)) ∧ (peki1 = peki2)) ∧
        //       (pekr1 = pekr2)) ∧
        //      (psk1 = psk2))
        let expected =
            "    (((((pki1 = pki2) \u{2227} (pkr1 = pkr2)) \u{2227} (peki1 = peki2)) \u{2227}\n      (pekr1 = pekr2)) \u{2227}\n     (psk1 = psk2))";
        assert_eq!(out, expected, "got:\n{out}\n---\nexpected:\n{expected}");
    }

    #[test]
    fn wireguard_aead_fsep_breaks_before_e() {
        // Mirror wireguard Handshake_Complete In( ... ) input.
        // Goal: pp_term `aead( h(<pair>), 'e', h(<pair>) )` at indent
        // = 10 should break before `'e',` per HS (line 626 in HS
        // output).
        //
        // HS's `prettyTerm` for App uses
        //   `ppFun f ts = text (f++"(") <> fsep (punctuate "," (map ppTerm ts)) <> text ")"`.
        // The `fsep` breaks at item boundaries when the next item
        // wouldn't fit.
        //
        // We approximate the inner h(<pair>) as a long opaque text
        // and verify the fsep breaks before "'e',".
        let arg1 = Doc::text("h(<h(<h(<h(<ci2, pekR, '1'>), z, '1'>), z.1, '1'>), ~psk, '3'>)");
        let arg2 = Doc::text("'e'");
        let arg3 = Doc::text(
            "h(<h(<hi1, pekR>), h(<h(<h(<h(<ci2, pekR, '1'>), z, '1'>), z.1, '1'>), ~psk, '2'>)>)",
        );
        let comma = Doc::text(",");
        let items = punctuate(comma, vec![arg1, arg2, arg3]);
        let body = fsep(items);
        let full = Doc::text("aead(").beside(body).beside(Doc::text(")"));
        // Layout at col 10 (after leading "          ").
        let lead = Doc::text("          ");
        let d = lead.beside(full);
        let out = d.render();
        // Verify there's a break before "'e',".
        let lines: Vec<&str> = out.split('\n').collect();
        assert!(lines.len() >= 3, "expected at least 3 lines, got: {out}");
        // Find the line that starts with the 'e' (after leading whitespace).
        let has_e_alone = lines.iter().any(|l| l.trim_start().starts_with("'e'"));
        assert!(has_e_alone, "expected 'e' on its own line; got:\n{out}");
    }

    #[test]
    fn sep_vertical_col_alignment() {
        // sep [text "a", text "b"] when wrapped: should b appear at
        // col 0 (where a started) or somewhere else?
        let d = sep(vec![Doc::text("aaaaaaaaaa"), Doc::text("bbbbbbbbbb")]);
        let out = d.render_with(10, 10);
        // Expected: "aaaaaaaaaa\nbbbbbbbbbb" — b at col 0.
        assert_eq!(out, "aaaaaaaaaa\nbbbbbbbbbb", "got: {out:?}");
    }

    #[test]
    fn nested_sep_indent_alignment() {
        // sep [quant, sep [dante.nest(1), conn, dsucc.nest(1)]]
        // When outer wraps, where does inner sep start?
        // If inner sep also wraps, where do conn and dsucc go?
        let quant = Doc::text("Q.");
        let dante = Doc::text("DANTE");
        let conn = Doc::text("c");
        let dsucc = Doc::text("DSUCC");
        let inner = sep(vec![dante.nest(1), conn, dsucc.nest(1)]);
        let outer = sep(vec![quant, inner]);
        // At width 10, both seps wrap.
        let out = outer.render_with(10, 10);
        // We want HS-like alignment:
        // "Q.\n DANTE\nc\n DSUCC"
        assert_eq!(out, "Q.\n DANTE\nc\n DSUCC");
    }

    // The guarded-formula layout runs through `guarded_to_doc` on this
    // engine — see `pretty_formula.rs::pretty_guarded_doublequoted`.

    #[test]
    fn pkcs11_eleven_tuple_close_bracket_glue() {
        // Regression for the pkcs11-templates variant-subst tuple wrap
        // (cannot_obtain_key et al.).  HS renders the AC-variant block via
        //   numbered' (map ppConj substs)   (SubstVFresh.hs:223-227)
        // where each numbered item is `text i <> ". " <> vcat[prettyEq..]`
        // at nest 4.  The `". " <>` BESIDE onto the multi-line vcat measures
        // the inner fcat's ribbon from the OUTER (numbered) line start, so an
        // 11-tuple `<x.16, …, x.26>` breaks BEFORE x.26 (gluing `>`).
        // Confirms the engine reproduces the HS structure
        // byte-for-byte (verified against Text.PrettyPrint.HughesPJ ll=110).
        // term_doc = pair_doc(11 elements) = fcat([ "<", e0", ", ... e10, ">" ]).
        // Elements x.16..x.26 are 4 chars each, nest(1)'d, comma-suffixed.
        let mk_pair = || {
            let n = 11;
            let mut parts: Vec<Doc> = Vec::with_capacity(n + 2);
            parts.push(Doc::text("<"));
            for i in 0..n {
                let name = format!("x.{}", 16 + i);
                let mut d = Doc::text(name);
                if i + 1 < n {
                    d = d.beside(Doc::text(", "));
                }
                parts.push(d.nest(1));
            }
            parts.push(Doc::text(">"));
            fcat(parts)
        };
        // HS structure (SubstVFresh.hs:227-229 + Class.hs:252-264):
        //   numbered' = numbered (text "") . map (text ". " <>)
        //   each item = text(flushRight w i) <> (text ". " <> vcat[prettyEq..])
        //   prettyEq (a,b) = text a $$ nest 6 (text "=" <-> term)
        // The whole `variants (modulo AC)` block sits at nest 4.
        let prettyeq = |v: &str, t: Doc| Doc::text(v).above(Doc::text("=").beside_sp(t).nest(6));
        let conj = prettyeq("v", mk_pair());
        let item = Doc::text("3").beside(Doc::text(". ").beside(conj));
        let out = item.nest(4).render();
        // HS-faithful expectation: break BEFORE x.26, glue '>' to it.
        let expected = "    3. v     = <x.16, x.17, x.18, x.19, x.20, x.21, x.22, x.23, x.24, x.25, \n                x.26>";
        assert_eq!(out, expected, "got:\n{out}");
    }

    #[test]
    fn dnp3_tuple_fill_keystatus_on_first_line() {
        // dnp3-proven Action goal:
        //   solve( !KU( senc(<~CDSK_j_USR_O, MDSK_j_USR_O, KSQ.1, $USR,
        //                     keystatus, CD_j>, ~UK_i_USR_O) ) @ #vk.11 )
        // HS packs `keystatus,` on the FIRST line of the tuple `fcat`
        // (the element fits within the ribbon measured from the line
        // start).  This pins the `fcat` fill-boundary byte-for-byte vs
        // `Text.PrettyPrint.HughesPJ` at lineLength 110 / ribbon 73.
        let elems = [
            "~CDSK_j_USR_O",
            "MDSK_j_USR_O",
            "KSQ.1",
            "$USR",
            "keystatus",
            "CD_j",
        ];
        let n = elems.len();
        let mut parts: Vec<Doc> = Vec::new();
        parts.push(Doc::text("<"));
        for (i, e) in elems.iter().enumerate() {
            let mut d = Doc::text(*e);
            if i + 1 < n {
                d = d.beside(Doc::text(", "));
            }
            parts.push(d.nest(1));
        }
        parts.push(Doc::text(">"));
        let tuple = fcat(parts);
        // senc( tuple , ~UK_i_USR_O ): "senc(" <> fsep(punctuate(",", [tuple,key])) <> ")"
        let senc_body = fsep(punctuate(
            Doc::char(','),
            vec![tuple, Doc::text("~UK_i_USR_O")],
        ));
        let senc = Doc::text("senc(").beside(senc_body).beside(Doc::text(")"));
        // !KU( senc ): nestShort' ("!KU(", ")", fsep([senc]))
        let lead = "!KU(";
        let nku_body = fsep(punctuate(Doc::char(','), vec![senc]));
        let nn = lead.chars().count() as isize + 1;
        let above = Doc::text(lead).above(nku_body.nest(nn));
        let nku = sep(vec![above, Doc::text(")")]);
        // Action goal: solve( !KU(...) @ #vk.11 )
        let goal = nku.beside_sp(Doc::text("@")).beside_sp(Doc::text("#vk.11"));
        let solve = Doc::text("solve(")
            .beside_sp(goal)
            .beside_sp(Doc::text(")"));
        let out = solve.nest(16).render();
        let first = out.split('\n').next().unwrap();
        assert!(
            first.trim_end().ends_with("keystatus,"),
            "expected `keystatus,` on the first tuple line; got:\n{out}",
        );
    }

    #[test]
    fn fcat_close_bracket_separate_item() {
        // Pattern 1: pair `<a, b, c>` modeled as fcat with `>` as a
        // separate final item.  When the items pack to fit, then add
        // `>` — if `>` would overflow at the boundary, fcat should
        // break BEFORE the `>`.
        let items = vec![
            Doc::text("<"),
            Doc::text("aaa,"),
            Doc::text("bbb,"),
            Doc::text("ccc,"),
            Doc::text("ddd"),
            Doc::text(">"),
        ];
        let d = fcat(items);
        // At width 12, items pack greedily.  "abc" pattern.
        let out = d.render_with(12, 12);
        // Verify '<' is on first line, '>' is on its own line or
        // attached to ddd.
        assert!(out.starts_with('<'), "got: {out:?}");
    }
}

#[cfg(test)]
mod sep_nb_regression {
    use super::*;

    /// Regression for the `sepNB`/`fillNBE` `nilAboveNest` column
    /// behaviour.
    ///
    /// HS `sepNB g Empty k ys` builds its wrapped tail via
    /// `nilAboveNest False k ...` — the flag is `False` (GHC's bundled
    /// pretty-1.1.3.6 settled on `False`; see the matching comment on
    /// the `sep_nb` `Empty` arm).  `nilAboveNest`'s flag governs where
    /// the wrapped tail item lands: this test pins that the second
    /// disjunct keeps its expected column rather than being inlined and
    /// dropped one column to the left.
    ///
    /// This case mirrors NSPK3 injective_agree's all-counterexamples
    /// guarded formula: a GDisj whose disjuncts are GGuarded with
    /// recursive `∀`-bodies that themselves wrap.  The expected output is
    /// byte-identical to `Text.PrettyPrint.HughesPJ` (verified against the
    /// real library at width 50 / ribbon 33).
    #[test]
    fn nested_sep_disjunct_second_item_column() {
        let opp = |d: Doc| Doc::text("(").beside(d).beside(Doc::text(")"));
        let fa = |atom: &str| {
            let quant = Doc::text("F.");
            let dante = opp(Doc::text(atom)).nest(1);
            let conn = Doc::text("=>");
            let dsucc = Doc::text("RHS").nest(1);
            sep(vec![quant, sep(vec![dante, conn, dsucc])])
        };
        let mkdj = |label: &str| {
            let quant = Doc::text(format!("Q{}.", label));
            let dante = opp(Doc::text("DANTE")).nest(1);
            let conn = Doc::text("C");
            let g1 = opp(fa("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")).beside(Doc::text(" &"));
            let g2 = opp(fa("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB"));
            let dsucc = sep(vec![g1, g2]).nest(1);
            sep(vec![quant, sep(vec![dante, conn, dsucc])])
        };
        let mp = punctuate(Doc::text(" |"), vec![opp(mkdj("x")), opp(mkdj("y"))]);
        let out = Doc::text("(")
            .beside(sep(mp))
            .beside(Doc::text(")"))
            .render_with(50, 33);
        let expected = "\
((Qx.
   (DANTE)
  C
   (F.
     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)
    =>
     RHS) &
   (F.
     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)
    =>
     RHS)) |
 (Qy.
   (DANTE)
  C
   (F.
     (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA)
    =>
     RHS) &
   (F.
     (BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB)
    =>
     RHS)))";
        assert_eq!(out, expected, "got:\n{out}");
    }
}
