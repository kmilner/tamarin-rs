// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! HughesPJ-faithful pretty-printer Doc engine.
//!
//! Port of the layout algorithm from
//! `Text.PrettyPrint.HughesPJ` (pretty-1.1.3.6) — the non-annotated
//! module used in production (HS `Text/PrettyPrint/Class.hs:64-67, see line 67`/`:72`).
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
//!
//! Construction combinators consume unreduced documents. Layout produces
//! private `Deferred` continuations; those reduced documents must not be fed
//! back into construction. In particular, the defensive `force` arms in
//! `sep1`/`fill1` are not a general evaluator for mixed construction/layout
//! graphs. Production rendering returns text, preserving this boundary.

use std::rc::Rc;

// HS `flushRight` (`Extension/Prelude.hs:204-209`): left-pad with spaces to a
// given character width, no truncation.
use crate::prelude_ext::flush_right;

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
///     `src/Web/Handler.hs:1015-1022, see line 1021`) and by `renderHtmlDoc`
///     (`Text/PrettyPrint/Html.hs:152-153`).
///
/// Defaults to 110/73 so the CLI path is unchanged; the server calls
/// [`set_display_width`] once at startup, before any rendering.  This is
/// presentation-only — it can never affect proof search or verdicts —
/// and the explicit `render_with`/`render_at` widths (WF/oracle/goal
/// rendering) are unaffected.
static DISPLAY_LINE_LENGTH: AtomicUsize = AtomicUsize::new(LINE_LENGTH);
static DISPLAY_RIBBON: AtomicUsize = AtomicUsize::new(RIBBON);

/// HughesPJ's own `style` default — `lineLength = 100`, ribbon
/// `round(100/1.5) = 67`.
///
/// This is the width of every document HS renders WITHOUT threading
/// `Main.Console`'s `lineWidth` through: the whole interactive web surface,
/// and the dot / JSON graph serializers on both the web and the batch side.
/// `LINE_LENGTH`/`RIBBON` above are the console width, which only the CLI's
/// `renderDoc` installs.
pub const DEFAULT_LINE_LENGTH: usize = 100;
pub const DEFAULT_RIBBON: usize = 67;

/// A page wider than any document this tree builds, so every `sep`, `fsep`
/// and `fcat` takes its flat branch and no break is inserted anywhere.
/// HughesPJ's `OneLineMode` ([`Doc::one_line_render`]) is a different string:
/// it takes each `Union`'s line-breaking branch and turns every break into
/// one space.
pub const FLAT_WIDTH: usize = usize::MAX / 4;

/// Override the bare-`render()` display width process-wide (see
/// [`DISPLAY_LINE_LENGTH`]).  Called once by the interactive server with
/// `(DEFAULT_LINE_LENGTH, DEFAULT_RIBBON)`.
pub fn set_display_width(line_length: usize, ribbon: usize) {
    DISPLAY_LINE_LENGTH.store(line_length, Ordering::Relaxed);
    DISPLAY_RIBBON.store(ribbon, Ordering::Relaxed);
}

thread_local! {
    /// When set, [`Doc::text`]/[`Doc::char`] measure each token's *fill* width
    /// as its HTML-entity-escaped column count instead of its visible column
    /// count.  This mirrors HS's web render path, which builds every document
    /// through the `HtmlDoc Doc` transformer: its `Document (HtmlDoc d)`
    /// instance (`Text/PrettyPrint/Html.hs:102-104`) runs `escapeHtmlEntities`
    /// on every `text`/`char` token BEFORE the HughesPJ fill measures it, so a
    /// `<`/`>` costs 4 columns (`&lt;`/`&gt;`) and a `'` costs 5 (`&#39;`) when
    /// deciding line breaks.  The interactive server escapes AFTER rendering
    /// (`html_escape`), so without matching this accounting its `fsep`/`fcat`
    /// wraps a pair-tuple `<…>` at a different column than HS (a space
    /// appears/disappears before a tuple's closing `>`).
    ///
    /// This is presentation-only: it never affects proof search or verdicts,
    /// and it is scoped (via [`HtmlEntityWidthGuard`]) to the web
    /// constraint-system pane only, so the `--prove` byte-identity corpus is
    /// untouched (the flag defaults to `false`).
    static HTML_ENTITY_WIDTH: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Column width of `s` after HTML-entity escaping, matching HS
/// `escapeHtmlEntities` (`Text/PrettyPrint/Html.hs:140-149`) and the server's
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
    ///     instance (`Html.hs:102-104`) — so the stored bytes are already escaped
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
    /// prettyGoal` regardless of the surrounding widget (ProofMethod.hs:597-623, see line 606):
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
pub use crate::pretty_html::escape_html_entities;

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
/// non-annotated module used in production, HS `Text/PrettyPrint/Class.hs:64-67, see line 67`/`:72`)
/// — minus the `Above`/`Beside` lazy constructors (we eagerly reduce on
/// build).
#[derive(Clone)]
pub enum Doc {
    /// Empty doc, length 0.
    Empty,
    /// `NilAbove p` — emit a newline, then `p` on the next line.
    NilAbove(DocRef),
    /// `TextBeside s p` — emit `s` (a text run of `width` cols) then
    /// continue with `p` on the same line.  `width` is decoupled from
    /// `s.len()` to support multi-byte chars (e.g. `∧` = 1 col).
    TextBeside(Rc<str>, usize, DocRef),
    /// `Nest n p` — add `n` to the current indent for the rest of `p`.
    Nest(isize, DocRef),
    /// `Union p q` — try `p` first; if it doesn't fit, use `q`.
    Union(DocRef, DocRef),
    /// Lazy variant of `Union`: the left (flat) branch `p` is materialised,
    /// but the right branch is a memoised thunk forced only when `p` does
    /// not fit.  HughesPJ relies on Haskell's laziness so that the `q`
    /// branch of a `Union` (which, in `fill1`/`fillNBE`/`sep1`, recursively
    /// re-lays the remaining items) is never built unless a line actually
    /// breaks there.  An eager Rust port materialises both branches at
    /// construction time, making the reduced tree O(2^depth) for deeply
    /// nested terms (e.g. TLS `Out( <senc(<..>, h(<..>)), ..> )`).  This
    /// thunk restores HS's laziness: unused right branches are not built.
    /// Combining documents can still copy their materialised spines.
    LazyUnion(DocRef, Rc<LazyRight>),
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

/// Shared document storage with iterative last-owner release, including cached
/// layouts and the inputs of unforced alternatives.
pub struct DocNode(Doc);

type DocRef = Rc<DocNode>;

impl std::ops::Deref for DocNode {
    type Target = Doc;
    fn deref(&self) -> &Doc {
        &self.0
    }
}

fn shared_or_leaf(doc: &DocRef) -> bool {
    Rc::strong_count(doc) > 1 || matches!(doc.0, Doc::Empty | Doc::NoDoc)
}

impl Drop for DocNode {
    fn drop(&mut self) {
        // Shared tails and leaves need no graph walk. Let their ordinary
        // Rc drop run without entering the drainer.
        match &self.0 {
            Doc::Empty | Doc::NoDoc => return,
            Doc::TextBeside(_, _, child) | Doc::Nest(_, child) | Doc::NilAbove(child)
                if shared_or_leaf(child) =>
            {
                return
            }
            _ => {}
        }
        release(Release::Doc(std::mem::replace(&mut self.0, Doc::Empty)));
    }
}

/// Memoised right branch or layout continuation. Production continuations are
/// data so both evaluation and destruction can use explicit worklists.
pub struct LazyRight {
    state: std::cell::RefCell<LazyState>,
}

enum Input {
    Ready(DocRef),
    Lazy(Rc<LazyRight>),
}

enum Tail {
    Doc(Doc),
    Sep(Vec<Doc>),
    Fill(bool, Vec<Doc>),
}

enum Build {
    Beside(bool, Doc),
    Above(bool, isize, Tail),
    NilAbove(bool, isize),
    NilBeside(bool),
}

enum LazyState {
    Ready(DocRef),
    Forcing,
    Build(Input, Box<Build>),
    FillBreak {
        g: bool,
        k: isize,
        items: Box<(Doc, Vec<Doc>)>,
    },
    Layout(Layout, DocRef),
    #[cfg(test)]
    Custom(Box<dyn FnOnce() -> Doc>),
}

impl LazyRight {
    fn op(op: LazyState) -> Rc<Self> {
        Rc::new(Self {
            state: std::cell::RefCell::new(op),
        })
    }
    fn build(input: Input, build: Build) -> Rc<Self> {
        Self::op(LazyState::Build(input, Box::new(build)))
    }
    #[cfg(test)]
    fn new(f: impl FnOnce() -> Doc + 'static) -> Rc<Self> {
        Self::op(LazyState::Custom(Box::new(f)))
    }
    fn force(self: &Rc<Self>) -> DocRef {
        if let LazyState::Ready(value) = &*self.state.borrow() {
            return value.clone();
        }
        if matches!(&*self.state.borrow(), LazyState::Layout(..)) {
            let op = std::mem::replace(&mut *self.state.borrow_mut(), LazyState::Forcing);
            let LazyState::Layout(layout, doc) = op else {
                unreachable!()
            };
            let value = rc(layout.run((*doc).clone()));
            *self.state.borrow_mut() = LazyState::Ready(value.clone());
            return value;
        }
        evaluate(Task::Force(self.clone())).doc()
    }
}

impl Drop for LazyRight {
    fn drop(&mut self) {
        match self.state.get_mut() {
            LazyState::Forcing => return,
            LazyState::Ready(doc) | LazyState::Layout(_, doc) if shared_or_leaf(doc) => return,
            _ => {}
        }
        release(Release::State(std::mem::replace(
            self.state.get_mut(),
            LazyState::Forcing,
        )));
    }
}

enum Release {
    Doc(Doc),
    Node(DocRef),
    Lazy(Rc<LazyRight>),
    State(LazyState),
}

fn release(mut item: Release) {
    // Follow single-child spines without allocating. Only a branch needs to
    // save another edge; extracting edges disables their ordinary Drop.
    let mut pending = Vec::new();
    loop {
        match item {
            Release::Node(node) => {
                if let Ok(node) = Rc::try_unwrap(node) {
                    // Transfer the sole field rather than calling Drop again
                    // for an emptied node.
                    let mut node = std::mem::ManuallyDrop::new(node);
                    item = Release::Doc(std::mem::replace(&mut node.0, Doc::Empty));
                    continue;
                }
            }
            Release::Lazy(lazy) => {
                if let Ok(mut lazy) = Rc::try_unwrap(lazy) {
                    item =
                        Release::State(std::mem::replace(lazy.state.get_mut(), LazyState::Forcing));
                    continue;
                }
            }
            Release::Doc(doc) => match doc {
                Doc::Empty | Doc::NoDoc => {}
                Doc::TextBeside(_, _, child) | Doc::Nest(_, child) | Doc::NilAbove(child) => {
                    item = Release::Node(child);
                    continue;
                }
                Doc::Union(left, right) => {
                    pending.push(Release::Node(right));
                    item = Release::Node(left);
                    continue;
                }
                Doc::LazyUnion(left, right) => {
                    pending.push(Release::Lazy(right));
                    item = Release::Node(left);
                    continue;
                }
                Doc::Deferred(lazy) => {
                    item = Release::Lazy(lazy);
                    continue;
                }
            },
            Release::State(op) => match op {
                LazyState::Forcing => {}
                LazyState::Ready(doc) | LazyState::Layout(_, doc) => {
                    item = Release::Node(doc);
                    continue;
                }
                LazyState::FillBreak { items, .. } => {
                    let (first, rest) = *items;
                    pending.extend(rest.into_iter().map(Release::Doc));
                    item = Release::Doc(first);
                    continue;
                }
                LazyState::Build(input, build) => {
                    match *build {
                        Build::Beside(_, doc) | Build::Above(_, _, Tail::Doc(doc)) => {
                            pending.push(Release::Doc(doc));
                        }
                        Build::Above(_, _, Tail::Sep(docs) | Tail::Fill(_, docs)) => {
                            pending.extend(docs.into_iter().map(Release::Doc));
                        }
                        Build::NilAbove(..) | Build::NilBeside(_) => {}
                    }
                    item = match input {
                        Input::Ready(doc) => Release::Node(doc),
                        Input::Lazy(lazy) => Release::Lazy(lazy),
                    };
                    continue;
                }
                #[cfg(test)]
                LazyState::Custom(_) => {}
            },
        }
        match pending.pop() {
            Some(next) => item = next,
            None => break,
        }
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
#[cfg(test)]
fn defer(f: impl FnOnce() -> Doc + 'static) -> Doc {
    Doc::Deferred(LazyRight::new(f))
}

/// HS `mkUnion` with a lazy right branch.
fn lazy_union(p: Doc, q: Rc<LazyRight>) -> Doc {
    if matches!(p, Doc::Empty) {
        return Doc::Empty;
    }
    Doc::LazyUnion(rc(p), q)
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
            Doc::TextBeside(Rc::from(s), width, rc(Doc::Empty))
        }
    }

    /// `text s` for a run that may be EMPTY.  Unlike [`Doc::text`], `""`
    /// stays a zero-width text run instead of collapsing to `Doc::Empty`,
    /// which is what HughesPJ's `text ""` is: `nilBeside` (ported below as
    /// `nil_beside`) drops a `<+>` separator only for `Empty`, so
    /// `d <+> text ""` keeps its space while `d <+> empty` does not.  Use
    /// this at any port of a `d <+> text s` chain over a possibly-absent `s`.
    pub fn text_hs<S: AsRef<str>>(s: S) -> Doc {
        let s = s.as_ref();
        if s.is_empty() {
            Doc::TextBeside(Rc::from(""), 0, rc(Doc::Empty))
        } else {
            Doc::text(s)
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
    /// exactly ONE space.  Used by HS `System/Dot.hs:371-376, see line 374`'s `oneLineRender`
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
// Highlighting + HTML markup (port of Text.PrettyPrint.Highlight / .Html).
// All markup is emitted as ZERO-WIDTH text so it never perturbs the layout
// the plain `--prove` path already produces byte-for-byte.  The highlight
// combinators are the identity in plain mode; the `with_tag`
// helpers are web-pane-only (never reached from `--prove`) and always emit
// their tags, mirroring HS's `HtmlDoc`/`NoHtmlDoc` split.
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

/// HS `parens p = char '(' <> p <> char ')'` (`Text/PrettyPrint/Class.hs:149-149`) — PLAIN parens
/// (no highlight), used e.g. around `(modulo AC)`.
pub fn parens(d: Doc) -> Doc {
    Doc::char('(').beside(d).beside(Doc::char(')'))
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

fn rc(d: Doc) -> DocRef {
    Rc::new(DocNode(d))
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
fn mk_nest(mut k: isize, mut p: Doc) -> Doc {
    loop {
        match p {
            Doc::Nest(k1, inner) => {
                k += k1;
                p = (*inner).clone();
            }
            Doc::NoDoc => return Doc::NoDoc,
            Doc::Empty => return Doc::Empty,
            _ if k == 0 => return p,
            _ => return nest_(k, p),
        }
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

// A construction walk follows the left spine and rebuilds its prefixes in
// reverse. Line-breaking alternatives stay memoised and unforced.
enum Prefix {
    Text(Rc<str>, usize),
    Nest(isize),
    NormalizedNest(isize),
    BesideGap(bool),
    Above(Box<Doc>, isize),
    Line,
    Choice(Rc<LazyRight>),
}

fn rebuild(mut prefixes: Vec<Prefix>, mut tail: Doc) -> Doc {
    while let Some(prefix) = prefixes.pop() {
        tail = match prefix {
            Prefix::Text(text, width) => text_beside_(text, width, tail),
            Prefix::Nest(indent) => nest_(indent, tail),
            Prefix::NormalizedNest(indent) => mk_nest(indent, tail),
            Prefix::BesideGap(gap) => nil_beside(gap, tail),
            Prefix::Above(left, offset) => above_nest(*left, false, offset, tail),
            Prefix::Line => nil_above_(tail),
            Prefix::Choice(right) => lazy_union(tail, right),
        };
    }
    tail
}

// A forward cursor owns each output tail exclusively. Reuse an owned input
// allocation, or copy a shared node without changing the original document.
fn spine_child(node: &mut Doc) -> &mut DocRef {
    match node {
        Doc::TextBeside(_, _, child)
        | Doc::Nest(_, child)
        | Doc::NilAbove(child)
        | Doc::LazyUnion(child, _) => child,
        _ => unreachable!("spine prefix"),
    }
}

fn take_spine(node: &mut Doc) -> Doc {
    let child = spine_child(node);
    if let Some(value) = Rc::get_mut(child) {
        std::mem::replace(&mut value.0, Doc::Empty)
    } else {
        let next = (**child).clone();
        *child = rc(Doc::Empty);
        next
    }
}

fn append_spine(cursor: &mut Doc, node: Doc) -> &mut Doc {
    *cursor = node;
    &mut Rc::get_mut(spine_child(cursor))
        .expect("unique output tail")
        .0
}

// mkUnion elides an Empty left branch. Delay consecutive choices until we
// know the transformed left branch has a constructor; never force the right.
fn append_choices<'a>(mut cursor: &'a mut Doc, choices: &mut Vec<Doc>) -> &'a mut Doc {
    for node in choices.drain(..) {
        cursor = append_spine(cursor, node);
    }
    cursor
}

fn beside_inner(mut p: Doc, g: bool, q: Doc) -> Doc {
    let mut output = Doc::Empty;
    let mut cursor = &mut output;
    let mut choices = Vec::new();
    let tail = loop {
        let mut node = match p {
            Doc::NoDoc => break Doc::NoDoc,
            Doc::Empty => break q,
            Doc::Union(left, right) => {
                let q2 = q.clone();
                let mut choice = Doc::LazyUnion(
                    left,
                    LazyRight::build(Input::Ready(right), Build::Beside(g, q2)),
                );
                p = take_spine(&mut choice);
                choices.push(choice);
                continue;
            }
            Doc::LazyUnion(left, right) => {
                let q2 = q.clone();
                let mut choice = Doc::LazyUnion(
                    left,
                    LazyRight::build(Input::Lazy(right), Build::Beside(g, q2)),
                );
                p = take_spine(&mut choice);
                choices.push(choice);
                continue;
            }
            Doc::TextBeside(s, w, rest) => {
                // HS nilBeside elides leading nests in q after the text tail.
                if matches!(&**rest, Doc::Empty) {
                    break text_beside_(s, w, nil_beside(g, q));
                }
                Doc::TextBeside(s, w, rest)
            }
            Doc::Nest(_, _) | Doc::NilAbove(_) => p,
            Doc::Deferred(_) => unreachable!("Deferred only appears in reduced docs"),
        };
        p = take_spine(&mut node);
        if !choices.is_empty() {
            cursor = append_choices(cursor, &mut choices);
        }
        cursor = append_spine(cursor, node);
    };
    if !matches!(tail, Doc::Empty) {
        cursor = append_choices(cursor, &mut choices);
    }
    *cursor = tail;
    output
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
fn above_nest(mut p: Doc, g: bool, mut k: isize, q: Doc) -> Doc {
    let mut output = Doc::Empty;
    let mut cursor = &mut output;
    let mut choices = Vec::new();
    let tail = loop {
        let mut node = match p {
            Doc::NoDoc => break Doc::NoDoc,
            Doc::Empty => break mk_nest(k, q),
            Doc::Union(left, right) => {
                let q2 = q.clone();
                let mut choice = Doc::LazyUnion(
                    left,
                    LazyRight::build(Input::Ready(right), Build::Above(g, k, Tail::Doc(q2))),
                );
                p = take_spine(&mut choice);
                choices.push(choice);
                continue;
            }
            Doc::LazyUnion(left, right) => {
                let q2 = q.clone();
                let mut choice = Doc::LazyUnion(
                    left,
                    LazyRight::build(Input::Lazy(right), Build::Above(g, k, Tail::Doc(q2))),
                );
                p = take_spine(&mut choice);
                choices.push(choice);
                continue;
            }
            Doc::Nest(indent, inner) => {
                k -= indent;
                Doc::Nest(indent, inner)
            }
            Doc::TextBeside(s, w, rest) => {
                k -= w as isize;
                if matches!(&**rest, Doc::Empty) {
                    break text_beside_(s, w, nil_above_nest(g, k, q));
                }
                Doc::TextBeside(s, w, rest)
            }
            Doc::NilAbove(_) => p,
            Doc::Deferred(_) => unreachable!("Deferred only appears in reduced docs"),
        };
        p = take_spine(&mut node);
        if !choices.is_empty() {
            cursor = append_choices(cursor, &mut choices);
        }
        cursor = append_spine(cursor, node);
    };
    if !matches!(tail, Doc::Empty) {
        cursor = append_choices(cursor, &mut choices);
    }
    *cursor = tail;
    output
}

/// HS `nilAboveNest`.
fn nil_above_nest(g: bool, mut k: isize, mut q: Doc) -> Doc {
    let mut prefixes = Vec::new();
    let tail = loop {
        q = match q {
            Doc::Empty => break Doc::Empty,
            Doc::Nest(indent, inner) => {
                k += indent;
                (*inner).clone()
            }
            Doc::LazyUnion(left, right) => {
                prefixes.push(Prefix::Choice(LazyRight::build(
                    Input::Lazy(right),
                    Build::NilAbove(g, k),
                )));
                (*left).clone()
            }
            other => {
                break if !g && k > 0 {
                    // HS's inline indentation when the next line can overlap.
                    let spaces = " ".repeat(k as usize);
                    text_beside_(Rc::from(spaces.as_str()), k as usize, other)
                } else {
                    nil_above_(mk_nest(k, other))
                };
            }
        };
    };
    rebuild(prefixes, tail)
}

// ============================================================================
// oneLiner
// ============================================================================

fn one_liner(mut d: Doc) -> Doc {
    let mut prefixes = Vec::new();
    let tail = loop {
        d = match d {
            Doc::NoDoc | Doc::NilAbove(_) => break Doc::NoDoc,
            Doc::Empty => break Doc::Empty,
            Doc::TextBeside(s, w, p) => {
                if matches!(&**p, Doc::Empty) {
                    break Doc::TextBeside(s, w, p);
                }
                prefixes.push(Prefix::Text(s, w));
                (*p).clone()
            }
            Doc::Nest(k, p) => {
                prefixes.push(Prefix::Nest(k));
                (*p).clone()
            }
            // oneLiner takes only the flat branch; never force q.
            Doc::Union(p, _) | Doc::LazyUnion(p, _) => (*p).clone(),
            Doc::Deferred(_) => unreachable!("Deferred only appears in reduced docs"),
        };
    };
    rebuild(prefixes, tail)
}

// ============================================================================
// sep / cat / fsep / fcat
// ============================================================================

/// HS `sep` — try one line (separated by spaces); else vertical.
pub fn sep(ds: Vec<Doc>) -> Doc {
    sep_x(true, ds)
}

/// HS `fsep` — fill-style paragraph (greedy wrap), space-separated.
pub fn fsep(ds: Vec<Doc>) -> Doc {
    fill(true, ds)
}

/// HS `fcat` — fill-style paragraph, no separator.
pub fn fcat(ds: Vec<Doc>) -> Doc {
    fill(false, ds)
}

/// HS `nestShort' lead finish body =
///   nestShort (length lead + 1) (text lead) (text finish) body
///   = sep [ text lead $$ nest n body, text finish ]`
/// where `$$` is HughesPJ `above` and `n = length lead + 1`
/// (Text/PrettyPrint/Class.hs:218-223).  Shared by the formula, fact and
/// SAPIC renderers.
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

/// HS `sep1` / `sepNB`. The inline state elides nests after text;
/// other constructors resume sep1. Both walks share one continuation stack.
fn sep1(g: bool, mut p: Doc, mut k: isize, mut ys: Vec<Doc>) -> Doc {
    let mut prefixes = Vec::new();
    let mut inline = false;
    let tail = loop {
        if inline {
            match p {
                Doc::Nest(_, inner) => {
                    p = (*inner).clone();
                    continue;
                }
                Doc::Empty => {
                    // HS sepNB (pretty-1.1.3.6 HughesPJ.hs:760-766):
                    // retain its False flag and the right-folded rest.
                    let rest = if g {
                        hsep(ys.clone())
                    } else {
                        hcat(ys.clone())
                    };
                    let left = one_liner(nil_beside(g, reduce_doc(rest)));
                    let right = nil_above_nest(false, k, reduce_doc(vcat(ys)));
                    break mk_union(left, right);
                }
                _ => inline = false,
            }
        }
        p = match p {
            Doc::NoDoc => break Doc::NoDoc,
            Doc::Union(p, q) => {
                let right_items = ys.clone();
                prefixes.push(Prefix::Choice(LazyRight::build(
                    Input::Ready(q),
                    Build::Above(false, k, Tail::Sep(right_items)),
                )));
                (*p).clone()
            }
            Doc::LazyUnion(p, rt) => {
                let right_items = ys.clone();
                prefixes.push(Prefix::Choice(LazyRight::build(
                    Input::Lazy(rt),
                    Build::Above(false, k, Tail::Sep(right_items)),
                )));
                (*p).clone()
            }
            Doc::Deferred(c) => (*c.force()).clone(),
            Doc::Empty => {
                // sep1 Empty k ys = mkNest k (sep ys). Resume that sep
                // here too, so a run of empty items does not recurse.
                if ys.is_empty() {
                    break Doc::Empty;
                }
                prefixes.push(Prefix::NormalizedNest(k));
                k = 0;
                reduce_doc(ys.remove(0))
            }
            Doc::Nest(n, inner) => {
                prefixes.push(Prefix::Nest(n));
                k -= n;
                (*inner).clone()
            }
            Doc::NilAbove(p) => {
                break nil_above_(above_nest((*p).clone(), false, k, reduce_doc(vcat(ys))));
            }
            Doc::TextBeside(s, w, p) => {
                prefixes.push(Prefix::Text(s, w));
                k -= w as isize;
                inline = true;
                (*p).clone()
            }
        };
    };
    rebuild(prefixes, tail)
}

/// HS `nilBeside`.
fn nil_beside(g: bool, mut p: Doc) -> Doc {
    let mut prefixes = Vec::new();
    let tail = loop {
        p = match p {
            Doc::Empty => break Doc::Empty,
            Doc::Nest(_, inner) => (*inner).clone(),
            Doc::LazyUnion(left, right) => {
                prefixes.push(Prefix::Choice(LazyRight::build(
                    Input::Lazy(right),
                    Build::NilBeside(g),
                )));
                (*left).clone()
            }
            other => {
                break if g {
                    text_beside_(Rc::from(" "), 1, other)
                } else {
                    other
                }
            }
        };
    };
    rebuild(prefixes, tail)
}

/// HS `fill` — paragraph-fill greedy wrap.
fn fill(g: bool, mut ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::Empty;
    }
    // A singleton has no inter-document break to choose. Re-filling its
    // existing layout walks the entire subtree without changing the result.
    if ds.len() == 1 {
        return ds.pop().unwrap();
    }
    let first = ds.remove(0);
    fill1(g, reduce_doc(first), 0, ds)
}

/// HS `fill1` / `fillNB` / `fillNBE` (pretty-1.1.3.6 HughesPJ.hs:824+).
/// Like sep1, the inline state elides nests after text. Continuations also
/// retain the operations awaiting a fill of the remaining list.
fn fill1(g: bool, mut p: Doc, mut k: isize, mut ys: Vec<Doc>) -> Doc {
    let mut prefixes = Vec::new();
    let mut inline = false;
    let tail = loop {
        if inline {
            match p {
                Doc::Nest(_, inner) => {
                    p = (*inner).clone();
                    continue;
                }
                Doc::Empty => {
                    let mut iter = ys.into_iter();
                    let y = loop {
                        match iter.next() {
                            None => break None,
                            Some(Doc::Empty) => continue,
                            Some(doc) => break Some(doc),
                        }
                    };
                    let Some(y) = y else { break Doc::Empty };
                    ys = iter.collect();
                    p = elide_nest(one_liner(reduce_doc(y.clone())));
                    let right_items = ys.clone();
                    // fillNBE's right branch re-fills (y:ys). Keep it lazy:
                    // evaluating it now constructs unused layout alternatives.
                    prefixes.push(Prefix::Choice(LazyRight::op(LazyState::FillBreak {
                        g,
                        k,
                        items: Box::new((y, right_items)),
                    })));
                    prefixes.push(Prefix::BesideGap(g));
                    k -= isize::from(g);
                    inline = false;
                    continue;
                }
                _ => inline = false,
            }
        }
        p = match p {
            Doc::NoDoc => break Doc::NoDoc,
            Doc::Union(left, right) => {
                let right_items = ys.clone();
                prefixes.push(Prefix::Choice(LazyRight::build(
                    Input::Ready(right),
                    Build::Above(false, k, Tail::Fill(g, right_items)),
                )));
                (*left).clone()
            }
            Doc::LazyUnion(left, right) => {
                let right_items = ys.clone();
                prefixes.push(Prefix::Choice(LazyRight::build(
                    Input::Lazy(right),
                    Build::Above(false, k, Tail::Fill(g, right_items)),
                )));
                (*left).clone()
            }
            Doc::Deferred(c) => (*c.force()).clone(),
            Doc::Nest(indent, inner) => {
                prefixes.push(Prefix::Nest(indent));
                k -= indent;
                (*inner).clone()
            }
            Doc::TextBeside(text, width, rest) => {
                prefixes.push(Prefix::Text(text, width));
                k -= width as isize;
                inline = true;
                (*rest).clone()
            }
            terminal => {
                match terminal {
                    Doc::Empty => prefixes.push(Prefix::NormalizedNest(k)),
                    Doc::NilAbove(rest) => {
                        prefixes.push(Prefix::Line);
                        prefixes.push(Prefix::Above(Box::new((*rest).clone()), k));
                    }
                    _ => unreachable!(),
                }
                // Resume fill(g, ys), preserving its empty/singleton cases.
                match ys.len() {
                    0 => break Doc::Empty,
                    1 => break ys.pop().unwrap(),
                    _ => {
                        k = 0;
                        reduce_doc(ys.remove(0))
                    }
                }
            }
        };
    };
    rebuild(prefixes, tail)
}

// ============================================================================
// best / get / get1 / nicest1 / fits
// ============================================================================

/// HS `best w r doc = get w doc`.
fn get_doc(w: isize, r: isize, d: &Doc) -> Doc {
    get(w, r, d.clone())
}

/// `get` and `get1` differ only in whether text has already been emitted on
/// this line. Keep that state with each deferred reduction.
#[derive(Clone, Copy)]
struct Layout {
    w: isize,
    r: isize,
    sl: Option<isize>,
}

impl Layout {
    fn defer(self, doc: DocRef) -> Doc {
        Doc::Deferred(LazyRight::op(LazyState::Layout(self, doc)))
    }
}

impl Layout {
    // Most reductions expose a text/line head immediately. Avoid allocating an
    // evaluator stack for those steps; only choices/dependencies need frames.
    fn head(self, mut doc: Doc) -> Result<Doc, Doc> {
        let Self { w, r, sl } = self;
        loop {
            return Ok(match doc {
                Doc::Empty | Doc::NoDoc => doc,
                Doc::NilAbove(p) => nil_above_(
                    Self {
                        w: w - sl.unwrap_or(0),
                        r,
                        sl: None,
                    }
                    .defer(p),
                ),
                Doc::TextBeside(s, sw, p) => text_beside_(
                    s,
                    sw,
                    Self {
                        w,
                        r,
                        sl: Some(sl.unwrap_or(0) + sw as isize),
                    }
                    .defer(p),
                ),
                Doc::Nest(k, p) => {
                    if sl.is_some() {
                        doc = (*p).clone();
                        continue;
                    }
                    nest_(
                        k,
                        Self {
                            w: w - k,
                            r,
                            sl: None,
                        }
                        .defer(p),
                    )
                }
                other => return Err(other),
            });
        }
    }
    fn run(self, doc: Doc) -> Doc {
        match self.head(doc) {
            Ok(head) => head,
            Err(doc) => (*evaluate(Task::Layout(self, rc(doc))).doc()).clone(),
        }
    }
}

enum Task {
    Force(Rc<LazyRight>),
    Memoize(Rc<LazyRight>),
    Build(Box<Build>),
    Layout(Layout, DocRef),
    LayoutForced(Layout),
    Fits(isize, DocRef),
    FitsForced(isize),
    Pick(Layout, Input),
    PickFitted(Layout, Input, DocRef),
}

enum Value {
    Doc(DocRef),
    Fits(bool),
}

impl Value {
    fn doc(&mut self) -> DocRef {
        match std::mem::replace(self, Self::Fits(false)) {
            Self::Doc(doc) => doc,
            Self::Fits(_) => unreachable!("expected a document"),
        }
    }
}

/// Evaluate only the requested head/first line. A choice saves its continuation
/// before evaluating the left branch; its right branch stays untouched unless
/// that line fails to fit. Lazy dependencies use this same worklist, so forcing
/// one continuation never recursively forces another.
fn evaluate(task: Task) -> Value {
    let mut tasks = vec![task];
    let mut value = Value::Fits(false);
    while let Some(task) = tasks.pop() {
        match task {
            Task::Force(lazy) => {
                if let LazyState::Ready(doc) = &*lazy.state.borrow() {
                    value = Value::Doc(doc.clone());
                    continue;
                }
                let op = std::mem::replace(&mut *lazy.state.borrow_mut(), LazyState::Forcing);
                tasks.push(Task::Memoize(lazy));
                match op {
                    LazyState::Forcing => panic!("LazyRight forced while already forcing (cycle)"),
                    LazyState::Ready(_) => unreachable!("cached value handled above"),
                    LazyState::Build(input, build) => {
                        tasks.push(Task::Build(build));
                        match input {
                            Input::Ready(doc) => value = Value::Doc(doc),
                            Input::Lazy(lazy) => tasks.push(Task::Force(lazy)),
                        }
                    }
                    LazyState::FillBreak { g, k, items } => {
                        let (first, rest) = *items;
                        let mut items = vec![first];
                        items.extend(rest);
                        value = Value::Doc(rc(nil_above_nest(false, k, fill(g, items))));
                    }
                    LazyState::Layout(layout, doc) => tasks.push(Task::Layout(layout, doc)),
                    #[cfg(test)]
                    LazyState::Custom(f) => value = Value::Doc(rc(f())),
                }
            }
            Task::Memoize(lazy) => {
                let doc = value.doc();
                *lazy.state.borrow_mut() = LazyState::Ready(doc.clone());
                value = Value::Doc(doc);
            }
            Task::Build(build) => {
                let doc = (*value.doc()).clone();
                value = Value::Doc(rc(match *build {
                    Build::Beside(g, right) => beside_inner(doc, g, right),
                    Build::Above(g, k, tail) => {
                        let right = match tail {
                            Tail::Doc(doc) => doc,
                            Tail::Sep(items) => reduce_doc(vcat(items)),
                            Tail::Fill(g, items) => fill(g, items),
                        };
                        above_nest(doc, g, k, right)
                    }
                    Build::NilAbove(g, k) => nil_above_nest(g, k, doc),
                    Build::NilBeside(g) => nil_beside(g, doc),
                }));
            }
            Task::LayoutForced(layout) => tasks.push(Task::Layout(layout, value.doc())),
            Task::Layout(layout, doc) => match layout.head((*doc).clone()) {
                Ok(head) => {
                    value = Value::Doc(rc(head));
                    continue;
                }
                Err(doc) => match doc {
                    Doc::Union(p, q) => {
                        tasks.push(Task::Pick(layout, Input::Ready(q)));
                        tasks.push(Task::Layout(layout, p));
                    }
                    Doc::LazyUnion(p, q) => {
                        tasks.push(Task::Pick(layout, Input::Lazy(q)));
                        tasks.push(Task::Layout(layout, p));
                    }
                    Doc::Deferred(lazy) => {
                        tasks.push(Task::LayoutForced(layout));
                        tasks.push(Task::Force(lazy));
                    }
                    _ => unreachable!("head handled non-choice constructors"),
                },
            },
            Task::Pick(layout, right) => {
                let left = value.doc();
                tasks.push(Task::PickFitted(layout, right, left.clone()));
                tasks.push(Task::Fits(
                    layout.w.min(layout.r) - layout.sl.unwrap_or(0),
                    left,
                ));
            }
            Task::PickFitted(layout, right, left) => {
                if matches!(value, Value::Fits(true)) {
                    value = Value::Doc(left);
                } else {
                    match right {
                        Input::Ready(doc) => tasks.push(Task::Layout(layout, doc)),
                        Input::Lazy(lazy) => {
                            tasks.push(Task::LayoutForced(layout));
                            tasks.push(Task::Force(lazy));
                        }
                    }
                }
            }
            Task::FitsForced(n) => tasks.push(Task::Fits(n, value.doc())),
            Task::Fits(mut n, doc) => {
                let mut current: &Doc = &doc;
                loop {
                    if n < 0 {
                        value = Value::Fits(false);
                        break;
                    }
                    match current {
                        Doc::NoDoc => {
                            value = Value::Fits(false);
                            break;
                        }
                        Doc::Empty | Doc::NilAbove(_) => {
                            value = Value::Fits(true);
                            break;
                        }
                        Doc::TextBeside(_, width, p) => {
                            n -= *width as isize;
                            current = p;
                        }
                        Doc::Nest(_, p) | Doc::Union(p, _) | Doc::LazyUnion(p, _) => current = p,
                        Doc::Deferred(lazy) => {
                            tasks.push(Task::FitsForced(n));
                            tasks.push(Task::Force(lazy.clone()));
                            break;
                        }
                    }
                }
            }
        }
    }
    value
}

fn get(w: isize, r: isize, d: Doc) -> Doc {
    Layout { w, r, sl: None }.run(d)
}

fn get1(w: isize, r: isize, sl: isize, d: Doc) -> Doc {
    Layout { w, r, sl: Some(sl) }.run(d)
}

/// HS `fits`: inspect only the first line of the flat branch.
#[cfg(test)]
fn fits(n: isize, d: &Doc) -> bool {
    matches!(evaluate(Task::Fits(n, rc(d.clone()))), Value::Fits(true))
}

// ============================================================================
// lay (render an RDoc to String)
// ============================================================================

/// HS `lay` — walk the reduced doc, accumulating output.
///
/// ITERATIVE: the walk is a pure state machine — `lay` (at
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
// Numbered lists + blank-line vertical join (HS Class.hs `numbered`,
// `numbered'`, `$--$`).
// ============================================================================

/// HS `$--$` (`Text/PrettyPrint/Class.hs:112-114`): vertical concatenation with an empty
/// line in between — `caseEmptyDoc`-guarded `d1 $-$ text "" $-$ d2`, where
/// Class's `$-$` is HughesPJ `$+$` (`Text/PrettyPrint/Class.hs:180`) = [`Doc::above_g`].
/// The separator is [`Doc::text_hs`]`("")` so it survives as a blank line
/// (indented under a surrounding `nest`).
pub fn above_blank(d1: Doc, d2: Doc) -> Doc {
    if matches!(d2, Doc::Empty) {
        return d1;
    }
    if matches!(d1, Doc::Empty) {
        return d2;
    }
    d1.above_g(Doc::text_hs("")).above_g(d2)
}

/// HS `numbered` (`Text/PrettyPrint/Class.hs:252-259`):
/// `foldr1 ($-$) $ intersperse vsep $ map pp $ zip [1..] ds` with
/// `pp (i, d) = text (flushRight nWidth (show i)) <> d` and
/// `nWidth = length (show (length ds))`.  `[]` yields the empty doc.
pub fn numbered(vsep: Doc, ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::Empty;
    }
    let n_width = ds.len().to_string().len();
    let entries: Vec<Doc> = ds
        .into_iter()
        .enumerate()
        .map(|(i, d)| Doc::text(flush_right(n_width, &(i + 1).to_string())).beside(d))
        .collect();
    // `foldr1 ($-$) (intersperse vsep entries)` — right fold over the
    // interleaved list.
    let n = entries.len();
    let mut interleaved: Vec<Doc> = Vec::with_capacity(2 * n - 1);
    for (i, e) in entries.into_iter().enumerate() {
        if i > 0 {
            interleaved.push(vsep.clone());
        }
        interleaved.push(e);
    }
    let mut acc = interleaved
        .pop()
        .expect("numbered: non-empty by construction");
    for d in interleaved.into_iter().rev() {
        acc = d.above_g(acc);
    }
    acc
}

/// HS `numbered'` (`Text/PrettyPrint/Class.hs:263-264`):
/// `numbered (text "") . map (text ". " <>)`.
pub fn numbered_prime(ds: Vec<Doc>) -> Doc {
    numbered(
        Doc::text_hs(""),
        ds.into_iter().map(|d| Doc::text(". ").beside(d)).collect(),
    )
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
#[path = "pretty_hpj_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "pretty_hpj_sep_nb_regression_tests.rs"]
mod sep_nb_regression_tests;
