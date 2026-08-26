// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Pretty-printer for the two formula representations of the port: the
//! locally-nameless [`LNFormula`]/[`SyntacticLNFormula`] and the solver's
//! `tamarin_theory::guarded::Guarded`.
//!
//! Ports of Haskell `prettyLNFormula`/`prettySyntacticLNFormula`
//! (`lib/theory/src/Theory/Model/Formula.hs:474-525`) and `prettyGuarded`
//! (`lib/theory/src/Theory/Constraint/System/Guarded.hs:824-828, see line 828`).
//!
//! Output uses Tamarin's interactive UI math glyphs:
//!   `∀`, `∃`, `⇒`, `∧`, `∨`, `¬`, `⊤`, `⊥`, `@`, `<`, `=`, `⊏`,
//!   `last(...)`.
//!
//! Both paths hand their atoms to `atom::pretty_natom` /
//! `atom::pretty_syntactic_natom`, which print through
//! `tamarin_term::pretty::pretty_term` and `fact::pretty_fact`.
//!
//! [`lnformula_doc`] and [`syntactic_lnformula_doc`] open each atom's bound
//! variables against the binders in scope; the `Guarded` path opens each
//! binder through `guarded::open_guarded` (HS `openGuarded`,
//! Guarded.hs:364-373).
//!
//! [`term_doc`] and [`fact_doc`] render a `tamarin_parser::ast::Term` /
//! `Fact` — the projection a print site holding an internal value builds
//! with `elaborate::lnterm_to_parser` / `elaborate::lnfact_to_parser`.

use tamarin_parser::ast as p;
use tamarin_term::lterm::{sort_prefix, LNTerm, LSort, LVar};
use tamarin_term::pretty::pp_lvar;
use tamarin_utils::fresh::PreciseFreshState;

use crate::atom::{map_atom, pretty_natom, pretty_syntactic_natom, MapSugar, ProtoAtom};
use crate::elaborate::{proto_atom_to_parser, SugarToParser};
use crate::formula::{
    avoid_precise_lnformula, open_bound_term, BLNTerm, Connective, LNFormula, LNProtoFormula,
    ProtoFormula, Quantifier, SugarTerms, SyntacticLNFormula,
};
use crate::guarded::{bvar_to_lvar, open_guarded, Guarded};
use crate::pretty_hpj::{self as hpj, Doc, FLAT_WIDTH};

/// Render the lemma-header line, mirroring HS `prettyLemma`
/// (lib/theory/src/Lemma.hs:119-122):
///   `nest 2 $ sep [ prettyTraceQuantifier, doubleQuotes (prettyLNFormula f) ]`
/// Built as ONE `Doc` through the HS-faithful engine so the `sep`
/// (quant-keyword vs formula) flat-or-wrap decision, the formula's
/// internal `sep`/`nest` wrapping, and the continuation-line indents are
/// byte-identical to HS.  `quant` is the trace-quantifier keyword (e.g.
/// `"all-traces"` / `"exists-trace"`), `formula_doc` the quoted formula from
/// whichever representation the caller holds.  The returned string begins at
/// column 0 (the `nest 2` indent IS included in the output, like HS's
/// `nest 2` rendered at the theory's column 0).
pub fn lemma_header_line_doc(quant: &str, formula_doc: Doc) -> String {
    // `doubleQuotes d = "\"" <> d <> "\""` (Text/PrettyPrint/Class.hs:148-148).
    let dq = Doc::text("\"").beside(formula_doc).beside(Doc::text("\""));
    // `sep [quant, dq]` then `nest 2`.
    let line = hpj::sep(vec![Doc::text(quant), dq]).nest(2);
    line.render()
}

/// Render `nest n $ doubleQuotes (prettyLNFormula f)` through the
/// HS-faithful engine (the restriction-body shape, TheoryObject.hs:889-893, see line 893)
/// around an already built formula `Doc`, whichever formula representation
/// produced it.  The `nest n` indent is included in the output; the `"` is a
/// real Doc `beside` so the formula's wrapped continuation lines indent to
/// the formula's start column.
pub(crate) fn doublequoted_nested_doc(formula_doc: Doc, nest_n: usize) -> String {
    doublequoted_nested(formula_doc, nest_n).render()
}

/// [`doublequoted_nested_doc`] at the HughesPJ default page width, for the
/// text HS builds with the plain `render` (Text/PrettyPrint/Class.hs:77-78)
/// rather than with the console's `renderDoc` — the wellformedness report,
/// which `Main/TheoryLoader.hs` folds into the theory as a comment string.
pub(crate) fn doublequoted_nested_doc_default_width(formula_doc: Doc, nest_n: usize) -> String {
    doublequoted_nested(formula_doc, nest_n)
        .render_with(hpj::DEFAULT_LINE_LENGTH, hpj::DEFAULT_RIBBON)
}

fn doublequoted_nested(formula_doc: Doc, nest_n: usize) -> Doc {
    let dq = Doc::text("\"").beside(formula_doc).beside(Doc::text("\""));
    dq.nest(nest_n as isize)
}

/// [`guarded_doc`] laid out flat — the one-line string the web layer's
/// disjunction-goal label quotes each disjunct with (HS `prettyGoal (DisjG
/// (Disj gfs))`, Constraints.hs:281-283).
pub fn pretty_guarded(g: &Guarded) -> String {
    guarded_doc(g).render_with(FLAT_WIDTH, FLAT_WIDTH)
}

/// Test-only: pretty-print a guarded formula with HS-style
/// `sep`/`nest`-driven line wrapping.  `indent` is the column where the
/// first character of the formula will land in the final output.  The page
/// /ribbon widths are the fixed `LINE_LENGTH`/`RIBBON` constants, so there
/// is no per-call width knob.  Mirrors Haskell's `prettyGuarded`
/// (Guarded.hs:824-866) composed with the HughesPJ `sep`/`nest` layout
/// semantics.
///
/// Routes through the HS-faithful Doc engine (`crate::pretty_hpj`):
/// `guarded_to_doc` builds a `Doc` tree that mirrors HS `prettyGuarded`'s
/// `sep`/`nest`/`fsep` structure node-for-node, then `render_at` lays it
/// out with the same `get1` per-NilAbove `w`-shrinkage HughesPJ uses
/// (HughesPJ.hs:1011).  `indent` is the column where the formula's first
/// char will land (e.g. 1, right after the opening `"` of the lemma's
/// `doubleQuotes` wrap, lib/theory/src/Lemma.hs:116-141, see line 138/141).
///
/// NOTE: `render_at`'s `sl_initial` only shrinks the budget; it does NOT
/// shift continuation lines by the leading prefix width.  In HS the
/// `prettyGuarded` doc is the RIGHT operand of `doubleQuotes`'s `<>`
/// (`"\"" <> prettyGuarded <> "\""`, Text/PrettyPrint/Class.hs:148-148), and HughesPJ `beside`
/// DOES shift the right doc's vertical layout by the leading `"`'s width
/// (1 col).  Callers that place the formula after a 1-col prefix must use
/// `pretty_guarded_doublequoted` (which models the `"` as a real Doc
/// `beside`, getting the continuation indent right).  Used only by the
/// unit tests in this module; production callers use
/// `pretty_guarded_doublequoted`.
#[cfg(test)]
fn pretty_guarded_wrapped(g: &Guarded, indent: usize) -> String {
    use crate::pretty_hpj as hpj;
    let mut state = avoid_precise_guarded(g);
    let doc = guarded_to_doc(g, &mut state);
    doc.render_at(hpj::LINE_LENGTH, hpj::RIBBON, indent)
}

/// HS `doubleQuotes (prettyGuarded gf)` (lib/theory/src/Lemma.hs:116-141, see line 138/141, Text/PrettyPrint/Class.hs:148-148).
/// Builds `"\"" <> guarded_doc <> "\""` as a single Doc and renders it,
/// so HughesPJ `beside`'s column-shift puts continuation lines at the
/// formula's start column (1, right after the opening quote) — matching
/// HS byte-exact.  The result is the full `"..."` string.
pub fn pretty_guarded_doublequoted(g: &Guarded) -> String {
    use crate::pretty_hpj::Doc;
    let mut state = avoid_precise_guarded(g);
    let doc = guarded_to_doc(g, &mut state);
    Doc::text("\"").beside(doc).beside(Doc::text("\"")).render()
}

/// HS bare `prettyGuarded gf` (Guarded.hs:824-866) as a Doc — WITHOUT the
/// lemma path's `doubleQuotes` wrap.  This is what
/// `prettyNonGraphSystem` renders the `sFormulas` / `sLemmas` /
/// `sSolvedFormulas` sections with (System.hs:1672-1685, see line 1675/1678/1680), so the
/// formula participates in the surrounding pane Doc and wraps at the
/// pane's width/nesting exactly as in HS.
pub(crate) fn guarded_doc(g: &Guarded) -> crate::pretty_hpj::Doc {
    let mut state = avoid_precise_guarded(g);
    guarded_to_doc(g, &mut state)
}

/// Build the `pretty_hpj::Doc` for a `prettyGoal (DisjG (Disj gfs))`
/// (Constraints.hs:282-283):
///   `fsep $ punctuate (operator_ "  ∥") (map (nest 1 . parens . prettyGuarded) gfs)`
/// Each disjunct is `nest 1 (parens (prettyGuarded gf))`, the separator is
/// `"  ∥"` (two spaces + ∥) placed AFTER each non-last item by `punctuate`,
/// and the items are joined by `fsep` (paragraph-fill, one space between).
pub fn disj_goal_to_doc(gfs: &[Guarded]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let items: Vec<Doc> = gfs
        .iter()
        .map(|g| {
            let mut state = avoid_precise_guarded(g);
            let inner = guarded_to_doc(g, &mut state);
            // `nest 1 (parens (prettyGuarded gf))` — `parens` (Text/PrettyPrint/Class.hs:149-149)
            // is `char '(' <> d <> char ')'` (PLAIN).
            Doc::char('(').beside(inner).beside(Doc::char(')')).nest(1)
        })
        .collect();
    // HS `punctuate (operator_ "  ∥")` (Constraints.hs:273-288, see line 283) — the `∥`
    // separator is an `hl_operator` span.
    let punct = hpj::punctuate(hpj::operator_("  \u{2225}"), items); // "  ∥"
    hpj::fsep(punct)
}

/// HS `multiComment_ ["unannotated"]`
/// (Theory/Text/Pretty.hs:105-106):
///   `comment $ fsep [text "/*", vcat $ map text ls, text "*/"]`
/// With a single line `"unannotated"`, `vcat [text "unannotated"]` is
/// just `text "unannotated"`, and `fsep` joins the three with single
/// spaces when they fit (they always do at any indent ≤ ribbon), giving
/// `/* unannotated */`.  `comment` is a highlight wrapper — a no-op for
/// raw (non-coloured) output.
fn unannotated_comment_doc() -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    hpj::fsep(vec![
        Doc::text("/*"),
        Doc::text("unannotated"),
        Doc::text("*/"),
    ])
}

/// Render a proof-step line that may carry the `/* unannotated */`
/// comment, reproducing HS `prettyIncrementalProof.ppStep`
/// (ProofSkeleton.hs:80-84):
///   `sep [ prettyProofMethod (psMethod step)
///        , if isNothing (psInfo step) then multiComment_ ["unannotated"]
///                                     else emptyDoc ]`
///
/// `method_doc` is the rendered proof method (e.g. `solve( … )`,
/// `simplify`, `by sorry` — the `by ` prefix, if any, must already be
/// `beside`-prepended into `method_doc` by the caller).  When `annotated`
/// is true the comment is omitted and only the method is laid out.
/// When false, HughesPJ's
/// `sep` first tries to fit `method <space> /* unannotated */` on one
/// line; if the (flattened) method + comment exceeds the ribbon, the
/// comment drops to its OWN line at the sep's base indent
/// (= `base_indent`, the proof step's depth indent).
///
/// The whole step is `nest`ed at `base_indent` and the leading
/// `base_indent` spaces are stripped from the FIRST line (the caller has
/// already emitted that indent), while a dropped comment line retains its
/// `base_indent` leading spaces.
pub fn step_line_with_unann(
    method_doc: crate::pretty_hpj::Doc,
    base_indent: usize,
    annotated: bool,
    prefix: &str,
) -> String {
    use crate::pretty_hpj as hpj;
    use crate::pretty_hpj::Doc;
    let core = if annotated {
        method_doc
    } else {
        hpj::sep(vec![method_doc, unannotated_comment_doc()])
    };
    // HS `ppCases ps [] = prettyCase ps (kwBy <> text " ") <> prettyStep ps`
    // (Theory/Proof.hs:1065-1066): the `by ` keyword is laid out BESIDE the WHOLE
    // `sep [method, comment]`, NOT folded into the first `sep` element.  So
    // when `sep` breaks vertically the dropped `/* unannotated */` aligns at
    // the sep's start column = `base_indent + len(prefix)`; `beside` shifts
    // the comment's continuation column identically to HughesPJ.
    let step = if prefix.is_empty() {
        core
    } else {
        Doc::text(prefix).beside(core)
    };
    let indented = step.nest(base_indent as isize);
    let rendered = indented.render();
    let strip = rendered
        .chars()
        .take(base_indent)
        .take_while(|c| *c == ' ')
        .count();
    rendered[strip..].to_string()
}

/// The Doc of a parser-AST fact (HS `prettyLNFact` / `prettyFact`).
pub fn fact_doc(fa: &p::Fact) -> crate::pretty_hpj::Doc {
    fact_to_doc(fa)
}

/// The Doc of a parser-AST term (HS `prettyLNTerm`).
pub fn term_doc(t: &p::Term) -> crate::pretty_hpj::Doc {
    term_to_doc(t)
}

/// [`term_doc`] laid out flat, for a caller that splices the term into a
/// line of its own making.
pub fn pretty_term(t: &p::Term) -> String {
    term_doc(t).render_with(FLAT_WIDTH, FLAT_WIDTH)
}

// ============================================================================
// Intruder-variant rendering — the `tamarin-prover variants` subcommand.
//
// HS `prettyIntruderVariants` (Theory/Model/Rule.hs:1465-1466):
//   `vcat . intersperse (text "") $ map prettyIntrRuleAC vs`
// each rule via `prettyNamedRule (kwRuleModulo "AC") (const emptyDoc)`
// (Theory/Model/Rule.hs:1446-1447) = `header $-$ nest 2 body`, where the body
// is `rule::pretty_rule_restr_gen` over the rule's `LNFact`s.
// The two blocks (DH then BP) concatenate with NO separating newline
// (HS `putStrLn (dhS ++ bpS)`, Main/Mode/Intruder.hs:43-63, see line 53).
// ============================================================================

/// HS intruder-rule name (`prettyIntrRuleACInfo`, Theory/Model/Rule.hs:1347-1357):
/// `c`/`d` prefix for Constr/Destr, fixed lowercase keywords otherwise, all
/// wrapped in `prefixIfReserved` (prepend `_` for reserved names / names
/// already starting with `_`).
///
/// Also the intruder half of the DOT node labels' rule case name
/// (`constraint::system::dot`, HS `showDotRuleCaseName`), which renders the
/// same function.
pub(crate) fn intr_rule_name(info: &crate::rule::IntrRuleACInfo) -> String {
    use crate::rule::{prefix_if_reserved, IntrRuleACInfo};
    match info {
        // ConstrRule/DestrRule names already carry a leading `_` (e.g.
        // `_exp`), so the Haskell `'c' : name` yields e.g. `c_exp` (a single
        // underscore), and `prefixIfReserved` is applied on top.
        IntrRuleACInfo::ConstrRule { name, .. } => {
            prefix_if_reserved(&format!("c{}", String::from_utf8_lossy(name)))
        }
        IntrRuleACInfo::DestrRule { name, .. } => {
            prefix_if_reserved(&format!("d{}", String::from_utf8_lossy(name)))
        }
        IntrRuleACInfo::IRecv => "irecv".to_string(),
        IntrRuleACInfo::ISend => "isend".to_string(),
        IntrRuleACInfo::Coerce => "coerce".to_string(),
        IntrRuleACInfo::FreshConstr => "fresh".to_string(),
        IntrRuleACInfo::PubConstr => "pub".to_string(),
        IntrRuleACInfo::NatConstr => "nat".to_string(),
        IntrRuleACInfo::IEquality => "iequality".to_string(),
    }
}

/// `renderDoc . prettyIntruderVariants` for a block of intruder rules
/// (Theory/Model/Rule.hs:1465-1466).  Each rule is `rule (modulo AC) NAME:` then
/// the `nest 2` body; rules are separated by ONE blank line
/// (`vcat . intersperse (text "")`).  Returns the block with NO trailing
/// newline, so a DH block and a BP block concatenate seamlessly (the DH
/// `d_inv` body abutting the BP `c_pmult` header), matching HS `dhS ++ bpS`.
pub fn pretty_intruder_variants(rules: &[crate::rule::IntrRuleAC]) -> String {
    use crate::pretty_hpj::Doc;
    rules
        .iter()
        .map(|r| {
            // HS `prettyNamedRule` header: `kwRuleModulo "AC" <-> name <> ":"`.
            let header = crate::pretty_hpj::kw_rule_modulo("AC")
                .beside_sp(Doc::text(intr_rule_name(&r.info)))
                .beside(Doc::text(":"));
            // Render header and body separately: the header is one logical
            // line, the body starts fresh at `nest 2`.
            let mut s = header.render();
            s.push('\n');
            s.push_str(
                &crate::rule::pretty_rule_restr_gen(&r.premises, &r.actions, &r.conclusions)
                    .nest(2)
                    .render(),
            );
            s
        })
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// HS `avoidPrecise = avoidPreciseVars . frees` (LTerm.hs:706-709,:714-715) on
/// a guarded formula: every free variable seeds its name's counter with
/// `maxIdx + 1`, so a binder whose name a free variable uses is drawn with a
/// larger index.  `fresh_ident name` returns the counter (default 0) and
/// bumps it, so a name seeded at 1 displays as `name.1` (HS `show LVar`,
/// LTerm.hs:550-557).
fn avoid_precise_guarded(g: &Guarded) -> PreciseFreshState {
    PreciseFreshState::avoid_precise(
        tamarin_term::lterm::frees(g)
            .into_iter()
            .map(|v| (v.name.to_string(), v.idx)),
    )
}

// =============================================================================
// Locally-nameless formulas — Doc-engine path
// (HS `prettyLFormula`, Theory/Model/Formula.hs:474-514)
// =============================================================================

/// HS `prettyLNFormula` (Theory/Model/Formula.hs:518-520):
/// `Precise.evalFresh (prettyLFormula prettyNAtom fm) (avoidPrecise fm)`.
pub fn lnformula_doc(f: &LNFormula) -> Doc {
    lformula_doc(
        f,
        &pretty_natom,
        &mut Vec::new(),
        &mut avoid_precise_lnformula(f),
    )
}

/// [`lnformula_doc`] laid out flat — the one-line string the prove-time
/// guarded-conversion error quotes on stderr.  The printed theory renders
/// the same Doc at its own width.
pub fn pretty_lnformula(f: &LNFormula) -> String {
    lnformula_doc(f).render_with(FLAT_WIDTH, FLAT_WIDTH)
}

/// HS `prettySyntacticLNFormula` (Theory/Model/Formula.hs:523-525): as
/// [`lnformula_doc`], with `prettySyntacticNAtom` (Atom.hs:236-239) printing
/// the atoms, so a `Pred` atom prints as its fact.
pub fn syntactic_lnformula_doc(f: &SyntacticLNFormula) -> Doc {
    lformula_doc(
        f,
        &pretty_syntactic_natom,
        &mut Vec::new(),
        &mut avoid_precise_lnformula(f),
    )
}

/// HS `prettyLFormula ppAtom` (Theory/Model/Formula.hs:474-514).  `scope`
/// holds the display `LVar` of every enclosing binder, innermost last, which
/// is what the `Bound` indices of an atom refer to.
fn lformula_doc<S: MapSugar<BLNTerm, LNTerm>>(
    f: &LNProtoFormula<S>,
    pp_atom: &dyn Fn(&ProtoAtom<S::Mapped, LNTerm>) -> Doc,
    scope: &mut Vec<LVar>,
    state: &mut PreciseFreshState,
) -> Doc {
    match f {
        // `pp (Ato a) = return $ ppAtom (fmap (mapLits (fmap extractFree)) a)`
        // (Theory/Model/Formula.hs:484): every bound variable of the atom,
        // the sugar's included, resolves to its binder's display `LVar`
        // before the atom printer sees it.
        ProtoFormula::Atom(a) => pp_atom(&map_atom(a, &mut |t| open_bound_term(t, scope))),
        // `pp (TF True) = operator_ "⊤"` / `pp (TF False) = operator_ "⊥"`
        // (Theory/Model/Formula.hs:485-486).
        ProtoFormula::Tf(true) => hpj::operator_("\u{22A4}"),
        ProtoFormula::Tf(false) => hpj::operator_("\u{22A5}"),
        // `operator_ "¬" <> opParens p'` (Theory/Model/Formula.hs:488-490).
        ProtoFormula::Not(p_) => hpj::operator_("\u{00AC}")
            .beside(hpj::op_parens(lformula_doc(p_, pp_atom, scope, state))),
        // `sep [opParens p' <-> ppOp op, opParens q']`
        // (Theory/Model/Formula.hs:493-501); `<->` is `<+>`.
        ProtoFormula::Conn(c, l, r) => {
            let op = match c {
                Connective::And => "\u{2227}",
                Connective::Or => "\u{2228}",
                Connective::Imp => "\u{21D2}",
                Connective::Iff => "\u{21D4}",
            };
            let l_doc = hpj::op_parens(lformula_doc(l, pp_atom, scope, state));
            let r_doc = hpj::op_parens(lformula_doc(r, pp_atom, scope, state));
            hpj::sep(vec![l_doc.beside_sp(hpj::operator_(op)), r_doc])
        }
        // `scopeFreshness $ do (vs, qua, fm') <- openFormulaPrefix fm; ...
        // sep [ppQuant qua <> ppVars vs <> operator_ ".", nest 1 d']`
        // (Theory/Model/Formula.hs:503-514).  `opForall`/`opExists` carry
        // their trailing space (Theory/Text/Pretty.hs:177-178) and
        // `ppVars = fsep . map (text . show)` makes the binder list
        // breakable.
        ProtoFormula::Qua(q, hint, body) => {
            let sym = match q {
                Quantifier::All => "\u{2200} ",
                Quantifier::Ex => "\u{2203} ",
            };
            state.scope_freshness(|state| {
                let depth = scope.len();
                let (vs, inner) = open_display_prefix(*q, hint, body, scope, state);
                let var_docs: Vec<Doc> = vs
                    .iter()
                    .map(|x| {
                        // `show LVar` (LTerm.hs:550-557).
                        let mut s = String::new();
                        pp_lvar(x, &mut s);
                        Doc::text(s)
                    })
                    .collect();
                let quant = hpj::operator_(sym)
                    .beside(hpj::fsep(var_docs))
                    .beside(hpj::operator_("."));
                let body_doc = lformula_doc(inner, pp_atom, scope, state);
                scope.truncate(depth);
                hpj::sep(vec![quant, body_doc.nest(1)])
            })
        }
    }
}

/// HS `openFormulaPrefix` (Theory/Model/Formula.hs:296-309) against the
/// display scope: collect the hint of the binder at hand and of every
/// directly nested binder of the same quantifier, allocate each a display
/// `LVar` (`freshLVar n s = LVar n s <$> freshIdent n`, LTerm.hs:301-302)
/// pushed onto `scope`, and return those `LVar`s with the body beneath the
/// prefix.  The caller truncates `scope` after recursing into the body.
fn open_display_prefix<'a, S>(
    q: Quantifier,
    hint: &(String, LSort),
    body: &'a LNProtoFormula<S>,
    scope: &mut Vec<LVar>,
    state: &mut PreciseFreshState,
) -> (Vec<LVar>, &'a LNProtoFormula<S>) {
    let mut hints = vec![hint];
    let mut inner = body;
    while let ProtoFormula::Qua(q2, hint2, body2) = inner {
        if *q2 != q {
            break;
        }
        hints.push(hint2);
        inner = body2.as_ref();
    }
    let vs = hints
        .into_iter()
        .map(|(name, sort)| {
            let x = LVar::new(name, *sort, state.fresh_ident(name));
            scope.push(x);
            x
        })
        .collect();
    (vs, inner)
}

// =============================================================================
// Locally-nameless formulas — parser-AST projection
// (HS `openFormula`, Theory/Model/Formula.hs:274-291)
// =============================================================================

/// Open an [`LNFormula`] into the parser-AST formula shape
/// [`crate::formula::from_parser`] closes, with the binder names
/// [`lnformula_doc`] prints.
///
/// `rule_restriction::lift_rule_restrictions` projects the restriction
/// `restriction::from_rule_restriction` generates through this, so the
/// parser-AST theory the wellformedness checker, the elaboration and the
/// renderer read carries it.
pub fn lnformula_to_parser(f: &LNFormula) -> p::Formula {
    formula_to_parser(f, &mut Vec::new(), &mut avoid_precise_lnformula(f))
}

/// [`lnformula_to_parser`] at the parser's sugar, keeping the `Pred` atoms.
pub fn syntactic_lnformula_to_parser(f: &SyntacticLNFormula) -> p::Formula {
    formula_to_parser(f, &mut Vec::new(), &mut avoid_precise_lnformula(f))
}

/// The recursion of both projections.  `scope` holds the display `LVar` of
/// every enclosing binder, innermost last, exactly as in [`lformula_doc`];
/// `state` is the shared fresh supply, rolled back per binder block by
/// `scope_freshness` (HS `scopeFreshness`, Theory/Model/Formula.hs:503-506).
///
/// The walk is HS `openFormulaPrefix` (Theory/Model/Formula.hs:296-309) under
/// the printer's own supply: [`avoid_precise_lnformula`] seeds the `Precise`
/// counters with the formula's free variables (HS `avoidPrecise`,
/// LTerm.hs:714-715), each binder takes a fresh index for its hint name, and
/// each atom is opened against the enclosing binders' display `LVar`s, so a
/// bound occurrence carries that same `(name, idx, sort)` identity — a binder
/// name never collides with a free variable, and a reopened occurrence never
/// resolves to a different binder.
/// A run of binders of one quantifier becomes one `Forall`/`Exists` list, the
/// shape HS's `foldr (hinted q) f vs` closes
/// (Theory/Text/Parser/Formula.hs:73-77).
fn formula_to_parser<S>(
    f: &LNProtoFormula<S>,
    scope: &mut Vec<LVar>,
    state: &mut PreciseFreshState,
) -> p::Formula
where
    S: MapSugar<BLNTerm, LNTerm> + SugarTerms<BLNTerm>,
    S::Mapped: SugarToParser,
{
    match f {
        ProtoFormula::Atom(a) => p::Formula::Atom(proto_atom_to_parser(&map_atom(a, &mut |t| {
            open_bound_term(t, scope)
        }))),
        ProtoFormula::Tf(true) => p::Formula::True,
        ProtoFormula::Tf(false) => p::Formula::False,
        ProtoFormula::Not(p_) => p::Formula::Not(Box::new(formula_to_parser(p_, scope, state))),
        ProtoFormula::Conn(c, l, r) => {
            let l_ast = Box::new(formula_to_parser(l, scope, state));
            let r_ast = Box::new(formula_to_parser(r, scope, state));
            match c {
                Connective::And => p::Formula::And(l_ast, r_ast),
                Connective::Or => p::Formula::Or(l_ast, r_ast),
                Connective::Imp => p::Formula::Implies(l_ast, r_ast),
                Connective::Iff => p::Formula::Iff(l_ast, r_ast),
            }
        }
        ProtoFormula::Qua(q, hint, body) => state.scope_freshness(|state| {
            let depth = scope.len();
            let (xs, inner) = open_display_prefix(*q, hint, body, scope, state);
            let vs: Vec<p::VarSpec> = xs
                .into_iter()
                .map(|x| p::VarSpec {
                    name: x.name.to_string(),
                    idx: x.idx,
                    sort: x.sort,
                    typ: None,
                })
                .collect();
            let body_ast = Box::new(formula_to_parser(inner, scope, state));
            scope.truncate(depth);
            match q {
                Quantifier::All => p::Formula::Forall(vs, body_ast),
                Quantifier::Ex => p::Formula::Exists(vs, body_ast),
            }
        }),
    }
}

// =============================================================================
// HS HughesPJ ribbon + fit constants, used by the Doc-engine
// `render_at` layout for both the full-formula and guarded wrapped paths.
// =============================================================================

/// HS ribbon width.  HS sets `lineWidth = 110` (`Main/Console.hs:241-243, see line 243`)
/// and `defaultStyle.ribbonsPerLine = 1.5` (`HughesPJ.hs:940`), giving
/// `ribbonLen = round(110/1.5) = 73` (`HughesPJ.hs:1010`).
pub const RIBBON: usize = 73;

/// HS hard page width.  Mirrors `lineWidth = 110`
/// (`Main/Console.hs:241-243, see line 243`).
pub const LINE_LENGTH: usize = 110;

/// The spelling of a parser-AST variable occurrence: HS `show LVar`
/// (LTerm.hs:550-557), `sortPrefix ++ name` with a `.<idx>` suffix for a
/// non-zero index.
fn var_display(v: &p::VarSpec) -> String {
    let mut s = String::from(sort_prefix(v.sort));
    s.push_str(&v.name);
    if v.idx > 0 {
        s.push('.');
        s.push_str(&v.idx.to_string());
    }
    s
}

// =============================================================================
// Term / Fact — HughesPJ Doc engine (HS-faithful wrapping)
//
// `term_to_doc` mirrors HS `prettyTerm` (Term/Term.hs:298-327): pairs use
// `ppTerms ", " 1 "<" ">" = fcat . (text "<":) . (++[text ">"]) . map (nest 1)
// . punctuate ", " . map ppTerm`; function applications use
// `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts))
// <> text ")"`.  `fact_to_doc` mirrors HS `prettyFact`/`ppFact`
// (Theory/Model/Fact.hs:567-574) = `nestShort' (n++"(") ")" . fsep .
// punctuate comma $ map ppTerm ts`, with `nestShort' lead finish =
// nestShort (length lead + 1) (text lead) (text finish)` and
// `nestShort n lead finish body = sep [lead $$ nest n body, finish]`
// (Text/PrettyPrint/Class.hs:218-223).  Building these as real `pretty_hpj::Doc` trees and
// letting the ported HughesPJ engine lay them out makes the fcat/fsep/sep
// wrap decisions byte-identical to HS.
// =============================================================================

/// HS `comma = char ','`.
fn comma_doc() -> crate::pretty_hpj::Doc {
    crate::pretty_hpj::Doc::char(',')
}

/// Build the bracketed fact-annotation suffix, e.g. `[+, no_precomp]`.
///
/// HS `ppAnn ann = brackets . fsep . punctuate comma $ map (text .
/// showFactAnnotation) $ S.toList ann` (Theory/Model/Fact.hs:573-574).
/// `S.toList` of a `Set FactAnnotation` yields elements in `FactAnnotation`
/// `Ord` order, which is the data-declaration order
/// `SolveFirst < SolveLast < NoSources` (Theory/Model/Fact.hs:154-155).  The parser-AST
/// path stores annotations in a `Vec` in source (parse) order, so we sort by
/// that key and dedup before rendering to match HS's set semantics.
///
/// For these three short annotations HS's `fsep`+`punctuate comma`+`brackets`
/// produces exactly `", "` separators and never wraps, so the flat `String`
/// here is byte-identical to the HS `Doc`; only the ordering is load-bearing.
fn fact_annotations_suffix(annotations: &[p::FactAnnotation]) -> Option<String> {
    if annotations.is_empty() {
        return None;
    }
    // `FactAnnotation` Ord rank (declaration order); also used to dedup.
    fn rank(a: &p::FactAnnotation) -> u8 {
        match a {
            p::FactAnnotation::SolveFirst => 0,
            p::FactAnnotation::SolveLast => 1,
            p::FactAnnotation::NoSources => 2,
        }
    }
    let mut ranks: Vec<u8> = annotations.iter().map(rank).collect();
    ranks.sort_unstable();
    ranks.dedup();
    let mut s = String::from("[");
    for (i, r) in ranks.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(match r {
            0 => "+",
            1 => "-",
            _ => "no_precomp",
        });
    }
    s.push(']');
    Some(s)
}

/// Pretty-print a parser-AST term as a `pretty_hpj::Doc`.  Faithful to HS
/// `prettyTerm`.
fn term_to_doc(t: &p::Term) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    use p::Term::*;
    match t {
        // HS `prettyTerm` (Term/Term.hs:299-303) sends a literal to `ppLit`,
        // which for `prettyNTerm` is `text . show` (Term/LTerm.hs:930-931) —
        // one unbreakable `text`.
        Var(v) => Doc::text(var_display(v)),
        PubLit(s) => Doc::text(format!("'{s}'")),
        FreshLit(s) => Doc::text(format!("~'{s}'")),
        NatLit(s) => Doc::text(format!("%'{s}'")),
        Number(n) => Doc::text(n.to_string()),
        // HS `fAppOne = fAppNoEq oneSym []` (Term/Term.hs:147-148), and
        // `prettyTerm` has NO special case for `oneSym` (Term/Term.hs:298-327)
        // — a nullary `NoEq` symbol falls through to `text (BC.unpack f)`,
        // i.e. its symbol string `"one"` (`oneSymString`,
        // Term/Term/FunctionSymbols.hs:226; `oneSym` at 255).  The `1` keyword
        // is only a *parser* spelling for this constant; HS always renders it
        // back as `one`.
        NumberOne => Doc::text("one"),
        NatOne => Doc::text("%1"),
        // HS `dhNeutralSym` is a nullary NoEq public constructor; HS
        // `prettyTerm` renders `FApp (NoEq (f,_)) []` as `text f` =
        // `dhNeutralSymString` = "DH_neutral" (Term/Term.hs:314;
        // Term/Term/FunctionSymbols.hs:229, mirrored by
        // `function_symbols::DH_NEUTRAL_SYM_STRING`).  NOT `1:msg`/`1`.
        DhNeutral => Doc::text("DH_neutral"),
        // The `=`-pattern prefix of a SAPIC pattern position, which HS parses
        // over a variable (`sapicpatternvar`,
        // Theory/Text/Parser/Token.hs:512-518) and carries in
        // `PatternSapicLVar`, not in the term.  There is no HS term arm for
        // it; it renders as one unbreakable `text`, whatever shape a `let`
        // substitution left under the `=`.
        PatMatch(inner) => Doc::text(format!(
            "={}",
            term_to_doc(inner).render_with(FLAT_WIDTH, FLAT_WIDTH)
        )),
        // HS `prettyTerm` (Term/Term.hs:313):
        //   `FApp (NoEq s) _ | s == pairSym -> ppTerms ", " 1 "<" ">" (split t)`
        // The arm fires on the pair SHAPE, so the prefix spelling `pair(a, b)`
        // renders `<a, b>` exactly like the `<a, b>` spelling; `split`
        // (`flatten_pair_terms`) walks the right spine of either form.  The
        // `App` case precedes the generic `App` arm below, which would
        // otherwise print `pair(a, b)` through `ppFun`.
        Pair(_) => pair_doc(&flatten_pair_terms(t)),
        App(name, args) if name == "pair" && args.len() == 2 => pair_doc(&flatten_pair_terms(t)),
        App(name, args) => {
            if args.is_empty() {
                // HS checks `s == natOneSym` BEFORE the generic nullary
                // fallthrough: `FApp (NoEq s) [] | s == natOneSym -> text
                // "%1"` (Term/Term.hs:298-327, see line 312).  `natOneSym = ("tone",
                // (0,Public,Constructor))`; the parser AST keeps only the
                // name, so match on nullary "tone", the shape an internal
                // nat-one takes when it is projected onto the parser AST.
                if name == "tone" {
                    Doc::text("%1")
                } else {
                    // HS `FApp (NoEq (f,_)) [] -> text f` (Term/Term.hs:298-327, see line 314).
                    Doc::text(name.clone())
                }
            } else {
                fun_doc(name, args)
            }
        }
        AlgApp(name, l, r) => fun_doc_two(name, l, r),
        // HS `prettyTerm` dedicated diff case (Term/Term.hs:298-327, see line 311):
        //   `... | s == diffSym -> text "diff" <> "(" <> ppTerm t1 <>
        //         ", " <> ppTerm t2 <> ")"` — all `<>` (no `fsep`), so it is
        //   fully flat and never breaks at the comma (unlike the generic
        //   `ppFun`/`fun_doc` path which joins args with a breakable `fsep`).
        Diff(l, r) => Doc::text("diff(")
            .beside(term_to_doc(l))
            .beside(Doc::text(", "))
            .beside(term_to_doc(r))
            .beside(Doc::text(")")),
        BinOp(op, l, r) => {
            // HS `prettyTerm` (Term/Term.hs:305-310):
            //   `FApp (AC o) ts -> ppTerms (ppACOp o) 1 "(" ")" ts`  (wraps via fcat)
            //   `FApp (NoEq s) [t1,t2] | s == expSym -> ppTerm t1 <> "^" <> ppTerm t2`
            //     (flat beside, never breaks).
            // exp renders flat; AC ops (Mult/Union/Xor/NatPlus and the
            // user-declared `[AC]` symbols) use the SAME fcat structure as
            // pairs, with `(`/`)` lead/finish and the AC-op symbol as
            // separator — bare for the builtins, space-surrounded for a
            // user-declared symbol (see `binop_symbol`).
            if matches!(op, p::BinOp::Exp) {
                // HS `prettyTerm` (Term/Term.hs:298-327, see line 310):
                //   `FApp (NoEq s) [t1,t2] | s == expSym -> ppTerm t1 <> "^" <> ppTerm t2`
                // The exp itself never breaks at the `^`, but its operands are
                // recursively `ppTerm`'d, so an AC exponent (e.g.
                // `'g'^(~a*~b)`) keeps its inner `fcat` BREAK POINTS — the
                // `*`-operands wrap when the term overruns at deep indent.
                // Composing the operand Docs with `beside` (HS `<>`) preserves
                // that inner fcat.
                term_to_doc(l).beside(Doc::text("^")).beside(term_to_doc(r))
            } else {
                // Flatten same-op children to the n-ary chain HS's `viewTerm`
                // exposes for AC symbols.
                let mut flat: Vec<&p::Term> = Vec::new();
                flatten_ac_terms(*op, l, &mut flat);
                flatten_ac_terms(*op, r, &mut flat);
                ac_op_doc(binop_symbol(*op), &flat)
            }
        }
    }
}

/// Flatten a same-op `BinOp` chain into the n-ary arg vector HS's `viewTerm`
/// exposes for AC symbols (Term/Term.hs).  Parser-AST variant.
fn flatten_ac_terms<'a>(op: p::BinOp, t: &'a p::Term, out: &mut Vec<&'a p::Term>) {
    match t {
        p::Term::BinOp(inner, l, r) if *inner == op => {
            flatten_ac_terms(op, l, out);
            flatten_ac_terms(op, r, out);
        }
        _ => out.push(t),
    }
}

/// HS `prettyTerm`'s `split` (Term/Term.hs:323-324): the operand list a
/// pair-headed term renders between `<` and `>`.  `split` recurses on the
/// RIGHT child while that child is itself `pairSym`-headed (`FPair`,
/// Term/Term/Raw.hs:194), so `pair(a, pair(b, c))` yields `[a, b, c]` while
/// the left-nested `pair(pair(a, b), c)` yields `[pair(a, b), c]`.  A non-pair
/// `t` yields `[t]`.
///
/// Both parser spellings feed the same spine: `Pair` holds `<a, b, c>` flat
/// where HS nests it `pair(a, pair(b, c))`, so every element but the last is
/// an operand and the last continues the spine; `App("pair", [a, b])` pushes
/// its left operand and continues on the right.  Mirror of
/// `crate::wellformedness::facts`'s `pair_split`.  Parser-AST variant.
fn pair_split_terms<'a>(t: &'a p::Term, out: &mut Vec<&'a p::Term>) {
    match t {
        p::Term::Pair(items) => {
            if let Some((last, init)) = items.split_last() {
                out.extend(init.iter());
                pair_split_terms(last, out);
            }
        }
        p::Term::App(n, args) if n == "pair" && args.len() == 2 => {
            out.push(&args[0]);
            pair_split_terms(&args[1], out);
        }
        _ => out.push(t),
    }
}

/// [`pair_split_terms`] as a `Vec`-returning helper for the two render paths.
fn flatten_pair_terms(t: &p::Term) -> Vec<&p::Term> {
    let mut flat: Vec<&p::Term> = Vec::new();
    pair_split_terms(t, &mut flat);
    flat
}

/// HS `ppTerms (ppACOp o) 1 "(" ")" ts` (Term/Term.hs:305-309; `ppTerms` at
/// Term/Term.hs:319-321) — a fcat of `text "("`, each element `nest 1`'d and
/// AC-op-suffixed (except last),
/// and `text ")"`.  Structurally identical to `pair_doc` with different
/// lead/finish/separator.  The AC-op symbol carries NO surrounding spaces
/// (HS `punctuate (text sepa)` with `sepa = "++"`/`"*"`/`"⊕"`/`"%+"`).
fn ac_op_doc(sym: &str, flat: &[&p::Term]) -> crate::pretty_hpj::Doc {
    crate::pretty_hpj::fcat_bracketed("(", sym, ")", flat, term_to_doc)
}

/// HS `ppTerms ", " 1 "<" ">" flat` (Term/Term.hs:313,319-321) — a fcat of
/// `text "<"`, each element `nest 1`'d and comma-suffixed (except last),
/// and `text ">"`.
fn pair_doc(flat: &[&p::Term]) -> crate::pretty_hpj::Doc {
    // HS punctuates with `text ", "`, so all but the last element get a
    // trailing ", "; then each is `nest 1`.
    crate::pretty_hpj::fcat_bracketed("<", ", ", ">", flat, term_to_doc)
}

/// HS `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts))
/// <> text ")"` (Term/Term.hs:326-327), over a slice of `&Term` so callers
/// (incl. the boxed-pair binary shapes) need not clone the subtrees.
fn fun_doc_refs(name: &str, args: &[&p::Term]) -> crate::pretty_hpj::Doc {
    crate::pretty_hpj::fun_app_doc(name, args, term_to_doc)
}

/// As `fun_doc_refs`, for callers holding an owned `&[p::Term]`.
fn fun_doc(name: &str, args: &[p::Term]) -> crate::pretty_hpj::Doc {
    let refs: Vec<&p::Term> = args.iter().collect();
    fun_doc_refs(name, &refs)
}

/// `fun_doc` for the binary algebraic / diff shapes that the parser stores
/// as boxed pairs rather than a `Vec` — passes the operands by reference
/// (no subtree clone).
fn fun_doc_two(name: &str, l: &p::Term, r: &p::Term) -> crate::pretty_hpj::Doc {
    fun_doc_refs(name, &[l, r])
}

/// Pretty-print a fact as a `pretty_hpj::Doc`.  Faithful to HS `prettyFact`
/// / `ppFact` (Theory/Model/Fact.hs:567-574) with `nestShort'`
/// (Text/PrettyPrint/Class.hs:218-223).
fn fact_to_doc(fa: &p::Fact) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let lead = {
        let mut s = String::new();
        if fa.persistent {
            s.push('!');
        }
        s.push_str(&fa.name);
        s.push('(');
        s
    };
    let arg_docs: Vec<Doc> = fa.args.iter().map(term_to_doc).collect();
    let body = hpj::fsep(hpj::punctuate(comma_doc(), arg_docs));
    let mut d = hpj::nest_short_doc(&lead, ")", body);
    // Fact annotations: `<> ppAnn an = brackets . fsep . punctuate comma` in
    // `FactAnnotation` Ord order (see `fact_annotations_suffix`).
    if let Some(ann) = fact_annotations_suffix(&fa.annotations) {
        d = d.beside(Doc::text(ann));
    }
    d
}

/// The separator table on [`p::BinOp`], narrowed to the `&'static str` the
/// `Doc` builders take.  A user-declared `[AC]` symbol's separator is its name
/// surrounded by spaces (HS `ppTerms (" " ++ BC.unpack f ++ " ") 1 "(" ")" ts`,
/// Term/Term.hs:305); `ac_fct_op_symbol` is the interning fast path for it, so
/// rendering a user-AC application allocates nothing.
fn binop_symbol(op: p::BinOp) -> &'static str {
    match op {
        p::BinOp::AcFct(name) => tamarin_term::pretty::ac_fct_op_symbol(name),
        _ => match op.separator() {
            std::borrow::Cow::Borrowed(s) => s,
            std::borrow::Cow::Owned(s) => tamarin_term::intern::intern_str(&s),
        },
    }
}

// =============================================================================
// Guarded — the `prettyGuarded` Doc
// =============================================================================
//
// Build a `pretty_hpj::Doc` tree mirroring HS `prettyGuarded`
// (Guarded.hs:824-866) EXACTLY, then render it via the HughesPJ-faithful
// engine (`crate::pretty_hpj`).  The formula-structural nodes
// (GDisj/GConj/GGuarded) carry the sep-Unions where the engine makes its
// byte-exact wrap decisions; the atoms and facts under them carry the break
// points `prettyNAtom`/`prettyFact`/`prettyTerm` give them.
//
// HS recurrences (Guarded.hs:830-866):
//   pp (GAto a)        = prettyNAtom (bvarToLVar a)            -- flat
//   pp (GDisj [])      = operator_ "⊥"
//   pp (GDisj xs)      = parens $ sep $ punctuate " ∨" (map opParens ps)
//   pp (GConj [])      = operator_ "⊤"
//   pp (GConj xs)      = sep $ punctuate " ∧" (map opParens ps)
//   pp (GGuarded ...)  = scopeFreshness $ ... with
//       dante      = nest 1 (pp (GConj antecedent))
//       quantifier = operator_ ppQ <-> ppVars vs <> operator_ "."
//       (Ex,_,GConj []) -> sep [quantifier, dante]
//       (All,[],GDisj []) | gfalse -> operator_ "¬" <> dante
//       _               -> dsucc = nest 1 (pp gf);
//                          sep [quantifier, sep [dante, connective, dsucc]]

/// Build a `pretty_hpj::Doc` for a guarded formula, mirroring HS `pp`
/// inside `prettyGuarded` (Guarded.hs:830-866).  Threads the Precise fresh
/// `state` through the scope-freshness each `GGuarded` opens, which is the
/// supply [`open_guarded`] draws that binder's names from.
fn guarded_to_doc(g: &Guarded, state: &mut PreciseFreshState) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    match g {
        // HS `pp (GAto a) = prettyNAtom (bvarToLVar a)` (Guarded.hs:831).
        Guarded::Atom(a) => pretty_natom(&bvar_to_lvar(a)),
        Guarded::Disj(xs) if xs.is_empty() => hpj::operator_("\u{22A5}"), // ⊥
        Guarded::Conj(xs) if xs.is_empty() => hpj::operator_("\u{22A4}"), // ⊤
        Guarded::Disj(xs) => {
            // HS: `parens $ sep $ punctuate (operator_ " ∨") (map opParens ps)`.
            let ps: Vec<Doc> = xs
                .iter()
                .map(|x| hpj::op_parens(guarded_to_doc(x, state)))
                .collect();
            let punct = hpj::punctuate(hpj::operator_(" \u{2228}"), ps); // " ∨"
                                                                         // `parens` (Text/PrettyPrint/Class.hs:149-149) is `char '(' <> d <> char ')'` — PLAIN.
            Doc::char('(')
                .beside(hpj::sep(punct))
                .beside(Doc::char(')'))
        }
        Guarded::Conj(xs) => {
            // HS: `sep $ punctuate (operator_ " ∧") (map opParens ps)`.
            let ps: Vec<Doc> = xs
                .iter()
                .map(|x| hpj::op_parens(guarded_to_doc(x, state)))
                .collect();
            let punct = hpj::punctuate(hpj::operator_(" \u{2227}"), ps); // " ∧"
            hpj::sep(punct)
        }
        // HS: `scopeFreshness $ do ...` (Guarded.hs:846-862).
        Guarded::GGuarded { .. } => state.scope_freshness(|state| gguarded_to_doc(g, state)),
    }
}

/// Doc for a `GGuarded`, after `scopeFreshness` saved the Precise state.
/// Mirrors HS Guarded.hs:849-862.
fn gguarded_to_doc(g: &Guarded, state: &mut PreciseFreshState) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    // HS `(qua, vs, atoms, gf) <- fromJust <$> openGuarded gf0`
    // (Guarded.hs:849): the binders are drawn from this scope's supply and
    // substituted into the guards and the body.
    let (qua, vs, atoms, body) = open_guarded(g, state).expect("gguarded_to_doc: not a GGuarded");

    // `dante = nest 1 $ pp (GConj (Conj antecedent))` with
    // `antecedent = map (GAto . fmap (fmapTerm (fmap Free))) atoms`
    // (Guarded.hs:850-854): each opened guard is a `pp (GAto …)` wrapped in
    // opParens, and an empty antecedent is `pp (GConj (Conj [])) =
    // operator_ "⊤"`.
    let dante = if atoms.is_empty() {
        hpj::operator_("\u{22A4}").nest(1)
    } else {
        let ps: Vec<Doc> = atoms
            .iter()
            .map(|a| hpj::op_parens(pretty_natom(a)))
            .collect();
        let punct = hpj::punctuate(hpj::operator_(" \u{2227}"), ps);
        hpj::sep(punct).nest(1)
    };

    // `quantifier = operator_ ppQuant <-> ppVars vs <> operator_ "."`.
    // `<->` is `<+>` (beside with one space); `ppVars = fsep . map (text .
    // show)` (Guarded.hs:864) over the drawn variables, whose `show` is the
    // sort prefix, the name and a `.<idx>` suffix past index 0
    // (LTerm.hs:550-557).
    let sym = match qua {
        Quantifier::All => "\u{2200}",
        Quantifier::Ex => "\u{2203}",
    };
    let var_docs: Vec<Doc> = vs.iter().map(|v| Doc::text(v.to_string())).collect();
    let ppvars = hpj::fsep(var_docs);
    let quantifier = hpj::operator_(sym)
        .beside_sp(ppvars)
        .beside(hpj::operator_("."));

    // Case analysis (Guarded.hs:855-862).
    let is_ex_trivial = matches!(qua, Quantifier::Ex) && body_is_true(&body);
    let is_neg = matches!(qua, Quantifier::All) && vs.is_empty() && body_is_false(&body);

    if is_neg {
        // `(All, [], GDisj []) | gf == gfalse -> operator_ "¬" <> dante`.
        hpj::operator_("\u{00AC}").beside(dante)
    } else if is_ex_trivial {
        // `(Ex, _, GConj []) -> sep [quantifier, dante]`.
        hpj::sep(vec![quantifier, dante])
    } else {
        // `_ -> dsucc = nest 1 (pp gf);
        //       sep [quantifier, sep [dante, connective, dsucc]]`.
        let connective = hpj::operator_(match qua {
            Quantifier::All => "\u{21D2}", // ⇒
            Quantifier::Ex => "\u{2227}",  // ∧
        });
        let dsucc = guarded_to_doc(&body, state).nest(1);
        let inner = hpj::sep(vec![dante, connective, dsucc]);
        hpj::sep(vec![quantifier, inner])
    }
}

fn body_is_false(g: &Guarded) -> bool {
    matches!(g, Guarded::Disj(v) if v.is_empty())
}

fn body_is_true(g: &Guarded) -> bool {
    matches!(g, Guarded::Conj(v) if v.is_empty())
}

#[cfg(test)]
#[path = "pretty_formula_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "pretty_formula_corpus_tests.rs"]
mod corpus_tests;
