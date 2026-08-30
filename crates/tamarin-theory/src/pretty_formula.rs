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

use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::pretty::pp_lvar;
use tamarin_utils::fresh::PreciseFreshState;

use crate::atom::{map_atom, pretty_natom, pretty_syntactic_natom, MapSugar, ProtoAtom};
use crate::formula::{
    avoid_precise_lnformula, open_bound_term, BLNTerm, Connective, LNFormula, LNProtoFormula,
    ProtoFormula, Quantifier, SyntacticLNFormula,
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
