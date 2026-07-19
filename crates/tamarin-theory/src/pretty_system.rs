// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, felixlinker, PhilipLukertWork, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs,
//   lib/term/src/Term/Substitution/SubstVFree.hs,
//   lib/theory/src/Pretty.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Text/Pretty.hs,
//   lib/theory/src/Theory/Tools/EquationStore.hs,
//   lib/theory/src/Theory/Tools/SubtermStore.hs,
//   lib/utils/src/Control/Monad/Disj/Class.hs,
//   lib/utils/src/Text/PrettyPrint/Class.hs, src/Web/Theory.hs

//! Pretty-printer for the constraint `System`.
//!
//! Port of `prettyNonGraphSystem` from
//! `lib/theory/src/Theory/Constraint/System.hs:1673-1686`.  Emits the same
//! ordered section list the Haskell interactive UI shows in its
//! "Constraint system" pane:
//!
//!   last:     ...
//!   formulas: ...
//!   subterms: ...
//!   equations: ...
//!   lemmas: ...
//!   allowed cases: ...
//!   solved formulas: ...
//!   unsolved constraints: ...
//!   solved constraints: ...
//!
//! NOTE: the `subterms` and `equations` section bodies are faithful
//! ports of Haskell's `prettySubtermStore` (SubtermStore.hs:569-581) and
//! `prettyEqStore` (EquationStore.hs:876-896) — same `Contradictory` /
//! `CONTRADICTORY` headers, numbered keyword sections and `∃`-quantified
//! disjuncts — built on the `pretty_hpj` HughesPJ Doc engine.  The whole
//! pane is ONE Doc (`vsep $ map combine_ …`, System.hs:1675-1686) rendered
//! once, so every term/formula/goal wraps at the pane width under its
//! real section nesting, exactly as HS.  Residual divergences documented
//! on `pretty_subterm_store` / `pretty_eq_store` (derived term `Ord` for
//! set iteration orders).  These are interactive-UI diagnostic panes only
//! and do not affect proof results or golden `--prove` output.

use tamarin_term::pretty::{pp_lvar, pretty_lnterm};
// HS `flushRight n str` (Extension.Prelude): left-pad `str` with spaces to width n.
use tamarin_utils::prelude_ext::flush_right;

use crate::pretty_hpj::{fsep, punctuate, Doc};
use crate::constraint::constraints::{Goal, NodeId};
use crate::constraint::system::{SourceKind, System};
use crate::fact::{fact_tag_name, LNFact};
use crate::guarded::Guarded;
use crate::pretty_formula::guarded_doc;

/// Emit just the non-graph-part of the system, matching Haskell's
/// `prettyNonGraphSystem` (System.hs:1675-1686):
/// `vsep $ map combine_ [("last", …), …]` — the entire pane is a single
/// Doc rendered once at the web display width.
pub fn pretty_non_graph_system(sys: &System) -> String {
    // HS renders this pane (Web/Theory.hs:513-611, see line 535 `preformatted (Just "sequent")
    // (prettyNonGraphSystem se)`) through the `HtmlDoc Doc` transformer via
    // `renderHtmlDoc`: keywords/operators become `hl_*` spans, every `text` is
    // entity-escaped, and the HughesPJ fill measures each token at its escaped
    // width (`&lt;`/`&gt;`/`&#39;`) when choosing line breaks (task #17 family
    // D).  The web callers install an [`HtmlDocGuard`] around this call, so the
    // Doc is built (and its per-token widths captured) under HtmlDoc mode; the
    // plain `--prove`/unit-test path builds it with no guard (visible-column
    // widths, no spans, no escaping), so it is unchanged.
    let sections = vec![
        combine("last", pretty_last(sys)),
        combine("formulas", pretty_formula_set(&sys.formulas)),
        combine("subterms", pretty_subterm_store(sys)),
        combine("equations", pretty_eq_store(sys)),
        combine("lemmas", pretty_formula_set(&sys.lemmas)),
        combine("allowed cases", Doc::text(pretty_source_kind(sys.source_kind))),
        combine("solved formulas", pretty_formula_set(&sys.solved_formulas)),
        combine("unsolved constraints", pretty_goals(sys, false)),
        combine("solved constraints", pretty_goals(sys, true)),
    ];
    vsep_docs(sections).render()
}

// ---------------------------------------------------------------------
// vsep / $--$ (HS Pretty.hs:83-84, Class.hs:112-114)
// ---------------------------------------------------------------------

// HS `d1 $--$ d2 = caseEmptyDoc d2 (caseEmptyDoc d1 (d1 $-$ text "" $-$ d2)
// d2) d1` (Class.hs:112-114): if d1 is Empty → d2; else if d2 is Empty →
// d1; else the two separated by a blank line (`$-$ text "" $-$`).
// `isEmpty` matches only the literal `Empty` constructor (HughesPJ).
fn above_blank(d1: Doc, d2: Doc) -> Doc {
    if matches!(d1, Doc::Empty) {
        return d2;
    }
    if matches!(d2, Doc::Empty) {
        return d1;
    }
    d1.above_g(blank_text()).above_g(d2)
}

// HS `vsep = foldr ($--$) emptyDoc` (Pretty.hs:83-84) — RIGHT fold.
fn vsep_docs(ds: Vec<Doc>) -> Doc {
    let mut acc = Doc::Empty;
    for d in ds.into_iter().rev() {
        acc = above_blank(d, acc);
    }
    acc
}

// HS `prettyNTerm t` (LTerm.hs:893-894, see line 894 `prettyTerm (text . show)`) as a Doc,
// via the parser-AST projection — the same Doc path the proof printer and
// web DOT renderer use, so fact/term wrapping is byte-faithful.
fn lnterm_doc(t: &tamarin_term::lterm::LNTerm) -> Doc {
    crate::pretty_formula::term_doc(&crate::pretty_theory::lnterm_to_parser(t))
}

// ---------------------------------------------------------------------
// last_atom
// ---------------------------------------------------------------------

// HS `maybe (text "none") prettyNodeId $ L.get sLastAtom se` (System.hs:1673-1686, see line 1676).
fn pretty_last(sys: &System) -> Doc {
    match &sys.last_atom {
        None => Doc::text("none"),
        Some(nid) => Doc::text(pretty_node_id(nid)),
    }
}

// ---------------------------------------------------------------------
// formulas / lemmas / solved_formulas
// ---------------------------------------------------------------------

/// Render a guarded-formula collection whose Haskell counterpart is a
/// `S.Set LNGuarded` (System.hs:1673-1686, see line 1679 renders `sLemmas` via `S.toList`,
/// i.e. ascending `Ord LNGuarded` with structural dedup).  RS stores
/// `sLemmas` as a `Vec<Guarded>` in *insertion* order (see
/// `System::insert_lemma`), so the raw Vec would render in a different
/// order than HS whenever two lemmas were inserted out of Ord order
/// (e.g. the two safety restrictions of `design-choices.spthy`).  Mirror
/// `S.toList` here by sorting a view of the Vec with the HS-faithful
/// `cmp_guarded` comparator (guarded.rs — the derived `Ord Guarded`) and
/// collapsing `Ord`-equal duplicates, exactly as the equivalent
/// sort+dedup in `rename_precise.rs` does for the live field.
///
/// This is a *render-time only* reordering: the live `sys.lemmas` Vec is
/// left untouched, so the constraint-solver iteration order (which some
/// implied-formula sites read in storage order) is unchanged and the
/// `--prove` byte-identity corpus is unaffected.  `prettyNonGraphSystem`
/// is reached only from the interactive/web constraint-system pane, never
/// from `--prove` output.
///
/// HS: `vsep $ map prettyGuarded $ S.toList` (System.hs:1673-1686, see line 1677/1680/1682) —
/// each formula is a real Doc (`guarded_doc`) and formulas are separated
/// by a blank line (`vsep` = fold `$--$`).
fn pretty_formula_set(items: &[std::sync::Arc<Guarded>]) -> Doc {
    if items.is_empty() { return Doc::Empty; }
    let mut sorted: Vec<&Guarded> = items.iter().map(|f| f.as_ref()).collect();
    sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    sorted.dedup_by(|a, b| crate::guarded::cmp_guarded(a, b) == std::cmp::Ordering::Equal);
    vsep_docs(sorted.into_iter().map(guarded_doc).collect())
}

// ---------------------------------------------------------------------
// subterm / equation stores
// ---------------------------------------------------------------------

// --- Doc helpers mirroring `Text.PrettyPrint.Class` -------------------

// HS `numbered vsep ds` (Class.hs:252-259): right-flushed 1-based indices,
// items joined vertically (`$-$`) with `vsep` interspersed between them.
fn numbered(vsep: Doc, ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::empty();
    }
    let n = ds.len();
    let n_width = n.to_string().len();
    let mut acc: Option<Doc> = None;
    for (i, d) in ds.into_iter().enumerate() {
        // `text (flushRight nWidth (show i)) <> d`
        let label = flush_right(n_width, &(i + 1).to_string());
        let item = Doc::text(label).beside(d);
        acc = Some(match acc {
            None => item,
            // intersperse vsep, fold with `$-$` (above_g)
            Some(prev) => prev.above_g(vsep.clone()).above_g(item),
        });
    }
    acc.unwrap_or_else(Doc::empty)
}

// HS `numbered'` (Class.hs:263-264): `numbered (text "") . map (". " <>)`.
// `text ""` is a zero-width text run (NOT `empty`); interspersed with `$-$`
// it inserts a *blank line* between numbered items.  `Doc::text("")`
// collapses to `Doc::Empty` (which would be dropped by `$-$`), so we build
// the zero-width text run explicitly via `blank_text`.
fn numbered_prime(ds: Vec<Doc>) -> Doc {
    let mapped: Vec<Doc> = ds
        .into_iter()
        .map(|d| Doc::text(". ").beside(d))
        .collect();
    numbered(blank_text(), mapped)
}

// HS `text ""` — a zero-width, zero-column text run.  Distinct from
// `Doc::Empty`: under `$$`/`$-$` it contributes a blank line, whereas
// `Empty` is the layout identity and collapses away.
fn blank_text() -> Doc {
    Doc::TextBeside(std::rc::Rc::from(""), 0, std::rc::Rc::new(Doc::Empty))
}

// HS `combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]`
// (SubtermStore.hs:569-581, see line 576 / EquationStore.hs:568-588, see line 574) — the section header is a
// `keyword_` span, the colon is plain.  `keyword_` is the identity in plain mode.
fn combine(header: &str, d: Doc) -> Doc {
    fsep(vec![crate::pretty_hpj::keyword_(header).beside(Doc::char(':')), d.nest(2)])
}

// Faithful port of Haskell `prettySubtermStore` (SubtermStore.hs:569-581).
// Emits an optional `Contradictory: yes` header, then (when the store is
// non-empty) three numbered keyword-headed sections `Negative Subterms` /
// `Subterms` / `Solved Subterms`, each item rendered as
// `prettyNTerm a $$ nest 3 (⊏ <-> prettyNTerm b)`.
//
// Known divergence (UI diagnostic pane only — not reached by raw
// `--prove` output): ordering is byte-faithful only for `neg_subterms`,
// which is kept sorted by `add_neg`'s `binary_search` insert (matching HS
// `S.toList` over the `negSt` Set). `subterms`/`solved_subterms` are
// `Vec`s in insertion order (`.push()` in `add`/`conjoin`), whereas HS
// emits the `posSt`/`solvedSt` Sets via `S.toList` in `Ord` order — so
// their numbered ordering may differ from Haskell. Left as-is: sorting
// needs a faithful `Ord LNTerm` (FunSym-by-name, like `guarded::cmp_term`
// but for raw LNTerms); the derived `VTerm` Ord could flip a
// currently-matching pane, so it is not safe to apply blindly. Tracked as
// a residual gap.
// Section structure, numbering, term wrapping (`prettyNTerm` Docs) and
// the `Contradictory` header are byte-faithful.
fn pretty_subterm_store(sys: &System) -> Doc {
    let st = &sys.subterm_store;

    // `ppSt (a,b) = prettyNTerm a $$ nest 3 (opSubterm <-> prettyNTerm b)`
    let pp_st = |small: &tamarin_term::lterm::LNTerm, big: &tamarin_term::lterm::LNTerm| {
        lnterm_doc(small).above(
            crate::pretty_hpj::operator_("\u{228F}") // ⊏  (opSubterm)
                .beside_sp(lnterm_doc(big))
                .nest(3),
        )
    };

    let all_empty = st.neg_subterms.is_empty()
        && st.subterms.is_empty()
        && st.solved_subterms.is_empty();

    let mut sections: Vec<Doc> = Vec::new();
    if st.contradictory {
        sections.push(combine("Contradictory", Doc::text("yes")));
    }
    if !all_empty {
        let neg: Vec<Doc> = st
            .neg_subterms
            .iter()
            .map(|(a, b)| pp_st(a, b))
            .collect();
        sections.push(combine("Negative Subterms", numbered_prime(neg)));

        let pos: Vec<Doc> = st
            .subterms
            .iter()
            .map(|c| pp_st(&c.small, &c.big))
            .collect();
        sections.push(combine("Subterms", numbered_prime(pos)));

        let solved: Vec<Doc> = st
            .solved_subterms
            .iter()
            .map(|c| pp_st(&c.small, &c.big))
            .collect();
        sections.push(combine("Solved Subterms", numbered_prime(solved)));
    }

    // HS `vcat $ map combine [...]`.
    vcat_doc(sections)
}

// Faithful port of Haskell `prettyEqStore` (EquationStore.hs:876-896).
// Emits a leading `CONTRADICTORY` line when `eqsIsFalse`, then a `subst:`
// section (`prettySubst (text.show) (text.show)`, i.e. `t <~ {vars}`
// lines) and a `conj:` section whose disjuncts are `N.` followed by
// `numbered'` of `∃ vars. a = b ∧ ...`.
//
// Known divergence (UI-only diagnostic pane, not raw `--prove` output):
// the `prettySubst` grouping uses Rust's derived `Ord` on terms for the
// `equivClasses` map iteration order, which may differ from Haskell's
// `Ord (VTerm c v)` in edge cases.
fn pretty_eq_store(sys: &System) -> Doc {
    let eq = &sys.eq_store;
    let mut lines: Vec<Doc> = Vec::new();

    if eq.is_false() {
        lines.push(Doc::text("CONTRADICTORY"));
    } else {
        // HS prepends `emptyDoc`; vcat drops it.
        lines.push(Doc::empty());
    }

    // subst: vcat (prettySubst (text.show) (text.show) substFree)
    lines.push(combine("subst", vcat_doc(pretty_subst_free(&eq.subst))));

    // conj: vcat (map ppDisj disjs)
    let disjs: Vec<Doc> = eq.conj.iter().map(pp_disj).collect();
    lines.push(combine("conj", vcat_doc(disjs)));

    vcat_doc(lines)
}

// HS `ppDisj (idx, substs) = text (show idx ++ ".") <-> numbered' conjs`
// where `conjs = map ppSubst (S.toList substs)`.
fn pp_disj(d: &crate::tools::equation_store::EqDisj) -> Doc {
    let conjs: Vec<Doc> = d.substs.iter().map(pp_subst_vfresh).collect();
    Doc::text(format!("{}.", d.split_id.0)).beside_sp(numbered_prime(conjs))
}

// HS `ppSubst subst = sep [ hsep (opExists : map prettyLVar (varsRangeVFresh subst)) <> opDot
//                         , nest 2 $ fsep $ intersperse opLAnd $ map ppEq (substToListVFresh subst) ]`
fn pp_subst_vfresh(subst: &crate::tools::equation_store::LNSubstVFresh) -> Doc {
    use crate::pretty_hpj::{hsep, operator_, sep};
    // hsep (opExists : map prettyLVar vars) <> opDot
    // opExists = operator_ "∃ " (Pretty.hs:177-177) — trailing space, one operator
    // token; opDot = operator_ "." (Pretty.hs:183-183). Both `operator_`, so they
    // carry `hl_operator` spans in HtmlDoc mode and are identity in plain mode.
    let mut quant_parts: Vec<Doc> = vec![operator_("\u{2203} ")]; // opExists "∃ "
    for v in subst.vars_range() {
        quant_parts.push(Doc::text(lvar_to_string(&v)));
    }
    let quant = hsep(quant_parts).beside(operator_(".")); // opDot

    // fsep $ intersperse opLAnd $ map ppEq (substToListVFresh subst)
    // opLAnd = operator_ "∧" (Pretty.hs:179-179).
    let eqs: Vec<Doc> = subst
        .to_list()
        .into_iter()
        .map(|(v, t)| pp_eq(&v, &t))
        .collect();
    let body = fsep(intersperse(operator_("\u{2227}"), eqs)).nest(2); // opLAnd ∧

    sep(vec![quant, body])
}

// HS `ppEq (a,b) = prettyNTerm (lit (Var a)) $$ nest 6 (opEqual <-> prettyNTerm b)`
fn pp_eq(a: &tamarin_term::lterm::LVar, b: &tamarin_term::vterm::VTerm<tamarin_term::lterm::Name, tamarin_term::lterm::LVar>) -> Doc {
    Doc::text(lvar_to_string(a)).above(
        crate::pretty_hpj::operator_("=") // opEqual
            .beside_sp(lnterm_doc(b))
            .nest(6),
    )
}

// HS `prettySubst (text.show) (text.show) subst` (SubstVFree.hs:314-320):
//   map pp . M.toList . equivClasses . substToList
//   pp (t, vs) = prettyTerm t <-> " <~ {" <> fsep (punctuate comma (map ppVar vs)) <> "}"
// `equivClasses` groups vars by their mapped term; the map is keyed/ordered
// by the term, and each var-set is ordered by `Ord v`.
fn pretty_subst_free(subst: &crate::tools::equation_store::LNSubst) -> Vec<Doc> {
    use std::collections::BTreeMap;
    // Group by mapped term, preserving term Ord via BTreeMap; var-sets
    // sorted by LVar Ord.
    let mut groups: BTreeMap<
        tamarin_term::vterm::VTerm<tamarin_term::lterm::Name, tamarin_term::lterm::LVar>,
        std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    > = BTreeMap::new();
    for (v, t) in subst.to_list() {
        groups.entry(t).or_default().insert(v);
    }
    groups
        .into_iter()
        .map(|(t, vs)| {
            let vars: Vec<Doc> = vs.iter().map(|v| Doc::text(lvar_to_string(v))).collect();
            // prettyTerm ppLit t <-> " <~ {" <> fsep (punctuate comma vars) <> "}"
            // (SubstVFree.hs:342-348) — the term is a real `prettyTerm` Doc,
            // so an over-wide term wraps at the pane width exactly as HS.
            lnterm_doc(&t)
                .beside_sp(crate::pretty_hpj::operator_(" <~ {")) // operator_ " <~ {"
                .beside(fsep(punctuate(Doc::text(","), vars)))
                .beside(crate::pretty_hpj::operator_("}"))
        })
        .collect()
}

// HS `intersperse sep xs`.
fn intersperse(sep: Doc, xs: Vec<Doc>) -> Vec<Doc> {
    let mut out = Vec::with_capacity(xs.len().saturating_mul(2).saturating_sub(1));
    for (i, x) in xs.into_iter().enumerate() {
        if i > 0 {
            out.push(sep.clone());
        }
        out.push(x);
    }
    out
}

// HS `vcat ds`: fold with `$$` (above). Empty operands collapse, matching
// HughesPJ's `vcat = foldr (\p q -> Above p False q) empty`.
fn vcat_doc(ds: Vec<Doc>) -> Doc {
    crate::pretty_hpj::vcat(ds)
}

// ---------------------------------------------------------------------
// goals
// ---------------------------------------------------------------------

// Mirrors Haskell `prettyGoals` (System.hs:1735-1753):
//   (goal, status) <- M.toList sGoals          -- Goal-Ord iteration
//   guard (solved == gsSolved status)
//   prettyGoal goal <-> lineComment_
//       ("nr: " ++ show nr ++ sourceRule ++ loopBreaker ++ show useful)
// where `sourceRule = " (from rule "++getRuleName ru++")"` for the goal's
// node rule (goalRule), `loopBreaker` from `gsLoopBreaker`, and `useful`
// the KU-usefulness classification.  `show useful` wraps the annotation in
// literal double-quotes (HS `Show String`).  Goals are rendered through the
// SAME faithful `prettyGoal` Doc the `--prove` proof tree uses
// (`solve_goal_to_doc`), so fact spacing (`!KU( ~ltk )`) and LVar dots match.
fn pretty_goals(sys: &System, want_solved: bool) -> Doc {
    // `M.toList sGoals` yields Goal-Ord; RS stores goals in a Vec (creation
    // order), so sort by the solver's `goal_cmp` before rendering.
    let mut ordered: Vec<_> = sys.goals.iter()
        .filter(|(_, st)| st.solved == want_solved)
        .collect();
    ordered.sort_by(|a, b|
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    let mut items: Vec<Doc> = Vec::with_capacity(ordered.len());
    for (g, st) in ordered {
        // sourceRule = HS `goalRule sys goal` → `nodeRuleSafe (goalNodeId g)`.
        // `goalNodeId` is the node of a Premise/Action goal; other goals have
        // none (→ no sourceRule).
        let source_rule = match g {
            Goal::Action(i, _) | Goal::Premise((i, _), _) => sys
                .node_rule_safe(i)
                .map(|ru| format!(" (from rule {})", crate::rule::rule_name_string(ru)))
                .unwrap_or_default(),
            _ => String::new(),
        };
        let loop_breaker = if st.looping { " (loop breaker)" } else { "" };
        // `show useful` — HS wraps the annotation string in literal quotes.
        let useful = crate::constraint::solver::goals::goal_useful_annotation(
            g, st.looping, sys);
        // HS `prettyGoal goal <-> lineComment_ (...)` where `lineComment_ =
        // lineComment . text` and `lineComment d = comment $ text "//" <-> d`
        // (Pretty.hs:96-100).  The comment is PART of the goal's Doc, so its
        // width participates in the goal's own layout decisions (a goal near
        // the ribbon wraps because of its trailing comment, exactly as HS).
        let comment = format!(
            "nr: {}{}{}\"{}\"",
            st.nr, source_rule, loop_breaker, useful,
        );
        items.push(
            crate::pretty_theory::solve_goal_to_doc(g)
                .beside_sp(crate::pretty_hpj::line_comment_(&comment)),
        );
    }
    // HS `vsep = foldr ($--$)` — a BLANK line between adjacent goals.
    vsep_docs(items)
}

// ---------------------------------------------------------------------
// source kind
// ---------------------------------------------------------------------

fn pretty_source_kind(sk: Option<SourceKind>) -> String {
    // Matches Haskell `instance Show SourceKind` (System.hs:346-348):
    //   show RawSource     = "raw"
    //   show RefinedSource = "refined"
    // The Haskell field is non-optional; the `None` arm is a Rust-only
    // fallback for an unset source kind.
    match sk {
        None => "raw".to_string(),
        Some(SourceKind::RawSources) => "raw".to_string(),
        Some(SourceKind::RefinedSources) => "refined".to_string(),
    }
}

// ---------------------------------------------------------------------
// LNFact / RuleACInst rendering
// ---------------------------------------------------------------------

/// Pretty-print an `LNFact` exactly as Haskell `prettyLNFact` /
/// `prettyFact` (Fact.hs:537-552): `showFactTag tag` (with the persistent
/// `!` prefix), the term list in parentheses (always emitted, even for
/// zero-arity facts, matching `nestShort'`), and a trailing `[...]`
/// annotation block. Used by the proof pretty-printer here and by the
/// web DOT renderer (`tamarin-server`'s `dot::format_fact`).
pub fn pretty_fact(fa: &LNFact) -> String {
    use crate::fact::{fact_tag_multiplicity, FactAnnotation, Multiplicity};
    // Matches Haskell `showFactTag` (Fact.hs:519-523): the `!` prefix is
    // applied to any tag whose `factTagMultiplicity` is `Persistent`,
    // which includes KU/KD as well as persistent proto facts.
    let prefix = if fact_tag_multiplicity(&fa.tag) == Multiplicity::Persistent {
        "!"
    } else {
        ""
    };
    let name = fact_tag_name(&fa.tag);
    let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
    let base = format!("{}{}({})", prefix, name, args.join(", "));
    // Matches Haskell `ppAnn` (Fact.hs:543-545): when annotations are
    // present, append `[a1, a2]` using `showFactAnnotation` for each.
    if fa.annotations.is_empty() {
        base
    } else {
        let anns: Vec<&str> = fa
            .annotations
            .iter()
            .map(|a| match a {
                FactAnnotation::SolveFirst => "+",
                FactAnnotation::SolveLast => "-",
                FactAnnotation::NoSources => "no_precomp",
            })
            .collect();
        format!("{}[{}]", base, anns.join(", "))
    }
}

fn pretty_node_id(nid: &NodeId) -> String {
    let mut s = String::new();
    pp_lvar(nid, &mut s);
    s
}

fn lvar_to_string(v: &tamarin_term::lterm::LVar) -> String {
    let mut s = String::new();
    pp_lvar(v, &mut s);
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;

    #[test]
    fn empty_system_renders_each_section() {
        let s = System::default();
        let out = pretty_non_graph_system(&s);
        for h in &[
            "last:", "formulas:", "subterms:", "equations:", "lemmas:",
            "allowed cases:", "solved formulas:", "unsolved constraints:",
            "solved constraints:",
        ] {
            assert!(out.contains(h), "missing header {} in:\n{}", h, out);
        }
        assert!(out.contains("none"));
    }

    #[test]
    fn subterm_store_numbered_sections_and_contradictory_header() {
        use crate::tools::subterm_store::{SubtermConstraint, SubtermStore};
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::var_term;

        let v = |n: &str, s: LSort| var_term(LVar::new(n, s, 0));
        let st = SubtermStore {
            subterms: vec![SubtermConstraint {
                small: v("x", LSort::Msg),
                big: v("y", LSort::Msg),
                propagated: false,
            }],
            solved_subterms: vec![SubtermConstraint {
                small: v("a", LSort::Msg),
                big: v("b", LSort::Msg),
                propagated: false,
            }],
            contradictory: true,
            neg_subterms: crate::tools::subterm_store::SortedPairSet::rebuild_from(
                vec![(v("p", LSort::Msg), v("q", LSort::Msg))]),
            old_neg_subterms: crate::tools::subterm_store::SortedPairSet::default(),
        };
        let mut sys = System::empty();
        *sys.subterm_store_mut() = st;
        let out = pretty_subterm_store(&sys).render();
        // Contradictory header + all three numbered keyword sections.
        assert!(out.contains("Contradictory: yes"), "got:\n{out}");
        assert!(out.contains("Negative Subterms:"), "got:\n{out}");
        assert!(out.contains("Subterms:"), "got:\n{out}");
        assert!(out.contains("Solved Subterms:"), "got:\n{out}");
        // numbered' uses "1. " prefixes and the ⊏ operator.
        assert!(out.contains("1. "), "got:\n{out}");
        assert!(out.contains('\u{228F}'), "got:\n{out}");
    }

    #[test]
    fn eq_store_contradictory_and_sections() {
        use crate::tools::equation_store::{EqDisj, EquationStore, SplitId};

        let mut eq = EquationStore::empty();
        // An empty disjunction makes the store contradictory.
        eq.conj.push(EqDisj { split_id: SplitId(0), substs: vec![] });
        let mut sys = System::empty();
        sys.set_eq_store(std::sync::Arc::new(eq));
        let out = pretty_eq_store(&sys).render();
        assert!(out.contains("CONTRADICTORY"), "got:\n{out}");
        assert!(out.contains("subst:"), "got:\n{out}");
        assert!(out.contains("conj:"), "got:\n{out}");
        // The disjunction index is rendered with a trailing dot.
        assert!(out.contains("0."), "got:\n{out}");
    }

    // Minimized web-pane repro for task #20 (json shape): the UM_three_pass
    // `/main/cases/raw/0/0` subst term `<'UM3', $A.5, $B.5, (<'1',…>++…)>
    // <~ {t.1}` must wrap EXACTLY as HS's `prettyEqStore`→`prettySubst`→
    // `prettyTerm` Doc does inside the `equations:`/`subst:` nesting under
    // the web HtmlDoc width (100/67 with entity fill-widths).  Expected
    // bytes extracted verbatim from the cached HS response for
    // `examples/ake/dh/UM_three_pass.spthy` (`&nbsp;`→space, `<br/>`→\n,
    // entities decoded, hl-spans stripped).
    #[test]
    fn um3_subst_term_wraps_like_hs() {
        use tamarin_parser::ast as p;

        let var = |name: &str, idx: u64, sort: p::SortHint| {
            p::Term::Var(p::VarSpec {
                name: name.to_string(),
                idx,
                sort,
                typ: None,
            })
        };
        let pube = |s: &str| p::Term::PubLit(s.to_string());
        let app = |n: &str, args: Vec<p::Term>| p::Term::App(n.to_string(), args);
        let pair = p::Term::Pair;
        let exp = |l: p::Term, r: p::Term| {
            p::Term::BinOp(p::BinOp::Exp, Box::new(l), Box::new(r))
        };
        let a5 = || var("A", 5, p::SortHint::Pub);
        let b5 = || var("B", 5, p::SortHint::Pub);
        let y5 = || var("Y", 5, p::SortHint::Msg);
        let z5 = || var("z", 5, p::SortHint::Msg);
        let ex5 = || var("ex", 5, p::SortHint::Fresh);
        let g_ex5 = || exp(pube("g"), ex5());
        let g_eax5 = || {
            exp(
                pube("g"),
                p::Term::BinOp(
                    p::BinOp::Mult,
                    Box::new(var("ea", 5, p::SortHint::Fresh)),
                    Box::new(var("x", 5, p::SortHint::Fresh)),
                ),
            )
        };
        let h_arg = || pair(vec![z5(), g_eax5(), a5(), b5(), g_ex5(), y5()]);
        let mac = |snd: p::Term| {
            app("MAC", vec![app("first", vec![app("h", vec![h_arg()])]), snd])
        };
        let t1 = pair(vec![pube("1"), g_ex5()]);
        let t2 = pair(vec![
            pube("2"),
            y5(),
            mac(pair(vec![pube("I"), a5(), b5(), g_ex5(), y5()])),
        ]);
        let t3 = pair(vec![
            pube("3"),
            mac(pair(vec![pube("R"), b5(), a5(), y5(), g_ex5()])),
        ]);
        let union = p::Term::BinOp(
            p::BinOp::Union,
            Box::new(p::Term::BinOp(p::BinOp::Union, Box::new(t1), Box::new(t2))),
            Box::new(t3),
        );
        let term = pair(vec![pube("UM3"), a5(), b5(), union]);

        // Build under the entity-width guard (HS HtmlDoc measures escaped
        // widths at `text` time; RS captures fill widths at Doc build).
        let _g = crate::pretty_hpj::HtmlEntityWidthGuard::enable();
        // The `prettySubst` mapping line (SubstVFree.hs:342-348).
        let line = crate::pretty_formula::term_doc(&term)
            .beside_sp(Doc::text(" <~ {"))
            .beside(fsep(punctuate(Doc::text(","), vec![Doc::text("t.1")])))
            .beside(Doc::text("}"));
        // Pane context: `combine ("equations", vcat [combine ("subst", …)])`
        // — the mapping sits at nest 2+2 exactly as in `prettyEqStore`.
        let doc = combine(
            "equations",
            vcat_doc(vec![combine("subst", vcat_doc(vec![line]))]),
        );
        let out = doc.render_with(100, 67);
        let expected = "equations:\n  \
subst:\n    \
<'UM3', $A.5, $B.5, \n     \
(<'1', 'g'^~ex.5>++\n      \
<'2', Y.5, \n       \
MAC(first(h(<z.5, 'g'^(~ea.5*~x.5), $A.5, $B.5, \n                    \
'g'^~ex.5, Y.5>)),\n           \
<'I', $A.5, $B.5, 'g'^~ex.5, Y.5>)\n      \
>++\n      \
<'3', \n       \
MAC(first(h(<z.5, 'g'^(~ea.5*~x.5), $A.5, $B.5, \n                    \
'g'^~ex.5, Y.5>)),\n           \
<'R', $B.5, $A.5, Y.5, 'g'^~ex.5>)\n      \
>\n     \
)\n    \
>  <~ {t.1}";
        assert_eq!(out, expected, "got:\n{out}\nexpected:\n{expected}");
    }
}
