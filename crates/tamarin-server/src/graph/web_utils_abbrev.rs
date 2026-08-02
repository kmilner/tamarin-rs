// Currently GPL 3.0 until granted permission by the following authors:
//   arcz, meiersi, jdreier, cascremers, felixlinker, Divya19gupta,
//   rsasse, Kanakanajm, beschmi, addap, BTom-GH, PhilipLukertWork,
//   YannColomb, xaDxelA, Mathias-AURAND, symphorien, racoucho1u,
//   Esslingen-Security-Privacy, kevinmorio, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, src/Web/Handler.hs, src/Web/Theory.hs,
//   src/Web/Utils.hs

//! Port of `Web.Utils` (`src/Web/Utils.hs`) — the server-side term
//! abbreviation the JSON graph endpoint applies when the request carries the
//! `abbrevInBackend` query parameter (`src/Web/Handler.hs:1440`).
//!
//! `abbrev n sys` picks every term of the constraint system's rule premises
//! and conclusions whose `size` is at least `n` and replaces it with a short
//! constant, returning the rewritten system plus the legend.  The web handler
//! keeps only the system (`src/Web/Theory.hs:1330-1333`), so the legend is not
//! materialised here.
//!
//! The short constant is `lit (Con (Name AbbrevName (NameId …)))`
//! (Utils.hs:71-88), whose `NameId` is the head symbol's own name plus, from
//! the second abbreviation of that symbol on, an occurrence counter (`aenc`,
//! `aenc1`, `aenc2`, …).  It renders as that bare id: `show (Name AbbrevName
//! n) = show n` (LTerm.hs:240), and its sort is `LSortMsg` (LTerm.hs:266).

use std::borrow::Cow;

use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::{LNTerm, Name, NameTag};
use tamarin_term::term::{lit, Term, TermSize};
use tamarin_term::vterm::Lit;

use tamarin_utils::FastMap;

use tamarin_theory::constraint::system::System;

/// HS `Web.Utils.abbrev`'s minimal term size, as passed by
/// `graphJsonThyPath` (`src/Web/Theory.hs:1331`).
pub const MIN_ABBREV_SIZE: usize = 30;

/// Port of `getTerms` (Utils.hs:40-41): every fact term of every rule's
/// conclusions followed by its premises.
///
/// `get sNodes` is a `M.Map NodeId RuleACInst` (System.hs:383) and the outer
/// `concatMap` folds it through `Foldable`, i.e. over `M.elems` — ascending
/// `NodeId`, where `Ord LVar` compares idx, then sort, then name
/// (LTerm.hs:546-548).  `System::nodes` is a `Vec` in insertion order, so the
/// borrowed view is sorted first.
fn get_terms(sys: &System) -> impl Iterator<Item = &LNTerm> {
    let mut ordered: Vec<_> = sys.nodes.iter().collect();
    ordered.sort_by_key(|a| a.0);
    ordered.into_iter().flat_map(|(_, ru)| {
        ru.conclusions
            .iter()
            .chain(ru.premises.iter())
            .flat_map(|f| f.terms.iter())
    })
}

/// HS's `TermState` (Utils.hs:35): how many abbreviations each head symbol has
/// already produced.
type TermState = FastMap<String, usize>;

/// Port of `shorten` (Utils.hs:71-88): a `NoEq` function application becomes an
/// `AbbrevName` constant named after its head symbol, everything else is
/// returned unchanged.
///
/// The first abbreviation of a symbol is the bare name; the counter is only
/// appended once the symbol is already in the state map, so `f` is followed by
/// `f1`, `f2`, ….
fn shorten(t: &LNTerm, state: &mut TermState) -> LNTerm {
    let Term::App(FunSym::NoEq(sym), _) = t else {
        return t.clone();
    };
    // `BC.unpack bs` — the bare symbol name, not `show bs`.
    let sym_name = String::from_utf8_lossy(sym.name).into_owned();
    let name_id = match state.get(&sym_name) {
        Some(n) => format!("{}{}", sym_name, n),
        None => sym_name.clone(),
    };
    *state.entry(sym_name).or_insert(0) += 1;
    lit(Lit::Con(Name::new(NameTag::Abbrev, name_id)))
}

/// The `Legend` (Utils.hs:31) `computeLegend` builds: a `Map LNTerm LNTerm`
/// assembled by `M.fromList . zip terms`, so when the same term is abbreviated
/// more than once the LAST shortened form is the one that survives.
type Legend = FastMap<LNTerm, LNTerm>;

/// Port of `computeLegend` (Utils.hs:61-65).
fn compute_legend(n: usize, sys: &System) -> Legend {
    let mut state = TermState::default();
    let mut legend = Legend::default();
    for t in get_terms(sys).filter(|t| t.size() >= n) {
        let short = shorten(t, &mut state);
        legend.insert(t.clone(), short);
    }
    legend
}

/// Port of `updateSystem` (Utils.hs:92-106): rewrite the top-level terms of
/// every rule's premises and conclusions through the legend.  A rewritten fact
/// is rebuilt from `(tag, annotations, terms)`, i.e. without its cached
/// fingerprints — matching HS's `Fact tag a ts` and safe because this system
/// only ever reaches the renderer.  A fact holding no legend key would be
/// rebuilt into an equal fact, so it is left in place: the rewrite is
/// top-level-only, so the guard scans exactly the terms it would consult.
fn update_system(legend: &Legend, sys: &mut System) {
    for (_, ru) in sys.nodes_mut().iter_mut() {
        for facts in [&mut ru.premises, &mut ru.conclusions] {
            for f in facts.iter_mut() {
                if f.terms.iter().any(|t| legend.contains_key(t)) {
                    *f = f.map_ref(|t| legend.get(t).unwrap_or(t).clone());
                }
            }
        }
    }
}

/// Port of `abbrev` (Utils.hs:109-116).
///
/// `abbreviate == false` is HS's `abbrev False _ sys = return (sys, M.empty)`,
/// which hands the system back untouched.
pub fn abbrev(abbreviate: bool, n: usize, sys: &System) -> Cow<'_, System> {
    if !abbreviate {
        return Cow::Borrowed(sys);
    }
    let legend = compute_legend(n, sys);
    // An empty legend maps every term to itself, so `updateSystem` is the
    // identity and the system is handed back as-is.
    if legend.is_empty() {
        return Cow::Borrowed(sys);
    }
    let mut out = sys.clone();
    update_system(&legend, &mut out);
    Cow::Owned(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_ac, f_app_no_eq, lit};
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleACInst, RuleAttributes, RuleInfo,
    };

    fn var(name: &str) -> LNTerm {
        lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
    }

    fn f(arg: LNTerm) -> LNTerm {
        f_app_no_eq(
            NoEqSym::new(
                b"f".to_vec(),
                1,
                Privacy::Public,
                Constructability::Constructor,
            ),
            vec![arg],
        )
    }

    /// `f(f(… f(v) …))` with 29 applications: `size` counts one per literal
    /// and one per application, so this is exactly [`MIN_ABBREV_SIZE`].
    fn big(v: &str) -> LNTerm {
        let mut t = var(v);
        for _ in 0..29 {
            t = f(t);
        }
        assert_eq!(t.size(), MIN_ABBREV_SIZE);
        t
    }

    /// The constant `shorten` builds for a head symbol abbreviated as `id`.
    fn abbrev_const(id: &str) -> LNTerm {
        lit(Lit::Con(Name::new(NameTag::Abbrev, id)))
    }

    /// A rule with no premises whose single conclusion carries `terms`.
    fn rule_with(terms: Vec<LNTerm>) -> RuleACInst {
        Rule::new(
            RuleInfo::<_, tamarin_theory::rule::IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(tamarin_term::intern::intern_str("R")),
                attributes: RuleAttributes::default(),
                loop_breakers: Vec::new(),
            }),
            Vec::new(),
            vec![Fact::new(
                FactTag::Proto(
                    Multiplicity::Linear,
                    tamarin_term::intern::intern_str("A"),
                    terms.len(),
                ),
                terms,
            )],
            Vec::new(),
        )
    }

    /// A system with a single rule whose one conclusion carries `terms`.
    fn system_with(terms: Vec<LNTerm>) -> System {
        let mut sys = System::default();
        sys.nodes_mut()
            .push((LVar::new("i", LSort::Node, 1), rule_with(terms)));
        sys
    }

    fn conclusion_terms(sys: &System) -> Vec<LNTerm> {
        sys.nodes[0].1.conclusions[0].terms.to_vec()
    }

    /// The conclusion terms of the node stored under `#i.idx`.
    fn node_conclusion_terms(sys: &System, idx: u64) -> Vec<LNTerm> {
        let (_, ru) = sys
            .nodes
            .iter()
            .find(|(id, _)| id.idx == idx)
            .expect("node present");
        ru.conclusions[0].terms.to_vec()
    }

    // A small term never reaches the size threshold, so the system comes back
    // unchanged even with abbreviation requested.
    #[test]
    fn small_terms_are_left_alone() {
        let sys = system_with(vec![f(var("x"))]);
        let out = abbrev(true, MIN_ABBREV_SIZE, &sys);
        assert_eq!(conclusion_terms(&out), conclusion_terms(&sys));
    }

    // A `NoEq`-headed term at or above the threshold is replaced by a constant
    // named after its head symbol, which renders as that bare name.
    #[test]
    fn large_noeq_term_becomes_an_abbrev_constant() {
        let sys = system_with(vec![big("x")]);
        let out = abbrev(true, MIN_ABBREV_SIZE, &sys);
        assert_eq!(conclusion_terms(&out), vec![abbrev_const("f")]);
        assert_eq!(
            Lit::<Name, LVar>::Con(Name::new(NameTag::Abbrev, "f")).to_string(),
            "f"
        );
        // Without the `abbrevInBackend` parameter nothing is rewritten.
        let plain = abbrev(false, MIN_ABBREV_SIZE, &sys);
        assert_eq!(conclusion_terms(&plain), conclusion_terms(&sys));
    }

    // The per-symbol counter is appended from the SECOND abbreviation of that
    // symbol on, so two distinct `f`-headed terms become `f` and `f1`.
    #[test]
    fn repeated_head_symbol_gets_a_counter_suffix() {
        let sys = system_with(vec![big("x"), big("y")]);
        let out = abbrev(true, MIN_ABBREV_SIZE, &sys);
        assert_eq!(
            conclusion_terms(&out),
            vec![abbrev_const("f"), abbrev_const("f1")]
        );
    }

    // The legend is `M.fromList . zip terms`, so a term occurring twice burns
    // two counter values and keeps the LAST one for BOTH occurrences.
    #[test]
    fn a_repeated_term_takes_its_last_abbreviation() {
        let sys = system_with(vec![big("x"), big("x")]);
        let out = abbrev(true, MIN_ABBREV_SIZE, &sys);
        assert_eq!(
            conclusion_terms(&out),
            vec![abbrev_const("f1"), abbrev_const("f1")]
        );
    }

    // `getTerms` folds `sNodes`, a `Map NodeId RuleACInst`, so it visits nodes
    // in ascending `NodeId` order however they were stored.  The per-symbol
    // counter runs across nodes, so the LOWEST id takes the bare `f` even when
    // it was added last.  `System::nodes` itself keeps insertion order —
    // `Reduction::set_nodes` relies on it to pick the surviving rule at an id
    // collision — so only the abbreviation's view is sorted.
    #[test]
    fn abbreviation_counter_follows_node_id_order_not_insertion_order() {
        let mut sys = System::default();
        sys.add_node(LVar::new("i", LSort::Node, 2), rule_with(vec![big("x")]));
        sys.add_node(LVar::new("i", LSort::Node, 1), rule_with(vec![big("y")]));
        assert_eq!(sys.nodes[0].0.idx, 2);
        let out = abbrev(true, MIN_ABBREV_SIZE, &sys);
        assert_eq!(node_conclusion_terms(&out, 1), vec![abbrev_const("f")]);
        assert_eq!(node_conclusion_terms(&out, 2), vec![abbrev_const("f1")]);
        assert_eq!(out.nodes[0].0.idx, 2);
    }

    // `shorten` only rewrites `NoEq` applications; a large AC-headed term
    // falls through its catch-all unchanged.
    #[test]
    fn large_ac_term_is_left_alone() {
        let t = f_app_ac(
            tamarin_term::function_symbols::AcSym::Xor,
            (0..30).map(|i| var(&format!("x{i}"))).collect(),
        );
        assert!(t.size() >= MIN_ABBREV_SIZE);
        let sys = system_with(vec![t]);
        let out = abbrev(true, MIN_ABBREV_SIZE, &sys);
        assert_eq!(conclusion_terms(&out), conclusion_terms(&sys));
    }
}
