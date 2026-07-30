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
//! constant, returning the rewritten system plus the legend.
//!
//! # Representability of the shortened constant
//!
//! `shorten` (Utils.hs:70-84) builds `lit (Con (Name AbbrevName (NameId …)))`.
//! `AbbrevName` is the fifth `NameTag` constructor (LTerm.hs:218-219), and
//! `instance Show Name` (LTerm.hs:235-239) has NO case for it — so as soon as
//! one of these constants reaches the JSON serialiser (or `prettyLNTerm`,
//! which `computeAbbreviations` runs over every candidate term), upstream
//! aborts the request with `Non-exhaustive patterns in function show` and
//! Yesod answers 500.  There is therefore no upstream rendering to port.
//!
//! [`abbrev`] reproduces that observable behaviour: it reports
//! [`AbbrevNameUnshowable`] the moment `shorten` would build such a constant,
//! and the handler turns that into a 500.  When no candidate term is headed by
//! a `NoEq` symbol, `shorten` returns its argument unchanged (Utils.hs:86), so
//! every legend entry is an identity and `updateSystem` (Utils.hs:90-104) is a
//! no-op — hence the system is returned untouched.
//!
//! Known deviation: upstream only aborts once such a constant is actually
//! rendered, so a shortened term sitting on a node that the graph pipeline
//! drops (compression / simplification) would still yield a 200 there.  This
//! port reports the error as soon as the constant is built.

use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::LNTerm;
use tamarin_term::term::{Term, TermSize};

use tamarin_theory::constraint::system::System;

/// Reported when [`abbrev`] would build the `Con (Name AbbrevName …)` literal
/// that upstream cannot `show` (see the module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbbrevNameUnshowable;

/// HS `Web.Utils.abbrev`'s minimal term size, as passed by
/// `graphJsonThyPath` (`src/Web/Theory.hs:1329`).
pub const MIN_ABBREV_SIZE: usize = 30;

/// Port of `getTerms` (Utils.hs:39-40): every fact term of every rule's
/// conclusions followed by its premises, over `sNodes` in `NodeId` order.
fn get_terms(sys: &System) -> impl Iterator<Item = &LNTerm> {
    sys.nodes.iter().flat_map(|(_, ru)| {
        ru.conclusions
            .iter()
            .chain(ru.premises.iter())
            .flat_map(|f| f.terms.iter())
    })
}

/// Port of `shorten` (Utils.hs:70-86): a `NoEq` function application gets a
/// short constant (unrepresentable here — see the module docs), everything
/// else is returned unchanged.
fn shorten(t: &LNTerm) -> Result<&LNTerm, AbbrevNameUnshowable> {
    match t {
        Term::App(FunSym::NoEq(_), _) => Err(AbbrevNameUnshowable),
        _ => Ok(t),
    }
}

/// Port of `abbrev` (Utils.hs:107-114) composed with `computeLegend`
/// (Utils.hs:60-64) and `updateSystem` (Utils.hs:90-104).
///
/// `abbreviate == false` is HS's `abbrev False _ sys = return (sys, M.empty)`.
/// Otherwise every term of `size >= n` is run through [`shorten`]; since the
/// only shortenable shape is unrepresentable, a successful run leaves the
/// system unchanged and is returned as-is.
pub fn abbrev(abbreviate: bool, n: usize, sys: &System) -> Result<&System, AbbrevNameUnshowable> {
    if !abbreviate {
        return Ok(sys);
    }
    for t in get_terms(sys).filter(|t| t.size() >= n) {
        shorten(t)?;
    }
    Ok(sys)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_no_eq, lit};
    use tamarin_term::vterm::Lit;
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    use tamarin_theory::rule::{
        ProtoRuleACInstInfo, ProtoRuleName, Rule, RuleAttributes, RuleInfo,
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

    /// A system with a single rule whose conclusion carries `term`.
    fn system_with(term: LNTerm) -> System {
        let mut sys = System::default();
        let ru = Rule::new(
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
                    1,
                ),
                vec![term],
            )],
            Vec::new(),
        );
        sys.nodes_mut().push((LVar::new("i", LSort::Node, 1), ru));
        sys
    }

    // A small term never reaches the size threshold, so the system is returned
    // unchanged even with abbreviation requested.
    #[test]
    fn small_terms_are_left_alone() {
        let sys = system_with(f(var("x")));
        assert!(abbrev(true, MIN_ABBREV_SIZE, &sys).is_ok());
    }

    // A `NoEq`-headed term at or above the threshold is what upstream replaces
    // by an unshowable `AbbrevName` constant.
    #[test]
    fn large_noeq_term_is_unshowable() {
        let mut t = var("x");
        // `size` counts one per literal and one per application, so 29 nested
        // unary applications over one literal reach exactly 30.
        for _ in 0..29 {
            t = f(t);
        }
        assert_eq!(t.size(), MIN_ABBREV_SIZE);
        let sys = system_with(t);
        assert_eq!(
            abbrev(true, MIN_ABBREV_SIZE, &sys),
            Err(AbbrevNameUnshowable)
        );
        // Without the `abbrevInBackend` parameter nothing is inspected.
        assert!(abbrev(false, MIN_ABBREV_SIZE, &sys).is_ok());
    }
}
