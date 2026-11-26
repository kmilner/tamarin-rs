//! Queries that no specialised variant solver covers. Folding variant
//! narrowing proposes the family and the certificate checker accepts it.
//! Before the proposer existed these calls went to the checked variants
//! export and did not return.
use super::*;
use tamarin_term::algebra_provenance::{Command, Origin};
use tamarin_term::builtin::{emap, exp, fst, inv, mult, sdec, xor};
use tamarin_term::maude_sig::{bp_maude_sig, dh_maude_sig, sym_enc_maude_sig, xor_maude_sig};
use tamarin_term::subst::{apply_vterm, Subst};

/// The number of members is the one Maude 3.5.1 lists for the query in the
/// same module.
#[test]
fn folding_proposes_the_variants_no_specialised_solver_covers() {
    let [w, x, y, z] = ["w", "x", "y", "z"].map(variable);
    let dh = || pair_maude_sig().merge(dh_maude_sig());
    let cases = [
        ("fst(z^w)", dh(), fst(exp(z.clone(), w.clone())), 52),
        ("inv(y^w)", dh(), inv(exp(y.clone(), w.clone())), 60),
        (
            "inv(x XOR z)",
            dh().merge(xor_maude_sig()),
            inv(xor(x.clone(), z.clone())),
            19,
        ),
        (
            "fst(w*w*w)",
            pair_maude_sig().merge(bp_maude_sig()),
            fst(mult(w.clone(), mult(w.clone(), w.clone()))),
            4,
        ),
        (
            "sdec(x, y^z)",
            dh().merge(sym_enc_maude_sig()),
            sdec(x.clone(), exp(y.clone(), z.clone())),
            96,
        ),
        (
            "inv(em(y, z))",
            pair_maude_sig().merge(bp_maude_sig()),
            inv(emap(y.clone(), z.clone())),
            48,
        ),
        // A query that is not in normal form: x XOR x is zero.
        (
            "x*(x XOR x)",
            dh().merge(xor_maude_sig()),
            mult(x.clone(), xor(x.clone(), x.clone())),
            6,
        ),
    ];
    for (label, sig, query, members) in cases {
        let h = MaudeHandle::start_with_backend(MISSING, sig, AlgebraBackend::ProvedOnly).unwrap();
        let family = h.variants(&query).unwrap();
        assert_eq!(family.len(), members, "{label}");
        // Maude lists the variant of the normalized query first.
        assert!(
            family[0]
                .iter()
                .all(|(_, image)| matches!(image, Term::Lit(Lit::Var(_)))),
            "{label}: {:?}",
            family[0]
        );
        // Every member is a normal substitution, and no two members have the
        // same images.
        let mut seen = std::collections::BTreeSet::new();
        for member in &family {
            for (_, image) in member {
                assert_eq!(&h.reduce(image).unwrap(), image, "{label}");
            }
            let subst = Subst::from_list(member.iter().cloned());
            let images = [&w, &x, &y, &z].map(|v| apply_vterm(&subst, v.clone()));
            assert!(seen.insert(images), "{label}");
        }
        // One family, and it counts as proved: these tables are certified
        // and the checker accepted the proposal.
        let tally = h.provenance();
        assert_eq!(tally.total(Command::Variants), 1, "{label}");
        assert_eq!(tally.fresh(Command::Variants, Origin::Proved), 1, "{label}");
        assert_eq!(h.stats().var_count, 0, "{label}");
        h.check_backend_status().unwrap();
    }
}
