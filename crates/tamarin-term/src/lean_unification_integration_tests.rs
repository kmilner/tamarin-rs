//! Differential coverage of the proved proved-only dispatch against a Maude oracle.

use crate::algebra_backend::AlgebraBackend;
use crate::algebra_provenance::{Command, Origin};
use crate::function_symbols::{AcSym, FunSym};
use crate::lterm::{pub_term, LNTerm, LSort, LVar};
use crate::maude_proc::MaudeHandle;
use crate::maude_sig::{mset_maude_sig, MaudeSig};
use crate::rewriting::Equal;
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use std::sync::atomic::Ordering;
use tamarin_test_support::require_maude_path;

fn native_session(sig: MaudeSig) -> MaudeHandle {
    MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::ProvedOnly).unwrap()
}

// The proved-only multiset session under test and its Maude oracle.
fn handles() -> Option<(MaudeHandle, MaudeHandle)> {
    let path = require_maude_path()?;
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    Some((native_session(mset_maude_sig()), oracle))
}

fn sum(atoms: &[usize]) -> LNTerm {
    f_app_ac(
        AcSym::Union,
        atoms
            .iter()
            .map(|atom| pub_term(format!("a{atom}")))
            .collect(),
    )
}

// Submit the unfactored equations directly to Maude, including cases where both
// normal dispatchers would otherwise return before sending a command.
#[test]
fn checked_factor_clashes_match_unfactored_maude_queries() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::maude_sig::hash_maude_sig;
    use crate::subst::Subst;
    use crate::term::f_app_no_eq;

    let Some(path) = require_maude_path() else {
        return;
    };
    let g = NoEqSym::new(b"g", 1, Privacy::Public, Constructability::Constructor);
    let mut sig = hash_maude_sig();
    sig.st_fun_syms.insert(g);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let table = native.native_rules().unwrap();
    let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let x = var("x");
    let y = var("y");
    let h_y = hash(y.clone());
    let g_y = f_app_no_eq(g, vec![y.clone()]);
    let clash = vec![eq(x.clone(), h_y.clone()), eq(x.clone(), g_y.clone())];
    let possible = vec![
        eq(x.clone(), h_y.clone()),
        eq(x.clone(), hash(pub_term("a"))),
    ];
    assert!(crate::unification::unify_lnterm_factored(clash.clone()).is_none());
    assert!(table.refutes_factor_clash(&clash).unwrap());
    assert!(!table.refutes_factor_clash(&possible).unwrap());
    assert_eq!(
        canonical_variants(native.unify(&possible).unwrap()),
        canonical_variants(
            oracle
                .unify_residuals_with_maude(&possible, &Subst::empty())
                .unwrap()
        )
    );
    assert!(native.unify(&clash).unwrap().is_empty());
    assert!(!native.unifiable(&clash).unwrap());
    assert!(oracle
        .unify_residuals_with_maude(&clash, &Subst::empty())
        .unwrap()
        .is_empty());
    assert_eq!(oracle.stats().unify_count, 2);
    assert_eq!(native.stats().unify_count, 0);

    let sig = sig.merge(mset_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let ac = |terms| f_app_ac(AcSym::Union, terms);
    let a = var("a");
    let b = var("b");
    // Together these rows force h(y) = g(y); the free factorer alone delays both.
    let rows = [
        eq(
            ac(vec![h_y.clone(), a.clone()]),
            ac(vec![g_y.clone(), b.clone()]),
        ),
        eq(ac(vec![h_y, a.clone(), a]), ac(vec![g_y, b.clone(), b])),
    ];
    assert_eq!(
        crate::unification::unify_lnterm_factored(rows.to_vec())
            .unwrap()
            .1
            .len(),
        2
    );
    assert!(native.unify(&rows).unwrap().is_empty());
    assert!(!native.unifiable(&rows).unwrap());
    assert!(oracle
        .unify_residuals_with_maude(&rows, &Subst::empty())
        .unwrap()
        .is_empty());
    assert_eq!(oracle.stats().unify_count, 1);
}

#[test]
fn successful_factor_preserves_the_original_family() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;
    use crate::subst::Subst;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = hash_maude_sig().merge(mset_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let table = native.native_rules().unwrap();
    let var = |name| LVar::new(name, LSort::Msg, 0);
    let term = |v| Term::Lit(Lit::Var(v));
    let (x, y, z) = (var("x"), var("y"), var("z"));
    let alias = Equal::new(hash(term(x)), hash(term(y)));
    let original = [alias.clone()];
    let a = pub_term("a");
    let b = pub_term("b");
    let alias_factor = Subst::from_list(vec![(x, term(y))]);
    assert!(table.accepts_factor(&original, &alias_factor, &[]).unwrap());
    // Both sides become h(a). This is a unifier but it cannot represent x=y=b.
    let specific = Subst::from_list(vec![(x, a.clone()), (y, a.clone())]);
    assert!(!table.accepts_factor(&original, &specific, &[]).unwrap());
    let compare = |eqs: &[Equal<LNTerm>]| {
        [
            native.unify(eqs).unwrap(),
            oracle
                .unify_residuals_with_maude(eqs, &Subst::empty())
                .unwrap(),
        ]
    };
    // A complete family can also contain narrower, redundant solutions.
    // Every arm must identify x and y, and one shared Msg witness covers all.
    for family in compare(&original) {
        let mut general = false;
        for arm in family {
            let bindings = crate::subst_vfresh::LNSubstVFresh::from_list(arm);
            let image = bindings.image_of(&x).expect("shared alias");
            assert_eq!(bindings.image_of(&y), Some(image));
            general |= matches!(image, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg);
        }
        assert!(
            general,
            "family fixed or narrowed the shared image of x and y"
        );
    }
    let unrelated = [Equal::new(term(z), term(z))];
    assert!(!table
        .accepts_factor(&original, &alias_factor, &unrelated)
        .unwrap());

    // The factor x=y is justified, but a residual fixing y=a loses the second partition.
    let ac = |l, r| f_app_ac(AcSym::Union, vec![l, r]);
    let rows = [
        alias,
        Equal::new(ac(term(x), term(z)), ac(a.clone(), b.clone())),
    ];
    let valid = [Equal::new(ac(term(y), term(z)), ac(a.clone(), b.clone()))];
    assert!(table.accepts_factor(&rows, &alias_factor, &valid).unwrap());
    let partial = [
        Equal::new(term(y), a.clone()),
        Equal::new(term(z), b.clone()),
    ];
    let expected = canonical_ground_answers(vec![
        vec![(x, a.clone()), (y, a.clone()), (z, b.clone())],
        vec![(x, b.clone()), (y, b), (z, a)],
    ]);
    assert!(!table
        .accepts_factor(&rows, &alias_factor, &partial)
        .unwrap());
    for family in compare(&rows) {
        assert_eq!(canonical_ground_answers(family), expected);
    }
    assert_eq!(oracle.stats().unify_count, 2);
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn packed_unification_uses_one_substitution_across_nested_coordinates() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::maude_sig::MaudeSig;
    use crate::subst::Subst;
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = MaudeSig::default();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 0);
    let i = LVar::new("i", LSort::Node, 0);
    let v = |var| Term::Lit(Lit::Var(var));
    let packed = |t| f_app_list(vec![f_app_list(vec![]), t, v(i)]);
    let lhs = f_app_list(vec![v(x), packed(v(x))]);
    for (second, possible) in [(pub_term("a"), true), (pub_term("b"), false)] {
        let rhs = f_app_list(vec![pub_term("a"), packed(second)]);
        let eqs = [Equal::new(lhs.clone(), rhs)];
        let raw = oracle
            .unify_residuals_with_maude(&eqs, &Subst::empty())
            .unwrap();
        let expected = if possible {
            vec![vec![(x, pub_term("a"))]]
        } else {
            vec![]
        };
        assert_eq!(canonical_variants(raw), expected);
        assert_eq!(canonical_variants(native.unify(&eqs).unwrap()), expected);
        assert_eq!(native.unifiable(&eqs).unwrap(), possible);
    }
    assert_eq!(oracle.stats().unify_count, 2);
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn packed_shape_clashes_preserve_the_full_query_for_both_operations() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::lean_unification::{match_modulo_attributes, unify_modulo_attributes, Outcome};
    use crate::maude_proc::MaudeError;
    use crate::maude_sig::pair_maude_sig;
    use crate::term::f_app_list as pack;

    let sig = pair_maude_sig();
    let native = |reference| {
        let mut h = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::ProvedOnly,
        )
        .unwrap();
        h.set_reference(reference);
        h
    };
    let x = LVar::new("x", LSort::Msg, 0);
    let vx = Term::Lit(Lit::Var(x));
    let a = pub_term("a");
    let empty = pack(vec![]);
    for eq in [
        Equal::new(pack(vec![vx.clone(), a.clone()]), pack(vec![a.clone()])),
        Equal::new(
            pack(vec![empty.clone(), vx.clone()]),
            pack(vec![a.clone(), empty.clone()]),
        ),
        Equal::new(empty.clone(), vx.clone()),
        Equal::new(vx.clone(), empty.clone()),
    ] {
        let eqs = [eq];
        assert_eq!(
            unify_modulo_attributes(&sig, &eqs).unwrap(),
            Outcome::Complete(vec![])
        );
        assert_eq!(
            match_modulo_attributes(&sig, &eqs, |_| true).unwrap(),
            Outcome::Complete(vec![])
        );
        for reference in [false, true] {
            let h = native(reference);
            assert!(h.unify(&eqs).unwrap().is_empty());
            assert!(!h.unifiable(&eqs).unwrap());
            assert!(h.match_eqs(&eqs).unwrap().is_empty());
            assert!(!h.has_match_eqs(&eqs).unwrap());
            assert!(h
                .match_eqs_skolemize_both(&eqs, &[(x.name, x.idx)].into_iter().collect())
                .unwrap()
                .is_empty());
            h.check_backend_status().unwrap();
        }
    }
    let malformed = crate::builtin::hash(a.clone()); // Undeclared in the pairing module.
    for rows in [
        vec![Equal::new(empty.clone(), pack(vec![malformed.clone()]))],
        vec![
            Equal::new(empty, vx.clone()),
            Equal::new(malformed.clone(), malformed),
        ],
    ] {
        assert_eq!(
            unify_modulo_attributes(&sig, &rows).unwrap(),
            Outcome::Unsupported
        );
        assert_eq!(
            match_modulo_attributes(&sig, &rows, |_| true).unwrap(),
            Outcome::Unsupported
        );
        for reference in [false, true] {
            let h = native(reference);
            assert!(matches!(
                h.unify(&rows),
                Err(MaudeError::UnsupportedOperation(_))
            ));
            assert!(h.check_backend_status().is_err());
            let h = native(reference);
            assert!(matches!(
                h.match_eqs(&rows),
                Err(MaudeError::UnsupportedOperation(_))
            ));
            assert!(h.check_backend_status().is_err());
        }
    }
    // Even when there are no algebraic coordinates, equal empty packs have an identity answer.
    let empty_eq = [Equal::new(pack(vec![]), pack(vec![]))];
    assert_eq!(
        unify_modulo_attributes(&sig, &empty_eq).unwrap(),
        Outcome::Complete(vec![vec![]])
    );
    assert_eq!(
        match_modulo_attributes(&sig, &empty_eq, |_| true).unwrap(),
        Outcome::Complete(vec![vec![]])
    );
}

fn canonical_ground_answers(mut answers: Vec<Vec<(LVar, LNTerm)>>) -> Vec<Vec<(LVar, LNTerm)>> {
    for answer in &mut answers {
        answer.sort();
    }
    answers.sort();
    answers.dedup();
    answers
}

fn canonical_variants(
    arms: crate::lean_unification::Substitutions,
) -> crate::lean_unification::Substitutions {
    let mut result: Vec<_> = arms
        .into_iter()
        .map(|arm| {
            crate::subst_vfresh::LSubstVFresh::from_list(arm)
                .remove_renamings()
                .drop_name_hints()
                .to_list()
        })
        .collect();
    result.sort();
    result
}

// In an AC image, changing witness names can change their traversal order.
// An alpha-renaming preserves each witness's sort and its multiset of
// ordered-context positions. Try every bijection inside those classes.
fn canonical_small_ac_answers(
    arms: crate::lean_unification::Substitutions,
) -> crate::lean_unification::Substitutions {
    use crate::lterm::HasFrees;
    use crate::subst_vfresh::LNSubstVFresh;
    type Arm = Vec<(LVar, LNTerm)>;
    fn positions(
        t: &LNTerm,
        path: &mut Vec<usize>,
        classes: &mut std::collections::BTreeMap<LVar, Vec<Vec<usize>>>,
    ) {
        match t {
            Term::Lit(Lit::Var(v)) => classes.entry(*v).or_default().push(path.clone()),
            Term::Lit(_) => {}
            Term::App(f, args) => {
                for (i, arg) in args.iter().enumerate() {
                    path.push(if matches!(f, FunSym::Ac(_) | FunSym::C(_)) {
                        0
                    } else {
                        i + 1
                    });
                    positions(arg, path, classes);
                    path.pop();
                }
            }
        }
    }
    fn visit(arm: &Arm, names: &mut [LVar], ends: &[usize], pos: usize, best: &mut Option<Arm>) {
        if pos == names.len() {
            let renamed = arm
                .iter()
                .map(|(key, image)| {
                    (
                        *key,
                        image.clone().map_free(&mut |v| {
                            let i = names.iter().position(|w| *w == v).unwrap();
                            LVar::new("", v.sort, i as u64)
                        }),
                    )
                })
                .collect();
            if best.as_ref().is_none_or(|current| renamed < *current) {
                *best = Some(renamed);
            }
            return;
        }
        for i in pos..ends[pos] {
            names.swap(pos, i);
            visit(arm, names, ends, pos + 1, best);
            names.swap(pos, i);
        }
    }

    let mut answers = Vec::new();
    for arm in arms {
        let arm = LNSubstVFresh::from_list(arm).remove_renamings().to_list();
        let mut classes = std::collections::BTreeMap::new();
        for (i, (_, t)) in arm.iter().enumerate() {
            positions(t, &mut vec![i], &mut classes);
        }
        let mut groups = std::collections::BTreeMap::new();
        for (v, mut paths) in classes {
            paths.sort_unstable();
            groups
                .entry((v.sort, paths))
                .or_insert_with(Vec::new)
                .push(v);
        }
        let mut names = Vec::new();
        let mut ends = Vec::new();
        for group in groups.into_values() {
            names.extend(group);
            ends.resize(names.len(), names.len());
        }
        let mut best = None;
        visit(&arm, &mut names, &ends, 0, &mut best);
        answers.push(best.unwrap());
    }
    answers.sort();
    answers
}

// Each arm as the images of all query variables in one term, after checking
// that it unifies the equations. The proved export may leave a query variable
// in its range where Maude prints a witness; both give the same row.
fn unifier_rows(
    eqs: &[Equal<LNTerm>],
    arms: crate::lean_unification::Substitutions,
) -> crate::lean_unification::Substitutions {
    use crate::subst::{apply_vterm, Subst};
    let mut vars = Vec::new();
    for eq in eqs {
        vars.extend(crate::lterm::frees_list(&eq.lhs));
        vars.extend(crate::lterm::frees_list(&eq.rhs));
    }
    vars.sort();
    vars.dedup();
    let inputs =
        crate::term::f_app_list(vars.into_iter().map(|v| Term::Lit(Lit::Var(v))).collect());
    let rows = arms
        .into_iter()
        .map(|arm| {
            let subst = Subst::from_list(arm);
            for eq in eqs {
                assert_eq!(
                    apply_vterm(&subst, eq.lhs.clone()),
                    apply_vterm(&subst, eq.rhs.clone()),
                    "{subst:?} does not unify {eq:?}"
                );
            }
            vec![(
                LVar::new("row", LSort::Msg, 0),
                apply_vterm(&subst, inputs.clone()),
            )]
        })
        .collect();
    canonical_small_ac_answers(rows)
}

// A complete family need not be minimal: the proved export can keep an arm
// that is a free instance of another one where Maude lists only the general
// arm, and the other way round. Drops such arms.
fn minimal_rows(
    rows: crate::lean_unification::Substitutions,
) -> crate::lean_unification::Substitutions {
    let instance = |arm: &LNTerm, general: &LNTerm| {
        let (Term::App(_, arm), Term::App(_, general)) = (arm, general) else {
            panic!("a row is a tuple")
        };
        let pairs = arm.iter().cloned().zip(general.iter().cloned()).collect();
        crate::unification::solve_match_lterm_no_ac(
            &crate::maude_types::sort_of_name,
            crate::rewriting::Match::DelayedMatches(pairs),
        )
        .is_some()
    };
    let mut kept = Vec::new();
    'rows: for (i, row) in rows.iter().enumerate() {
        for (j, other) in rows.iter().enumerate() {
            // Of two rows that are instances of each other the first stays.
            if i != j
                && instance(&row[0].1, &other[0].1)
                && (j < i || !instance(&other[0].1, &row[0].1))
            {
                continue 'rows;
            }
        }
        kept.push(row.clone());
    }
    kept
}

// Proved-only and Maude return the same unifiers once the instances of other
// arms are dropped. Returns the number of the remaining ones.
fn assert_same_minimal_unifiers(
    native: &MaudeHandle,
    oracle: &MaudeHandle,
    eqs: &[Equal<LNTerm>],
) -> usize {
    let actual = minimal_rows(unifier_rows(eqs, native.unify(eqs).unwrap()));
    let expected = minimal_rows(unifier_rows(eqs, oracle.unify(eqs).unwrap()));
    assert_eq!(actual, expected, "{eqs:?}");
    actual.len()
}

// Proved-only and Maude return the same unifiers up to witness names and arm
// order. Returns their number.
fn assert_same_unifiers(
    native: &MaudeHandle,
    oracle: &MaudeHandle,
    eqs: &[Equal<LNTerm>],
) -> usize {
    let actual = unifier_rows(eqs, native.unify(eqs).unwrap());
    assert_eq!(
        actual,
        unifier_rows(eqs, oracle.unify(eqs).unwrap()),
        "{eqs:?}"
    );
    actual.len()
}

fn multisets(length: usize, minimum: usize) -> Vec<Vec<usize>> {
    if length == 0 {
        return vec![vec![]];
    }
    (minimum..3)
        .flat_map(|head| {
            multisets(length - 1, head)
                .into_iter()
                .map(move |mut tail| {
                    tail.insert(0, head);
                    tail
                })
        })
        .collect()
}

#[test]
fn lean_one_variable_matches_maude_for_small_multisets_in_both_orientations() {
    let Some((lean, oracle)) = handles() else {
        return;
    };
    let x = LVar::new("x", LSort::Msg, 7);
    let tails: Vec<_> = (1..=2).flat_map(|length| multisets(length, 0)).collect();
    let right_sides: Vec<_> = (2..=4).flat_map(|length| multisets(length, 0)).collect();
    let mut queries = 0;
    for tail in &tails {
        for rhs in &right_sides {
            let mut terms = vec![Term::Lit(Lit::Var(x))];
            terms.extend(tail.iter().map(|atom| pub_term(format!("a{atom}"))));
            let pattern = f_app_ac(AcSym::Union, terms);
            let ground = sum(rhs);
            for (lhs, rhs) in [
                (pattern.clone(), ground.clone()),
                (ground.clone(), pattern.clone()),
            ] {
                let eqs = [Equal { lhs, rhs }];
                assert_eq!(
                    canonical_ground_answers(lean.unify(&eqs).unwrap()),
                    canonical_ground_answers(oracle.unify(&eqs).unwrap()),
                    "tail {tail:?}, ground {ground:?}"
                );
                queries += 1;
            }
        }
    }
    // Requests that differ only in the names of their atoms are one request
    // to the export, whose reply is kept and decoded again.
    let provenance = lean.provenance();
    assert_eq!(
        provenance.fresh(Command::Unify, Origin::Proved)
            + provenance.cached(Command::Unify, Origin::Proved),
        queries
    );
    assert!(provenance.fresh(Command::Unify, Origin::Proved) > 0);
    assert_eq!(lean.stats().unify_count, 0);
}

#[test]
fn lean_ground_dispatch_matches_maude_exhaustively_for_small_multisets() {
    let Some((lean, oracle)) = handles() else {
        return;
    };
    let multisets: Vec<_> = (0..3)
        .flat_map(|a| (a..3).flat_map(move |b| (b..3).map(move |c| [a, b, c])))
        .collect();
    let mut queries = 0;
    for lhs in &multisets {
        for rhs in &multisets {
            let eqs = [Equal {
                lhs: sum(lhs),
                rhs: sum(rhs),
            }];
            assert_eq!(lean.unify(&eqs).unwrap(), oracle.unify(&eqs).unwrap());
            queries += 1;
        }
    }
    // Requests that differ only in the names of their atoms are one request
    // to the export, whose reply is kept and decoded again.
    let provenance = lean.provenance();
    assert_eq!(
        provenance.fresh(Command::Unify, Origin::Proved)
            + provenance.cached(Command::Unify, Origin::Proved),
        queries
    );
    assert!(provenance.fresh(Command::Unify, Origin::Proved) > 0);
    assert_eq!(lean.stats().unify_count, 0);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn ground_identity_row_keeps_the_binding_of_the_free_row() {
    let Some((lean, oracle)) = handles() else {
        return;
    };
    let x = LVar::new("free", LSort::Msg, 4);
    let eqs = [
        Equal {
            lhs: Term::Lit(Lit::Var(x)),
            rhs: pub_term("bound"),
        },
        Equal {
            lhs: sum(&[0, 1, 1]),
            rhs: sum(&[1, 0, 1]),
        },
    ];
    let actual = lean.unify(&eqs).unwrap();
    assert_eq!(actual, oracle.unify(&eqs).unwrap());
    assert_eq!(actual, vec![vec![(x, pub_term("bound"))]]);
    assert_eq!(lean.provenance().fresh(Command::Unify, Origin::Proved), 1);
}

#[test]
fn ground_equality_does_not_apply_xor_cancellation_equations() {
    let Some(path) = require_maude_path() else {
        return;
    };
    let lean = native_session(crate::maude_sig::xor_maude_sig());
    let oracle = MaudeHandle::start_with_backend(
        &path,
        crate::maude_sig::xor_maude_sig(),
        AlgebraBackend::Maude,
    )
    .unwrap();
    let a = pub_term("a");
    let b = pub_term("b");
    let eqs = [Equal {
        lhs: f_app_ac(AcSym::Xor, vec![a.clone(), a]),
        rhs: f_app_ac(AcSym::Xor, vec![b.clone(), b]),
    }];
    assert_eq!(lean.unify(&eqs).unwrap(), Vec::<Vec<_>>::new());
    assert_eq!(lean.unify(&eqs).unwrap(), oracle.unify(&eqs).unwrap());
    // The repeat is a hit in the session memo.
    let provenance = lean.provenance();
    assert_eq!(provenance.fresh(Command::Unify, Origin::Proved), 1);
    assert_eq!(provenance.cached(Command::Unify, Origin::Proved), 1);
    assert!(matches!(eqs[0].lhs, Term::App(FunSym::Ac(AcSym::Xor), _)));
}

#[test]
fn undeclared_symbols_and_natural_literals_are_errors_on_both_backends() {
    use crate::maude_proc::MaudeError;
    let Some(path) = require_maude_path() else {
        return;
    };
    let n = Term::Lit(Lit::Con(crate::lterm::Name::new(
        crate::lterm::NameTag::Nat,
        "n",
    )));
    let term = f_app_ac(AcSym::Union, vec![n, pub_term("a")]);
    for (sig, term) in [
        (crate::maude_sig::pair_maude_sig(), sum(&[0, 1])),
        (mset_maude_sig(), term),
    ] {
        let undeclared = [Equal {
            lhs: term.clone(),
            rhs: term,
        }];
        let oracle =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        assert!(oracle.unify(&undeclared).is_err());
        // The unsupported request latches the native session.
        let native = native_session(sig);
        assert!(matches!(
            native.unify(&undeclared),
            Err(MaudeError::UnsupportedOperation(_))
        ));
        assert!(native.check_backend_status().is_err());
        assert_eq!(native.provenance().total(Command::Unify), 0);
    }
}

#[test]
fn cached_ground_bindings_keep_full_variable_identity() {
    let Some((lean, oracle)) = handles() else {
        return;
    };
    let x = LVar::new("x", LSort::Msg, 7);
    let y = LVar::new("other-name", LSort::Msg, 7);
    let free = LVar::new("free", LSort::Msg, 2);
    for variable in [x, y, x] {
        for value in ["first", "second"] {
            let eqs = [
                Equal {
                    lhs: Term::Lit(Lit::Var(free)),
                    rhs: pub_term(value),
                },
                Equal {
                    lhs: f_app_ac(
                        AcSym::Union,
                        vec![Term::Lit(Lit::Var(variable)), pub_term("a0")],
                    ),
                    rhs: sum(&[0, 1, 1]),
                },
            ];
            let result = lean.unify(&eqs).unwrap();
            assert_eq!(
                canonical_ground_answers(result.clone()),
                canonical_ground_answers(oracle.unify(&eqs).unwrap())
            );
            assert!(result[0].contains(&(free, pub_term(value))));
            assert!(result[0].contains(&(variable, sum(&[1, 1]))));
        }
    }
    // The second pass over x repeats two requests of the first, and requests
    // that differ only in the name of the constant share one stored reply.
    let provenance = lean.provenance();
    let fresh = provenance.fresh(Command::Unify, Origin::Proved);
    let cached = provenance.cached(Command::Unify, Origin::Proved);
    assert_eq!(fresh + cached, 6);
    assert!((1..=4).contains(&fresh), "{fresh}");
}

#[test]
fn conjunctions_of_single_variable_equations_match_maude() {
    let Some((lean, oracle)) = handles() else {
        return;
    };
    let x = LVar::new("x", LSort::Msg, 7);
    // Numeric indices alone must not collapse distinct input variables.
    let y = LVar::new("y", LSort::Msg, 7);
    let rhs: Vec<_> = (2..=3).flat_map(|n| multisets(n, 0)).collect();
    let equation = |v, tail, rhs: &[usize]| Equal {
        lhs: f_app_ac(
            AcSym::Union,
            vec![Term::Lit(Lit::Var(v)), pub_term(format!("a{tail}"))],
        ),
        rhs: sum(rhs),
    };
    let mut queries = 0;
    for first in &rhs {
        for second in &rhs {
            let second = equation(y, 1, second);
            let eqs = [
                equation(x, 0, first),
                Equal {
                    lhs: second.rhs,
                    rhs: second.lhs,
                },
                Equal {
                    lhs: sum(&[0, 2]),
                    rhs: sum(&[2, 0]),
                },
            ];
            assert_eq!(
                canonical_ground_answers(lean.unify(&eqs).unwrap()),
                canonical_ground_answers(oracle.unify(&eqs).unwrap())
            );
            queries += 1;
        }
    }
    assert_eq!(queries, 256);
    assert_eq!(
        lean.provenance().fresh(Command::Unify, Origin::Proved),
        queries
    );
    assert_eq!(lean.stats().unify_count, 0);
}

#[test]
fn conjunction_shared_bindings_match_maude_and_conflicts_have_no_unifier() {
    let Some((lean, oracle)) = handles() else {
        return;
    };
    let x = LVar::new("x", LSort::Msg, 7);
    let equation = |tail, rest: &[usize]| {
        let mut ground = vec![tail];
        ground.extend_from_slice(rest);
        Equal {
            lhs: f_app_ac(
                AcSym::Union,
                vec![Term::Lit(Lit::Var(x)), pub_term(format!("a{tail}"))],
            ),
            rhs: sum(&ground),
        }
    };
    for rest in (1..=3).flat_map(|n| multisets(n, 0)) {
        let eqs = [equation(0, &rest), equation(1, &rest), equation(2, &rest)];
        assert_eq!(
            canonical_ground_answers(lean.unify(&eqs).unwrap()),
            canonical_ground_answers(oracle.unify(&eqs).unwrap())
        );
    }
    let conflict = [equation(0, &[1]), equation(1, &[2])];
    assert!(lean.unify(&conflict).unwrap().is_empty());
    assert!(!lean.unifiable(&conflict).unwrap());
    assert!(oracle.unify(&conflict).unwrap().is_empty());
    let provenance = lean.provenance();
    assert_eq!(provenance.fresh(Command::Unify, Origin::Proved), 20);
    assert_eq!(provenance.cached(Command::Unify, Origin::Proved), 1);
}

#[test]
fn pairing_recipes_match_maude_modulo_fresh_witness_names() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, pair, snd};
    use crate::maude_sig::pair_maude_sig;
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        pair_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, pair_maude_sig(), AlgebraBackend::Maude).unwrap();
    for idx in [0, 7, 65535] {
        let x = Term::Lit(Lit::Var(LVar::new("original", LSort::Msg, idx)));
        let y = Term::Lit(Lit::Var(LVar::new("other", LSort::Msg, idx)));
        let queries = [
            x.clone(),
            pair(x.clone(), y.clone()),
            f_app_list(vec![x.clone(), y.clone(), pair(x.clone(), y)]),
            fst(x.clone()),
            snd(x.clone()),
            f_app_list(vec![x.clone(), fst(x.clone()), fst(x.clone())]),
            f_app_list(vec![x.clone(), snd(x.clone()), snd(x)]),
        ];
        for query in queries {
            assert_eq!(
                canonical_variants(native.variants(&query).unwrap()),
                canonical_variants(oracle.variants(&query).unwrap()),
                "{query:?}"
            );
        }
    }
    let variable = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
    let terms = [
        pub_term("a"),
        variable("x", 7),
        pair(variable("x", 7), pub_term("b")),
    ];
    for a in &terms {
        for b in &terms {
            for term in [
                fst(pair(a.clone(), b.clone())),
                snd(pair(a.clone(), b.clone())),
            ] {
                assert_eq!(native.reduce(&term).unwrap(), oracle.reduce(&term).unwrap());
            }
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
    assert!(oracle.stats().var_count > 0);
    assert!(oracle.stats().norm_count > 0);
}

#[test]
fn reflexive_fresh_union_matches_maude_with_shared_variables_and_free_rows() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, 3)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Fresh, 3)));
    for tail in (1..=3).flat_map(|n| multisets(n, 0)) {
        let mk = |var: LNTerm| {
            let mut args = vec![var];
            args.extend(tail.iter().map(|n| pub_term(format!("a{n}"))));
            let term = f_app_ac(AcSym::Union, args);
            Equal {
                lhs: term.clone(),
                rhs: term,
            }
        };
        for query in [
            vec![mk(x.clone())],
            vec![mk(x.clone()), mk(x.clone()), mk(y.clone())],
            vec![
                Equal {
                    lhs: Term::Lit(Lit::Var(LVar::new("k", LSort::Msg, 20))),
                    rhs: x.clone(),
                },
                mk(x.clone()),
            ],
        ] {
            assert_eq!(assert_same_unifiers(&native, &oracle, &query), 1);
        }
    }
    assert!(native.provenance().fresh(Command::Unify, Origin::Proved) > 0);
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn combined_pairing_multiset_variants_and_reductions_match_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, pair, snd};
    use crate::maude_sig::pair_maude_sig;
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    let wrap = NoEqSym::new(b"wrap", 1, Privacy::Public, Constructability::Constructor);
    let combine = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let mut sig = pair_maude_sig()
        .merge(mset_maude_sig())
        .merge(crate::maude_sig::hash_maude_sig());
    sig.st_fun_syms.insert(wrap);
    sig.st_ac_fun_syms.insert(combine);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 7)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 7)));
    let union = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let terms = [
        x.clone(),
        Term::App(FunSym::NoEq(wrap), vec![x.clone()].into()),
        f_app_ac(AcSym::AcFct(combine), vec![x.clone(), pub_term("a")]),
        pub_term("a"),
        union(x.clone(), x.clone()),
        union(x.clone(), y.clone()),
        pair(union(x.clone(), y), pub_term("b")),
    ];
    for a in &terms {
        for b in &terms {
            let query = f_app_list(vec![
                a.clone(),
                b.clone(),
                union(a.clone(), b.clone()),
                pair(a.clone(), b.clone()),
            ]);
            assert_eq!(
                canonical_variants(native.variants(&query).unwrap()),
                canonical_variants(oracle.variants(&query).unwrap()),
                "{query:?}"
            );
            for projection in [fst, snd] {
                let term = projection(pair(a.clone(), b.clone()));
                assert_eq!(
                    native.reduce(&term).unwrap(),
                    oracle.reduce(&term).unwrap(),
                    "{term:?}"
                );
            }
        }
    }
    for projection in [fst, snd] {
        let query = f_app_list(vec![
            x.clone(),
            projection(x.clone()),
            projection(x.clone()),
        ]);
        assert_eq!(
            canonical_variants(native.variants(&query).unwrap()),
            canonical_variants(oracle.variants(&query).unwrap())
        );
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
    assert!(oracle.stats().var_count > 0);
    assert!(oracle.stats().norm_count > 0);
}

#[test]
fn directional_ac_matching_matches_maude_with_shared_variables_and_rigid_contexts() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 0);
    let vx = Term::Lit(Lit::Var(x));
    let normalize = |mut answers: Vec<Vec<(LVar, LNTerm)>>| {
        for answer in &mut answers {
            answer.sort();
        }
        answers.sort();
        answers
    };
    for n in 2..=4 {
        for rhs in multisets(n, 0) {
            for tail in multisets(1, 0).into_iter().chain(multisets(2, 0)) {
                let mut children = vec![vx.clone()];
                children.extend(tail.iter().map(|i| pub_term(format!("a{i}"))));
                let query = Equal {
                    lhs: sum(&rhs),
                    rhs: f_app_ac(AcSym::Union, children),
                };
                let eqs = [query.clone(), query];
                assert_eq!(
                    normalize(native.match_eqs(&eqs).unwrap()),
                    normalize(oracle.match_eqs(&eqs).unwrap()),
                    "{eqs:?}"
                );
            }
        }
    }
    let rigid = Term::Lit(Lit::Var(LVar::new("rigid", LSort::Fresh, u64::MAX)));
    let context = [(x.name, x.idx)].into_iter().collect();
    let eqs = [Equal {
        lhs: f_app_ac(AcSym::Union, vec![vx, rigid.clone()]),
        rhs: f_app_ac(AcSym::Union, vec![rigid.clone(), rigid, pub_term("a")]),
    }];
    assert_eq!(
        normalize(native.match_eqs_skolemize_both(&eqs, &context).unwrap()),
        normalize(oracle.match_eqs_skolemize_both(&eqs, &context).unwrap())
    );
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);
}

#[test]
fn native_oracle_rigid_ground_comparisons_and_bare_captures_match_without_rewriting() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, fst, pair};
    use crate::maude_sig::{dh_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 0);
    let vx = Term::Lit(Lit::Var(x));
    let rigid = Term::Lit(Lit::Var(LVar::new("r", LSort::Fresh, 41)));
    let context = [(x.name, x.idx)].into_iter().collect();
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let a = pub_term("a");
    let tower = exp(exp(a.clone(), rigid.clone()), rigid.clone());
    let projection = fst(pair(a.clone(), rigid.clone()));
    for image in [projection.clone(), tower.clone()] {
        let capture = eq(vx.clone(), image.clone());
        for (guard, second, expected) in [
            (
                eq(tower.clone(), tower.clone()),
                capture.clone(),
                vec![vec![(x, image.clone())]],
            ),
            (eq(projection.clone(), a.clone()), capture.clone(), vec![]),
            (eq(a.clone(), a.clone()), eq(vx.clone(), a.clone()), vec![]),
        ] {
            let query = [guard, capture.clone(), second];
            assert_eq!(
                maude.match_eqs_skolemize_both(&query, &context).unwrap(),
                expected
            );
            assert_eq!(
                native.match_eqs_skolemize_both(&query, &context).unwrap(),
                expected
            );
        }
    }
}

#[test]
fn native_oracle_shared_captures_constrain_ground_structural_matches() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::maude_sig::pair_maude_sig;
    let sig = mset_maude_sig().merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = require_maude_path()
        .map(|p| MaudeHandle::start_with_backend(&p, sig, AlgebraBackend::Maude).unwrap());
    let x = LVar::new("x", LSort::Msg, 1);
    let y = LVar::new("y", LSort::Msg, 2);
    let vx = Term::Lit(Lit::Var(x));
    let vy = Term::Lit(Lit::Var(y));
    let rigid = Term::Lit(Lit::Var(LVar::new("k", LSort::Msg, 3)));
    let context = [(x.name, x.idx), (y.name, y.idx)].into_iter().collect();
    let a = pub_term("1");
    let union = |xs| f_app_ac(AcSym::Union, xs);
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let pattern = union(vec![vx.clone(), vy.clone()]);
    let joined = union(vec![a.clone(), rigid.clone()]);
    let capture = eq(vx.clone(), joined.clone());
    let repeated = |t: &LNTerm| pair(t.clone(), t.clone());
    let queries = [
        (
            vec![
                eq(pattern.clone(), union(vec![a.clone(), a.clone()])),
                capture.clone(),
            ],
            vec![],
        ),
        // Both observations account for the same rigid variable, with one AC occurrence left for y.
        (
            vec![
                capture.clone(),
                eq(pattern, union(vec![rigid.clone(), a.clone(), a.clone()])),
            ],
            vec![vec![(x, joined.clone()), (y, a.clone())]],
        ),
        (
            vec![
                eq(repeated(&vx), repeated(&joined)),
                capture.clone(),
                capture.clone(),
            ],
            vec![vec![(x, joined.clone())]],
        ),
        (
            vec![eq(repeated(&vx), pair(joined.clone(), a.clone())), capture],
            vec![],
        ),
        (
            vec![
                eq(vy.clone(), rigid.clone()),
                eq(pair(vx.clone(), vy.clone()), pair(a.clone(), rigid.clone())),
                eq(vx, a.clone()),
            ],
            vec![vec![(x, a), (y, rigid)]],
        ),
    ];
    for (q, expected) in queries {
        let expected = canonical_ground_answers(expected);
        assert_eq!(
            canonical_ground_answers(native.match_eqs_skolemize_both(&q, &context).unwrap()),
            expected
        );
        if let Some(o) = &oracle {
            assert_eq!(
                canonical_ground_answers(o.match_eqs_skolemize_both(&q, &context).unwrap()),
                expected
            );
        }
    }
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn native_oracle_ground_captures_specialize_repeated_ac_occurrences_before_partitioning() {
    use crate::algebra_backend::AlgebraBackend;
    let sig = mset_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = require_maude_path()
        .map(|p| MaudeHandle::start_with_backend(&p, sig, AlgebraBackend::Maude).unwrap());
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Msg, 1);
    let vx = Term::Lit(Lit::Var(x));
    let vy = Term::Lit(Lit::Var(y));
    let context = [(x.name, x.idx), (y.name, y.idx)].into_iter().collect();
    let a = pub_term("1");
    let copies = |n| f_app_ac(AcSym::Union, vec![a.clone(); n]);
    for (xs, capture, y_count) in [(1, 10, None), (1, 1, Some(8)), (2, 4, Some(1))] {
        let mut factors = vec![vx.clone(); xs];
        factors.push(vy.clone());
        let q = [
            Equal {
                lhs: f_app_ac(AcSym::Union, factors),
                rhs: copies(9),
            },
            Equal {
                lhs: vx.clone(),
                rhs: copies(capture),
            },
        ];
        let expected = y_count
            .into_iter()
            .map(|count| vec![(x, copies(capture)), (y, copies(count))])
            .collect::<Vec<_>>();
        assert_eq!(
            canonical_ground_answers(native.match_eqs_skolemize_both(&q, &context).unwrap()),
            expected
        );
        if let Some(o) = &oracle {
            assert_eq!(
                canonical_ground_answers(o.match_eqs_skolemize_both(&q, &context).unwrap()),
                expected
            );
        }
    }
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn mixed_sort_matches_agree_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::lterm::{fresh_term, Name, NameTag};
    use crate::maude_sig::nat_maude_sig;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(nat_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let atoms = [
        pub_term("n"),
        fresh_term("n"),
        Term::Lit(Lit::Con(Name::new(NameTag::Nat, "n"))),
    ];
    let union = |terms| f_app_ac(AcSym::Union, terms);
    for sort in [LSort::Pub, LSort::Fresh, LSort::Nat] {
        let x = LVar::new("narrow", sort, 1);
        for other in [LSort::Pub, LSort::Fresh, LSort::Nat, LSort::Msg] {
            let y = LVar::new("other", other, 1);
            for pattern in [vec![x, y], vec![x, x, y]] {
                let pat = union(
                    pattern
                        .into_iter()
                        .map(|v| Term::Lit(Lit::Var(v)))
                        .collect(),
                );
                for size in 2..=4 {
                    for ids in multisets(size, 0) {
                        let subject = union(ids.into_iter().map(|i| atoms[i].clone()).collect());
                        let eqs = [Equal {
                            lhs: subject,
                            rhs: pat.clone(),
                        }];
                        let expected = oracle.match_eqs(&eqs).unwrap();
                        assert!(expected.len() <= 1);
                        assert_eq!(native.has_match_eqs(&eqs).unwrap(), !expected.is_empty());
                        assert_eq!(
                            canonical_ground_answers(native.match_eqs(&eqs).unwrap()),
                            canonical_ground_answers(expected),
                            "{eqs:?}"
                        );
                    }
                }
            }
        }
    }
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);
}

#[test]
fn open_compound_matches_agree_with_maude_for_shared_and_repeated_occurrences() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::lean_unification::{match_compound_ground, Outcome};
    use crate::maude_sig::hash_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::ProvedOnly).unwrap();
    let x = LVar::new("x", LSort::Msg, 7);
    let y = LVar::new("y", LSort::Msg, 7);
    let narrow = LVar::new("p", LSort::Pub, 7);
    let v = |x| Term::Lit(Lit::Var(x));
    let a = pub_term("a");
    let pool = [a.clone(), hash(a), hash(pub_term("b"))];
    let u = |xs| f_app_ac(AcSym::Union, xs);
    let patterns = [
        vec![hash(v(x)), v(y)],
        vec![hash(v(x)), v(x)],
        vec![hash(v(x)), hash(v(x))],
        vec![hash(v(x)), hash(v(y))],
        vec![hash(v(x)), v(y), v(y)],
        vec![hash(v(x)), v(x), v(y)],
        vec![hash(v(narrow)), v(narrow), v(y)],
        vec![hash(v(x)), v(narrow), v(y)],
        vec![v(x), v(y)],
    ];
    let mut checked = 0;
    for factors in patterns {
        let pat = u(factors);
        for size in 2..=5 {
            for ids in multisets(size, 0) {
                let subject = u(ids.iter().map(|&i| pool[i].clone()).collect());
                let oriented = Equal {
                    lhs: pat.clone(),
                    rhs: subject.clone(),
                };
                let Outcome::Complete(lean) = match_compound_ground(&[oriented]).unwrap() else {
                    panic!("unexpected deferral for {pat:?} against {subject:?}");
                };
                let query = [Equal {
                    lhs: subject,
                    rhs: pat.clone(),
                }];
                let maude = canonical_ground_answers(oracle.match_eqs(&query).unwrap());
                assert_eq!(canonical_ground_answers(lean), maude, "{query:?}");
                assert_eq!(
                    canonical_ground_answers(native.match_eqs(&query).unwrap()),
                    maude,
                    "{query:?}"
                );
                assert_eq!(native.has_match_eqs(&query).unwrap(), !maude.is_empty());
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 468);
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn open_matching_agrees_with_maude_in_both_entry_points() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 7)));
    let u = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let pattern = u(hash(v("x")), v("y"));
    let a = pub_term("a");
    let one_binding = [Equal {
        lhs: u(hash(a.clone()), a.clone()),
        rhs: u(hash(v("x")), v("x")),
    }];
    assert_eq!(
        native.match_eqs(&one_binding).unwrap(),
        oracle.match_eqs(&one_binding).unwrap()
    );
    let unique = [Equal {
        lhs: u(hash(a.clone()), a.clone()),
        rhs: pattern.clone(),
    }];
    // Maude prints y before x for this match. Both backends expose
    // the upstream substitution map's traversal order.
    let expected = vec![vec![
        (LVar::new("x", LSort::Msg, 7), a.clone()),
        (LVar::new("y", LSort::Msg, 7), a.clone()),
    ]];
    assert_eq!(oracle.match_eqs(&unique).unwrap(), expected);
    assert_eq!(native.match_eqs(&unique).unwrap(), expected);
    let bindable = [("x", 7), ("y", 7)].into_iter().collect();
    let rigid = [Equal {
        lhs: unique[0].rhs.clone(),
        rhs: unique[0].lhs.clone(),
    }];
    assert_eq!(
        oracle.match_eqs_skolemize_both(&rigid, &bindable).unwrap(),
        expected
    );
    assert_eq!(
        native.match_eqs_skolemize_both(&rigid, &bindable).unwrap(),
        expected
    );
    // Proved-only lists the two arms in the order of their binding maps,
    // Maude in its own. The first match is the least one on both.
    let ambiguous = [Equal {
        lhs: u(hash(a), hash(pub_term("b"))),
        rhs: pattern,
    }];
    assert!(native.has_match_eqs(&ambiguous).unwrap());
    let answers = canonical_ground_answers(oracle.match_eqs(&ambiguous).unwrap());
    assert_eq!(answers.len(), 2);
    assert_eq!(native.match_eqs(&ambiguous).unwrap(), answers);
    assert_eq!(
        native.first_match_eqs(&ambiguous).unwrap(),
        oracle.first_match_eqs(&ambiguous).unwrap()
    );
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn independent_side_binding_keeps_its_subject_rigid() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = native_session(mset_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 0);
    let z = LVar::new("z", LSort::Msg, 1);
    let var = |v| Term::Lit(Lit::Var(v));
    let a = pub_term("a");
    let b = pub_term("b");
    let sum = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let leaf = Equal {
        lhs: sum(a.clone(), b.clone()),
        rhs: sum(var(x), b),
    };
    let side = Equal {
        lhs: var(x),
        rhs: var(z),
    };
    for eqs in [
        vec![side.clone(), leaf.clone(), side.clone()],
        vec![leaf.clone(), side],
    ] {
        let expected = vec![vec![(x, a.clone()), (z, var(x))]];
        assert_eq!(oracle.match_eqs(&eqs).unwrap(), expected);
        assert_eq!(native.match_eqs(&eqs).unwrap(), expected);
    }
    // Reusing a residual pattern variable as the side domain prevents
    // independent extension. An incompatible pair must yield no answer.
    let shared = [
        leaf,
        Equal {
            lhs: var(z),
            rhs: var(x),
        },
    ];
    assert!(oracle.match_eqs(&shared).unwrap().is_empty());
    assert!(native.match_eqs(&shared).unwrap().is_empty());
    assert!(!native.has_match_eqs(&shared).unwrap());
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn ambiguous_sorted_matches_agree_with_maude_as_sets() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let u = |terms| f_app_ac(AcSym::Union, terms);
    let x = LVar::new("x", LSort::Msg, 0);
    let y = LVar::new("y", LSort::Pub, 1);
    let k = LVar::new("k", LSort::Msg, 2);
    let v = |key| Term::Lit(Lit::Var(key));
    let (a, b, z) = (pub_term("a"), pub_term("b"), pub_term("z"));
    let query = [
        Equal {
            lhs: u(vec![b.clone(), z.clone()]),
            rhs: u(vec![v(k), z]),
        },
        Equal {
            lhs: u(vec![a.clone(), b.clone()]),
            rhs: u(vec![v(x), v(y)]),
        },
    ];
    assert!(native.has_match_eqs(&query).unwrap());
    let answers = canonical_ground_answers(oracle.match_eqs(&query).unwrap());
    assert_eq!(answers.len(), 2);
    assert_eq!(native.match_eqs(&query).unwrap(), answers);
    assert_eq!(
        native.first_match_eqs(&query).unwrap(),
        oracle.first_match_eqs(&query).unwrap()
    );

    let bindable = [(x.name, x.idx), (y.name, y.idx)].into_iter().collect();
    let rigid = [Equal {
        lhs: u(vec![v(x), v(y), b.clone()]),
        rhs: u(vec![a, b.clone(), b]),
    }];
    let answers =
        canonical_ground_answers(oracle.match_eqs_skolemize_both(&rigid, &bindable).unwrap());
    assert_eq!(answers.len(), 2);
    assert_eq!(
        canonical_ground_answers(native.match_eqs_skolemize_both(&rigid, &bindable).unwrap()),
        answers
    );
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn mixed_literal_and_compound_leaves_under_free_heads_agree_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::lterm::fresh_term;
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Fresh, 0);
    let y = LVar::new("y", LSort::Msg, 0);
    let v = |var| Term::Lit(Lit::Var(var));
    let u = |terms| f_app_ac(AcSym::Union, terms);
    let fixed = hash(pub_term("h"));
    let a = fresh_term("a");
    let b = pub_term("b");
    let pattern = pair(u(vec![v(x), fixed.clone()]), u(vec![v(x), v(x), v(y)]));
    for (expected, first) in [(1, a.clone()), (0, fresh_term("c"))] {
        let subject = pair(
            u(vec![first, fixed.clone()]),
            u(vec![a.clone(), a.clone(), b.clone()]),
        );
        let eqs = [Equal {
            lhs: subject.clone(),
            rhs: pattern.clone(),
        }];
        let answer = native.match_eqs(&eqs).unwrap();
        assert_eq!(answer.len(), expected);
        assert_eq!(answer, oracle.match_eqs(&eqs).unwrap());
        let oriented = [Equal {
            lhs: pattern.clone(),
            rhs: subject,
        }];
        let bindable = [(x.name, x.idx), (y.name, y.idx)].into_iter().collect();
        assert_eq!(
            native
                .match_eqs_skolemize_both(&oriented, &bindable)
                .unwrap(),
            oracle
                .match_eqs_skolemize_both(&oriented, &bindable)
                .unwrap()
        );
    }
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);
}

#[test]
fn native_oracle_repeated_subjects_match_at_their_distinct_image_cost() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::function_symbols::nat_one_sym;
    use crate::maude_sig::nat_maude_sig;
    use crate::term::f_app_no_eq;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = nat_maude_sig().merge(mset_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    for (symbol, sort, constant) in [
        (
            AcSym::NatPlus,
            LSort::Nat,
            f_app_no_eq(nat_one_sym(), vec![]),
        ),
        (AcSym::Union, LSort::Msg, pub_term("a")),
    ] {
        let x = LVar::new("x", sort, 0);
        let y = LVar::new("y", sort, 1);
        let vars = [(x.name, x.idx), (y.name, y.idx)].into_iter().collect();
        let sum = |terms| f_app_ac(symbol, terms);
        for atom in [constant, Term::Lit(Lit::Var(LVar::new("rigid", sort, 2)))] {
            for (p, q, width) in [(2, 3, 9), (1, 1, 9), (2, 0, 65), (2, 0, 66), (32, 33, 65)] {
                let pattern = sum([
                    vec![Term::Lit(Lit::Var(x)); p],
                    vec![Term::Lit(Lit::Var(y)); q],
                ]
                .concat());
                let subject = sum(vec![atom.clone(); width]);
                let expected = canonical_ground_answers(
                    (1..=width / p)
                        .filter_map(|i| {
                            let rest = width - p * i;
                            let mut arm = vec![(x, sum(vec![atom.clone(); i]))];
                            if q > 0 {
                                if rest == 0 || rest % q != 0 {
                                    return None;
                                }
                                arm.push((y, sum(vec![atom.clone(); rest / q])));
                            } else if rest != 0 {
                                return None;
                            }
                            Some(arm)
                        })
                        .collect(),
                );
                let plain = [Equal {
                    lhs: subject.clone(),
                    rhs: pattern.clone(),
                }];
                let restricted = [Equal {
                    lhs: pattern,
                    rhs: subject,
                }];
                for h in [&native, &oracle] {
                    assert_eq!(
                        canonical_ground_answers(h.match_eqs(&plain).unwrap()),
                        expected
                    );
                    assert_eq!(
                        canonical_ground_answers(
                            h.match_eqs_skolemize_both(&restricted, &vars).unwrap()
                        ),
                        expected
                    );
                }
            }
        }
    }
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);

    let ambiguous = [Equal {
        lhs: f_app_ac(AcSym::Union, vec![pub_term("a"); 9]),
        rhs: f_app_ac(
            AcSym::Union,
            vec![
                crate::builtin::msg_var("x", 0),
                crate::builtin::msg_var("y", 0),
            ],
        ),
    }];
    assert!(native.has_match_eqs(&ambiguous).unwrap());
    let answers = native.match_eqs(&ambiguous).unwrap();
    assert_eq!(answers.len(), 8);
    assert_eq!(
        answers,
        canonical_ground_answers(oracle.match_eqs(&ambiguous).unwrap())
    );
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn multi_variable_flat_matching_matches_maude_exhaustively() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 7);
    let y = LVar::new("y", LSort::Msg, 7);
    let z = LVar::new("z", LSort::Msg, 7);
    let patterns = [
        vec![x, y],
        vec![x, x],
        vec![x, x, y],
        vec![x, y, z],
        vec![x, y, x, y],
    ];
    for pattern in patterns {
        for tail in [vec![], vec![pub_term("a0")]] {
            let mut terms: Vec<_> = pattern.iter().map(|v| Term::Lit(Lit::Var(*v))).collect();
            terms.extend(tail);
            let pattern = f_app_ac(AcSym::Union, terms);
            for size in 2..=4 {
                for subject in multisets(size, 0) {
                    let eqs = [Equal {
                        lhs: sum(&subject),
                        rhs: pattern.clone(),
                    }];
                    assert_eq!(
                        canonical_ground_answers(native.match_eqs(&eqs).unwrap()),
                        canonical_ground_answers(oracle.match_eqs(&eqs).unwrap()),
                        "{eqs:?}"
                    );
                }
            }
        }
    }
    for first in multisets(2, 0) {
        for second in multisets(2, 0) {
            let eqs = [
                Equal {
                    lhs: sum(&first),
                    rhs: f_app_ac(
                        AcSym::Union,
                        vec![Term::Lit(Lit::Var(x)), Term::Lit(Lit::Var(y))],
                    ),
                },
                Equal {
                    lhs: sum(&second),
                    rhs: f_app_ac(
                        AcSym::Union,
                        vec![Term::Lit(Lit::Var(x)), Term::Lit(Lit::Var(z))],
                    ),
                },
            ];
            assert_eq!(
                canonical_ground_answers(native.match_eqs(&eqs).unwrap()),
                canonical_ground_answers(oracle.match_eqs(&eqs).unwrap()),
                "joined {eqs:?}"
            );
        }
    }
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);
}

#[test]
fn nested_constructor_matches_and_ground_side_unifiers_agree_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::maude_sig::pair_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = pair_maude_sig().merge(mset_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 7)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 7)));
    let z = Term::Lit(Lit::Var(LVar::new("z", LSort::Msg, 7)));
    let xy = f_app_ac(AcSym::Union, vec![x.clone(), y]);
    let wrap = |l, r| pair(pair(l, pub_term("marker")), r);
    for other in [x.clone(), z] {
        let pat = f_app_ac(AcSym::Union, vec![x.clone(), other]);
        for a in multisets(2, 0) {
            for b in multisets(3, 0) {
                let eq = Equal {
                    lhs: wrap(sum(&a), sum(&b)),
                    rhs: wrap(xy.clone(), pat.clone()),
                };
                let eqs = std::slice::from_ref(&eq);
                assert_eq!(
                    canonical_ground_answers(native.match_eqs(eqs).unwrap()),
                    canonical_ground_answers(oracle.match_eqs(eqs).unwrap()),
                    "{eqs:?}"
                );

                let eqs = [
                    Equal {
                        lhs: sum(&a),
                        rhs: xy.clone(),
                    },
                    Equal {
                        lhs: pat.clone(),
                        rhs: sum(&b),
                    },
                ];
                assert_eq!(
                    canonical_ground_answers(native.unify(&eqs).unwrap()),
                    canonical_ground_answers(oracle.unify(&eqs).unwrap()),
                    "{eqs:?}"
                );
            }
        }
    }
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn sorted_residuals_agree_with_independent_assignments_and_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::lterm::{fresh_term, Name, NameTag};
    use crate::maude_sig::nat_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(nat_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();

    // Deliberately give all three rigid atoms the same spelling. Only the tag
    // distinguishes them. Generate potential images independently of subtraction.
    let atoms = [
        pub_term("same"),
        fresh_term("same"),
        Term::Lit(Lit::Con(Name::new(NameTag::Nat, "same"))),
    ];
    let sorts = [LSort::Pub, LSort::Fresh, LSort::Nat];
    let product = |ids: &[usize]| {
        f_app_ac(
            AcSym::Union,
            ids.iter().map(|i| atoms[*i].clone()).collect(),
        )
    };
    let candidates: Vec<_> = (1..=3).flat_map(|n| multisets(n, 0)).collect();
    let subjects: Vec<_> = (2..=4).flat_map(|n| multisets(n, 0)).collect();
    let mut queries = 0;
    for sort in [LSort::Msg, LSort::Pub, LSort::Fresh, LSort::Nat] {
        let var = LVar::new("v", sort, 7);
        for tail in (1..=2).flat_map(|n| multisets(n, 0)) {
            let pattern = f_app_ac(
                AcSym::Union,
                std::iter::once(Term::Lit(Lit::Var(var)))
                    .chain(tail.iter().map(|i| atoms[*i].clone()))
                    .collect(),
            );
            for subject in &subjects {
                let expected: Vec<_> = candidates
                    .iter()
                    .filter(|image| {
                        if sort != LSort::Msg && (image.len() != 1 || sorts[image[0]] != sort) {
                            return false;
                        }
                        let mut instantiated = tail.clone();
                        instantiated.extend_from_slice(image);
                        instantiated.sort_unstable();
                        instantiated == *subject
                    })
                    .map(|image| vec![(var, product(image))])
                    .collect();
                let mut eq = Equal {
                    lhs: product(subject),
                    rhs: pattern.clone(),
                };
                let check = |answer| {
                    assert_eq!(
                        expected, answer,
                        "sort={sort:?}, literal tail={tail:?}, subject={subject:?}"
                    )
                };
                check(native.match_eqs(std::slice::from_ref(&eq)).unwrap());
                check(maude.match_eqs(std::slice::from_ref(&eq)).unwrap());
                if queries % 2 == 0 {
                    std::mem::swap(&mut eq.lhs, &mut eq.rhs);
                }
                check(native.unify(std::slice::from_ref(&eq)).unwrap());
                check(maude.unify(std::slice::from_ref(&eq)).unwrap());
                queries += 1;
            }
        }
    }
    assert_eq!(queries, 1116);
    assert_eq!(native.stats().match_count, 0);
    assert!(native.provenance().fresh(Command::Unify, Origin::Proved) > 0);
    assert!(maude.stats().match_count > 0 && maude.stats().unify_count > 0);
}

#[test]
fn cancellation_agrees_with_maude_under_ground_instances_of_the_free_variable() {
    use crate::algebra_backend::AlgebraBackend;

    let Some(path) = require_maude_path() else {
        return;
    };
    let native = native_session(mset_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 7);
    let y = LVar::new("y", LSort::Msg, 7);
    let c = LVar::new("c", LSort::Msg, 7);
    let v = |var| Term::Lit(Lit::Var(var));
    let product = |terms| f_app_ac(AcSym::Union, terms);
    let mut checked = 0;
    // The second equation forces c without a syntactic variable equation.
    // This lets us compare complete ground arms despite Maude also being
    // allowed to enumerate specializations of an unconstrained c.
    for extra in [vec![x], vec![x, x], vec![x, y], vec![x, x, y], vec![x, c]] {
        for repeat in 1..=2 {
            for size in 1..=3 {
                for subject in multisets(size, 0) {
                    let mut left = vec![v(c); repeat];
                    left.extend(extra.iter().copied().map(v));
                    let mut right = vec![v(c); repeat];
                    right.extend(subject.iter().map(|i| pub_term(format!("a{i}"))));
                    let (lhs, rhs) = if checked % 2 == 0 {
                        (left, right)
                    } else {
                        (right, left)
                    };
                    let query = Equal {
                        lhs: product(lhs),
                        rhs: product(rhs),
                    };
                    assert_same_unifiers(&native, &oracle, std::slice::from_ref(&query));
                    for image in [pub_term("a0"), sum(&[0, 1])] {
                        let anchored = [
                            query.clone(),
                            Equal {
                                lhs: product(vec![v(c), v(c)]),
                                rhs: product(vec![image.clone(), image.clone()]),
                            },
                        ];
                        assert_eq!(
                            canonical_ground_answers(native.unify(&anchored).unwrap()),
                            canonical_ground_answers(oracle.unify(&anchored).unwrap()),
                            "{anchored:?}"
                        );
                    }
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 190);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn ground_branch_filter_matches_maude_for_both_sided_equations() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native = native_session(mset_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 9)));
    let product = |terms| f_app_ac(AcSym::Union, terms);
    let mut checked = 0;
    let mut nonempty = 0;
    for size in 2..=4 {
        for subject in multisets(size, 0) {
            for left in 0..3 {
                for right in 0..3 {
                    let mut eqs = [
                        Equal {
                            lhs: product(vec![v("x"), v("y")]),
                            rhs: sum(&subject),
                        },
                        Equal {
                            lhs: product(vec![v("x"), pub_term(format!("a{left}"))]),
                            rhs: product(vec![v("y"), pub_term(format!("a{right}"))]),
                        },
                    ];
                    if checked % 2 == 0 {
                        eqs.reverse();
                    }
                    let arms = native.unify(&eqs).unwrap();
                    nonempty += usize::from(!arms.is_empty());
                    assert_eq!(
                        canonical_ground_answers(arms),
                        canonical_ground_answers(oracle.unify(&eqs).unwrap()),
                        "{eqs:?}"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 279);
    assert!(nonempty > 0 && nonempty < checked);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn shared_offset_agrees_with_maude_modulo_per_answer_witness_names() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::lterm::fresh_term;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(crate::maude_sig::pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let atoms = [
        pub_term("a"),
        pub_term("b"),
        fresh_term("a"),
        fresh_term("b"),
    ];
    let mut count = 0;
    for i in [0, 5, 987] {
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)));
        let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, i)));
        let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Msg, i + 30)));
        let t = Term::Lit(Lit::Var(LVar::new("t", LSort::Msg, i + 17)));
        for a in &atoms {
            for b in atoms.iter().filter(|b| *b != a) {
                let eq = Equal {
                    lhs: f_app_ac(AcSym::Union, vec![x.clone(), a.clone()]),
                    rhs: f_app_ac(AcSym::Union, vec![y.clone(), b.clone()]),
                };
                for (lhs, rhs) in [(&eq.lhs, &eq.rhs), (&eq.rhs, &eq.lhs)] {
                    let single = Equal {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                    };
                    for eqs in [
                        vec![single.clone()],
                        vec![
                            Equal {
                                lhs: k.clone(),
                                rhs: pair(x.clone(), t.clone()),
                            },
                            single,
                        ],
                    ] {
                        assert_eq!(assert_same_unifiers(&native, &oracle, &eqs), 2);
                        count += 1;
                    }
                }
            }
        }
    }
    assert_eq!(count, 144);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn constructor_variants_follow_the_active_rule_table_and_agree_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{adec, aenc, fst, hash, pair, pk, sdec, senc, sign, xor};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{
        asym_enc_maude_sig, bp_maude_sig, hash_maude_sig, pair_maude_sig, signature_maude_sig,
        sym_enc_maude_sig, xor_maude_sig,
    };
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = pair_maude_sig()
        .merge(mset_maude_sig())
        .merge(sym_enc_maude_sig())
        .merge(asym_enc_maude_sig())
        .merge(signature_maude_sig())
        .merge(hash_maude_sig())
        .merge(bp_maude_sig())
        .merge(xor_maude_sig());
    let theory = RuleTable::new(&sig).unwrap();
    let maude = MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::ProvedOnly).unwrap();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 8)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 8)));
    let k = pub_term("key");
    let mut count = 0;
    for t in [
        x.clone(),
        y.clone(),
        k.clone(),
        pk(x.clone()),
        hash(y.clone()),
        pair(x.clone(), y.clone()),
        sum(&[0, 0, 1]),
    ] {
        for s in [x.clone(), k.clone(), t.clone()] {
            for term in [
                senc(t.clone(), s.clone()),
                aenc(t.clone(), pk(s.clone())),
                sign(t.clone(), s.clone()),
                f_app_ac(AcSym::Union, vec![s.clone(), t.clone()]),
            ] {
                let packed = f_app_list(vec![s.clone(), term.clone(), x.clone(), term]);
                let expected = vec![vec![]];
                assert_eq!(
                    theory.variants(&packed).unwrap(),
                    Outcome::Complete(expected.clone())
                );
                assert_eq!(native.variants(&packed).unwrap(), expected);
                // The Maude decoder spells out the identity with fresh range
                // variables. Every observed variable must retain its own sort
                // and remain independent of every other observed variable.
                let reference = maude.variants(&packed).unwrap();
                assert_eq!(reference.len(), 1, "{packed:?}");
                let arm = crate::subst_vfresh::LSubstVFresh::from_list(reference[0].clone());
                assert!(arm.is_renaming(), "{packed:?}: {reference:?}");
                assert_eq!(arm.remove_renamings().to_list(), expected[0]);
                count += 1;
            }
        }
    }
    assert_eq!(count, 84);
    assert_eq!(native.stats().var_count, 0);
    assert!(maude.stats().var_count > 0);
    for defined in [
        sdec(x.clone(), y.clone()),
        adec(x.clone(), y.clone()),
        fst(x.clone()),
        xor(x.clone(), y.clone()),
    ] {
        let packed = f_app_list(vec![k.clone(), hash(defined)]);
        assert_eq!(theory.variants(&packed).unwrap(), Outcome::Unsupported);
    }
    // A nested defined head needs a broader narrowing search.
    let nested = hash(sdec(x, y));
    assert_eq!(
        canonical_variants(native.variants(&nested).unwrap()),
        canonical_variants(maude.variants(&nested).unwrap())
    );
}

#[test]
fn single_rule_narrowing_matches_maude_and_preserves_shared_parameters() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{adec, aenc, fst, pair, pk, sdec, senc, snd};
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::maude_sig::{asym_enc_maude_sig, pair_maude_sig, sym_enc_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::{f_app_list, f_app_no_eq};

    let Some(path) = require_maude_path() else {
        return;
    };
    let mut sig = pair_maude_sig()
        .merge(sym_enc_maude_sig())
        .merge(asym_enc_maude_sig());
    let d = NoEqSym::new("unseal", 3, Privacy::Public, Constructability::Destructor);
    sig.st_fun_syms.insert(d);
    let variable = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
    let l = variable("left", 0);
    let r = variable("right", 0);
    // unseal(pair(l,r), pair(r,r), l) = r. The same parameter appears
    // several times within a field and is shared with another query image.
    sig.st_rules.insert(CtxtStRule::new(
        f_app_no_eq(
            d,
            vec![pair(l.clone(), r.clone()), pair(r.clone(), r.clone()), l],
        ),
        StRhs {
            positions: vec![vec![0, 1], vec![1, 0], vec![1, 1]],
            term: r,
        },
    ));
    let sig = sig.refresh();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::ProvedOnly).unwrap();
    for idx in [0, 49, 65535] {
        let x = variable("x", idx);
        let y = variable("y", idx);
        let z = variable("z", idx);
        for (query, result) in [
            (fst(pair(x.clone(), y.clone())), x.clone()),
            (snd(pair(x.clone(), y.clone())), y.clone()),
            (adec(aenc(z.clone(), pk(x.clone())), x.clone()), z.clone()),
            (sdec(senc(y.clone(), z.clone()), z.clone()), y.clone()),
            (
                f_app_no_eq(
                    d,
                    vec![
                        pair(z.clone(), y.clone()),
                        pair(y.clone(), y.clone()),
                        z.clone(),
                    ],
                ),
                y.clone(),
            ),
        ] {
            assert_eq!(oracle.reduce(&query).unwrap(), result);
            assert_eq!(native.reduce(&query).unwrap(), result);
        }
        for (args, app) in [
            (vec![x.clone()], fst(x.clone())),
            (vec![y.clone()], snd(y.clone())),
            (vec![y.clone(), x.clone()], adec(x.clone(), y.clone())),
            (vec![y.clone(), x.clone()], sdec(x.clone(), y.clone())),
            (
                vec![x.clone(), z.clone(), y.clone()],
                f_app_no_eq(d, vec![z.clone(), y.clone(), x.clone()]),
            ),
        ] {
            let packed = f_app_list([vec![app.clone()], args, vec![app.clone()]].concat());
            for query in [app, packed] {
                let expected = oracle.variants(&query).unwrap();
                let actual = native.variants(&query).unwrap();
                assert_eq!(actual.len(), 2);
                assert_eq!(
                    canonical_variants(actual),
                    canonical_variants(expected),
                    "{query:?}"
                );
            }
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn single_rule_narrowing_rejects_ambiguous_and_out_of_fragment_requests() {
    use crate::builtin::{fst, hash, pair, sdec, senc, snd};
    use crate::lean_unification::{Error, Outcome, RuleTable};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig, sym_enc_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::f_app_list;
    let variable = |name, sort, idx| Term::Lit(Lit::Var(LVar::new(name, sort, idx)));
    let x = variable("x", LSort::Msg, 0);
    let y = variable("y", LSort::Msg, 0);
    let mut sig = sym_enc_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let theory = RuleTable::new(&sig).unwrap();
    // Matching at a concrete root must check every repeated key, including
    // two input variables that share an index but have different names.
    assert_eq!(
        theory
            .reduce(&sdec(senc(x.clone(), x.clone()), y.clone()))
            .unwrap(),
        None
    );
    assert_eq!(
        theory
            .reduce(&sdec(senc(hash(x.clone()), y.clone()), y.clone()))
            .unwrap(),
        Some(hash(x.clone()))
    );
    // The free variable x is rigid during concrete reduction. fst(x) is
    // normal, so the projection can return it even though fst has a rule.
    let wrapped = sdec(senc(fst(x.clone()), y.clone()), y.clone());
    assert_eq!(theory.reduce(&wrapped).unwrap(), Some(fst(x.clone())));
    if let Some(path) = require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(
            &path,
            sig.clone(),
            crate::algebra_backend::AlgebraBackend::Maude,
        )
        .unwrap();
        assert_eq!(oracle.reduce(&wrapped).unwrap(), fst(x.clone()));
    }
    for query in [
        sdec(x.clone(), x.clone()),
        sdec(x.clone(), variable("n", LSort::Pub, 0)),
        sdec(x.clone(), pub_term("key")),
        f_app_list(vec![fst(x.clone()), snd(x.clone())]),
        f_app_list(vec![fst(x.clone()), y.clone()]),
    ] {
        assert_eq!(
            theory.variants(&query).unwrap(),
            Outcome::Unsupported,
            "{query:?}"
        );
    }
    assert_eq!(
        theory.variants(&sdec(x.clone(), variable("max", LSort::Msg, u64::MAX))),
        Err(Error::FreshVariableOverflow),
    );
    let mut extra = sig.clone();
    extra.st_rules.insert(CtxtStRule::new(
        sdec(pair(x.clone(), y.clone()), y.clone()),
        StRhs {
            positions: vec![vec![0, 0]],
            term: x.clone(),
        },
    ));
    assert_eq!(
        RuleTable::new(&extra)
            .unwrap()
            .variants(&sdec(x.clone(), y.clone()))
            .unwrap(),
        Outcome::Unsupported
    );
    // A second rule headed by senc invalidates the assumption that the
    // freshened left-hand side of the sdec rule consists of constructors.
    sig.st_rules.insert(CtxtStRule::new(
        senc(hash(x.clone()), y.clone()),
        StRhs {
            positions: vec![vec![0, 0]],
            term: x.clone(),
        },
    ));
    assert_eq!(
        RuleTable::new(&sig).unwrap().variants(&sdec(x, y)).unwrap(),
        Outcome::Unsupported
    );
}

#[test]
fn native_oracle_joint_destructors_preserve_normal_values_and_ambient_names() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, sdec, snd};
    use crate::lterm::HasFrees;
    use crate::maude_sig::{pair_maude_sig, sym_enc_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    use std::collections::BTreeMap;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = pair_maude_sig().merge(sym_enc_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();

    // The stand-alone fst(x0) leaf would use x1 and x2 for the pair.
    // Both names already belong to the packed query, in different roles.
    let [x, y, ambient] = [0, 1, 2].map(|i| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i))));
    for (ops, expected) in [
        (vec![fst(x.clone()), snd(y.clone())], 4),
        (vec![fst(x.clone()), snd(x.clone()), fst(x.clone())], 2),
        // The same x cannot simultaneously have the pair and encryption heads.
        (vec![fst(x.clone()), sdec(x.clone(), y.clone())], 3),
        (vec![sdec(x.clone(), y.clone()), snd(y.clone())], 4),
        (vec![fst(x.clone())], 2),
    ] {
        let terms: Vec<_> = [ambient.clone(), y.clone(), x.clone()]
            .into_iter()
            .chain(ops)
            .collect();
        let query = f_app_list(terms.clone());
        let observe = |session: &MaudeHandle| {
            let mut signatures = Vec::new();
            for arm in session.variants(&query).unwrap() {
                let subst = Subst::from_list(arm);
                let mut names = BTreeMap::new();
                // Compare every input image AND every reconstructed value,
                // using one renaming throughout the entire variant.
                let values: Vec<_> = terms
                    .iter()
                    .map(|t| {
                        let term = apply_vterm(&subst, t.clone());
                        session.reduce(&term).unwrap().map_free(&mut |v| {
                            let next = names.len() as u64;
                            *names.entry(v).or_insert(LVar::new("w", v.sort, next))
                        })
                    })
                    .collect();
                signatures.push(values);
            }
            signatures.sort();
            signatures
        };
        let reference = observe(&oracle);
        assert_eq!(reference.len(), expected, "{query:?}");
        assert_eq!(observe(&native), reference, "{query:?}");
        // The family is also listed as Maude lists it: the members in the
        // order of Maude's narrowing, and their witnesses under its names.
        let listing = |session: &MaudeHandle| -> Vec<_> {
            session
                .variants(&query)
                .unwrap()
                .into_iter()
                .map(|arm| {
                    crate::subst_vfresh::LSubstVFresh::from_list(arm)
                        .remove_renamings()
                        .to_list()
                })
                .collect()
        };
        assert_eq!(listing(&native), listing(&oracle), "{query:?}");
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn fixed_message_variants_preserve_tls_observers_and_nested_captures() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair, pk, sign, true_const, verify};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig, signature_maude_sig};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = signature_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::ProvedOnly).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 5)));
    let signature = var("sig", LSort::Msg);
    let public_key = var("pk", LSort::Msg);
    let message = var("msg", LSort::Msg);
    let other = var("other", LSort::Msg);
    let fresh = var("fresh", LSort::Fresh);
    let tag = pub_term("tag");
    for m in [
        message.clone(),
        tag.clone(),
        pair(
            tag.clone(),
            hash(pair(other.clone(), pair(message.clone(), other.clone()))),
        ),
        pair(fresh.clone(), message.clone()),
    ] {
        let app = verify(signature.clone(), m.clone(), public_key.clone());
        for packed in [
            app.clone(),
            f_app_list(vec![app.clone(), other.clone(), tag.clone(), app.clone()]),
            f_app_list(vec![
                message.clone(),
                signature.clone(),
                fresh.clone(),
                other.clone(),
                public_key.clone(),
                app,
            ]),
        ] {
            let expected = oracle.variants(&packed).unwrap();
            assert_eq!(expected.len(), 2);
            assert_eq!(
                canonical_variants(native.variants(&packed).unwrap()),
                canonical_variants(expected),
                "{packed:?}"
            );
        }
        let valid = verify(sign(m.clone(), fresh.clone()), m.clone(), pk(fresh.clone()));
        assert_eq!(oracle.reduce(&valid).unwrap(), true_const());
        assert_eq!(native.reduce(&valid).unwrap(), true_const());
        let invalid = verify(
            sign(m.clone(), fresh.clone()),
            hash(m.clone()),
            pk(fresh.clone()),
        );
        assert_eq!(table.reduce(&invalid).unwrap(), None);
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
    for query in [
        verify(
            signature.clone(),
            pair(other.clone(), signature.clone()),
            public_key.clone(),
        ),
        verify(signature.clone(), tag, signature),
        verify(hash(other.clone()), message.clone(), public_key.clone()),
        verify(other, crate::builtin::fst(message), public_key),
    ] {
        assert_eq!(
            table.variants(&query).unwrap(),
            Outcome::Unsupported,
            "{query:?}"
        );
    }
}

#[test]
fn ground_result_narrowing_checks_all_anchor_occurrences_and_the_declared_rhs() {
    use crate::builtin::{hash, pair, true_const};
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig, signature_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::f_app_no_eq;
    let head = NoEqSym::new(
        "checkTwice",
        3,
        Privacy::Public,
        Constructability::Constructor,
    );
    let call = |a, b, c| f_app_no_eq(head, vec![a, b, c]);
    let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let x = var("x");
    let a = pub_term("a");
    let b = pub_term("b");
    let result = pair(true_const(), true_const());
    let mut sig = signature_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    sig.st_fun_syms.insert(head);
    sig.st_rules.insert(CtxtStRule::new(
        call(hash(x.clone()), x.clone(), x.clone()),
        StRhs {
            positions: vec![],
            term: result.clone(),
        },
    ));
    let table = RuleTable::new(&sig).unwrap();
    // Both rigid argument positions refer to the same rule variable. The
    // classifier receives both anchors and declines specialization here.
    assert_eq!(
        table
            .variants(&call(var("z"), a.clone(), b.clone()))
            .unwrap(),
        Outcome::Unsupported
    );
    let valid = call(hash(a.clone()), a.clone(), a.clone());
    assert_eq!(table.reduce(&valid).unwrap(), Some(result));
    assert_eq!(table.reduce(&call(hash(a.clone()), a, b)).unwrap(), None);
    // A closed RHS that contains an active rewrite head is outside this path.
    sig.st_rules.insert(CtxtStRule::new(
        true_const(),
        StRhs {
            positions: vec![],
            term: hash(true_const()),
        },
    ));
    assert_eq!(RuleTable::new(&sig).unwrap().reduce(&valid).unwrap(), None);
}

#[test]
fn common_children_residuals_match_maude_in_sorted_conjunctions() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let variable = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 5)));
    let (u, v, w) = (
        variable("u", LSort::Pub),
        variable("v", LSort::Pub),
        variable("w", LSort::Msg),
    );
    let z = variable("z", LSort::Msg);
    let a = pub_term("a");
    let b = pub_term("b");
    let plus = |children| f_app_ac(AcSym::Union, children);
    let equal = |l, r| Equal { lhs: l, rhs: r };
    let mut checked = 0;
    for common in [
        variable("n", LSort::Fresh),
        pub_term("token"),
        hash(z.clone()),
        pair(z.clone(), hash(u.clone())),
        hash(plus(vec![a.clone(), w.clone()])),
    ] {
        let sides = |l, r| equal(plus(vec![common.clone(), l]), plus(vec![common.clone(), r]));
        let twice = |item| plus(vec![common.clone(), common.clone(), item]);
        for residual in [
            vec![sides(u.clone(), v.clone())],
            vec![sides(hash(u.clone()), hash(v.clone()))],
            vec![sides(w.clone(), plus(vec![u.clone(), v.clone()]))],
            vec![sides(u.clone(), plus(vec![a.clone(), b.clone()]))],
            vec![sides(z.clone(), hash(z.clone()))],
            vec![sides(u.clone(), a.clone()), sides(u.clone(), b.clone())],
            vec![
                equal(twice(u.clone()), twice(v.clone())),
                sides(hash(u.clone()), hash(v.clone())),
            ],
            vec![equal(
                plus(vec![common.clone(), common.clone()]),
                twice(a.clone()),
            )],
            vec![sides(w.clone(), a.clone()), sides(w.clone(), a.clone())],
            vec![
                sides(u.clone(), v.clone()),
                equal(
                    plus(vec![hash(u.clone()), z.clone()]),
                    plus(vec![hash(v.clone()), a.clone()]),
                ),
            ],
        ] {
            for mut eqs in [
                residual.clone(),
                residual
                    .iter()
                    .map(|e| equal(e.rhs.clone(), e.lhs.clone()))
                    .collect(),
            ] {
                eqs.push(equal(variable("k", LSort::Msg), pair(z.clone(), w.clone())));
                assert_same_unifiers(&native, &oracle, &eqs);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 100);
}

#[test]
fn native_oracle_repeated_product_unifies_shared_alien_factors() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, msg_var};
    use crate::maude_sig::hash_maude_sig;
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let (x, a, b, r) = (
        msg_var("x", 0),
        msg_var("a", 1),
        msg_var("b", 2),
        msg_var("r", 3),
    );
    let inputs = f_app_list(vec![x.clone(), a.clone(), b.clone(), r.clone()]);
    let oracle = tamarin_test_support::maude_path()
        .map(|path| MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap());
    for alien in [hash(a.clone()), hash(hash(a.clone()))] {
        let eq = Equal {
            lhs: f_app_ac(AcSym::Union, vec![x.clone(), x.clone()]),
            rhs: f_app_ac(AcSym::Union, vec![r.clone(), a.clone(), b.clone(), alien]),
        };
        let observed = |handle: &MaudeHandle| {
            let projected = handle
                .unify(std::slice::from_ref(&eq))
                .unwrap()
                .into_iter()
                .map(|arm| {
                    let subst = Subst::from_list(arm);
                    assert_eq!(
                        apply_vterm(&subst, eq.lhs.clone()),
                        apply_vterm(&subst, eq.rhs.clone())
                    );
                    vec![(
                        LVar::new("row", LSort::Msg, 0),
                        apply_vterm(&subst, inputs.clone()),
                    )]
                })
                .collect();
            canonical_small_ac_answers(projected)
        };
        let arms = observed(&native);
        assert_eq!(arms.len(), 100);
        if let Some(oracle) = &oracle {
            assert_eq!(arms, observed(oracle));
        }
    }
}

#[test]
fn rigid_allocation_agrees_with_maude_after_factoring_and_reversing_the_query() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::lterm::{fresh_term, Name, NameTag};
    use crate::maude_sig::nat_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(nat_maude_sig())
        .merge(crate::maude_sig::hash_maude_sig())
        .merge(crate::maude_sig::pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let mut count = 0;
    for (symbol, sort, atom) in [
        (AcSym::Union, LSort::Msg, pub_term("a")),
        (AcSym::Union, LSort::Msg, fresh_term("a")),
        (AcSym::Union, LSort::Msg, hash(hash(pub_term("one")))),
        (
            AcSym::NatPlus,
            LSort::Nat,
            Term::Lit(Lit::Con(Name::new(NameTag::Nat, "a"))),
        ),
    ] {
        let v = |name, idx| Term::Lit(Lit::Var(LVar::new(name, sort, idx)));
        for (x, y, z) in [
            (v("x", 0), v("y", 1), v("z", 2)),
            (v("same", 8), v("same", 7), v("same", 6)),
            (v("z", 9), v("y", 9), v("x", 9)),
        ] {
            let xy = f_app_ac(symbol, vec![x.clone(), y.clone()]);
            let za = f_app_ac(symbol, vec![z.clone(), atom.clone()]);
            for (lhs, rhs) in [(&xy, &za), (&za, &xy)] {
                let eq = Equal {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                let alias = Equal {
                    lhs: Term::Lit(Lit::Var(LVar::new("alias", LSort::Msg, 88))),
                    rhs: pair(x.clone(), pair(z.clone(), v("ambient", 550))),
                };
                for eqs in [vec![eq.clone()], vec![eq, alias]] {
                    assert_eq!(assert_same_unifiers(&native, &oracle, &eqs), 4);
                    count += 1;
                }
            }
        }
    }
    assert_eq!(count, 48);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn compound_ground_factors_match_maude_in_both_matching_entry_points() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    // The direct matcher is compared with both of Maude's entry points.
    let a = pub_term("a");
    let b = pub_term("b");
    let terms = [a.clone(), hash(a.clone()), hash(b)];
    let mut checked = 0;
    for sort in [LSort::Msg, LSort::Pub, LSort::Fresh] {
        let x = LVar::new("x", sort, 7);
        let bindable = [(x.name, x.idx)].into_iter().collect();
        for t in &terms {
            let pattern = f_app_ac(AcSym::Union, vec![Term::Lit(Lit::Var(x)), t.clone()]);
            for n in 2..=3 {
                for indices in multisets(n, 0) {
                    let subject = f_app_ac(
                        AcSym::Union,
                        indices.into_iter().map(|i| terms[i].clone()).collect(),
                    );
                    let eq = Equal {
                        lhs: pattern.clone(),
                        rhs: subject.clone(),
                    };
                    let native =
                        crate::lean_unification::match_compound_ground(std::slice::from_ref(&eq))
                            .unwrap();
                    let crate::lean_unification::Outcome::Complete(answer) = native else {
                        panic!("unsupported {eq:?}");
                    };
                    assert_eq!(
                        answer,
                        oracle
                            .match_eqs(&[Equal {
                                lhs: subject,
                                rhs: pattern.clone()
                            }])
                            .unwrap()
                    );
                    assert_eq!(
                        answer,
                        oracle.match_eqs_skolemize_both(&[eq], &bindable).unwrap()
                    );
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 144);
}

#[test]
fn persistent_offsets_agree_with_maude_and_keep_ambient_variables_shared() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 5)));
    let sum = |x, y| f_app_ac(AcSym::Union, vec![x, y]);
    let (x, y, p, q) = (v("x"), v("y"), v("p"), v("q"));
    let alias = Equal {
        lhs: v("alias"),
        rhs: pair(y.clone(), pair(p.clone(), v("unused"))),
    };
    let mut count = 0;
    for (a, b) in [
        (pub_term("one"), hash(p.clone())),
        (hash(p.clone()), pair(q.clone(), p.clone())),
        (pair(p.clone(), p.clone()), hash(sum(q.clone(), p.clone()))),
        (
            hash(sum(p.clone(), pub_term("one"))),
            pair(q.clone(), q.clone()),
        ),
    ] {
        let left = sum(x.clone(), a);
        let right = sum(y.clone(), b);
        for (lhs, rhs) in [(&left, &right), (&right, &left)] {
            let single = Equal {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            };
            for eqs in [vec![single.clone()], vec![alias.clone(), single]] {
                assert_eq!(assert_same_unifiers(&native, &oracle, &eqs), 2);
                count += 1;
            }
        }
    }
    assert_eq!(count, 16);
}

#[test]
fn dependent_allocation_keeps_the_same_witness_inside_every_rigid_factor() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig};

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 5)));
    let (x, y, z, alias) = (var("x"), var("y"), var("z"), var("alias"));
    let plus = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let mut checked = 0;
    for dependent in [&x, &y] {
        for factor in [
            hash(dependent.clone()),
            pair(dependent.clone(), hash(dependent.clone())),
            hash(plus(dependent.clone(), pub_term("a"))),
        ] {
            let xy = plus(x.clone(), y.clone());
            let zf = plus(z.clone(), factor);
            for (lhs, rhs) in [(&xy, &zf), (&zf, &xy)] {
                let eqs = vec![
                    Equal {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                    },
                    Equal {
                        lhs: alias.clone(),
                        rhs: pair(dependent.clone(), z.clone()),
                    },
                ];
                // Each arm is applied to the query, so a factor that lost the
                // shared witness would no longer unify it.
                assert_eq!(assert_same_unifiers(&native, &oracle, &eqs), 2);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 12);
}

#[test]
fn commutative_branches_agree_with_maude_in_the_original_query_scope() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash, pair};
    use crate::lterm::fresh_term;
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let signature = bp_maude_sig()
        .merge(dh_maude_sig())
        .merge(mset_maude_sig())
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(signature.clone());
    let oracle = MaudeHandle::start_with_backend(&path, signature, AlgebraBackend::Maude).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 17)));
    let (x, y, z, u) = (
        var("x", LSort::Msg),
        var("y", LSort::Msg),
        var("z", LSort::Msg),
        var("u", LSort::Msg),
    );
    let a = pub_term("same");
    let b = fresh_term("same");
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let plus = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let skolem = pub_term(format!("{}example", crate::maude_types::SKOLEM_MSG_PREFIX));
    let mut tested = 0;
    for residual in [
        vec![eq(
            emap(var("p", LSort::Pub), var("q", LSort::Msg)),
            emap(a.clone(), skolem.clone()),
        )],
        vec![eq(
            emap(var("p", LSort::Pub), var("q", LSort::Pub)),
            emap(a.clone(), skolem.clone()),
        )],
        vec![eq(emap(x.clone(), y.clone()), emap(z.clone(), u.clone()))],
        vec![eq(emap(x.clone(), a.clone()), emap(y.clone(), a.clone()))],
        vec![eq(emap(x.clone(), x.clone()), emap(z.clone(), u.clone()))],
        vec![eq(emap(x.clone(), x.clone()), emap(a.clone(), b.clone()))],
        vec![eq(
            emap(hash(x.clone()), x.clone()),
            emap(hash(y.clone()), z.clone()),
        )],
        vec![
            eq(emap(x.clone(), y.clone()), emap(a.clone(), b.clone())),
            eq(emap(y.clone(), z.clone()), emap(b.clone(), a.clone())),
        ],
        vec![eq(
            emap(emap(x.clone(), y.clone()), z.clone()),
            emap(emap(a.clone(), b.clone()), a.clone()),
        )],
        vec![eq(
            emap(hash(x.clone()), hash(x.clone())),
            emap(hash(y.clone()), hash(z.clone())),
        )],
        vec![eq(
            emap(var("f", LSort::Fresh), var("p", LSort::Pub)),
            emap(a.clone(), b.clone()),
        )],
        vec![eq(
            emap(var("f", LSort::Fresh), var("p", LSort::Pub)),
            emap(a.clone(), a.clone()),
        )],
        vec![eq(
            emap(plus(x.clone(), a.clone()), x.clone()),
            emap(plus(a.clone(), b.clone()), b.clone()),
        )],
        vec![eq(
            emap(plus(x.clone(), a.clone()), hash(x.clone())),
            emap(plus(y.clone(), b.clone()), hash(u.clone())),
        )],
    ] {
        for mut eqs in [
            residual.clone(),
            residual
                .iter()
                .map(|e| eq(e.rhs.clone(), e.lhs.clone()))
                .collect(),
        ] {
            for with_alias in [false, true] {
                if with_alias {
                    eqs.push(eq(
                        var("alias", LSort::Msg),
                        pair(x.clone(), var("ambient", LSort::Msg)),
                    ));
                }
                // An orientation that only repeats an instance of the other
                // one is listed by the proved export and dropped by Maude.
                assert_same_minimal_unifiers(&native, &oracle, &eqs);
                tested += 1;
            }
        }
    }
    assert_eq!(tested, 56);
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn cancellation_exposing_commutative_roots_agrees_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash, pair};
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(bp_maude_sig())
        .merge(dh_maude_sig())
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 17)));
    let sum = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let common = hash(v("ambient"));
    let left = sum(common.clone(), emap(v("x"), v("y")));
    let right = sum(common.clone(), emap(v("s"), v("t")));
    let alias = eq(
        sum(common.clone(), v("k")),
        sum(common.clone(), pair(v("x"), v("ambient"))),
    );
    let mut tested = 0;
    for (overlap, q) in [
        (false, eq(left.clone(), right.clone())),
        (
            true,
            eq(
                emap(hash(v("x")), left.clone()),
                emap(hash(v("s")), right.clone()),
            ),
        ),
        (
            false,
            eq(emap(hash(v("p")), left), emap(hash(v("q")), right)),
        ),
    ] {
        for single in [q.clone(), eq(q.rhs.clone(), q.lhs.clone())] {
            for qs in [
                vec![single.clone()],
                vec![alias.clone(), single.clone()],
                vec![single, alias.clone()],
            ] {
                let actual = unifier_rows(&qs, native.unify(&qs).unwrap());
                let maude = unifier_rows(&qs, oracle.unify(&qs).unwrap());
                assert_eq!(actual.len(), 2);
                assert_eq!(actual, maude, "{qs:?}");
                // x=s is already known when C(x,y)=C(s,t) becomes visible. The
                // second arm is then the diagonal x=y=s=t, an instance of the
                // general arm in *all* its images, including the alias.
                assert_eq!(minimal_rows(actual).len(), if overlap { 1 } else { 2 });
                tested += 1;
            }
        }
    }
    assert_eq!(tested, 18);
}

#[test]
fn natural_kind_probes_agree_with_maude_before_free_elimination() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::nat_plus;
    use crate::function_symbols::nat_one_sym;
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::nat_maude_sig;
    use crate::term::{f_app_list, f_app_no_eq};

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = nat_maude_sig();
    let table = RuleTable::new(&sig).unwrap();
    let native =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::ProvedOnly).unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let one = f_app_no_eq(nat_one_sym(), vec![]);
    let nat = var("n", LSort::Nat);
    let natural = nat_plus(nat.clone(), one.clone());
    let eq = |lhs, rhs| Equal { lhs, rhs };
    for sort in [LSort::Pub, LSort::Fresh] {
        let w = LVar::new("w", sort, 0);
        let v = Term::Lit(Lit::Var(w));
        let raw = nat_plus(v.clone(), one.clone());
        let query = f_app_list(vec![v, raw.clone(), raw.clone()]);
        assert_eq!(
            table.variants(&query).unwrap(),
            Outcome::Complete(vec![vec![]])
        );
        let answers = oracle.variants(&query).unwrap();
        let [variant] = answers.as_slice() else {
            panic!("{answers:?}")
        };
        assert!(
            matches!(variant.as_slice(), [(x, Term::Lit(Lit::Var(y)))] if *x == w && y.sort == sort)
        );
        for good in [natural.clone(), nat.clone(), var("m", LSort::Msg)] {
            for query in [eq(raw.clone(), good.clone()), eq(good, raw.clone())] {
                let qs = [query];
                assert!(native.unify(&qs).unwrap().is_empty());
                assert!(oracle.unify(&qs).unwrap().is_empty());
            }
        }
        let qs = [eq(raw.clone(), nat_plus(var("other", sort), one.clone()))];
        assert!(!native.unify(&qs).unwrap().is_empty());
        assert!(!oracle.unify(&qs).unwrap().is_empty());
    }
    let qs = [eq(nat_plus(var("m", LSort::Msg), one), natural)];
    assert!(!native.unify(&qs).unwrap().is_empty());
    assert!(!oracle.unify(&qs).unwrap().is_empty());
    assert!(oracle.stats().unify_count > 0);
}

#[test]
fn dh_reconstructs_each_maude_peer_variant_in_its_original_tuple() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::exp;
    use crate::lean_unification::RuleTable;
    use crate::maude_sig::dh_maude_sig;
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig();
    let table = RuleTable::new(&sig).unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |s, sort| Term::Lit(Lit::Var(LVar::new(s, sort, 7)));
    let peer = v("peer", LSort::Msg);
    let r = v("r", LSort::Fresh);
    let pow = exp(peer.clone(), r.clone());
    for mut obs in [
        vec![
            r.clone(),
            v("a", LSort::Msg),
            v("b", LSort::Msg),
            peer.clone(),
            v("t", LSort::Msg),
        ],
        vec![
            peer.clone(),
            pow.clone(),
            exp(pub_term("g"), r.clone()),
            r.clone(),
        ],
    ] {
        obs.push(pow.clone());
        let arms = oracle.variants(&f_app_list(obs.clone())).unwrap();
        let crate::lean_unification::Outcome::Complete(native) =
            table.variants(&f_app_list(obs.clone())).unwrap()
        else {
            panic!("expected a seven-arm candidate");
        };
        assert_eq!(arms.len(), 7);
        assert_eq!(native.len(), arms.len());
        for (candidate, arm) in native.into_iter().zip(arms) {
            // Keep arm order observable while allowing fresh-range renaming.
            assert_eq!(
                canonical_variants(vec![candidate]),
                canonical_variants(vec![arm.clone()])
            );
            // Apply once, simultaneously, to preserve the relationship between
            // the observed fresh exponent and any inverse in the peer image.
            let subst = Subst::from_list(arm);
            for original in &obs {
                let instance = apply_vterm(&subst, original.clone());
                let reference = oracle.reduce(&instance).unwrap();
                assert_eq!(
                    table.reduce(&instance).unwrap(),
                    Some(reference),
                    "{instance:?}"
                );
            }
        }
    }
    assert!(oracle.stats().norm_count > 0);
}

#[test]
fn native_oracle_received_base_towers_cover_all_cancellation_subsets() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, hash, inv, mult};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 1)));
    let base = var("x", LSort::Msg);
    let a = var("a", LSort::Fresh);
    let b = var("b", LSort::Fresh);
    let c = hash(var("x", LSort::Pub));
    for (power, expected_count) in [
        (exp(exp(base.clone(), b.clone()), a.clone()), 15),
        (exp(base.clone(), mult(a.clone(), b.clone())), 15),
        (exp(exp(base.clone(), a.clone()), a.clone()), 11),
        (
            exp(exp(base.clone(), c.clone()), mult(a.clone(), b.clone())),
            31,
        ),
    ] {
        let observations = vec![
            base.clone(),
            a.clone(),
            b.clone(),
            power.clone(),
            c.clone(),
            power,
        ];
        let query = f_app_list(observations.clone());
        let rows = native.variants(&query).unwrap();
        let reference = oracle.variants(&query).unwrap();
        assert_eq!(reference.len(), expected_count);
        assert_eq!(rows.len(), expected_count);
        assert_eq!(
            canonical_variants(rows.clone()),
            canonical_variants(reference)
        );
        for row in rows {
            let subst = Subst::from_list(row);
            for t in &observations {
                let instance = apply_vterm(&subst, t.clone());
                assert_eq!(
                    native
                        .reduce(&instance)
                        .unwrap_or_else(|err| panic!("{instance:?}: {err}")),
                    oracle.reduce(&instance).unwrap()
                );
            }
        }
    }
    let deep = (0..8).fold(base.clone(), |t, _| exp(t, a.clone()));
    for (tower, count) in [(deep.clone(), 35), (exp(deep, a.clone()), 39)] {
        let slots = [tower, base.clone(), a.clone()];
        let expected = valued_variant_rows(&oracle, &slots);
        assert_eq!(expected.len(), count);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
    }
    for (exponent, count) in [
        (base.clone(), 12),
        (inv(a.clone()), 1),
        (hash(base.clone()), 7),
        (var("arbitrary", LSort::Msg), 160),
    ] {
        let slots = [exp(exp(base.clone(), a.clone()), exponent)];
        let expected = valued_variant_rows(&oracle, &slots);
        assert_eq!(expected.len(), count);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
    }
}

#[test]
fn native_oracle_free_exponent_preserves_joint_gdh_observations() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, fst, hash, inv, mult, pair};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig, pair_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 1)));
    let y = var("x", LSort::Msg);
    let r = var("r", LSort::Fresh);
    let a = var("a", LSort::Pub);
    let g = pub_term("g");
    let power = exp(g.clone(), y.clone());
    let tower = exp(power.clone(), r.clone());
    // The first assertion uses the complete rule-variant query from sp14/GDH.
    let corpus = vec![
        pub_term("one"),
        pub_term("two"),
        pub_term("three"),
        a.clone(),
        var("b", LSort::Pub),
        var("c", LSort::Pub),
        r.clone(),
        var("z", LSort::Msg),
        var("w", LSort::Msg),
        var("v", LSort::Msg),
        y.clone(),
        power.clone(),
        tower.clone(),
    ];
    let full_rows = |rows: crate::lean_unification::Substitutions| {
        let mut canonical: Vec<_> = rows
            .into_iter()
            .map(|row| {
                crate::subst_vfresh::LSubstVFresh::from_list(row)
                    .drop_name_hints()
                    .to_list()
            })
            .collect();
        canonical.sort();
        canonical
    };
    let h = hash(a.clone());
    let product = mult(y.clone(), h.clone());
    let projection = fst(pair(y.clone(), var("hidden", LSort::Msg)));
    for obs in [
        corpus,
        vec![product.clone()],
        vec![projection.clone(), product.clone(), power.clone()],
        vec![hash(projection.clone()), product.clone(), power.clone()],
        vec![
            pair(hash(product.clone()), projection.clone()),
            hash(power.clone()),
        ],
        vec![
            product.clone(),
            y.clone(),
            exp(a.clone(), product.clone()),
            exp(exp(g.clone(), y.clone()), h.clone()),
            h.clone(),
            a.clone(),
            exp(hash(y.clone()), product.clone()),
            product.clone(),
        ],
        vec![tower.clone(), tower.clone(), power.clone()],
    ] {
        let query = f_app_list(obs.clone());
        assert_eq!(table.variants(&query).unwrap(), Outcome::Unsupported);
        let rows = native.variants(&query).unwrap();
        let reference = oracle.variants(&query).unwrap();
        assert_eq!(reference.len(), 6, "{query:?}");
        assert_eq!(rows.len(), reference.len());
        assert_eq!(full_rows(rows.clone()), full_rows(reference), "{query:?}");
        for row in rows {
            let subst = Subst::from_list(row);
            for t in &obs {
                let instance = apply_vterm(&subst, t.clone());
                assert_eq!(
                    native
                        .reduce(&instance)
                        .unwrap_or_else(|err| panic!("{instance:?}: {err}")),
                    oracle.reduce(&instance).unwrap(),
                    "{instance:?}"
                );
            }
        }
    }
    for query in [power.clone(), exp(power.clone(), hash(y.clone()))] {
        let slots = [query];
        let expected = valued_variant_rows(&oracle, &slots);
        assert_eq!(expected.len(), 2);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
    }
    for (slots, count) in [
        (vec![tower.clone(), exp(power.clone(), a.clone())], 14),
        (vec![exp(power.clone(), inv(r.clone()))], 6),
        (
            vec![tower.clone(), exp(g.clone(), var("other", LSort::Msg))],
            12,
        ),
    ] {
        let expected = valued_variant_rows(&oracle, &slots);
        assert_eq!(expected.len(), count);
        assert_eq!(valued_variant_rows(&native, &slots), expected);
    }
    let base = var("base", LSort::Msg);
    for app in [
        exp(exp(base.clone(), y.clone()), r.clone()),
        exp(base.clone(), mult(y.clone(), r)),
    ] {
        for slots in [
            [app.clone(), base.clone(), y.clone()],
            [y.clone(), base.clone(), app.clone()],
        ] {
            let expected = valued_variant_rows(&oracle, &slots);
            assert_eq!(expected.len(), 160);
            assert_eq!(valued_variant_rows(&native, &slots), expected);
        }
    }
}

#[test]
fn native_oracle_mixed_uniform_reductions_and_dh_powers_preserve_all_query_bindings() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, fst, pair};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{dh_maude_sig, pair_maude_sig};
    use crate::rewriting::RRule;
    use crate::subst::{apply_vterm, Subst};
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(pair_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let y = var("base", LSort::Msg);
    let a = var("a", LSort::Fresh);
    let b = var("b", LSort::Fresh);
    let hidden = LVar::new("x", LSort::Msg, 41);
    let erased = fst(pair(b.clone(), Term::Lit(Lit::Var(hidden))));
    let tower = exp(exp(pub_term("g"), a.clone()), b.clone());
    let peer = exp(y.clone(), a.clone());
    for observed in [
        vec![erased.clone(), tower.clone(), peer.clone(), tower.clone()],
        vec![pair(erased.clone(), b.clone()), peer.clone()],
        vec![pair(peer.clone(), erased.clone()), tower.clone()],
        vec![
            peer.clone(),
            tower.clone(),
            erased.clone(),
            exp(y.clone(), b.clone()),
        ],
    ] {
        let query = f_app_list(observed.clone());
        assert_eq!(table.variants(&query).unwrap(), Outcome::Unsupported);
        let arms = native.variants(&query).unwrap();
        assert!(arms.len() >= 7);
        let expected = oracle.variants(&query).unwrap();
        assert_eq!(
            canonical_variants(arms.clone()),
            canonical_variants(expected)
        );
        for arm in arms {
            assert!(arm.iter().any(|(k, image)| *k == hidden && matches!(image, Term::Lit(Lit::Var(v)) if v.sort == hidden.sort && *v != hidden)));
            let subst = Subst::from_list(arm);
            for t in &observed {
                let instance = apply_vterm(&subst, t.clone());
                assert_eq!(
                    native.reduce(&instance).unwrap(),
                    oracle.reduce(&instance).unwrap()
                );
            }
        }
    }

    // Both free-root rules match this observation. Dropping it would hide
    // the two different possible observed values after specialization.
    let x = var("x", LSort::Msg);
    let z = var("z", LSort::Msg);
    let extra = RRule::new(fst(pair(x, z.clone())), z);
    let mut overlap = sig;
    overlap
        .st_rules
        .insert(rrule_to_ctxt_st_rule(&extra).unwrap());
    let table = RuleTable::new(&overlap).unwrap();
    assert_eq!(
        table
            .joined_variants(&f_app_list(vec![erased, peer, tower]))
            .unwrap(),
        Outcome::Unsupported
    );
}

#[test]
fn dh_public_values_and_fresh_products_agree_with_maude_as_one_variant_tuple() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, hash, inv, mult};
    use crate::lterm::fresh_term;
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let fresh = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Fresh, 0)));
    let mut count = 0;
    for base in [pub_term("g"), hash(pub_term("seed"))] {
        for x in [fresh("x"), fresh_term("alice")] {
            for y in [x.clone(), fresh("y"), fresh_term("bob")] {
                let tower = exp(exp(base.clone(), x.clone()), y.clone());
                let value = exp(base.clone(), mult(x.clone(), y.clone()));
                let tuple = f_app_list(vec![
                    x.clone(),
                    y.clone(),
                    tower.clone(),
                    inv(y.clone()),
                    tower.clone(),
                ]);
                assert_eq!(oracle.reduce(&tower).unwrap(), value);
                assert_eq!(native.reduce(&tower).unwrap(), value);
                let reference = canonical_variants(oracle.variants(&tuple).unwrap());
                assert_eq!(reference, vec![vec![]]);
                assert_eq!(native.variants(&tuple).unwrap(), reference);
                count += 1;
            }
        }
    }
    assert_eq!(count, 12);
    assert_eq!(native.stats().norm_count, 0);
    assert_eq!(native.stats().var_count, 0);

    // The same exponent with an arbitrary message as base admits neutral,
    // exponentiation and inverse-cancellation instances. Returning only the
    // identity for this mixed tuple would lose legal protocol instances.
    let msg = Term::Lit(Lit::Var(LVar::new("received", LSort::Msg, 0)));
    let r = fresh("r");
    let open = f_app_list(vec![msg.clone(), r.clone(), exp(msg, r.clone())]);
    let expected = canonical_variants(oracle.variants(&open).unwrap());
    assert!(expected.len() > 1);
    assert_eq!(
        canonical_variants(native.variants(&open).unwrap()),
        expected
    );
    let g = pub_term("g");
    let cancel = exp(exp(g.clone(), inv(r.clone())), r);
    assert_eq!(oracle.reduce(&cancel).unwrap(), g);
    assert_eq!(native.reduce(&cancel).unwrap(), g);
}

#[test]
fn fresh_xor_variant_substitutions_and_reductions_agree_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{xor, zero_const};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::xor_maude_sig;
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = xor_maude_sig();
    let theory = RuleTable::new(&sig).unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let fresh = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Fresh, idx)));
    let mut checked = 0;
    for (x, y) in [
        (fresh("a", 7), fresh("b", 7)),
        (fresh("x", 12), fresh("x", 19)),
        (fresh("r", 9), fresh("r", 9)),
    ] {
        let term = xor(x.clone(), y.clone());
        let normal = theory.fresh_xor_reduce(&term).unwrap().unwrap();
        assert_eq!(normal, if x == y { zero_const() } else { term.clone() });
        assert_eq!(normal, oracle.reduce(&term).unwrap());
        for q in [
            term.clone(),
            f_app_list(vec![x.clone(), y.clone(), term.clone()]),
            f_app_list(vec![term.clone(), y.clone(), term.clone(), x.clone()]),
            f_app_list(vec![term.clone(), term.clone()]),
        ] {
            let Outcome::Complete(arms) = theory.fresh_xor_variants(&q).unwrap() else {
                panic!()
            };
            assert_eq!(arms.len(), if x == y { 1 } else { 2 });
            assert_eq!(
                canonical_variants(arms),
                canonical_variants(oracle.variants(&q).unwrap()),
                "{q:?}"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 12);
}

#[test]
fn flat_fresh_xor_matches_maude_variants_and_every_reconstructed_value() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::zero_const;
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::lterm::fresh_term;
    use crate::maude_sig::xor_maude_sig;
    use crate::subst::{apply_vterm, Subst};

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = xor_maude_sig();
    let theory = RuleTable::new(&sig).unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let vars: Vec<_> = (0..6)
        .map(|i| Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, i))))
        .collect();
    let cases: &[(&[usize], usize)] = &[
        (&[0, 1, 2], 4),
        (&[0, 1, 2, 3], 10),
        (&[0, 1, 2, 3, 4], 26),
        (&[0, 1, 2, 3, 4, 5], 76),
        (&[0, 1, 0, 1], 1),
        (&[0, 1, 0], 1),
        (&[2, 0, 2, 1, 0, 0], 2),
        (&[2, 0, 1, 2, 1, 2, 1], 4),
    ];
    for &(indices, count) in cases {
        // Bypass the smart constructor so the parity pass also sees unsorted
        // and nonadjacent equal operands, as allowed by the term type.
        let args: Vec<_> = indices.iter().map(|&i| vars[i].clone()).collect();
        let query = Term::App(FunSym::Ac(AcSym::Xor), args.into());
        let Outcome::Complete(answers) = theory.fresh_xor_variants(&query).unwrap() else {
            panic!("missing flat XOR variants for {indices:?}");
        };
        assert_eq!(answers.len(), count, "{indices:?}");
        assert_eq!(
            canonical_variants(answers.clone()),
            canonical_variants(oracle.variants(&query).unwrap()),
            "{indices:?}"
        );
        for arm in answers {
            let instance = apply_vterm(&Subst::from_list(arm), query.clone());
            assert_eq!(
                theory.reduce_native(&instance).unwrap().unwrap(),
                oracle.reduce(&instance).unwrap(),
                "{indices:?}: {instance:?}"
            );
        }
    }

    let name = fresh_term("n");
    let other = fresh_term("m");
    let x = vars[0].clone();
    for (args, expected) in [
        (vec![name.clone(), x.clone(), name.clone()], x.clone()),
        (
            vec![x.clone(), name.clone(), x.clone(), name.clone()],
            zero_const(),
        ),
        (
            vec![other.clone(), x.clone(), name.clone(), x.clone()],
            f_app_ac(AcSym::Xor, vec![name, other]),
        ),
    ] {
        let raw = Term::App(FunSym::Ac(AcSym::Xor), args.into());
        assert_eq!(theory.reduce_native(&raw).unwrap(), Some(expected.clone()));
        assert_eq!(oracle.reduce(&raw).unwrap(), expected);
    }
}

#[test]
fn flat_fresh_xor_checks_width_after_parity_and_requires_the_active_xor_rules() {
    use crate::builtin::xor;
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::xor_maude_sig;
    use crate::rewriting::RRule;
    use crate::subst::{apply_vterm, Subst};
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use std::collections::{BTreeMap, BTreeSet};

    let sig = xor_maude_sig();
    let theory = RuleTable::new(&sig).unwrap();
    let vars: Vec<_> = (0..10)
        .map(|i| Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, i))))
        .collect();
    let all = f_app_ac(AcSym::Xor, vars.clone());
    // Wider coverage is allowed, but exhausting a budget cannot publish
    // a prefix of the 9,496 distinct width-ten matchings.
    if let Outcome::Complete(rows) = theory.fresh_xor_variants(&all).unwrap() {
        assert_eq!(
            canonical_variants(rows)
                .into_iter()
                .collect::<BTreeSet<_>>()
                .len(),
            9496
        );
    }
    let occupied = LVar::new("x", LSort::Fresh, u64::MAX);
    let edge = f_app_ac(
        AcSym::Xor,
        vec![
            vars[0].clone(),
            vars[1].clone(),
            Term::Lit(Lit::Var(occupied)),
        ],
    );
    let Outcome::Complete(boundary) = theory.fresh_xor_variants(&edge).unwrap() else {
        panic!("fresh witnesses fit below the occupied highest index");
    };
    assert_eq!(boundary.len(), 4);
    for (key, image) in boundary.into_iter().flatten() {
        let Term::Lit(Lit::Var(w)) = image else {
            panic!("expected Fresh witness");
        };
        assert_ne!(key, w);
        assert!(![0, 1, u64::MAX].contains(&w.idx));
    }
    let mut cancelled = vars.clone();
    cancelled.push(vars[9].clone());
    let Outcome::Complete(arms) = theory
        .fresh_xor_variants(&f_app_ac(AcSym::Xor, cancelled))
        .unwrap()
    else {
        panic!("nine odd operands after cancellation must be covered");
    };
    // Count partitions independently of the solver's choice of witnesses or
    // explicit identity bindings. The tenth variable cancels and stays free.
    let mut matchings = BTreeSet::new();
    for arm in arms {
        let sub = Subst::from_list(arm);
        let mut classes = BTreeMap::<LVar, Vec<usize>>::new();
        for (i, v) in vars.iter().enumerate() {
            let Term::Lit(Lit::Var(w)) = apply_vterm(&sub, v.clone()) else {
                panic!("expected a fresh variable image");
            };
            assert_eq!(w.sort, LSort::Fresh);
            classes.entry(w).or_default().push(i);
        }
        let mut pairs = Vec::new();
        for class in classes.into_values() {
            match class.as_slice() {
                [_] => {}
                &[a, b] if b < 9 => pairs.push((a, b)),
                _ => panic!("unexpected matching class {class:?}"),
            }
        }
        pairs.sort_unstable();
        assert!(matchings.insert(pairs), "duplicate matching");
    }
    assert_eq!(matchings.len(), 2620);

    let mixed = f_app_ac(
        AcSym::Xor,
        vec![vars[0].clone(), vars[1].clone(), pub_term("p")],
    );
    assert_eq!(
        theory.fresh_xor_variants(&mixed).unwrap(),
        Outcome::Unsupported
    );
    assert_eq!(theory.fresh_xor_reduce(&mixed).unwrap(), None);

    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 0)));
    let mut altered = sig;
    altered
        .st_rules
        .insert(rrule_to_ctxt_st_rule(&RRule::new(xor(x.clone(), y), x)).unwrap());
    let altered = RuleTable::new(&altered).unwrap();
    let triple = f_app_ac(AcSym::Xor, vars[..3].to_vec());
    assert_eq!(
        altered.fresh_xor_variants(&triple).unwrap(),
        Outcome::Unsupported
    );
    assert_eq!(altered.fresh_xor_reduce(&triple).unwrap(), None);
}

#[test]
fn native_oracle_joint_fresh_xors_cover_shared_inputs_and_triangle() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{xor, zero_const};
    use crate::lterm::fresh_term;
    use crate::maude_sig::xor_maude_sig;
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    use std::collections::BTreeMap;

    let sig = xor_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let vars = [4, 5, 6].map(|i| LVar::new("x", LSort::Fresh, i));
    let [a, b, c] = vars.map(|v| Term::Lit(Lit::Var(v)));
    let ab = xor(a.clone(), b.clone());
    let bc = xor(b.clone(), c.clone());
    let ca = xor(c.clone(), a.clone());
    // x6 is precisely the first diagonal witness of the isolated x4 ⊕ x5 call.
    // In the tuple it is an independent caller variable.
    let oracle = require_maude_path()
        .map(|path| MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap());
    for (edges, count) in [
        (vec![ab.clone(), bc.clone()], 4),
        (vec![ab.clone(), bc.clone(), ca.clone()], 5),
        (vec![ca.clone(), bc.clone(), ab.clone(), ca], 5),
    ] {
        let query = f_app_list(
            [a.clone(), b.clone(), c.clone()]
                .into_iter()
                .chain(edges.iter().cloned())
                .collect(),
        );
        let arms = native.variants(&query).unwrap();
        assert_eq!(arms.len(), count);
        if let Some(reference) = &oracle {
            assert_eq!(
                canonical_variants(arms.clone()),
                canonical_variants(reference.variants(&query).unwrap())
            );
        }
        // Compute the concrete XOR values independently. Every assignment to
        // the three variables must factor through a single returned row with
        // the same normal values at all positions, using only substitution.
        let observations = arms
            .into_iter()
            .map(|arm| {
                let subst = Subst::from_list(arm);
                let images = vars.map(|v| {
                    let Term::Lit(Lit::Var(w)) = apply_vterm(&subst, Term::Lit(Lit::Var(v))) else {
                        panic!("a fresh XOR input needs a fresh leaf");
                    };
                    assert_eq!(w.sort, LSort::Fresh);
                    w
                });
                let values = edges
                    .iter()
                    .map(|t| native.reduce(&apply_vterm(&subst, t.clone())).unwrap())
                    .collect::<Vec<_>>();
                (images, values)
            })
            .collect::<Vec<_>>();
        for ordinal in 0..27 {
            let indices = [ordinal % 3, ordinal / 3 % 3, ordinal / 9];
            let leaves = indices.map(|i| fresh_term(format!("a{i}")));
            let ground = Subst::from_list(vars.into_iter().zip(leaves.clone()));
            let expected = edges
                .iter()
                .map(|t| {
                    let Term::App(_, args) = apply_vterm(&ground, t.clone()) else {
                        unreachable!()
                    };
                    if args[0] == args[1] {
                        zero_const()
                    } else {
                        xor(args[0].clone(), args[1].clone())
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(
                observations
                    .iter()
                    .filter(|(images, values)| {
                        let mut common = BTreeMap::new();
                        for (w, t) in images.iter().zip(&leaves) {
                            if let Some(prior) = common.insert(*w, t.clone())
                                && prior != *t
                            {
                                return false;
                            }
                        }
                        let instance = Subst::from_list(common);
                        values
                            .iter()
                            .map(|t| apply_vterm(&instance, t.clone()))
                            .eq(expected.iter().cloned())
                    })
                    .count(),
                1,
                "assignment {indices:?}"
            );
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_joint_fresh_xor_and_dh_variants_preserve_the_shared_exponent() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, xor};
    use crate::maude_sig::{dh_maude_sig, xor_maude_sig};
    use crate::term::f_app_list;

    let sig = dh_maude_sig().merge(xor_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = require_maude_path()
        .map(|path| MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap());
    let var = |index, sort| Term::Lit(Lit::Var(LVar::new("x", sort, index)));
    let y = var(1, LSort::Msg);
    let a = var(2, LSort::Fresh);
    let b = var(3, LSort::Fresh);
    let power = exp(y.clone(), a.clone());
    let sum = xor(a.clone(), b.clone());
    for observations in [[power.clone(), sum.clone()], [sum, power]] {
        let query = f_app_list(
            [y.clone(), a.clone(), b.clone()]
                .into_iter()
                .chain(observations)
                .collect(),
        );
        let actual = native.variants(&query).unwrap();
        assert_eq!(actual.len(), 14);
        if let Some(reference) = &oracle {
            assert_eq!(
                canonical_small_ac_answers(actual),
                canonical_small_ac_answers(reference.variants(&query).unwrap())
            );
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn binary_ac_with_two_fresh_factors_uses_sorted_simultaneous_orientations() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::lterm::fresh_term;
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig, pair_maude_sig, xor_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = xor_maude_sig()
        .merge(mset_maude_sig())
        .merge(dh_maude_sig())
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |n, s| Term::Lit(Lit::Var(LVar::new(n, s, 0)));
    let (f, g, x, y) = (
        v("f", LSort::Fresh),
        v("g", LSort::Fresh),
        v("x", LSort::Msg),
        v("y", LSort::Msg),
    );
    let mut checked = 0;
    for symbol in [AcSym::Xor, AcSym::Union, AcSym::Mult] {
        let sum = |a, b| f_app_ac(symbol, vec![a, b]);
        for (l, r) in [
            (sum(f.clone(), g.clone()), sum(x.clone(), y.clone())),
            (sum(f.clone(), f.clone()), sum(x.clone(), y.clone())),
            (sum(f.clone(), g.clone()), sum(x.clone(), x.clone())),
            (
                sum(f.clone(), g.clone()),
                sum(fresh_term("a"), fresh_term("b")),
            ),
            (sum(f.clone(), g.clone()), sum(y.clone(), pub_term("a"))),
            (sum(f.clone(), g.clone()), sum(x.clone(), hash(y.clone()))),
        ] {
            for (lhs, rhs) in [(&l, &r), (&r, &l)] {
                let eqs = [
                    Equal {
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                    },
                    Equal {
                        lhs: v("alias", LSort::Msg),
                        rhs: pair(f.clone(), x.clone()),
                    },
                ];
                assert_same_unifiers(&native, &oracle, &eqs);
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 36);
}

#[test]
fn reflexive_conjunctions_and_one_differing_row_agree_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash, pair};
    use crate::lterm::fresh_term;
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(bp_maude_sig())
        .merge(dh_maude_sig())
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 42)));
    let ac = |terms: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::Union), terms.into());
    let raw_c = |a, b| {
        Term::App(
            FunSym::C(crate::function_symbols::CSym::EMap),
            vec![a, b].into(),
        )
    };
    let (x, y) = (v("x", LSort::Msg), v("y", LSort::Msg));
    let (a, b) = (pub_term("a"), fresh_term("a"));
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let ac_left = ac(vec![x.clone(), ac(vec![a.clone(), b.clone()]), x.clone()]);
    let ac_right = ac(vec![b.clone(), x.clone(), x.clone(), a.clone()]);
    let base = [
        eq(hash(ac_left), hash(ac_right)),
        eq(
            raw_c(x.clone(), v("x", LSort::Pub)),
            raw_c(v("x", LSort::Pub), x.clone()),
        ),
        eq(pair(x.clone(), y.clone()), pair(x.clone(), y.clone())),
    ];
    for p in [
        vec![],
        vec![base[0].clone()],
        base.to_vec(),
        base.iter().cloned().rev().collect(),
    ] {
        assert_eq!(
            canonical_variants(native.unify(&p).unwrap()),
            vec![vec![]],
            "{p:?}"
        );
        let maude = canonical_variants(oracle.unify(&p).unwrap());
        assert!(maude.contains(&vec![]), "{p:?}");
    }
    for different in [
        eq(x.clone(), y.clone()),
        eq(x.clone(), v("x", LSort::Fresh)),
        eq(a.clone(), b.clone()),
        eq(hash(x.clone()), hash(y.clone())),
        eq(pair(a.clone(), b.clone()), pair(b.clone(), a.clone())),
        eq(emap(a.clone(), b.clone()), ac(vec![a.clone(), b.clone()])),
        eq(
            ac(vec![a.clone(), a.clone(), b.clone()]),
            ac(vec![a.clone(), b.clone()]),
        ),
    ] {
        let mut qs = base.to_vec();
        qs.push(different);
        let reference = canonical_variants(oracle.unify(&qs).unwrap());
        assert!(!reference.contains(&vec![]));
        assert_eq!(
            canonical_variants(native.unify(&qs).unwrap()),
            reference,
            "{qs:?}"
        );
    }
}

#[test]
fn ground_contradiction_decides_a_conjunction_with_open_equations() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash, pair};
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(bp_maude_sig())
        .merge(dh_maude_sig())
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let sum = |x, y| f_app_ac(AcSym::Union, vec![x, y]);
    let eq = |lhs, rhs| Equal { lhs, rhs };
    let open = eq(sum(v("x"), v("y")), sum(v("z"), v("w")));
    let a = pub_term("a");
    let b = pub_term("b");
    for closed in [
        eq(pair(a.clone(), b.clone()), pair(b.clone(), a.clone())),
        eq(emap(a.clone(), b.clone()), emap(b.clone(), b.clone())),
        eq(
            sum(a.clone(), sum(a.clone(), b.clone())),
            sum(a.clone(), sum(b.clone(), b.clone())),
        ),
        eq(
            hash(sum(a.clone(), b.clone())),
            hash(emap(a.clone(), b.clone())),
        ),
    ] {
        for qs in [
            vec![open.clone(), closed.clone()],
            vec![closed, open.clone()],
        ] {
            assert!(native.unify(&qs).unwrap().is_empty());
            assert!(!native.unifiable(&qs).unwrap());
            assert!(oracle.unify(&qs).unwrap().is_empty());
        }
    }
}

#[test]
fn orbit_identity_preserves_correlations_with_a_free_alias_row() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::function_symbols::CSym;
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, pair_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(bp_maude_sig())
        .merge(dh_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = LVar::new("n", LSort::Msg, 5);
    let y = LVar::new("n", LSort::Fresh, 5);
    let z = LVar::new("ambient", LSort::Msg, 80);
    let k = LVar::new("result", LSort::Msg, 90);
    let v = |i| Term::Lit(Lit::Var(i));
    let raw = |sym, args: Vec<LNTerm>| Term::App(sym, args.into());
    let lhs = raw(
        FunSym::Ac(AcSym::Union),
        vec![raw(FunSym::C(CSym::EMap), vec![v(x), v(y)]), v(y), v(x)],
    );
    let rhs = raw(
        FunSym::Ac(AcSym::Union),
        vec![
            v(x),
            raw(
                FunSym::Ac(AcSym::Union),
                vec![v(y), raw(FunSym::C(CSym::EMap), vec![v(y), v(x)])],
            ),
        ],
    );
    // The first row is an identity modulo AC and C in its raw spelling.
    let full = [
        Equal { lhs, rhs },
        Equal {
            lhs: v(k),
            rhs: pair(v(x), pair(v(y), v(z))),
        },
    ];
    let reference = oracle.unify(&full).unwrap();
    assert!(reference.iter().all(|arm| !arm.is_empty()));
    let arms = native.unify(&full).unwrap();
    assert_eq!(arms.len(), 1);
    let subst = Subst::from_list(arms[0].clone());
    let image = |var| apply_vterm(&subst, v(var));
    assert_eq!(image(k), pair(image(x), pair(image(y), image(z))));
    assert_ne!(image(x), image(z));
    assert_ne!(image(x), image(y));
    let expected = unifier_rows(&full, arms);
    assert!(unifier_rows(&full, reference).contains(&expected[0]));
}

#[test]
fn undeclared_or_malformed_reflexive_rows_are_unsupported_on_native() {
    use crate::builtin::{hash, pair};
    use crate::maude_proc::MaudeError;
    use crate::maude_sig::pair_maude_sig;
    // The reflexive roots do not excuse the terms from validation.
    let atom = pub_term("a");
    let mut shared = atom.clone();
    for _ in 0..12 {
        shared = pair(shared.clone(), shared);
    }
    let node = Term::Lit(Lit::Var(LVar::new("i", LSort::Node, 0)));
    let reflexive = |term: LNTerm| {
        [Equal {
            lhs: term.clone(),
            rhs: term,
        }]
    };
    for term in [
        hash(atom.clone()),
        Term::Lit(Lit::Var(LVar::new("n", LSort::Nat, 0))),
        Term::App(
            FunSym::NoEq(crate::function_symbols::pair_sym()),
            vec![atom.clone()].into(),
        ),
    ] {
        let native = native_session(pair_maude_sig());
        assert!(
            matches!(
                native.unify(&reflexive(term.clone())),
                Err(MaudeError::UnsupportedOperation(_))
            ),
            "{term:?}"
        );
        assert!(native.check_backend_status().is_err());
    }
    // Sharing is no obstacle: this declared term has 4096 leaves. A node
    // variable below a free symbol is a term of the wire module as well.
    let native = native_session(pair_maude_sig());
    for term in [shared, pair(node, atom)] {
        assert_eq!(
            canonical_variants(native.unify(&reflexive(term)).unwrap()),
            vec![vec![]]
        );
    }
}

#[test]
fn homogeneous_basis_answers_match_maude_up_to_branch_and_witness_renaming() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::lean_unification::Substitutions;
    use crate::lterm::HasFrees;
    use crate::subst::{apply_vterm, Subst};
    use std::collections::BTreeMap;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig();
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let vars = ["x", "y", "z", "w"].map(|n| LVar::new(n, LSort::Msg, 0));
    let side = |xs: &[usize]| {
        f_app_ac(
            AcSym::Union,
            xs.iter().map(|&i| Term::Lit(Lit::Var(vars[i]))).collect(),
        )
    };
    let eq = |lhs: &[usize], rhs: &[usize]| Equal {
        lhs: side(lhs),
        rhs: side(rhs),
    };
    // A column counts one shared witness across every input image. Sorting the
    // columns removes the choice of witness names while keeping all aliases.
    let columns = |arms: Substitutions, live: &[LVar]| {
        let mut result = Vec::new();
        for arm in arms {
            let arm = Subst::from_list(arm);
            let mut cols = BTreeMap::<LVar, Vec<usize>>::new();
            for (i, v) in live.iter().enumerate() {
                apply_vterm(&arm, Term::Lit(Lit::Var(*v))).for_each_free(&mut |w| {
                    cols.entry(*w).or_insert_with(|| vec![0; live.len()])[i] += 1
                });
            }
            let mut cols: Vec<_> = cols.into_values().collect();
            cols.sort();
            result.push(cols);
        }
        result.sort();
        result
    };
    let compare = |q: Vec<Equal<LNTerm>>, live: &[LVar]| {
        assert_eq!(
            columns(native.unify(&q).unwrap(), live),
            columns(oracle.unify(&q).unwrap(), live),
            "{q:?}"
        );
    };
    for q in [
        vec![eq(&[0, 0], &[1]), eq(&[1, 2], &[3])],
        vec![eq(&[3], &[2, 1]), eq(&[1], &[0, 0])],
        vec![eq(&[0, 1], &[2, 3])],
        vec![eq(&[0, 1], &[2, 3]), eq(&[0], &[2])],
    ] {
        compare(q, &vars);
    }
    compare(vec![eq(&[0, 0], &[1]), eq(&[1, 1], &[0])], &vars[..2]);
    // The full coordinate boxes for these rows exceeded the previous budget.
    // Include a neutral column, both orientations, and a constraint on the
    // shared witness in the same matrix.
    let ratio = eq(&[0; 11], &[1; 13]);
    compare(vec![ratio.clone()], &vars[..2]);
    compare(vec![eq(&[1; 13], &[0; 11])], &vars[..2]);
    compare(vec![ratio.clone(), eq(&[0], &[1])], &vars[..2]);
    compare(vec![eq(&[0], &[1]), ratio.clone()], &vars[..2]);
    compare(vec![eq(&[0, 0, 0, 1], &[2, 2])], &vars[..3]);
    compare(vec![eq(&[0, 0, 0, 1, 2], &[3, 3, 2])], &vars);
    compare(vec![eq(&[2, 2], &[1]), ratio], &vars[..3]);
    for a in 1..=3 {
        for b in 1..=3 {
            compare(
                vec![eq(&vec![0; a], &vec![1; b]), eq(&[0, 1], &[1, 0])],
                &vars[..2],
            );
        }
    }
}

#[test]
fn native_oracle_compact_nonunit_plane_preserves_all_five_substitutions() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::lean_unification::Substitutions;
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let vars = ["x", "y", "z"].map(|n| Term::Lit(Lit::Var(LVar::new(n, LSort::Msg, 0))));
    let valued = |arms: Substitutions| {
        assert_eq!(arms.len(), 5);
        canonical_small_ac_answers(
            arms.into_iter()
                .map(|arm| {
                    let subst = Subst::from_list(arm);
                    let images = vars
                        .iter()
                        .map(|t| apply_vterm(&subst, t.clone()))
                        .collect();
                    vec![(LVar::new("row", LSort::Msg, 0), f_app_list(images))]
                })
                .collect(),
        )
    };
    // For coprime p,q, the primitive columns of pX+qY=(p+q)Z are
    // (p+q,0,p), (1,1,1) and (0,p+q,q). Exactly five subsets cover all inputs.
    // Scaling every coefficient by the same factor preserves the five substitutions.
    for (p, q) in [(7, 8), (24, 25), (60, 61), (140, 160)] {
        let lhs = f_app_ac(
            AcSym::Union,
            [vec![vars[0].clone(); p], vec![vars[1].clone(); q]].concat(),
        );
        let rhs = f_app_ac(AcSym::Union, vec![vars[2].clone(); p + q]);
        for equation in [
            Equal {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            Equal { lhs: rhs, rhs: lhs },
        ] {
            let eqs = std::slice::from_ref(&equation);
            assert_eq!(
                valued(native.unify(eqs).unwrap()),
                valued(oracle.unify(eqs).unwrap()),
                "coefficient pair ({p}, {q})"
            );
        }
    }
}

#[test]
fn abstract_operands_reconcile_complete_branches_against_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash, pair};
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let other = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let mut sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig())
        .merge(bp_maude_sig())
        .merge(dh_maude_sig());
    sig.st_ac_fun_syms.insert(other);
    let sig = sig.refresh();
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let node = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Node, u64::MAX)));
    let narrow = || Term::Lit(Lit::Var(LVar::new("x", LSort::Pub, u64::MAX)));
    let eq = |lhs, rhs| Equal { lhs, rhs };
    for symbol in [AcSym::Union, AcSym::AcFct(other)] {
        let sum = |a, b| f_app_ac(symbol, vec![a, b]);
        let offset = |x, a, b| eq(sum(x, a), sum(v("z"), b));
        let same = offset(v("x"), hash(v("y")), hash(v("w")));
        for (query, count) in [
            (vec![same.clone()], 3),
            // A shared factor cancels under the hash before C branches.
            (
                vec![offset(
                    v("x"),
                    hash(sum(v("k"), emap(v("a"), v("b")))),
                    hash(sum(v("k"), emap(v("c"), v("d")))),
                )],
                4,
            ),
            (
                vec![offset(v("x"), emap(v("a"), v("b")), emap(v("c"), v("d")))],
                4,
            ),
            (
                vec![offset(
                    v("x"),
                    hash(emap(v("a"), v("b"))),
                    hash(emap(v("c"), v("d"))),
                )],
                4,
            ),
            (
                vec![offset(v("x"), emap(v("a"), v("a")), emap(v("c"), v("d")))],
                3,
            ),
            (
                vec![
                    offset(v("x"), emap(v("a"), v("b")), emap(v("c"), v("d"))),
                    eq(v("z"), v("x")),
                    eq(v("a"), pub_term("a")),
                    eq(v("c"), pub_term("c")),
                ],
                1,
            ),
            (vec![eq(same.rhs.clone(), same.lhs.clone())], 3),
            (vec![same.clone(), eq(v("y"), pub_term("a"))], 3),
            (vec![same.clone(), eq(node("i"), node("j"))], 3),
            (vec![same.clone(), eq(v("z"), v("x"))], 1),
            (
                vec![
                    same.clone(),
                    eq(v("y"), pub_term("a")),
                    eq(v("w"), pub_term("b")),
                ],
                2,
            ),
            (
                vec![
                    eq(v("x"), sum(v("y"), pub_term("a"))),
                    eq(
                        v("y"),
                        f_app_ac(
                            if symbol == AcSym::Union {
                                AcSym::AcFct(other)
                            } else {
                                AcSym::Union
                            },
                            vec![v("x"), pub_term("b")],
                        ),
                    ),
                ],
                0,
            ),
            (
                vec![offset(
                    v("x"),
                    pair(v("y"), v("y")),
                    pair(v("w"), pub_term("b")),
                )],
                3,
            ),
            (vec![offset(v("x"), pub_term("a"), hash(v("x")))], 0),
            (vec![offset(narrow(), pub_term("a"), pub_term("b"))], 1),
        ] {
            assert_eq!(
                assert_same_unifiers(&native, &oracle, &query),
                count,
                "{query:?}"
            );
        }
        let inner_symbol = if symbol == AcSym::Union {
            AcSym::AcFct(other)
        } else {
            AcSym::Union
        };
        for inner in [symbol, inner_symbol] {
            let nested = |a, b| hash(f_app_ac(inner, vec![v(a), v(b)]));
            let wrapped = eq(nested("a", "b"), nested("c", "d"));
            let outer = offset(v("x"), wrapped.lhs.clone(), wrapped.rhs.clone());
            let correlated = offset(v("x"), nested("x", "b"), nested("c", "d"));
            for (query, count) in [
                (vec![outer.clone()], 9),
                (vec![outer, eq(v("x"), v("z"))], 7),
                (
                    vec![eq(
                        emap(v("p"), sum(v("a"), v("b"))),
                        emap(v("q"), sum(v("c"), v("d"))),
                    )],
                    8,
                ),
                // One shared variable links two matrices below a free root.
                (
                    vec![eq(
                        pair(
                            sum(v("a"), v("a")),
                            f_app_ac(inner_symbol, vec![v("b"), v("b")]),
                        ),
                        pair(
                            sum(v("b"), v("b")),
                            f_app_ac(inner_symbol, vec![v("c"), v("c")]),
                        ),
                    )],
                    1,
                ),
                // In seven of these arms an earlier matrix witness survives
                // only in the images of x and z when the inner matrix runs.
                (
                    vec![
                        offset(v("x"), pub_term("left"), pub_term("right")),
                        wrapped.clone(),
                    ],
                    14,
                ),
                (vec![wrapped], 7),
                (vec![correlated, eq(v("x"), v("z"))], 7),
                (vec![eq(nested("a", "a"), nested("c", "c"))], 1),
            ] {
                assert_eq!(
                    assert_same_unifiers(&native, &oracle, &query),
                    count,
                    "{query:?}"
                );
            }
        }
    }
}

#[test]
fn native_oracle_disjoint_atomic_sorts_exclude_declared_ac_rules() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::lterm::fresh_term;
    use crate::maude_sig::hash_maude_sig;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::{f_app_list, f_app_no_eq};

    let Some(path) = require_maude_path() else {
        return;
    };
    let op = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let unit = NoEqSym::new(b"unit", 0, Privacy::Public, Constructability::Constructor);
    let marker = f_app_no_eq(unit, vec![]);
    let combine = |args| f_app_ac(AcSym::AcFct(op), args);
    let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let p = Term::Lit(Lit::Var(LVar::new("p", LSort::Pub, u64::MAX)));
    let n = var("n", LSort::Fresh);
    let x = var("x", LSort::Msg);
    let y = var("y", LSort::Msg);
    let z = var("z", LSort::Msg);
    let mut sig = hash_maude_sig();
    sig.st_fun_syms.insert(unit);
    sig.st_ac_fun_syms.insert(op);
    sig.st_rules
        .insert(rule(combine(vec![x.clone(), x.clone()]), hash(x.clone())));
    sig.st_rules
        .insert(rule(combine(vec![x.clone(), marker.clone()]), x.clone()));
    let binary_rules = sig.clone().refresh();
    sig.st_rules.insert(rule(
        combine(vec![x.clone(), y.clone(), z.clone()]),
        hash(marker.clone()),
    ));
    let sig = sig.refresh();
    let table = RuleTable::new(&sig).unwrap();
    let native = MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        sig.clone(),
        AlgebraBackend::ProvedOnly,
        Default::default(),
    )
    .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    // Neither disjoint operand can expand into a hidden AC product. A
    // separate unrestricted observation exercises the packed caller interface.
    for public in [p.clone(), pub_term("p")] {
        for fresh in [n.clone(), fresh_term("n")] {
            let term = combine(vec![public.clone(), fresh.clone()]);
            let query = f_app_list(vec![
                z.clone(),
                fresh,
                term.clone(),
                public.clone(),
                term.clone(),
            ]);
            assert_eq!(
                canonical_variants(native.variants(&query).unwrap()),
                vec![vec![]]
            );
            assert_eq!(
                canonical_variants(oracle.variants(&query).unwrap()),
                vec![vec![]]
            );
            assert_eq!(native.reduce(&term).unwrap(), term);
            assert_eq!(oracle.reduce(&term).unwrap(), term);
        }
    }

    // The diagonal is a real variant when distinct inputs have a common sort.
    let shared = combine(vec![p.clone(), var("q", LSort::Pub)]);
    let reference = canonical_variants(oracle.variants(&shared).unwrap());
    assert_eq!(reference.len(), 2);
    if let Outcome::Complete(arms) = table.joined_variants(&shared).unwrap() {
        assert_eq!(canonical_variants(arms), reference);
    }
    let a = pub_term("a");
    let b = fresh_term("b");
    for (redex, normal) in [
        (combine(vec![a.clone(), a.clone()]), hash(a.clone())),
        (combine(vec![marker.clone(), b.clone()]), b.clone()),
        (
            combine(vec![a.clone(), b.clone(), pub_term("c")]),
            hash(marker.clone()),
        ),
    ] {
        assert_eq!(oracle.reduce(&redex).unwrap(), normal);
        if let Some(native) = table.reduce_native(&redex).unwrap() {
            assert_eq!(native, normal);
        }
    }

    // A Msg input may contain the unit or expand to enough factors to fire
    // the triple rule. Concrete instances above witness both possibilities.
    let open = combine(vec![x.clone(), n.clone()]);
    if let Outcome::Complete(arms) = table.joined_variants(&open).unwrap() {
        assert!(canonical_variants(arms).iter().any(|arm| !arm.is_empty()));
    }

    // The same diagonal and unit rules admit a stable three-factor product.
    // Checking its whole root alone would miss the diagonal in a proper
    // subbag when two public factors become equal.
    let binary = RuleTable::new(&binary_rules).unwrap();
    let native_binary = MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        binary_rules.clone(),
        AlgebraBackend::ProvedOnly,
        Default::default(),
    )
    .unwrap();
    let binary_oracle =
        MaudeHandle::start_with_backend(&path, binary_rules, AlgebraBackend::Maude).unwrap();
    let rigid = hash(n.clone());
    let inert = combine(vec![p.clone(), n.clone(), rigid.clone()]);
    assert_eq!(
        canonical_variants(native_binary.variants(&inert).unwrap()),
        vec![vec![]]
    );
    assert_eq!(
        canonical_variants(binary_oracle.variants(&inert).unwrap()),
        vec![vec![]]
    );
    assert_eq!(native_binary.reduce(&inert).unwrap(), inert);
    let possible = combine(vec![p.clone(), var("q", LSort::Pub), rigid.clone()]);
    // Check the actual specialized normal value: Maude's variant listing
    // for this user-defined rule can omit the proper-subbag specialization.
    if let Outcome::Complete(arms) = binary.joined_variants(&possible).unwrap() {
        assert_eq!(canonical_variants(arms), reference);
    }
    let inside = combine(vec![a.clone(), a.clone(), rigid.clone()]);
    let rewritten = combine(vec![hash(a.clone()), rigid]);
    assert_eq!(binary_oracle.reduce(&inside).unwrap(), rewritten);
    if let Some(actual) = binary.reduce_native(&inside).unwrap() {
        assert_eq!(actual, rewritten);
    }

    // Source-rule names and query names are numbered by separate Maude
    // conversion contexts. A Rust name mismatch cannot prove disjointness.
    let mut literal = sig.clone();
    literal.st_rules.insert(rule(
        combine(vec![pub_term("rule-literal"), x.clone()]),
        marker.clone(),
    ));
    let literal = literal.refresh();
    let guarded = RuleTable::new(&literal).unwrap();
    let literal_oracle =
        MaudeHandle::start_with_backend(&path, literal, AlgebraBackend::Maude).unwrap();
    let collision = combine(vec![pub_term("query-literal"), n.clone()]);
    assert_eq!(literal_oracle.reduce(&collision).unwrap(), marker);
    if let Some(actual) = guarded.reduce_native(&collision).unwrap() {
        assert_eq!(actual, marker);
    }

    // Adding one linear binary rule invalidates the exclusion, even on
    // disjoint sorts. Its result is visible in the normal value of the pair.
    let mut active = sig;
    active
        .st_rules
        .insert(rule(combine(vec![x, y]), marker.clone()));
    let active = active.refresh();
    let generic = RuleTable::new(&active).unwrap();
    let reference = MaudeHandle::start_with_backend(&path, active, AlgebraBackend::Maude).unwrap();
    let ground = combine(vec![a, b]);
    assert_eq!(reference.reduce(&ground).unwrap(), marker);
    if let Some(actual) = generic.reduce_native(&ground).unwrap() {
        assert_eq!(actual, marker);
    }
}

#[test]
fn defined_ac_identity_variants_check_the_entire_factor_multiset() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::hash_maude_sig;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_no_eq;

    let Some(path) = require_maude_path() else {
        return;
    };
    let f = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let combine = |xs| f_app_ac(AcSym::AcFct(f), xs);
    let fresh = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Fresh, 0)));
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
    let symbol = NoEqSym::new(b"marker", 0, Privacy::Public, Constructability::Constructor);
    let marker = f_app_no_eq(symbol, vec![]);
    let mut sig = hash_maude_sig();
    sig.st_ac_fun_syms.insert(f);
    sig.st_fun_syms.insert(symbol);
    let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
    sig.st_rules.insert(rule(
        combine(vec![hash(x.clone()), marker.clone()]),
        x.clone(),
    ));
    let sig = sig.refresh();
    let table = RuleTable::new(&sig).unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let inert = combine(vec![fresh("u"), marker.clone(), fresh("v")]);
    assert_eq!(
        table.variants(&inert).unwrap(),
        Outcome::Complete(vec![vec![]])
    );
    assert_eq!(
        canonical_variants(oracle.variants(&inert).unwrap()),
        vec![vec![]]
    );

    // AC regrouping exposes hash(a) and marker as a subterm even in a
    // larger product. An identity *normal form* would be false here.
    let a = pub_term("a");
    let b = pub_term("b");
    let c = pub_term("c");
    let redex = combine(vec![b.clone(), marker.clone(), c.clone(), hash(a.clone())]);
    assert_eq!(table.reduce(&redex).unwrap(), None);
    assert_eq!(oracle.reduce(&redex).unwrap(), combine(vec![b, c, a]));
    // After substitution an unrestricted factor can itself contain hash(a).
    assert_eq!(
        table.variants(&combine(vec![x.clone(), marker])).unwrap(),
        Outcome::Unsupported
    );

    let mut extra = sig;
    extra
        .st_rules
        .insert(rule(combine(vec![x.clone(), x.clone()]), x));
    let extra = RuleTable::new(&extra).unwrap();
    // A new rule with only variable factors defeats the earlier exclusion.
    assert_eq!(extra.variants(&inert).unwrap(), Outcome::Unsupported);
}

#[test]
fn root_exclusion_checks_every_equation_and_every_child() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, hash, pair};
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::lean_unification::RuleTable;
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::f_app_no_eq;

    let sym = NoEqSym::new(
        "selectArg",
        2,
        Privacy::Public,
        Constructability::Destructor,
    );
    let select = |a, b| f_app_no_eq(sym, vec![a, b]);
    let union = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let x = var("x");
    let y = var("y");
    let z = var("z");
    let mut sig = mset_maude_sig()
        .merge(pair_maude_sig())
        .merge(hash_maude_sig());
    sig.st_fun_syms.insert(sym);
    // The first equation constrains argument zero and the second constrains
    // argument one. They overlap when both arguments have the indicated heads.
    for (lhs, position) in [
        (select(hash(x.clone()), z.clone()), vec![0, 0]),
        (select(z.clone(), union(x.clone(), y.clone())), vec![1, 0]),
    ] {
        sig.st_rules.insert(CtxtStRule::new(
            lhs,
            StRhs {
                positions: vec![position],
                term: x.clone(),
            },
        ));
    }
    let sig = sig.refresh();
    let table = RuleTable::new(&sig).unwrap();
    let inert = select(fst(x.clone()), y.clone());
    let nested = union(pair(inert.clone(), x.clone()), inert.clone());
    let possible = select(z.clone(), union(x.clone(), y.clone()));
    assert_eq!(table.reduce(&nested).unwrap(), Some(nested.clone()));
    let matched = select(hash(x.clone()), y.clone());
    assert_eq!(table.reduce(&matched).unwrap(), Some(x.clone()));
    for term in [
        possible.clone(),
        pair(inert.clone(), possible.clone()),
        select(fst(pair(x.clone(), y.clone())), y.clone()),
        Term::App(FunSym::Ac(AcSym::Union), vec![y.clone(), x.clone()].into()),
    ] {
        assert_eq!(table.reduce(&term).unwrap(), None, "{term:?}");
    }

    if let Some(path) = require_maude_path() {
        let native = native_session(sig.clone());
        // The certifier does not accept this table: only the session of a
        // theory, whose author asserts convergence, reduces on it.
        let theory = MaudeHandle::start_for_tamarin_theory(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::ProvedOnly,
            Default::default(),
        )
        .unwrap();
        let maude =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        for term in [&nested, &matched] {
            assert_eq!(theory.reduce(term).unwrap(), maude.reduce(term).unwrap());
        }
        assert_eq!(theory.stats().norm_count, 0);
        // The AC rule returns either summand here, and Maude picks one. The
        // certifier does not accept such a table, and a raw proved-only
        // session reports that instead of choosing.
        assert_ne!(maude.reduce(&possible).unwrap(), possible);
        assert!(matches!(
            native.reduce(&possible),
            Err(crate::maude_proc::MaudeError::UnsupportedOperation(_))
        ));
        assert!(native.check_backend_status().is_err());
    }

    let mut wildcard = sig;
    wildcard.st_rules.insert(CtxtStRule::new(
        select(x.clone(), y),
        StRhs {
            positions: vec![vec![0]],
            term: x.clone(),
        },
    ));
    let wildcard = RuleTable::new(&wildcard).unwrap();
    assert_eq!(wildcard.reduce(&inert).unwrap(), Some(fst(x)));
    // The wildcard and hash rule both match, with different results.
    assert_eq!(wildcard.reduce(&matched).unwrap(), None);
}

#[test]
fn observed_projection_preserves_shared_slots_under_nested_ac() {
    use crate::builtin::pair;
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::pair_maude_sig;
    use crate::subterm_rule::{CtxtStRule, StRhs};
    use crate::term::f_app_no_eq;

    let d = NoEqSym::new(
        "projectSection",
        2,
        Privacy::Public,
        Constructability::Destructor,
    );
    let application = |a, b| f_app_no_eq(d, vec![a, b]);
    let union = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let var = |name, i| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, i)));
    let a = var("a", 0);
    let b = var("b", 0);
    // projectSection(pair(a+b,a),b) -> a. The variable chosen by the rule
    // occurs both below AC and at an independently observable free position.
    let mut sig = mset_maude_sig().merge(pair_maude_sig());
    sig.st_fun_syms.insert(d);
    sig.st_rules.insert(CtxtStRule::new(
        application(pair(union(a.clone(), b.clone()), a.clone()), b.clone()),
        StRhs {
            positions: vec![vec![0, 1]],
            term: a.clone(),
        },
    ));
    let sig = sig.refresh();
    let query = application(var("x", 12), var("y", 16));
    let table = RuleTable::new(&sig).unwrap();
    let arms = table
        .observed_application_variants(&query)
        .unwrap()
        .unwrap();
    let [base, split] = arms.as_slice() else {
        panic!("missing arm: {arms:?}")
    };
    assert_eq!(base.value, query);
    assert!(base.bindings.is_empty());
    let [(vx, first), (vy, second)] = split.bindings.as_slice() else {
        panic!("missing binding")
    };
    assert_eq!(
        (*vx, *vy),
        (
            LVar::new("x", LSort::Msg, 12),
            LVar::new("y", LSort::Msg, 16)
        )
    );
    assert_ne!(&split.value, second);
    assert_eq!(
        *first,
        pair(
            union(split.value.clone(), second.clone()),
            split.value.clone()
        )
    );
    for t in [&split.value, second] {
        assert!(matches!(t, Term::Lit(Lit::Var(v)) if v.idx > 16));
    }
    assert_eq!(
        table
            .observed_application_variants(&application(a.clone(), a.clone()))
            .unwrap(),
        None
    );
    // Repeated independent results require the general tuple contract.
    assert_eq!(
        table
            .variants(&crate::term::f_app_list(vec![query.clone(), query.clone()]))
            .unwrap(),
        Outcome::Unsupported
    );

    let mut overlap = sig;
    overlap.st_rules.insert(CtxtStRule::new(
        application(a, b.clone()),
        StRhs {
            positions: vec![vec![1]],
            term: b,
        },
    ));
    assert_eq!(
        RuleTable::new(&overlap)
            .unwrap()
            .observed_application_variants(&query)
            .unwrap(),
        None
    );
}

#[test]
fn projection_of_raw_nested_ac_captures_matches_maudes_structural_result() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, pair};
    use crate::maude_sig::{pair_maude_sig, sym_enc_maude_sig};

    let Some(path) = require_maude_path() else {
        return;
    };
    let a = pub_term("a");
    let b = pub_term("b");
    let union = FunSym::Ac(AcSym::Union);
    let unordered = Term::App(union, vec![b.clone(), a.clone()].into());
    let nested = Term::App(union, vec![b.clone(), unordered].into());
    let input = fst(pair(pair(a.clone(), nested), b.clone()));
    let expected = pair(a.clone(), f_app_ac(AcSym::Union, vec![a, b.clone(), b]));
    let pairing = pair_maude_sig().merge(mset_maude_sig());
    for sig in [pairing.clone(), pairing.merge(sym_enc_maude_sig())] {
        for backend in [AlgebraBackend::Maude, AlgebraBackend::ProvedOnly] {
            let handle = MaudeHandle::start_with_backend(&path, sig.clone(), backend).unwrap();
            assert_eq!(handle.reduce(&input).unwrap(), expected);
            if backend == AlgebraBackend::ProvedOnly {
                assert_eq!(handle.stats().norm_count, 0);
            }
        }
    }
}

#[test]
fn free_row_beside_a_matrix_matches_maude_on_the_full_request() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::maude_sig::pair_maude_sig;
    use crate::subst::{apply_vterm, Subst};

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let [key, outsider, x, y] = ["key", "x", "u", "v"].map(|name| LVar::new(name, LSort::Msg, 0));
    let term = |v| Term::Lit(Lit::Var(v));
    // One child of the free row observes the shared matrix witness. The other
    // must stay independent of it.
    let original = [
        Equal {
            lhs: term(key),
            rhs: pair(term(x), term(outsider)),
        },
        Equal {
            lhs: f_app_ac(AcSym::Union, vec![term(x); 2]),
            rhs: f_app_ac(AcSym::Union, vec![term(y); 3]),
        },
    ];
    let actual = native.unify(&original).unwrap();
    assert_eq!(actual.len(), 1);
    let subst = Subst::from_list(actual[0].clone());
    let image = |v| apply_vterm(&subst, term(v));
    assert_eq!(image(key), pair(image(x), image(outsider)));
    let Term::Lit(Lit::Var(independent)) = image(outsider) else {
        panic!("expected an independent variable");
    };
    assert!(!crate::lterm::frees(&image(x)).contains(&independent));
    assert!(!crate::lterm::frees(&image(y)).contains(&independent));
    assert_eq!(assert_same_unifiers(&native, &oracle, &original), 1);
}

#[test]
fn ground_ac_split_agrees_with_maude_on_partially_grounded_conjunctions() {
    use crate::algebra_backend::AlgebraBackend;

    let Some(path) = require_maude_path() else {
        return;
    };
    let native = native_session(mset_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
    let plus = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let reverse = |eq: &Equal<LNTerm>| Equal {
        lhs: eq.rhs.clone(),
        rhs: eq.lhs.clone(),
    };
    let split = Equal {
        lhs: plus(v("x"), v("y")),
        rhs: plus(pub_term("a"), pub_term("b")),
    };
    for (q, count) in [("a", 2), ("b", 1), ("c", 0)] {
        let check = Equal {
            lhs: plus(v("x"), pub_term("a")),
            rhs: plus(v("z"), pub_term(q)),
        };
        for pivot in [split.clone(), reverse(&split)] {
            for other in [check.clone(), reverse(&check)] {
                for request in [[pivot.clone(), other.clone()], [other, pivot.clone()]] {
                    let actual = canonical_ground_answers(native.unify(&request).unwrap());
                    assert_eq!(actual.len(), count);
                    assert_eq!(
                        actual,
                        canonical_ground_answers(oracle.unify(&request).unwrap())
                    );
                }
            }
        }
    }
}

#[test]
fn ground_unification_propagates_open_constructor_matches_in_either_orientation() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
    let u = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let pattern = u(hash(v("x")), v("y"));
    let subject = u(hash(pub_term("a")), hash(pub_term("b")));
    // Both choices match the first equation. Only x=a, y=H(b) survives
    // the shared second equation, which then fixes z=b.
    let pending = Equal {
        lhs: u(v("x"), v("y")),
        rhs: u(pub_term("a"), hash(v("z"))),
    };
    for (lhs, rhs) in [(pattern.clone(), subject.clone()), (subject, pattern)] {
        let eqs = [pending.clone(), Equal { lhs, rhs }];
        let expected = canonical_ground_answers(oracle.unify(&eqs).unwrap());
        assert_eq!(expected.len(), 1);
        assert_eq!(
            canonical_ground_answers(native.unify(&eqs).unwrap()),
            expected
        );
    }

    // The partition below H fixes x to a product. Reusing x outside H
    // filters the other partitions, and the pending equation binds z.
    let ab = u(pub_term("a"), pub_term("b"));
    let c = pub_term("c");
    let pattern = u(hash(u(v("x"), v("y"))), v("x"));
    let subject = u(hash(u(ab.clone(), c.clone())), ab);
    let pending = Equal {
        lhs: u(hash(v("y")), v("z")),
        rhs: u(hash(c), pub_term("d")),
    };
    for (lhs, rhs) in [(pattern.clone(), subject.clone()), (subject, pattern)] {
        let eqs = [Equal { lhs, rhs }, pending.clone()];
        let expected = canonical_ground_answers(oracle.unify(&eqs).unwrap());
        assert_eq!(expected.len(), 1);
        assert_eq!(
            canonical_ground_answers(native.unify(&eqs).unwrap()),
            expected
        );
    }
}

#[test]
fn partially_grounded_conjunction_with_closed_compounds_agrees_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
    let compound = |s| hash(pub_term(s));
    let plus = |xs| f_app_ac(AcSym::Union, xs);
    let query = [
        Equal {
            lhs: plus(vec![compound("a"), compound("b"), compound("b")]),
            rhs: plus(vec![var("x"), compound("a")]),
        },
        Equal {
            lhs: plus(vec![var("x"), compound("c")]),
            rhs: plus(vec![var("z"), compound("b")]),
        },
    ];
    let actual = native.unify(&query).unwrap();
    assert_eq!(actual.len(), 1);
    assert_eq!(
        canonical_ground_answers(actual),
        canonical_ground_answers(oracle.unify(&query).unwrap())
    );
}

#[test]
fn nested_ground_split_keeps_bindings_from_before_constructor_decomposition() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::maude_sig::pair_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, 0)));
    let sum = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let request = [
        Equal {
            lhs: var("u"),
            rhs: pair(var("y"), var("z")),
        },
        Equal {
            lhs: pair(sum(var("x"), var("y")), sum(var("x"), pub_term("a"))),
            rhs: pair(
                sum(pub_term("a"), pub_term("b")),
                sum(var("z"), pub_term("b")),
            ),
        },
    ];
    let arms = native.unify(&request).unwrap();
    assert_eq!(arms.len(), 1);
    assert!(arms[0].contains(&(
        LVar::new("u", LSort::Msg, 0),
        pair(pub_term("a"), pub_term("a"))
    )));
    assert_eq!(
        canonical_ground_answers(arms),
        canonical_ground_answers(oracle.unify(&request).unwrap())
    );
}

#[test]
fn nested_commutative_ac_matching_agrees_with_maude() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash};
    use crate::lean_unification::{match_compound_ground, Outcome};
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, hash_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(hash_maude_sig())
        .merge(bp_maude_sig())
        .merge(dh_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig, AlgebraBackend::ProvedOnly).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let narrow = Term::Lit(Lit::Var(LVar::new("p", LSort::Pub, 0)));
    let (a, b) = (pub_term("a"), pub_term("b"));
    let ab = emap(a.clone(), b.clone());
    let pool = [
        a.clone(),
        b.clone(),
        hash(ab.clone()),
        hash(emap(a.clone(), a.clone())),
        ab,
        hash(emap(a.clone(), emap(a.clone(), b.clone()))),
    ];
    let patterns = [
        vec![hash(emap(v("x"), v("y"))), v("x")],
        vec![hash(emap(v("x"), v("x"))), v("y")],
        vec![hash(emap(v("x"), v("y"))), v("z")],
        vec![hash(emap(v("x"), emap(v("y"), v("z")))), v("y")],
        vec![hash(emap(narrow.clone(), v("y"))), narrow],
        vec![emap(v("x"), v("y")), v("x"), v("z")],
        vec![v("x"), v("x"), v("y")],
        vec![hash(emap(v("x"), v("y"))), hash(emap(v("x"), v("z")))],
    ];
    let mut checked = 0;
    let mut ambiguous = 0;
    for factors in patterns {
        let pattern = f_app_ac(AcSym::Union, factors);
        for (i, first) in pool.iter().enumerate() {
            for (j, second) in pool.iter().enumerate().skip(i) {
                let pair = vec![first.clone(), second.clone()];
                for third in std::iter::once(None).chain(pool[j..].iter().map(Some)) {
                    let mut factors = pair.clone();
                    factors.extend(third.cloned());
                    let subject = f_app_ac(AcSym::Union, factors);
                    let oriented = Equal {
                        lhs: pattern.clone(),
                        rhs: subject.clone(),
                    };
                    let Outcome::Complete(actual) = match_compound_ground(&[oriented]).unwrap()
                    else {
                        panic!("nested matcher deferred {pattern:?} against {subject:?}");
                    };
                    let query = [Equal {
                        lhs: subject,
                        rhs: pattern.clone(),
                    }];
                    let expected = canonical_ground_answers(oracle.match_eqs(&query).unwrap());
                    assert_eq!(canonical_ground_answers(actual), expected, "{query:?}");
                    assert_eq!(
                        canonical_ground_answers(native.match_eqs(&query).unwrap()),
                        expected,
                        "{query:?}"
                    );
                    assert_eq!(
                        native.has_match_eqs(&query).unwrap(),
                        !expected.is_empty(),
                        "{query:?}"
                    );
                    ambiguous += usize::from(expected.len() > 1);
                    checked += 1;
                }
            }
        }
    }
    assert_eq!(checked, 616);
    assert!(ambiguous > 0);
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn recursive_ac_matching_agrees_with_maude_on_multisets() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
    use crate::lean_unification::{match_compound_ground, Outcome};
    use crate::maude_sig::hash_maude_sig;
    use crate::subst::{apply_vterm, Subst};

    let Some(path) = require_maude_path() else {
        return;
    };
    let combine = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let mut sig = mset_maude_sig().merge(hash_maude_sig());
    sig.st_ac_fun_syms.insert(combine);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let (a, b) = (pub_term("a"), pub_term("b"));
    let pool = [a.clone(), b.clone(), hash(a.clone())];
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let p = Term::Lit(Lit::Var(LVar::new("p", LSort::Pub, 0)));
    let outer = |left, right| f_app_ac(AcSym::Union, vec![left, right]);
    let mut checked = 0;
    for op in [AcSym::Union, AcSym::AcFct(combine)] {
        // Equal AC heads are separated by a free symbol. A different
        // head is itself an atomic outer factor and needs no wrapper.
        let nested = |factors| {
            let product = f_app_ac(op, factors);
            if op == AcSym::Union {
                hash(product)
            } else {
                product
            }
        };
        for (factors, tail_pattern) in [
            (vec![v("x"), v("y")], v("x")),
            (vec![v("x"), v("y")], v("z")),
            (vec![v("x"), v("x"), v("y")], v("x")),
            (vec![p.clone(), v("y")], p.clone()),
            (vec![hash(v("x")), v("y")], v("x")),
            (vec![a.clone(), v("y")], v("y")),
        ] {
            let pattern = outer(nested(factors), tail_pattern);
            let mut successes = 0;
            let mut clashes = 0;
            for size in 2..=4 {
                for ids in multisets(size, 0) {
                    let product = nested(ids.iter().map(|&id| pool[id].clone()).collect());
                    for tail in [
                        a.clone(),
                        b.clone(),
                        hash(a.clone()),
                        outer(a.clone(), b.clone()),
                    ] {
                        let subject = outer(product.clone(), tail);
                        let oriented = Equal {
                            lhs: pattern.clone(),
                            rhs: subject.clone(),
                        };
                        let Outcome::Complete(answers) =
                            match_compound_ground(&[oriented]).unwrap()
                        else {
                            panic!("deferred {pattern:?} against {subject:?}");
                        };
                        for bindings in &answers {
                            assert_eq!(
                                apply_vterm(
                                    &Subst::from_list(bindings.iter().cloned()),
                                    pattern.clone()
                                ),
                                subject
                            );
                        }
                        let query = [Equal {
                            lhs: subject,
                            rhs: pattern.clone(),
                        }];
                        let expected = canonical_ground_answers(oracle.match_eqs(&query).unwrap());
                        assert_eq!(canonical_ground_answers(answers), expected, "{query:?}");
                        assert_eq!(
                            canonical_ground_answers(native.match_eqs(&query).unwrap()),
                            expected,
                            "{query:?}"
                        );
                        assert_eq!(native.has_match_eqs(&query).unwrap(), !expected.is_empty());
                        successes += usize::from(!expected.is_empty());
                        clashes += usize::from(expected.is_empty());
                        checked += 1;
                    }
                }
            }
            assert!(successes > 0);
            // The unrestricted x+y,z pattern can match every generated term.
            if pattern != outer(nested(vec![v("x"), v("y")]), v("z")) {
                assert!(clashes > 0);
            }
        }
    }
    assert_eq!(checked, 1488);
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn rigid_raw_ground_match_compares_with_the_maude_wire() {
    use crate::algebra_backend::AlgebraBackend;
    let Some(path) = require_maude_path() else {
        return;
    };
    let oracle =
        MaudeHandle::start_with_backend(&path, mset_maude_sig(), AlgebraBackend::Maude).unwrap();
    let native = native_session(mset_maude_sig());
    let (a, b, c) = (pub_term("a"), pub_term("b"), pub_term("c"));
    let raw = |args: Vec<LNTerm>| Term::App(FunSym::Ac(AcSym::Union), args.into());
    let nested = |tail| raw(vec![c.clone(), raw(vec![tail, a.clone()])]);
    for (tail, expected) in [(b.clone(), true), (c.clone(), false)] {
        let q = [Equal {
            lhs: nested(tail),
            rhs: f_app_ac(AcSym::Union, vec![a.clone(), b.clone(), c.clone()]),
        }];
        let answers = oracle.match_eqs(&q).unwrap();
        assert_eq!(!answers.is_empty(), expected);
        assert_eq!(native.match_eqs(&q).unwrap(), answers);
        assert_eq!(
            oracle
                .match_eqs_skolemize_both(&q, &Default::default())
                .unwrap(),
            answers
        );
        assert_eq!(
            native
                .match_eqs_skolemize_both(&q, &Default::default())
                .unwrap(),
            answers
        );
    }
    assert_eq!(native.stats().match_count, 0);
    assert!(oracle.stats().match_count > 0);
}

#[test]
fn dh_intruder_product_unifiers_match_ordinary_maude_including_mixed_sorts() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{inv, mult};
    use crate::maude_sig::dh_maude_sig;

    let Some(path) = require_maude_path() else {
        return;
    };
    let native = native_session(dh_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, dh_maude_sig(), AlgebraBackend::Maude).unwrap();
    let var = |i, s| Term::Lit(Lit::Var(LVar::new("x", s, i)));
    let f = |i| var(i, LSort::Fresh);
    let m = |i| var(i, LSort::Msg);
    let left = mult(f(0), m(1));
    for (lhs, rhs, n) in [
        (left.clone(), mult(f(2), f(3)), 2),
        (left.clone(), mult(f(2), m(3)), 3),
        (left.clone(), mult(m(2), inv(f(3))), 2),
        (left, mult(m(2), inv(mult(f(3), m(4)))), 2),
        (mult(f(0), f(1)), mult(f(0), f(1)), 1),
        (mult(f(0), inv(f(0))), crate::builtin::one_const(), 0),
    ] {
        let eq = [Equal { lhs, rhs }];
        assert_eq!(native.unifiable(&eq).unwrap(), n != 0, "{eq:?}");
        assert_eq!(assert_same_unifiers(&native, &oracle, &eq), n, "{eq:?}");
    }
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn reflexive_products_of_strict_subsort_operands_preserve_maude_identity_arm() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::maude_sig::{dh_maude_sig, xor_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig()
        .merge(mset_maude_sig())
        .merge(xor_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let alphabet = [
        Term::Lit(Lit::Var(LVar::new("r", LSort::Fresh, 0))),
        Term::Lit(Lit::Var(LVar::new("r", LSort::Fresh, 1))),
        Term::Lit(Lit::Var(LVar::new("r", LSort::Pub, 0))),
        pub_term("a"),
        crate::lterm::fresh_term("a"),
        pub_term("__skMSG__rigid"),
    ];
    for symbol in [AcSym::Mult, AcSym::Union, AcSym::Xor] {
        for a in &alphabet[..3] {
            for b in &alphabet {
                for c in &alphabet {
                    let term = f_app_ac(symbol, vec![a.clone(), b.clone(), c.clone()]);
                    let eq = [Equal {
                        lhs: term.clone(),
                        rhs: term,
                    }];
                    assert_same_unifiers(&native, &oracle, &eq);
                }
            }
        }
    }
    assert!(native.provenance().fresh(Command::Unify, Origin::Proved) > 0);
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn received_power_with_rigid_compound_exponent_matches_all_ordered_maude_arms() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, fst, hash, inv, mult, one_const, pair};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig, pair_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig())
        .merge(mset_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let table = RuleTable::new(&sig).unwrap();
    let variable = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 7)));
    let peer = variable("peer", LSort::Msg);
    let a = variable("a", LSort::Msg);
    let nonce = variable("a", LSort::Fresh);
    let pubvar = variable("p", LSort::Pub);
    let hashed = hash(pair(a.clone(), nonce.clone()));
    for exponent in [
        pub_term("constant"),
        pubvar,
        hashed.clone(),
        pair(nonce.clone(), nonce.clone()),
        f_app_ac(AcSym::Union, vec![a.clone(), nonce.clone()]),
        hash(f_app_ac(AcSym::Union, vec![a.clone(), nonce.clone()])),
    ] {
        let power = exp(peer.clone(), exponent.clone());
        for obs in [
            vec![power.clone()],
            vec![
                a.clone(),
                peer.clone(),
                power.clone(),
                exponent.clone(),
                nonce.clone(),
                power.clone(),
            ],
            vec![power.clone(), exponent.clone(), a.clone(), nonce.clone()],
        ] {
            let query = f_app_list(obs.clone());
            let expected = oracle.variants(&query).unwrap();
            // Queries that first introduce two variables through an AC node
            // can have a different raw Maude numbering under reassociation.
            match table.variants(&query).unwrap() {
                Outcome::Complete(ordered) => {
                    assert_eq!(ordered, expected, "exact numbering for {query:?}")
                }
                Outcome::Unsupported => assert!(
                    matches!(exponent, Term::App(FunSym::Ac(_), _))
                        || matches!(&exponent, Term::App(_, xs) if matches!(&xs[0], Term::App(FunSym::Ac(_), _)))
                ),
            }
            let Outcome::Complete(actual) = table.joined_variants(&query).unwrap() else {
                panic!("single-power native dispatch deferred: {query:?}")
            };
            assert_eq!(actual.len(), 7, "{query:?}");
            assert_eq!(actual.len(), expected.len());
            for (native, reference) in actual.into_iter().zip(expected) {
                assert_eq!(
                    canonical_variants(vec![native.clone()]),
                    canonical_variants(vec![reference]),
                    "{query:?}"
                );
                let bindings = Subst::from_list(native);
                for t in &obs {
                    let instance = apply_vterm(&bindings, t.clone());
                    assert_eq!(
                        table.reduce(&instance).unwrap(),
                        Some(oracle.reduce(&instance).unwrap()),
                        "{instance:?}"
                    );
                }
            }
        }
    }

    for unsupported in [
        a.clone(),
        mult(nonce.clone(), a.clone()),
        inv(nonce.clone()),
        one_const(),
        hash(peer.clone()),
        fst(a),
    ] {
        let answer = table.variants(&exp(peer.clone(), unsupported)).unwrap();
        assert!(!matches!(answer, Outcome::Complete(ref arms) if arms.len()==7));
    }
}

#[test]
fn joins_received_power_variants_on_naxos_shared_peers_and_exponents() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, hash, pair};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig, pair_maude_sig};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
    let table = RuleTable::new(&sig).unwrap();
    let v = |s, i| Term::Lit(Lit::Var(LVar::new("x", s, i)));
    let [x, y] = [0, 1].map(|i| v(LSort::Msg, i));
    let [a, b] = [2, 3].map(|i| v(LSort::Fresh, i));
    let h = hash(pair(a.clone(), b.clone()));
    for (obs, count) in [
        (
            vec![exp(x.clone(), b.clone()), exp(x.clone(), h.clone())],
            15,
        ),
        (
            vec![exp(x.clone(), b.clone()), exp(y.clone(), h.clone())],
            49,
        ),
        (
            vec![
                a,
                b.clone(),
                x.clone(),
                y.clone(),
                exp(x.clone(), b),
                exp(x, h.clone()),
                exp(y, h),
            ],
            105,
        ),
    ] {
        let query = f_app_list(obs);
        let reference = oracle.variants(&query).unwrap();
        assert_eq!(reference.len(), count);
        let Outcome::Complete(rows) = table.joined_variants(&query).unwrap() else {
            panic!("join deferred for {count} expected arms")
        };
        assert_eq!(rows.len(), count);
        assert_eq!(
            canonical_variants(rows),
            canonical_variants(reference),
            "{count} arms"
        );
    }
}

#[test]
fn rejects_inverse_factor_against_an_unsplittable_nonce_and_free_constructor() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, hash, inv, mult, pair};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let fresh = |i| Term::Lit(Lit::Var(LVar::new("x", LSort::Fresh, i)));
    let msg = |i| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)));
    let eq = [Equal {
        lhs: mult(fresh(0), hash(pair(fresh(1), fresh(2)))),
        rhs: mult(msg(3), inv(msg(4))),
    }];
    assert!(oracle.unify(&eq).unwrap().is_empty());
    assert!(native.unify(&eq).unwrap().is_empty());

    let original = [
        Equal {
            lhs: msg(3),
            rhs: msg(5),
        },
        Equal {
            lhs: exp(pub_term("g"), eq[0].lhs.clone()),
            rhs: exp(msg(6), eq[0].rhs.clone()),
        },
    ];
    assert!(!native.unifiable(&original).unwrap());
    assert!(native.unify(&original).unwrap().is_empty());
    assert!(oracle.unify(&original).unwrap().is_empty());
}

#[test]
fn two_indivisible_factors_constrain_the_remaining_shared_ac_equation() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, mult, pair};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let fresh = |i| Term::Lit(Lit::Var(LVar::new("f", LSort::Fresh, i)));
    let msg = |i| Term::Lit(Lit::Var(LVar::new("m", LSort::Msg, i)));
    let eqs = [
        Equal {
            lhs: mult(fresh(0), hash(pair(fresh(1), fresh(2)))),
            rhs: mult(fresh(3), msg(4)),
        },
        Equal {
            lhs: mult(msg(5), msg(6)),
            rhs: mult(msg(4), hash(pair(fresh(7), fresh(3)))),
        },
    ];
    assert_eq!(assert_same_unifiers(&native, &oracle, &eqs), 2);
}

#[test]
fn joined_power_rows_preserve_sharing_when_exponents_can_unify_or_contain_another_peer() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, hash};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(hash_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let (a, b, x, y) = (v("a"), v("b"), v("x"), v("y"));
    for (case, applications) in [
        [
            exp(x.clone(), hash(a.clone())),
            exp(x.clone(), hash(b.clone())),
        ],
        [
            exp(x.clone(), hash(y.clone())),
            exp(y.clone(), hash(x.clone())),
        ],
    ]
    .into_iter()
    .enumerate()
    {
        let query = f_app_list(
            [a.clone(), b.clone(), x.clone(), y.clone()]
                .into_iter()
                .chain(applications)
                .collect(),
        );
        let actual = table.joined_variants(&query).unwrap();
        let expected = oracle.variants(&query).unwrap();
        let Outcome::Complete(arms) = actual else {
            // Normality of a hash containing another specialized peer can
            // exceed the reducer's scope. The entire joint query must defer.
            assert_eq!(case, 1, "independent exponent inputs must complete");
            continue;
        };
        assert_eq!(
            canonical_variants(arms),
            canonical_variants(expected),
            "{query:?}"
        );
    }
}

#[test]
fn wide_ac_pivot_preserves_each_rigid_occurrence_and_the_shared_remainder() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let product = |a| f_app_ac(AcSym::Union, a);
    let lhs = product(vec![var("x"), hash(var("a"))]);
    // The matrix has more than 32 distinct columns. Both identical hash
    // factors remain in the transferred product if the pivot goes into Y.
    let mut terms: Vec<_> = (0..29).map(|i| pub_term(format!("p{i}"))).collect();
    terms.extend([
        var("y"),
        hash(pub_term("one")),
        hash(pub_term("one")),
        hash(pub_term("two")),
    ]);
    let rhs = product(terms);
    for (lhs, rhs) in [(lhs.clone(), rhs.clone()), (rhs, lhs)] {
        let eqs = [Equal { lhs, rhs }];
        assert_eq!(assert_same_unifiers(&native, &oracle, &eqs), 4);
    }
}

#[test]
fn native_oracle_gdh_unification_selects_product_rows_and_keeps_the_original_scope() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{inv, mult};
    use crate::maude_sig::{dh_maude_sig, mset_maude_sig};
    use crate::subst::{apply_vterm, Subst};

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(mset_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |idx, sort| Term::Lit(Lit::Var(LVar::new("x", sort, idx)));
    let x = |i| var(i, LSort::Msg);
    let f = |i| var(i, LSort::Fresh);
    let left = mult(mult(x(1), f(2)), f(3));
    let right = mult(mult(x(4), x(5)), f(6));
    let inv_context = |t: &LNTerm| mult(f(2), inv(t.clone()));
    let eq = |l: LNTerm, r| Equal { lhs: l, rhs: r };
    let refl = |t: LNTerm| eq(t.clone(), t);
    let copies = |n| f_app_ac(AcSym::Union, vec![pub_term("1"); n]);
    // The 23 residual rows of sp14/GDH key_reachable_2, including their order.
    let mut rows: Vec<_> = [2, 3, 2, 3, 2, 2, 3, 2].map(|n| refl(copies(n))).to_vec();
    rows.push(refl(left.clone()));
    rows.extend([2, 3, 3, 2, 2, 2, 3, 2].map(|n| refl(copies(n))));
    rows.extend(vec![eq(left.clone(), right.clone()); 3]);
    rows.extend([
        eq(inv_context(&left), inv_context(&right)),
        refl(copies(4)),
        refl(copies(3)),
    ]);
    assert_eq!(rows.len(), 23);
    for with_extra_scope in [false, true] {
        if with_extra_scope {
            rows.push(eq(right.clone(), left.clone()));
            rows.push(refl(f_app_ac(AcSym::Union, vec![x(0), pub_term("1")])));
            // The variable that occurs only in the reflexive row stays a
            // variable of its sort, apart from the image of every other one.
            for arm in native.unify(&rows).unwrap() {
                let subst = Subst::from_list(arm);
                let Term::Lit(Lit::Var(scoped)) = apply_vterm(&subst, x(0)) else {
                    panic!("the scoped variable was specialized");
                };
                assert_eq!(scoped.sort, LSort::Msg);
                for i in 1..=6 {
                    for sort in [LSort::Msg, LSort::Fresh] {
                        let image = apply_vterm(&subst, var(i, sort));
                        assert!(!crate::lterm::frees_list(&image).contains(&scoped));
                    }
                }
            }
        }
        assert_eq!(assert_same_unifiers(&native, &oracle, &rows), 20);
    }
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn native_oracle_coupled_gdh_products_preserve_all_84_unifiers() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{inv, mult};
    use crate::maude_sig::dh_maude_sig;
    use crate::subst::{apply_vterm, Subst};
    use std::collections::BTreeMap;

    let sig = dh_maude_sig().merge(mset_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let sorts = [
        LSort::Fresh,
        LSort::Fresh,
        LSort::Msg,
        LSort::Msg,
        LSort::Fresh,
        LSort::Msg,
        LSort::Msg,
        LSort::Msg,
        LSort::Fresh,
    ];
    let keys = std::array::from_fn(|i| LVar::new("x", sorts[i], i as u64 + 1));
    let [a, b, x, y, c, unused, u, v, d] = keys.map(|k| Term::Lit(Lit::Var(k)));
    let left = mult(mult(a.clone(), b.clone()), x);
    let eq = |lhs: LNTerm, rhs| Equal { lhs, rhs };
    let first = eq(left.clone(), mult(mult(b, y), c));
    let second = eq(left.clone(), mult(mult(u, v), d));
    let context = |t| mult(a.clone(), inv(t));
    let under_inv = eq(context(left), context(second.rhs.clone()));
    let refl = |t: LNTerm| eq(t.clone(), t);
    let ones = |n| refl(f_app_ac(AcSym::Union, vec![pub_term("1"); n]));
    let scoped = refl(f_app_ac(AcSym::Union, vec![unused, pub_term("1")]));
    // Original equation order, repeated observations and a caller variable
    // appearing only in a reflexive row come from the depth-20 GDH query.
    let rows = [
        ones(2),
        first.clone(),
        ones(2),
        ones(2),
        ones(3),
        first,
        ones(3),
        ones(3),
        ones(3),
        scoped,
        second.clone(),
        second.clone(),
        second,
        under_inv,
        ones(4),
        ones(3),
    ];
    let signatures = |arms: crate::lean_unification::Substitutions| {
        let mut result = Vec::new();
        for arm in arms {
            assert!(arm.iter().all(|(key, _)| keys.contains(key)));
            let subst = Subst::from_list(arm);
            for row in &rows {
                assert_eq!(
                    apply_vterm(&subst, row.lhs.clone()),
                    apply_vterm(&subst, row.rhs.clone())
                );
            }
            // A witness is identified up to renaming by its sort and its
            // multiplicity in each of the nine input images. Transposing
            // the images this way retains sharing, including across rows.
            let mut occurrences = BTreeMap::new();
            for (i, key) in keys.iter().enumerate() {
                let identity = Term::Lit(Lit::Var(*key));
                let image = subst.image_of(key).unwrap_or(&identity);
                let factors = match image {
                    Term::App(FunSym::Ac(AcSym::Mult), factors) => factors.as_ref(),
                    t => std::slice::from_ref(t),
                };
                for factor in factors {
                    let Term::Lit(Lit::Var(witness)) = factor else {
                        panic!("unexpected product factor {factor:?}");
                    };
                    occurrences.entry(*witness).or_insert([0usize; 9])[i] += 1;
                }
            }
            let mut signature: Vec<_> = occurrences
                .into_iter()
                .map(|(v, ns)| (v.sort, ns))
                .collect();
            signature.sort();
            result.push(signature);
        }
        result.sort();
        result
    };
    // After cancelling b in the first row, each occurrence from {a,x}
    // also occurs in {y,c}. The second row sends it to one of {u,v,d}.
    // Occurrences from b go directly to {u,v,d}. A Fresh column takes
    // exactly one occurrence and every column must have a nonempty image.
    let mut columns = Vec::new();
    for target in [6, 7, 8] {
        let mut from_b = [0usize; 9];
        from_b[1] = 1;
        from_b[target] = 1;
        columns.push(from_b);
        for source in [0, 2] {
            for middle in [3, 4] {
                let mut column = [0; 9];
                for i in [source, middle, target] {
                    column[i] = 1;
                }
                columns.push(column);
            }
        }
    }
    let mut expected = Vec::new();
    for choice in 0..1u32 << columns.len() {
        let mut unused_image = [0usize; 9];
        unused_image[5] = 1;
        let mut counts = unused_image;
        let mut signature = vec![(LSort::Msg, unused_image)];
        for (j, column) in columns.iter().enumerate() {
            if choice & (1 << j) == 0 {
                continue;
            }
            let mut witness_sort = LSort::Msg;
            for (i, n) in column.iter().enumerate() {
                counts[i] += n;
                if *n != 0 && sorts[i] == LSort::Fresh {
                    witness_sort = LSort::Fresh;
                }
            }
            signature.push((witness_sort, *column));
        }
        if counts
            .iter()
            .zip(sorts)
            .all(|(&n, sort)| n > 0 && (sort != LSort::Fresh || n == 1))
        {
            signature.sort();
            expected.push(signature);
        }
    }
    expected.sort();
    assert_eq!(expected.len(), 84);
    assert_eq!(signatures(native.unify(&rows).unwrap()), expected);
    assert_eq!(native.stats().unify_count, 0);
    if let Some(path) = require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(signatures(oracle.unify(&rows).unwrap()), expected);
    }
}

#[test]
fn native_oracle_public_unify_keeps_a_correlated_equation_across_a_wide_pivot() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::hash_maude_sig;

    let sig = mset_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let var = |name| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)));
    let x = var("x");
    let a = var("a");
    let narrow = f_app_ac(AcSym::Union, vec![x.clone(), hash(a)]);
    let mut operands: Vec<_> = (0..29).map(|i| pub_term(format!("p{i}"))).collect();
    operands.extend([
        var("y"),
        hash(pub_term("one")),
        hash(pub_term("one")),
        hash(pub_term("two")),
    ]);
    let wide = f_app_ac(AcSym::Union, operands);
    // The first equation observes the complete X returned by each pivot arm.
    // The pivot itself is the second equation and has its wide side first.
    let eqs = [
        Equal {
            lhs: var("seen"),
            rhs: hash(x),
        },
        Equal {
            lhs: wide,
            rhs: narrow,
        },
    ];
    let actual = native.unify(&eqs).unwrap();
    assert_eq!(actual.len(), 4);
    let seen = LVar::new("seen", LSort::Msg, 0);
    let x = LVar::new("x", LSort::Msg, 0);
    for arm in &actual {
        let image = |v| {
            arm.iter()
                .find(|(key, _)| *key == v)
                .map(|(_, t)| t)
                .unwrap()
        };
        assert_eq!(*image(seen), hash(image(x).clone()));
    }
    assert_eq!(native.stats().unify_count, 0);

    if let Some(path) = require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(
            canonical_small_ac_answers(actual),
            canonical_small_ac_answers(oracle.unify(&eqs).unwrap())
        );
    }
}

#[test]
fn native_oracle_indivisible_ac_pivot_preserves_occurrences_and_shared_tail() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig};
    let sig = dh_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = require_maude_path()
        .map(|p| MaudeHandle::start_with_backend(&p, sig, AlgebraBackend::Maude).unwrap());
    let var = |sort, i| Term::Lit(Lit::Var(LVar::new("x", sort, i)));
    let [f0, f1, f2, f3] = [0, 1, 2, 3].map(|i| var(LSort::Fresh, i));
    let x = var(LSort::Msg, 4);
    let seen = LVar::new("seen", LSort::Msg, 5);
    let mul = |xs| f_app_ac(AcSym::Mult, xs);
    let wide = mul(vec![f0.clone(), f1.clone(), f1.clone(), f2.clone()]);
    for (a, width, observe) in [(f3.clone(), 3, false), (f3, 3, true), (f1, 1, true)] {
        let narrow = mul(vec![x.clone(), a]);
        for (lhs, rhs) in [(&wide, &narrow), (&narrow, &wide)] {
            let mut eqs = vec![Equal {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            }];
            if observe {
                eqs.insert(
                    0,
                    Equal {
                        lhs: Term::Lit(Lit::Var(seen)),
                        rhs: hash(x.clone()),
                    },
                );
            }
            let actual = native.unify(&eqs).unwrap();
            assert_eq!(actual.len(), width, "{eqs:?}");
            if observe {
                for arm in &actual {
                    let image = |v: LVar| &arm.iter().find(|(k, _)| *k == v).unwrap().1;
                    assert_eq!(
                        image(seen),
                        &hash(image(LVar::new("x", LSort::Msg, 4)).clone())
                    );
                }
            }
            if let Some(oracle) = &oracle {
                assert_eq!(
                    canonical_small_ac_answers(actual),
                    canonical_small_ac_answers(oracle.unify(&eqs).unwrap()),
                    "{eqs:?}"
                );
            }
        }
    }
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn independent_and_shared_peer_exponents_preserve_the_entire_product_family() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::exp;
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::maude_sig::dh_maude_sig;
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig();
    let table = RuleTable::new(&sig).unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let var = |sort, i| Term::Lit(Lit::Var(LVar::new("x", sort, i)));
    // A-GDH2 role C shares its exponent. Role D uses distinct exponents
    // and includes four public observations not used in a peer power.
    for (n, shared) in [(3, true), (4, false)] {
        let mut terms: Vec<_> = (0..4).map(|i| var(LSort::Pub, i)).collect();
        let mut apps = Vec::new();
        for i in 0..n {
            let base = var(LSort::Msg, i + 8);
            let exponent = var(LSort::Fresh, if shared { 4 } else { 4 + i });
            terms.extend([base.clone(), exponent.clone()]);
            apps.push(exp(base, exponent));
        }
        terms.extend(apps);
        let query = f_app_list(terms);
        let Outcome::Complete(rows) = table.joined_variants(&query).unwrap() else {
            panic!("deferred a product of {n} peer-power families");
        };
        assert_eq!(rows.len(), 7usize.pow(n as u32));
        assert_eq!(
            canonical_variants(rows),
            canonical_variants(oracle.variants(&query).unwrap())
        );
    }
}

#[test]
fn native_oracle_specializes_variant_families_to_caller_operands() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, sdec, senc, xor, zero_const};
    use crate::maude_sig::{hash_maude_sig, sym_enc_maude_sig, xor_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = xor_maude_sig()
        .merge(hash_maude_sig())
        .merge(sym_enc_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let v = |i, sort| Term::Lit(Lit::Var(LVar::new("x", sort, i)));
    let x = v(0, LSort::Msg);
    let fresh = v(1, LSort::Fresh);
    let a = pub_term("a");
    let mut cases = vec![
        vec![a.clone(), xor(a.clone(), x.clone())],
        vec![
            xor(fresh.clone(), x.clone()),
            xor(fresh.clone(), v(2, LSort::Fresh)),
        ],
        vec![sdec(x.clone(), a.clone()), x.clone()],
        vec![sdec(senc(x.clone(), a.clone()), v(2, LSort::Msg))],
    ];
    let operands = [
        a,
        zero_const(),
        fresh,
        x.clone(),
        v(2, LSort::Msg),
        hash(x.clone()),
        hash(v(2, LSort::Msg)),
        hash(pub_term("a")),
    ];
    for (i, left) in operands.iter().enumerate() {
        for right in &operands[i..] {
            cases.push(vec![x.clone(), xor(left.clone(), right.clone())]);
        }
    }
    for slots in cases {
        let q = f_app_list(slots.clone());
        let rows = native.variants(&q).unwrap_or_else(|e| panic!("{q}: {e}"));
        let reference = canonical_small_ac_answers(oracle.variants(&q).unwrap());
        assert_eq!(canonical_small_ac_answers(rows.clone()), reference, "{q}");
        let wrapped = f_app_list(slots.iter().cloned().map(hash).collect());
        assert_eq!(
            canonical_small_ac_answers(native.variants(&wrapped).unwrap()),
            reference,
            "{wrapped}"
        );
        for arm in rows {
            let subst = Subst::from_list(arm);
            for t in &slots {
                let instance = apply_vterm(&subst, t.clone());
                assert_eq!(
                    native.reduce(&instance).unwrap(),
                    oracle.reduce(&instance).unwrap(),
                    "{instance}"
                );
            }
        }
    }
    assert_eq!(native.stats().var_count, 0);
}

#[test]
fn native_oracle_free_variant_contexts_preserve_every_observation() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, hash, snd, xor};
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig, xor_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::{f_app_list, f_app_no_eq};

    let Some(path) = require_maude_path() else {
        return;
    };
    let wrap = NoEqSym::new("record", 3, Privacy::Public, Constructability::Constructor);
    let mut sig = hash_maude_sig()
        .merge(xor_maude_sig())
        .merge(pair_maude_sig());
    sig.st_fun_syms.insert(wrap);
    let sig = sig.refresh();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 0)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 0)));
    let a = pub_term("a");
    let sum = xor(a.clone(), x.clone());
    let record = |a, b, c| f_app_no_eq(wrap, vec![a, b, c]);
    for (slots, count) in [
        (vec![a.clone(), hash(sum.clone())], 4),
        (
            vec![record(hash(hash(sum.clone())), y.clone(), sum.clone())],
            4,
        ),
        (
            vec![
                record(fst(x.clone()), snd(x.clone()), y.clone()),
                hash(fst(x.clone())),
            ],
            2,
        ),
        (
            vec![record(fst(x.clone()), snd(y.clone()), x.clone()), y.clone()],
            4,
        ),
    ] {
        let query = f_app_list(slots.clone());
        let rows = native.variants(&query).unwrap();
        assert_eq!(rows.len(), count, "{query}");
        assert_eq!(
            canonical_small_ac_answers(rows.clone()),
            canonical_small_ac_answers(oracle.variants(&query).unwrap()),
            "{query}"
        );
        for arm in rows {
            let subst = Subst::from_list(arm);
            for t in &slots {
                let instance = apply_vterm(&subst, t.clone());
                assert_eq!(
                    native.reduce(&instance).unwrap(),
                    oracle.reduce(&instance).unwrap(),
                    "{instance}"
                );
            }
        }
    }
    // An active parent can introduce its own root variants after the child
    // narrows. Transparently exposing the child would lose these answers.
    let active = hash(fst(sum.clone()));
    let expected = oracle.variants(&active).unwrap();
    assert!(expected.len() > oracle.variants(&sum).unwrap().len());
    assert_eq!(
        canonical_small_ac_answers(native.variants(&active).unwrap()),
        canonical_small_ac_answers(expected)
    );
    assert_eq!(native.stats().var_count, 0);
}

#[test]
fn native_oracle_packed_variants_keep_shared_variables_beside_unique_ground_observations() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, pair, xor};
    use crate::maude_proc::MaudeError;
    use crate::maude_sig::{pair_maude_sig, xor_maude_sig};
    use crate::rewriting::RRule;
    use crate::subst::{apply_vterm, Subst};
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_list;

    // The native-oracle CI job exercises both separate sessions.
    let union = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let var = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let u = var("u", LSort::Msg);
    let v = var("v", LSort::Msg);
    let a = pub_term("a");
    let b = pub_term("b");
    let closed = union(pair(a.clone(), b.clone()), b.clone());
    let mut sig = mset_maude_sig()
        .merge(pair_maude_sig())
        .merge(xor_maude_sig());
    // A user equation independent of XOR. Its only match on closed yields a.
    sig.st_rules.insert(
        rrule_to_ctxt_st_rule(&RRule::new(
            union(pair(u.clone(), v.clone()), v.clone()),
            u.clone(),
        ))
        .unwrap(),
    );
    let sig = sig.refresh();
    let native = |s| {
        MaudeHandle::start_for_tamarin_theory(
            "/nonexistent",
            s,
            AlgebraBackend::ProvedOnly,
            Default::default(),
        )
        .unwrap()
    };
    let h = native(sig.clone());
    let x = var("x", LSort::Fresh);
    let erased = var("erased", LSort::Msg);
    let projection = fst(pair(x.clone(), erased));
    let fixed = pair(closed.clone(), projection);
    let active = xor(x.clone(), var("y", LSort::Fresh));
    let observations = [fixed.clone(), active, closed.clone(), fixed];
    let q = f_app_list(observations.to_vec());
    let arms = h.variants(&q).unwrap();
    assert_eq!(arms.len(), 2);
    if let Some(path) = require_maude_path() {
        let oracle =
            MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();
        assert_eq!(
            canonical_variants(arms.clone()),
            canonical_variants(oracle.variants(&q).unwrap())
        );
        for arm in arms {
            let subst = Subst::from_list(arm);
            for t in &observations {
                let instance = apply_vterm(&subst, t.clone());
                assert_eq!(
                    h.reduce(&instance).unwrap(),
                    oracle.reduce(&instance).unwrap()
                );
            }
        }
    }
    assert_eq!(h.stats().var_count, 0);

    // The second rule yields b on the very same closed term. Neither the
    // closed slot nor its enclosing free constructor may now be skipped.
    let mut ambiguous = sig;
    ambiguous.st_rules.insert(
        rrule_to_ctxt_st_rule(&RRule::new(union(pair(u.clone(), v.clone()), v.clone()), v))
            .unwrap(),
    );
    assert!(matches!(
        native(ambiguous.refresh()).variants(&f_app_list(vec![pair(x, closed)])),
        Err(MaudeError::UnsupportedOperation("variant generation"))
    ));
}

#[test]
fn native_oracle_binary_ac_reduction_agrees_with_maude_for_every_rule_and_alignment() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{pair, xor, zero_const};
    use crate::lean_unification::RuleTable;
    use crate::maude_sig::{pair_maude_sig, xor_maude_sig};
    use crate::subterm_rule::{CtxtStRule, StRhs};

    let x = |name, sort| Term::Lit(Lit::Var(LVar::new(name, sort, 0)));
    let u = x("u", LSort::Msg);
    let v = x("v", LSort::Msg);
    let union = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let rule = |lhs, rhs| {
        CtxtStRule::new(
            lhs,
            StRhs {
                positions: vec![],
                term: rhs,
            },
        )
    };
    let mut sig = mset_maude_sig().merge(pair_maude_sig());
    sig.st_rules
        .insert(rule(union(u.clone(), u.clone()), u.clone()));
    sig.st_rules.insert(rule(
        union(pair(u.clone(), v.clone()), v.clone()),
        u.clone(),
    ));
    let sig = sig.refresh();
    let native = MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        sig.clone(),
        AlgebraBackend::ProvedOnly,
        Default::default(),
    )
    .unwrap();
    let path = require_maude_path();
    let oracle = path
        .as_ref()
        .map(|p| MaudeHandle::start_with_backend(p, sig.clone(), AlgebraBackend::Maude).unwrap());
    // The first query deliberately reuses the local rule-variable name in
    // the subject. The second requires one binding shared by both operands.
    let a = pub_term("a");
    let b = pub_term("b");
    for (subject, expected) in [
        (union(u.clone(), u.clone()), u.clone()),
        (union(pair(v.clone(), u.clone()), u.clone()), v.clone()),
        (union(pair(a.clone(), b.clone()), b.clone()), a.clone()),
        (
            union(pair(a.clone(), b.clone()), a.clone()),
            union(pair(a.clone(), b.clone()), a.clone()),
        ),
    ] {
        assert_eq!(native.reduce(&subject).unwrap(), expected);
        if let Some(reference) = &oracle {
            assert_eq!(reference.reduce(&subject).unwrap(), expected);
        }
    }
    for first in [&a, &u, &v] {
        for second in [&b, &u, &v] {
            for other_operand in [&b, &u, &v] {
                let nested = pair(first.clone(), second.clone());
                let query = union(nested, other_operand.clone());
                let expected = if other_operand == second {
                    first
                } else {
                    &query
                };
                assert_eq!(&native.reduce(&query).unwrap(), expected);
                if let Some(reference) = &oracle {
                    assert_eq!(&reference.reduce(&query).unwrap(), expected);
                }
            }
        }
    }
    assert_eq!(native.stats().norm_count, 0);

    // One rule alone can expose two different normal RHS instances via
    // commutativity. A conclusive native reduction must check both.
    let mut ambiguous = mset_maude_sig();
    ambiguous
        .st_rules
        .insert(rule(union(u.clone(), v.clone()), u.clone()));
    let table = RuleTable::new(&ambiguous.refresh()).unwrap();
    assert_eq!(
        table.reduce_native(&union(a.clone(), b.clone())).unwrap(),
        None
    );
    assert_eq!(
        table.reduce_native(&union(a.clone(), a.clone())).unwrap(),
        Some(a.clone())
    );
    // A second matching rule in the same bucket can disagree as well.
    let mut conflict = sig;
    conflict.st_rules.insert(rule(
        union(u.clone(), u.clone()),
        pair(u.clone(), u.clone()),
    ));
    let table = RuleTable::new(&conflict.refresh()).unwrap();
    assert_eq!(
        table.reduce_native(&union(a.clone(), a.clone())).unwrap(),
        None
    );

    let mut unbound = mset_maude_sig();
    unbound
        .st_rules
        .insert(rule(union(u.clone(), u.clone()), v.clone()));
    assert_eq!(
        RuleTable::new(&unbound.refresh())
            .unwrap()
            .reduce_native(&union(a.clone(), a.clone()))
            .unwrap(),
        None
    );

    // The same rules also handle existing equational theories. Neither
    // Pub nor Msg variables are admitted by the Fresh-XOR specialization.
    let sig = xor_maude_sig();
    let native = MaudeHandle::start_for_tamarin_theory(
        "/nonexistent",
        sig.clone(),
        AlgebraBackend::ProvedOnly,
        Default::default(),
    )
    .unwrap();
    let oracle =
        path.map(|p| MaudeHandle::start_with_backend(&p, sig, AlgebraBackend::Maude).unwrap());
    for sort in [LSort::Pub, LSort::Msg] {
        let name = x("operand", sort);
        let distinct = xor(name.clone(), x("another", sort));
        for (subject, expected) in [
            (distinct.clone(), distinct),
            (xor(name.clone(), name.clone()), zero_const()),
            (xor(name.clone(), zero_const()), name),
        ] {
            assert_eq!(native.reduce(&subject).unwrap(), expected);
            if let Some(reference) = &oracle {
                assert_eq!(reference.reduce(&subject).unwrap(), expected);
            }
        }
    }
    assert_eq!(native.stats().norm_count, 0);
}

fn renamed_cancellation_signature() -> (crate::maude_sig::MaudeSig, AcSym, LNTerm) {
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, NoEqSym, Privacy};
    use crate::maude_sig::hash_maude_sig;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_no_eq;

    let op = AcFctSym::new(
        b"combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    let e = NoEqSym::new(
        b"neutral",
        0,
        Privacy::Public,
        Constructability::Constructor,
    );
    let unit = f_app_no_eq(e, vec![]);
    let combine = |args| f_app_ac(AcSym::AcFct(op), args);
    let var = |name, id| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, id)));
    let [u, v, w, z] = [
        ("dup", 15),
        ("withUnit", 9),
        ("doubled", 4),
        ("survivor", 1),
    ]
    .map(|(name, id)| var(name, id));
    let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
    let mut sig = hash_maude_sig();
    sig.st_fun_syms.insert(e);
    sig.st_ac_fun_syms.insert(op);
    sig.st_rules
        .insert(rule(combine(vec![u.clone(), u]), unit.clone()));
    sig.st_rules
        .insert(rule(combine(vec![unit.clone(), v.clone()]), v));
    sig.st_rules
        .insert(rule(combine(vec![w.clone(), z.clone(), w]), z));
    (sig.refresh(), AcSym::AcFct(op), unit)
}

#[test]
fn native_oracle_binary_msg_cancellation_recognizes_renamed_rules_and_checks_parity() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_proc::MaudeError;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;

    let Some(path) = require_maude_path() else {
        return;
    };
    let (sig, op, unit) = renamed_cancellation_signature();
    let combine = |args| f_app_ac(op, args);
    let var = |name, id| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, id)));
    let rule = |lhs, rhs| rrule_to_ctxt_st_rule(&RRule::new(lhs, rhs)).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, sig.clone(), AlgebraBackend::Maude).unwrap();

    let open = combine(vec![var("left", 21), var("right", 22)]);
    let variants = native.variants(&open).unwrap();
    assert_eq!(variants.len(), 7);
    assert_eq!(
        canonical_small_ac_answers(variants),
        canonical_small_ac_answers(oracle.variants(&open).unwrap())
    );

    // Vary two nonground/rigid factors independently; include two copies of
    // the unit even when both real factors disappear.
    let a = var("atom", 30);
    let b = hash(pub_term("b"));
    let specialized = combine(vec![a.clone(), b.clone()]);
    let rows = native.variants(&specialized).unwrap();
    assert_eq!(rows.len(), 4);
    assert_eq!(
        canonical_small_ac_answers(rows),
        canonical_small_ac_answers(oracle.variants(&specialized).unwrap())
    );
    for i in 0..=3 {
        for j in 0..=3 {
            let mut factors = vec![unit.clone(); 2];
            factors.extend(std::iter::repeat_n(a.clone(), i));
            factors.extend(std::iter::repeat_n(b.clone(), j));
            let subject = combine(factors);
            let expected = match (i % 2, j % 2) {
                (0, 0) => unit.clone(),
                (1, 0) => a.clone(),
                (0, 1) => b.clone(),
                _ => combine(vec![a.clone(), b.clone()]),
            };
            assert_eq!(
                native.reduce(&subject).unwrap(),
                expected,
                "multiplicities {i}, {j}"
            );
            assert_eq!(
                oracle.reduce(&subject).unwrap(),
                expected,
                "multiplicities {i}, {j}"
            );
        }
    }

    // This fourth rule makes two distinct, nonunit factors disappear.
    let h = var("h", 7);
    let exceptional = combine(vec![h.clone(), hash(h)]);
    let mut changed = sig;
    changed.st_rules.insert(rule(exceptional, unit.clone()));
    let changed = changed.refresh();
    let changed_native = MaudeHandle::start_with_backend(
        "/nonexistent",
        changed.clone(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    assert!(matches!(
        changed_native.variants(&open),
        Err(MaudeError::UnsupportedOperation(_))
    ));
    assert!(matches!(
        changed_native.variants(&specialized),
        Err(MaudeError::UnsupportedOperation(_))
    ));
    let changed_oracle =
        MaudeHandle::start_with_backend(&path, changed, AlgebraBackend::Maude).unwrap();
    let ground = pub_term("example");
    let exceptional = combine(vec![ground.clone(), hash(ground)]);
    assert_eq!(native.reduce(&exceptional).unwrap(), exceptional);
    assert_eq!(changed_oracle.reduce(&exceptional).unwrap(), unit);
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_binary_msg_cancellation_packed_seven_preserve_ambient_values() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{pair, xor};
    use crate::lterm::frees_list;
    use crate::maude_sig::{pair_maude_sig, xor_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = xor_maude_sig().merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    // x.6 is the first witness the isolated x.4 XOR x.5 family would allocate.
    let [x, y, ambient] = [4, 5, 6].map(|i| Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i))));
    let op = xor(x.clone(), y.clone());
    let slots = vec![
        ambient.clone(),
        op.clone(),
        pair(ambient.clone(), x.clone()),
        y.clone(),
        op,
    ];
    let query = f_app_list(slots.clone());
    let variants = native.variants(&query).unwrap();
    assert_eq!(variants.len(), 7);
    assert_eq!(
        canonical_small_ac_answers(variants.clone()),
        canonical_small_ac_answers(oracle.variants(&query).unwrap())
    );
    for arm in variants {
        let subst = Subst::from_list(arm);
        let instance = |t: &LNTerm| apply_vterm(&subst, t.clone());
        let Term::Lit(Lit::Var(a)) = instance(&ambient) else {
            panic!("ambient image must remain free")
        };
        for t in [&x, &y] {
            assert!(!frees_list(&instance(t)).contains(&a));
        }
        for slot in &slots {
            let applied = instance(slot);
            assert_eq!(
                native.reduce(&applied).unwrap(),
                oracle.reduce(&applied).unwrap(),
                "slot {slot:?}, instance {applied:?}"
            );
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_open_subject_matching_preserves_joint_rigid_images() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, pair};
    use crate::maude_sig::{bp_maude_sig, dh_maude_sig, pair_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = mset_maude_sig()
        .merge(bp_maude_sig())
        .merge(dh_maude_sig())
        .merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = LVar::new("x", LSort::Msg, 2);
    let y = LVar::new("y", LSort::Msg, 2);
    let p = LVar::new("x", LSort::Pub, 2);
    let var = |v| Term::Lit(Lit::Var(v));
    let supplied = Term::Lit(Lit::Con(super::skolem_name(0, &x)));
    let bag = |a, b| f_app_ac(AcSym::Union, vec![a, b]);
    let eq = |lhs, rhs| Equal { lhs, rhs }; // subject, pattern
    let matched = |qs: &[Equal<LNTerm>], expected: Vec<Vec<(LVar, LNTerm)>>| {
        let expected = canonical_ground_answers(expected);
        assert_eq!(
            canonical_ground_answers(maude.match_eqs(qs).unwrap()),
            expected,
            "{qs:?}"
        );
        assert_eq!(native.match_eqs(qs).unwrap(), expected, "{qs:?}");
        assert_eq!(native.has_match_eqs(qs).unwrap(), !expected.is_empty());
    };
    // A simultaneous image may contain its own domain variable. Matching
    // never chases y in x's image, including across separate equations.
    let image = pair(var(x), var(y));
    matched(
        &[eq(image.clone(), var(x)), eq(var(x), var(y))],
        vec![vec![(x, image), (y, var(x))]],
    );
    matched(&[eq(var(x), var(p))], vec![]);
    matched(&[eq(var(p), var(x))], vec![vec![(x, var(p))]]);
    matched(&[eq(var(x), bag(var(y), supplied.clone()))], vec![]);
    // Even an atom with an internal-looking spelling is distinct from the
    // subject variable in the other AC factor.
    matched(
        &[eq(
            bag(supplied.clone(), var(x)),
            bag(supplied.clone(), var(y)),
        )],
        vec![vec![(y, var(x))]],
    );
    matched(&[eq(var(x), var(y)), eq(supplied, var(y))], vec![]);

    // The common x belongs to different namespaces. Both orientations must
    // survive under C and under AC, also when that choice sits below a free head.
    let arms = [
        vec![(x, var(x)), (y, var(p))],
        vec![(x, var(p)), (y, var(x))],
    ];
    for (pattern, subject) in [
        (emap(var(x), var(y)), emap(var(x), var(p))),
        (bag(var(x), var(y)), bag(var(x), var(p))),
    ] {
        matched(
            &[eq(pair(subject, var(p)), pair(pattern, var(p)))],
            arms.iter()
                .map(|a| {
                    let mut a = a.clone();
                    a.push((p, var(p)));
                    a
                })
                .collect(),
        );
    }
    // AC partitions can put an entire nonempty product in one binding.
    // Exercise every pair of patterns/subjects, including repeated variables
    // inside C factors and cross-equation constraints on a surviving witness.
    let terms = [
        var(x),
        var(p),
        bag(var(x), var(y)),
        bag(var(x), var(x)),
        bag(bag(var(p), var(y)), var(x)),
        emap(var(p), var(x)),
        bag(emap(var(p), var(x)), var(y)),
        bag(emap(var(p), var(x)), emap(var(y), var(p))),
    ];
    for pattern in &terms {
        for subject in &terms {
            let first = eq(subject.clone(), pattern.clone());
            for query in [vec![first.clone()], vec![first.clone(), eq(var(p), var(y))]] {
                assert_eq!(
                    native.match_eqs(&query).unwrap(),
                    canonical_ground_answers(maude.match_eqs(&query).unwrap()),
                    "{query:?}"
                );
            }
        }
    }
    assert_eq!(native.stats().match_count, 0);
}

#[test]
fn native_oracle_mixed_cancellation_preserves_all_nine_xor_observations() {
    check_mixed_cancellation_rows(
        crate::maude_sig::xor_maude_sig(),
        AcSym::Xor,
        crate::builtin::zero_const(),
    );
}

#[test]
fn native_oracle_mixed_cancellation_preserves_all_nine_renamed_observations() {
    let (signature, op, unit) = renamed_cancellation_signature();
    check_mixed_cancellation_rows(signature, op, unit);
}

fn check_mixed_cancellation_rows(
    signature: crate::maude_sig::MaudeSig,
    symbol: AcSym,
    zero: LNTerm,
) {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::pair;
    use crate::maude_sig::pair_maude_sig;
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let literal = |v| Term::Lit(Lit::Var(v));
    let primary = [
        LVar::new("left", LSort::Fresh, 4),
        LVar::new("right", LSort::Fresh, 8),
        LVar::new("payload", LSort::Msg, 6),
    ];
    let [left, right, payload] = primary.map(literal);
    // The isolated leaf currently chooses x.11 as its third (Msg) witness.
    // The packed observer with that identity must stay independent of the leaf.
    let ambient = LVar::new("x", LSort::Msg, 11);
    let inputs = [primary[0], primary[1], primary[2], ambient];
    let signature = signature.merge(pair_maude_sig());
    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        signature.clone(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, signature, AlgebraBackend::Maude).unwrap();
    let product = |xs: &[&LNTerm]| f_app_ac(symbol, xs.iter().map(|t| (*t).clone()).collect());
    let slots = |a: &LNTerm, b: &LNTerm, m: &LNTerm, sum: &LNTerm, other: &LNTerm| {
        vec![
            other.clone(),
            sum.clone(),
            pair(other.clone(), a.clone()),
            b.clone(),
            m.clone(),
            a.clone(),
            sum.clone(),
        ]
    };
    let query_slots = slots(
        &left,
        &right,
        &payload,
        &product(&[&left, &right, &payload]),
        &literal(ambient),
    );
    let query = f_app_list(query_slots.clone());
    // The full observation vector goes into a single synthetic binding so
    // canonical_small_ac_answers uses one witness renaming for every slot.
    let row_key = LVar::new("row", LSort::Msg, 0);
    let (a, b, u, other) = (
        left.clone(),
        right.clone(),
        payload.clone(),
        literal(ambient),
    );
    let expected = [
        (&b, u.clone(), product(&[&a, &b, &u])),
        (&b, zero.clone(), product(&[&a, &b])),
        (&b, a.clone(), b.clone()),
        (&b, b.clone(), a.clone()),
        (&b, product(&[&a, &u]), product(&[&b, &u])),
        (&b, product(&[&b, &u]), product(&[&a, &u])),
        (&b, product(&[&a, &b]), zero),
        (&b, product(&[&a, &b, &u]), u.clone()),
        (&a, u.clone(), u.clone()),
    ]
    .into_iter()
    .map(|(second, m, value)| vec![(row_key, f_app_list(slots(&a, second, &m, &value, &other)))])
    .collect();
    let expected = canonical_small_ac_answers(expected);
    for backend in [&oracle, &native] {
        let variants = backend.variants(&query).unwrap();
        assert_eq!(variants.len(), 9, "{symbol:?}");
        let mut rows = Vec::new();
        for arm in variants {
            assert!(arm.iter().all(|(key, _)| inputs.contains(key)));
            let substitution = Subst::from_list(arm);
            let values = query_slots
                .iter()
                .map(|t| {
                    backend
                        .reduce(&apply_vterm(&substitution, t.clone()))
                        .unwrap()
                })
                .collect();
            rows.push(vec![(row_key, f_app_list(values))]);
        }
        assert_eq!(canonical_small_ac_answers(rows), expected, "{symbol:?}");
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_staged_cancellation_and_guarded_ac_contexts() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{hash, pair};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig, xor_maude_sig};
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let (renamed, custom, _) = renamed_cancellation_signature();
    for (signature, symbol) in [
        (xor_maude_sig().merge(hash_maude_sig()), AcSym::Xor),
        (renamed, custom),
    ] {
        let signature = signature.merge(pair_maude_sig());
        let native = native_session(signature.clone());
        let oracle =
            MaudeHandle::start_with_backend(&path, signature, AlgebraBackend::Maude).unwrap();
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 2)));
        let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Fresh, 2)));
        let a = pub_term("a");
        let b = pub_term("b");
        let sum = |args| f_app_ac(symbol, args);
        let inner = sum(vec![x.clone(), a.clone(), b.clone()]);
        let guarded = sum(vec![hash(inner.clone()), pair(y.clone(), inner.clone())]);
        let observation = LVar::new("row", LSort::Msg, 0);
        for t in [
            inner.clone(),
            sum(vec![x.clone(), y.clone(), a.clone(), y.clone()]),
            sum(vec![x.clone(), hash(y.clone()), a.clone(), b.clone()]),
            sum(vec![x.clone(), a.clone(), b.clone(), a.clone(), b.clone()]),
            guarded.clone(),
        ] {
            // Observe all caller images and the final value under a single
            // witness renaming, retaining the raw number of returned rows.
            let slots = [x.clone(), y.clone(), t];
            let query = f_app_list(slots.to_vec());
            let valued = |backend: &MaudeHandle| {
                let rows = backend
                    .variants(&query)
                    .unwrap_or_else(|e| panic!("{query}: {e}"));
                canonical_small_ac_answers(
                    rows.into_iter()
                        .map(|arm| {
                            let subst = Subst::from_list(arm);
                            let values = slots
                                .iter()
                                .map(|t| backend.reduce(&apply_vterm(&subst, t.clone())).unwrap())
                                .collect();
                            vec![(observation, f_app_list(values))]
                        })
                        .collect(),
                )
            };
            assert_eq!(valued(&native), valued(&oracle), "{query}");
        }
        // Equal heads permit a real root cancellation after the inner sum
        // reduces. A guard that only checked constructor stability would
        // wrongly reconstruct the unreduced pair.
        let z = hash(sum(vec![a.clone(), a.clone(), b.clone()]));
        let reducible = sum(vec![z, hash(b.clone())]);
        assert_eq!(
            native.reduce(&reducible).unwrap(),
            oracle.reduce(&reducible).unwrap()
        );
        assert_eq!(native.stats().var_count, 0);
        assert_eq!(native.stats().norm_count, 0);
    }
}

/// Compare the raw caller images and every normalized observation together,
/// up to a single witness renaming. A reducible image is an invalid row.
fn valued_variant_rows(
    handle: &MaudeHandle,
    slots: &[LNTerm],
) -> crate::lean_unification::Substitutions {
    use crate::subst::{apply_vterm, Subst};
    use crate::term::f_app_list;
    let query = f_app_list(slots.to_vec());
    let rows = handle
        .variants(&query)
        .unwrap_or_else(|e| panic!("{query}: {e}"));
    let mut inputs = crate::lterm::frees_list(&query);
    inputs.sort();
    inputs.dedup();
    canonical_small_ac_answers(
        rows.into_iter()
            .map(|row| {
                for (key, image) in &row {
                    assert!(inputs.contains(key), "{query}: unexpected binding {key}");
                    assert_eq!(
                        handle.reduce(image).unwrap(),
                        crate::term::map_lits(image, &mut |lit| *lit),
                        "{query}: reducible image for {key}"
                    );
                }
                let subst = Subst::from_list(row);
                let mut values: Vec<_> = inputs
                    .iter()
                    .map(|&k| apply_vterm(&subst, Term::Lit(Lit::Var(k))))
                    .collect();
                values.extend(slots.iter().map(|t| {
                    let instance = apply_vterm(&subst, t.clone());
                    handle
                        .reduce(&instance)
                        .unwrap_or_else(|err| panic!("{query}: {instance}: {err}"))
                }));
                vec![(LVar::new("row", LSort::Msg, 0), f_app_list(values))]
            })
            .collect(),
    )
}

#[test]
fn native_oracle_nested_cancellation_shares_normal_values_and_images() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::maude_sig::{hash_maude_sig, xor_maude_sig};
    use crate::term::f_app_list;

    let Some(path) = require_maude_path() else {
        return;
    };
    let (custom_signature, custom, _) = renamed_cancellation_signature();
    for (signature, symbol) in [
        (xor_maude_sig().merge(hash_maude_sig()), AcSym::Xor),
        (custom_signature, custom),
    ] {
        let native = native_session(signature.clone());
        let reference =
            MaudeHandle::start_with_backend(&path, signature, AlgebraBackend::Maude).unwrap();
        let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 7)));
        let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 8)));
        let sum = |a, b| f_app_ac(symbol, vec![a, b]);
        let inners = [
            sum(x.clone(), pub_term("a")),
            sum(y.clone(), pub_term("b")),
            sum(x.clone(), y.clone()),
        ];
        // Both local families are irredundant. Joining them introduces an
        // extra (x=0,y=0) row already covered by another joint variant.
        let joined = vec![sum(x.clone(), y.clone()), sum(x.clone(), pub_term("a"))];
        assert_eq!(
            native.variants(&f_app_list(joined.clone())).unwrap().len(),
            23
        );
        let mut cases = vec![joined];
        for outer in [x.clone(), y.clone(), hash(x.clone())] {
            for inner in &inners {
                cases.push(vec![sum(outer.clone(), hash(inner.clone())), inner.clone()]);
            }
        }
        cases.push(vec![sum(hash(inners[0].clone()), hash(inners[0].clone()))]);
        cases.push(vec![
            sum(hash(inners[0].clone()), hash(inners[1].clone())),
            inners[1].clone(),
        ]);
        let deep = sum(x.clone(), hash(sum(x.clone(), hash(inners[0].clone()))));
        cases.push(vec![deep, inners[0].clone()]);
        cases.push(vec![f_app_ac(
            symbol,
            vec![pub_term("a"), x.clone(), hash(inners[1].clone())],
        )]);
        for slots in cases {
            let query = f_app_list(slots.clone());
            assert_eq!(
                valued_variant_rows(&native, &slots),
                valued_variant_rows(&reference, &slots),
                "{query}"
            );
        }
        assert_eq!(native.stats().var_count, 0);
        assert_eq!(native.stats().norm_count, 0);
    }
}

#[test]
fn nested_cancellation_does_not_assume_a_unique_value_for_unrelated_rules() {
    use crate::builtin::{fst, hash, pair};
    use crate::function_symbols::{Constructability, NoEqSym, Privacy};
    use crate::lean_unification::{Outcome, RuleTable};
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    use crate::term::f_app_no_eq;

    let (mut sig, symbol, _) = renamed_cancellation_signature();
    let choice = NoEqSym::new(b"choice", 2, Privacy::Public, Constructability::Constructor);
    let apply = |l, r| f_app_no_eq(choice, vec![l, r]);
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 1)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 2)));
    sig.st_fun_syms.insert(choice);
    for result in [x.clone(), y.clone()] {
        sig.st_rules.insert(
            rrule_to_ctxt_st_rule(&RRule::new(apply(x.clone(), y.clone()), result)).unwrap(),
        );
    }
    let sig = sig.merge(crate::maude_sig::pair_maude_sig()).refresh();
    let table = RuleTable::new(&sig).unwrap();
    // Root cancellation and independent rewrites in the two copies can lead
    // to different normal values for exactly the same caller substitution.
    let child = apply(x.clone(), hash(x));
    for arg in [
        child.clone(),
        fst(pair(child.clone(), y.clone())),
        fst(hash(child.clone())),
    ] {
        let query = f_app_ac(symbol, vec![arg.clone(), arg]);
        assert_eq!(table.joined_variants(&query).unwrap(), Outcome::Unsupported);
    }
}

#[test]
fn native_oracle_positional_parents_stage_normal_values_and_repeated_keys() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fst, hash, pair, pk, sdec, senc, sign, snd, verify, xor};
    use crate::maude_sig::{
        hash_maude_sig, pair_maude_sig, signature_maude_sig, sym_enc_maude_sig, xor_maude_sig,
    };

    let Some(path) = require_maude_path() else {
        return;
    };
    let (renamed, second, _) = renamed_cancellation_signature();
    let sig = pair_maude_sig()
        .merge(renamed)
        .merge(signature_maude_sig())
        .merge(xor_maude_sig())
        .merge(hash_maude_sig())
        .merge(sym_enc_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let reference = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 7)));
    let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, 8)));
    let a = pub_term("a");
    let sum = xor(x.clone(), y.clone());
    let combine = |left, right| f_app_ac(second, vec![left, right]);
    let product = xor(x.clone(), a.clone());
    let exposed = fst(pair(product.clone(), x.clone()));
    let projected_sum = xor(exposed.clone(), a.clone());
    let alternating = combine(
        xor(
            fst(pair(combine(x.clone(), a.clone()), y.clone())),
            a.clone(),
        ),
        y.clone(),
    );
    assert_eq!(native.reduce(&projected_sum).unwrap(), x);
    assert_eq!(reference.reduce(&projected_sum).unwrap(), x);
    for slots in [
        vec![verify(
            sign(fst(x.clone()), y.clone()),
            snd(x.clone()),
            pk(y.clone()),
        )],
        vec![xor(y.clone(), fst(x.clone())), fst(x.clone())],
        vec![projected_sum, exposed],
        vec![combine(x.clone(), xor(x.clone(), a.clone())), x.clone()],
        vec![alternating, x.clone()],
        vec![fst(snd(x.clone()))],
        vec![xor(y.clone(), hash(fst(x.clone()))), fst(x.clone())],
        vec![
            xor(hash(fst(x.clone())), hash(snd(x.clone()))),
            snd(x.clone()),
        ],
        vec![fst(sum.clone()), sum],
        vec![
            sdec(senc(y.clone(), fst(x.clone())), snd(x.clone())),
            x.clone(),
        ],
        vec![sdec(y.clone(), hash(fst(x.clone()))), fst(x.clone())],
        vec![sdec(senc(snd(x.clone()), fst(x.clone())), fst(x.clone()))],
        vec![fst(pair(snd(x.clone()), y.clone())), y.clone()],
        vec![fst(hash(snd(x.clone()))), fst(snd(hash(a.clone())))],
    ] {
        assert_eq!(
            valued_variant_rows(&native, &slots),
            valued_variant_rows(&reference, &slots),
            "{slots:?}"
        );
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_wide_nested_cancellation_with_fresh_variables() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fresh_var, hash, msg_var, pair};
    use crate::maude_sig::{hash_maude_sig, pair_maude_sig, xor_maude_sig};
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = xor_maude_sig()
        .merge(hash_maude_sig())
        .merge(pair_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let (x, y, z) = (msg_var("m", 0), msg_var("m", 1), fresh_var("f", 0));
    let sum = |xs| f_app_ac(AcSym::Xor, xs);
    let inner = sum(vec![x.clone(), y.clone()]);
    let sibling = sum(vec![pub_term("b"), x.clone()]);
    for variable in [&x, &y] {
        for value in [hash(inner.clone()), pair(sibling.clone(), inner.clone())] {
            let slots = [sum(vec![z.clone(), variable.clone(), value])];
            assert_eq!(
                valued_variant_rows(&native, &slots),
                valued_variant_rows(&oracle, &slots),
                "{}",
                slots[0]
            );
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_signed_graph_compares_all_caller_and_observation_coordinates() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{inv, msg_var, mult};
    use crate::lean_unification::RuleTable;
    use crate::maude_sig::dh_maude_sig;
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig();
    let table = RuleTable::new(&sig).unwrap();
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = msg_var("caller", 0);
    let y = msg_var("caller", 1);
    let direct = mult(x.clone(), y.clone());
    let quotient = mult(x.clone(), inv(y.clone()));
    let sq = mult(x.clone(), x.clone());
    let cube = mult(x.clone(), sq.clone());
    for slots in [
        vec![cube.clone(), x.clone(), cube.clone()],
        vec![inv(cube.clone()), x.clone()],
        vec![msg_var("other", 1), cube.clone(), x.clone()],
        vec![crate::builtin::fresh_var("caller", 0), cube, x.clone()],
        vec![inv(x.clone()), sq],
        vec![x.clone(), direct.clone(), y.clone()],
        vec![inv(direct.clone()), y.clone(), x.clone()],
        vec![x.clone(), quotient, y.clone()],
        vec![mult(x.clone(), inv(x.clone())), x.clone()],
    ] {
        let query = f_app_list(slots.clone());
        let mut keys = crate::lterm::frees_list(&query);
        keys.sort();
        keys.dedup();
        let expected = valued_variant_rows(&oracle, &slots);
        let packet = table
            .signed_graph_probe(&keys, &slots)
            .unwrap()
            .unwrap_or_else(|| panic!("deferred {query} (Maude produced {} rows)", expected.len()));
        let got = canonical_small_ac_answers(
            packet
                .into_iter()
                .map(|terms| vec![(LVar::new("row", LSort::Msg, 0), f_app_list(terms))])
                .collect(),
        );
        assert_eq!(got, expected, "{query}");
        assert_eq!(
            valued_variant_rows(&native, &slots),
            expected,
            "public {query}"
        );
    }
}

#[path = "lean_variant_frontier_tests.rs"]
mod frontier;

#[path = "lean_pairing_power_tests.rs"]
mod pairing_power;

#[test]
fn native_oracle_narrowing_preserves_signed_dh_products_and_powers() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{exp, fresh_var, inv, msg_var, mult};
    use crate::maude_sig::dh_maude_sig;
    let Some(path) = require_maude_path() else {
        return;
    };
    let native =
        MaudeHandle::start_with_backend("/nonexistent", dh_maude_sig(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle =
        MaudeHandle::start_with_backend(&path, dh_maude_sig(), AlgebraBackend::Maude).unwrap();
    let x = msg_var("x", 0);
    let y = msg_var("y", 1);
    let r = fresh_var("r", 0);
    for (app, count) in [
        (inv(x.clone()), 4),
        (mult(x.clone(), x.clone()), 4),
        (inv(mult(x.clone(), x.clone())), 4),
        (mult(x.clone(), y.clone()), 47),
        (mult(x.clone(), inv(y.clone())), 47),
        (inv(mult(x.clone(), y.clone())), 64),
        (mult(inv(x.clone()), inv(y.clone())), 64),
        (mult(mult(x.clone(), y.clone()), r.clone()), 158),
        (exp(x.clone(), y.clone()), 48),
        (exp(pub_term("g"), mult(x.clone(), y.clone())), 48),
        (exp(exp(pub_term("g"), x.clone()), y), 48),
        (mult(x.clone(), r.clone()), 6),
        (mult(x.clone(), inv(r.clone())), 6),
        (inv(mult(x.clone(), r.clone())), 8),
    ] {
        for slots in [[app.clone(), x.clone()], [x.clone(), app.clone()]] {
            let expected = valued_variant_rows(&oracle, &slots);
            assert_eq!(expected.len(), count, "{slots:?}");
            assert_eq!(valued_variant_rows(&native, &slots), expected, "{slots:?}");
        }
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_oracle_scalar_action_rows_share_inputs_and_outputs() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, hash, inv, msg_var, pmult};
    use crate::maude_sig::{bp_maude_sig, hash_maude_sig};

    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = bp_maude_sig().merge(hash_maude_sig());
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    // Names deliberately overlap the implementation's fresh point and scalar
    // variables. A third, unobserved-by-the-component variable remains independent.
    let x = msg_var("point", 0);
    let y = msg_var("scalar", 0);
    let unrelated = msg_var("x", 1);
    for (app, count) in [
        (pmult(x.clone(), y.clone()), 47),
        (pmult(inv(x.clone()), y.clone()), 47),
        (pmult(y.clone(), inv(x.clone())), 53),
        (emap(y.clone(), inv(x.clone())), 54),
        (emap(x.clone(), y.clone()), 48),
    ] {
        for slots in [
            vec![app.clone(), x.clone(), y.clone()],
            vec![
                hash(unrelated.clone()),
                y.clone(),
                hash(app.clone()),
                x.clone(),
                app.clone(),
            ],
        ] {
            let wanted = valued_variant_rows(&oracle, &slots);
            assert_eq!(wanted.len(), count);
            assert_eq!(valued_variant_rows(&native, &slots), wanted, "{slots:?}");
        }
    }
    for app in [
        pmult(inv(x.clone()), inv(y.clone())),
        emap(inv(x.clone()), inv(y.clone())),
    ] {
        let slots = [app, x.clone(), y.clone()];
        let wanted = valued_variant_rows(&oracle, &slots);
        assert!(!wanted.is_empty());
        assert_eq!(valued_variant_rows(&native, &slots), wanted, "{slots:?}");
    }
    let f = crate::builtin::fresh_var("point", 0);
    for (app, count) in [
        (pmult(x.clone(), pmult(f.clone(), y.clone())), 159),
        (emap(pmult(f.clone(), x.clone()), y.clone()), 160),
        (emap(x.clone(), pmult(f.clone(), x.clone())), 8),
        (emap(inv(x.clone()), pmult(f.clone(), y.clone())), 178),
        (
            emap(pmult(f.clone(), x.clone()), pmult(f.clone(), y.clone())),
            336,
        ),
        (
            emap(x.clone(), pmult(f.clone(), pmult(f.clone(), x.clone()))),
            8,
        ),
    ] {
        let slots = [app, x.clone(), y.clone(), f.clone()];
        let wanted = valued_variant_rows(&oracle, &slots);
        assert_eq!(wanted.len(), count, "{slots:?}");
        assert_eq!(valued_variant_rows(&native, &slots), wanted, "{slots:?}");
    }
    assert_eq!(native.stats().var_count, 0);
    assert_eq!(native.stats().norm_count, 0);
}

#[test]
fn native_point_reduction_uses_changed_rules_even_without_refresh() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, msg_var, pmult};
    use crate::maude_sig::bp_maude_sig;
    use crate::rewriting::RRule;
    use crate::subterm_rule::rrule_to_ctxt_st_rule;
    let x = msg_var("x", 0);
    let y = msg_var("y", 0);
    let a = pub_term("a");
    let b = pub_term("b");
    for (lhs, query) in [
        (emap(x.clone(), x.clone()), emap(a.clone(), a.clone())),
        (pmult(x.clone(), y), pmult(a.clone(), b)),
    ] {
        let mut sig = bp_maude_sig();
        sig.st_rules
            .insert(rrule_to_ctxt_st_rule(&RRule::new(lhs, x.clone())).unwrap());
        let h = MaudeHandle::start_for_tamarin_theory(
            "/nonexistent",
            sig,
            AlgebraBackend::ProvedOnly,
            Default::default(),
        )
        .unwrap();
        assert_eq!(h.reduce(&query).unwrap(), a, "{query}");
        assert_eq!(h.stats().norm_count, 0);
    }
}

#[test]
fn native_oracle_signed_stable_leaves_share_subterms_and_sorted_variables() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{fresh_var, hash, inv, msg_var, mult};
    use crate::lean_unification::RuleTable;
    use crate::maude_sig::{dh_maude_sig, hash_maude_sig};
    use crate::term::f_app_list;
    let Some(path) = require_maude_path() else {
        return;
    };
    let sig = dh_maude_sig().merge(hash_maude_sig());
    let table = RuleTable::new(&sig).unwrap();
    let native = native_session(sig.clone());
    let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    let x = msg_var("shared", 0);
    let r = fresh_var("shared", 0);
    let h = hash(x.clone());
    let c = pub_term("c");
    for slots in [
        vec![mult(x.clone(), r.clone()), r.clone(), x.clone()],
        vec![mult(x.clone(), h.clone()), h.clone(), x.clone()],
        vec![mult(x.clone(), inv(h.clone())), x.clone()],
        vec![mult(c.clone(), inv(r.clone())), r.clone(), c],
        vec![
            mult(mult(x.clone(), x.clone()), r.clone()),
            x.clone(),
            r.clone(),
        ],
        vec![
            mult(mult(x.clone(), x.clone()), h.clone()),
            x.clone(),
            h.clone(),
        ],
        vec![
            mult(r.clone(), inv(fresh_var("other", 1))),
            r.clone(),
            fresh_var("other", 1),
        ],
        vec![inv(mult(r.clone(), r.clone())), r.clone()],
    ] {
        let query = f_app_list(slots.clone());
        let mut keys = crate::lterm::frees_list(&query);
        keys.sort();
        keys.dedup();
        let expected = valued_variant_rows(&oracle, &slots);
        let packet = table
            .signed_leaf_probe(&keys, &slots)
            .unwrap()
            .unwrap_or_else(|| panic!("leaf graph deferred {query}"));
        let got = canonical_small_ac_answers(
            packet
                .into_iter()
                .map(|terms| vec![(LVar::new("row", LSort::Msg, 0), f_app_list(terms))])
                .collect(),
        );
        assert_eq!(got, expected, "stable leaf graph for {query}");
        assert_eq!(
            valued_variant_rows(&native, &slots),
            expected,
            "public {query}"
        );
    }
}

fn distributed_class_equation(vars: &[LNTerm], a: usize, b: usize, c: usize) -> Equal<LNTerm> {
    let split = vars.len() - 2;
    Equal {
        lhs: f_app_ac(
            AcSym::Union,
            vars[..split]
                .iter()
                .flat_map(|v| std::iter::repeat_n(v.clone(), a))
                .chain(std::iter::repeat_n(vars[split].clone(), b))
                .collect(),
        ),
        rhs: f_app_ac(AcSym::Union, vec![vars[split + 1].clone(); c]),
    }
}

#[test]
fn public_full_unifiers_distribute_a_mixed_weight_column_class() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::subst::{apply_vterm, Subst};
    use std::collections::BTreeSet;

    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let vars: Vec<_> = (0..8)
        .map(|i| Term::Lit(Lit::Var(LVar::new("v", LSort::Msg, i))))
        .collect();
    // Let S be the sum of the first six images, B and C the remaining two.
    // The equations 29S+31B=60C and 17S+16B=33C force S=B=C for each
    // atom separately. Thus the unique most general answer has one distinct
    // witness per original summand, with both B and C equal to their sum.
    let rows = [
        distributed_class_equation(&vars, 29, 31, 60),
        distributed_class_equation(&vars, 17, 16, 33),
    ];
    let arms = native.unify(&rows).unwrap();
    assert_eq!(arms.len(), 1);
    let subst = Subst::from_list(arms.into_iter().next().unwrap());
    let images: Vec<_> = vars
        .iter()
        .map(|v| apply_vterm(&subst, v.clone()))
        .collect();
    assert!(images[..6]
        .iter()
        .all(|t| matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg)));
    assert_eq!(images[..6].iter().collect::<BTreeSet<_>>().len(), 6);
    let joined = f_app_ac(AcSym::Union, images[..6].to_vec());
    assert_eq!(images[6], joined);
    assert_eq!(images[7], joined);
    assert_eq!(native.stats().unify_count, 0);
}

#[test]
fn public_full_unifiers_keep_all_five_covering_distributions() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::subst::{apply_vterm, Subst};
    use std::collections::BTreeMap;

    let native = MaudeHandle::start_with_backend(
        "/nonexistent",
        mset_maude_sig(),
        AlgebraBackend::ProvedOnly,
    )
    .unwrap();
    let vars: Vec<_> = (0..4)
        .map(|i| Term::Lit(Lit::Var(LVar::new("u", LSort::Msg, i))))
        .collect();
    let rows = [
        distributed_class_equation(&vars, 29, 31, 89),
        distributed_class_equation(&vars, 17, 16, 50),
    ];
    let mut actual = Vec::new();
    for arm in native.unify(&rows).unwrap() {
        let subst = Subst::from_list(arm);
        let mut witnesses = BTreeMap::new();
        for (i, v) in vars.iter().enumerate() {
            let image = apply_vterm(&subst, v.clone());
            let parts = match &image {
                Term::App(FunSym::Ac(AcSym::Union), factors) => factors.as_ref(),
                t => std::slice::from_ref(t),
            };
            for t in parts {
                let Term::Lit(Lit::Var(w)) = t else {
                    panic!("unexpected AC factor {t:?}")
                };
                assert_eq!(w.sort, LSort::Msg);
                witnesses.entry(*w).or_insert([0; 4])[i] += 1;
            }
        }
        let mut signature = witnesses.into_values().collect::<Vec<_>>();
        signature.sort();
        actual.push(signature);
    }
    // Writing S = u0+u1, the equations imply S=2u2 and u2=u3.
    // An irreducible atom therefore takes one of these three columns.
    // Exactly five subsets cover all four nonempty images.
    let a = [0, 2, 1, 1];
    let b = [1, 1, 1, 1];
    let c = [2, 0, 1, 1];
    let mut expected = vec![vec![b], vec![a, c], vec![a, b], vec![b, c], vec![a, b, c]];
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected);
    assert_eq!(native.stats().unify_count, 0);
}

// The proved export lists the whole family. That of the 33-by-2 system has
// billions of members, so only its existence is asked.
#[test]
fn wide_homogeneous_system_under_a_commutative_root_is_unifiable() {
    use crate::builtin::emap;
    let var = |i| Term::Lit(Lit::Var(LVar::new("v", LSort::Msg, i)));
    let native = native_session(mset_maude_sig().merge(crate::maude_sig::bp_maude_sig()));
    let wide = f_app_ac(AcSym::Union, (0..33).map(var).collect());
    let rhs = f_app_ac(AcSym::Union, vec![var(33), var(34)]);
    let qs = [Equal {
        lhs: emap(var(35), wide),
        rhs: emap(var(36), rhs),
    }];
    assert!(native.unifiable(&qs).unwrap());
}

// Thirteen independent orientations: no prefix of the 8192 arms is complete.
#[test]
fn independent_commutative_rows_list_every_combination_of_orientations() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::emap;
    let var = |i| Term::Lit(Lit::Var(LVar::new("v", LSort::Msg, i)));
    let sig = mset_maude_sig().merge(crate::maude_sig::bp_maude_sig());
    let native = native_session(sig.clone());
    let qs: Vec<_> = (0..13)
        .map(|i| Equal {
            lhs: emap(var(2 * i), var(2 * i + 1)),
            rhs: emap(pub_term("a"), pub_term("b")),
        })
        .collect();
    let arms = canonical_ground_answers(native.unify(&qs).unwrap());
    assert_eq!(arms.len(), 1 << 13);
    if let Some(path) = require_maude_path() {
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        assert_eq!(arms, canonical_ground_answers(oracle.unify(&qs).unwrap()));
    }
}

// Proved-only lists every match. Each family below is too large for a prefix
// of it to stand for the whole.
#[cfg(test)]
mod large_match {
    use super::*;
    use crate::maude_sig::pair_maude_sig;

    fn variable(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
    }
    fn sum(a: LNTerm, b: LNTerm) -> LNTerm {
        f_app_ac(AcSym::Union, vec![a, b])
    }
    // The number of distinct answers; proved-only returns them without repeats.
    fn matches(h: &MaudeHandle, eq: Equal<LNTerm>) -> usize {
        let query = [eq];
        assert!(h.has_match_eqs(&query).unwrap());
        let count = h.match_eqs(&query).unwrap().len();
        assert_eq!(h.stats().match_count, 0);
        count
    }

    #[test]
    fn ac_match_lists_every_split_of_ten_atoms_over_three_variables() {
        let h = native_session(mset_maude_sig());
        let pattern = f_app_ac(
            AcSym::Union,
            vec![variable("x"), variable("y"), variable("z")],
        );
        let subject = f_app_ac(
            AcSym::Union,
            (0..10).map(|i| pub_term(format!("a{i}"))).collect(),
        );
        let query = Equal {
            lhs: subject,
            rhs: pattern,
        };
        // Surjections of ten distinct atoms onto three variables.
        assert_eq!(matches(&h, query), 3usize.pow(10) - 3 * (1 << 10) + 3);
    }

    #[test]
    fn open_match_lists_every_choice_of_the_compound_factor() {
        use crate::builtin::hash;
        use crate::maude_sig::hash_maude_sig;
        let h = native_session(mset_maude_sig().merge(hash_maude_sig()));
        let u = |xs| f_app_ac(AcSym::Union, xs);
        // Each of the nine choices of H(x) leaves eight factors for two variables.
        let eq = Equal {
            lhs: u((0..9).map(|i| hash(pub_term(format!("v{i}")))).collect()),
            rhs: u(vec![hash(variable("x")), variable("y"), variable("z")]),
        };
        assert_eq!(matches(&h, eq), 9 * ((1 << 8) - 2));
    }

    #[test]
    fn nested_c_match_lists_every_combination_of_orientations() {
        use crate::builtin::{emap, pair};
        use crate::maude_sig::{bp_maude_sig, dh_maude_sig};
        let sig = mset_maude_sig()
            .merge(bp_maude_sig())
            .merge(dh_maude_sig())
            .merge(pair_maude_sig());
        let h = native_session(sig);
        let mut p = pub_term("end");
        let mut t = p.clone();
        // Twelve independent binary choices all succeed.
        for i in 0..12 {
            let x = Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, i)));
            let y = Term::Lit(Lit::Var(LVar::new("y", LSort::Msg, i)));
            p = pair(emap(x, y), p);
            t = pair(emap(pub_term("a"), pub_term("b")), t);
        }
        let query = Equal {
            lhs: sum(t, pub_term("tag")),
            rhs: sum(p, variable("tail")),
        };
        assert_eq!(matches(&h, query), 1 << 12);
    }

    #[test]
    fn nested_ac_match_lists_the_product_of_independent_subtrees() {
        use crate::builtin::{hash, pair};
        use crate::maude_sig::hash_maude_sig;
        let sig = mset_maude_sig()
            .merge(hash_maude_sig())
            .merge(pair_maude_sig());
        let h = native_session(sig);
        let mut pattern = pub_term("end");
        let mut subject = pattern.clone();
        for i in 0..18 {
            let v = |s| Term::Lit(Lit::Var(LVar::new(s, LSort::Msg, i)));
            pattern = pair(hash(sum(v("x"), v("y"))), pattern);
            subject = pair(hash(sum(pub_term("a"), pub_term("b"))), subject);
        }
        // Each individual inner match is easy. Together they have 2^18 distinct
        // answers, so returning the first successful branches would lose matches.
        let eq = Equal {
            lhs: sum(subject, pub_term("tag")),
            rhs: sum(pattern, variable("tail")),
        };
        assert_eq!(matches(&h, eq), 1 << 18);
    }
}

#[test]
fn reference_unification_preserves_joint_orientations_and_aliases() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::{emap, fst, pair};
    use crate::lean_unification::{unify_modulo_attributes, Outcome};
    use crate::maude_sig::{bp_maude_sig, pair_maude_sig};
    use crate::subst_vfresh::LNSubstVFresh;
    use crate::term::f_app_list;

    let sig = bp_maude_sig()
        .merge(mset_maude_sig())
        .merge(pair_maude_sig());
    let mut handle =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::ProvedOnly)
            .unwrap();
    handle.set_reference(true);
    let [x, y, z, w] = ["x", "y", "z", "w"].map(|s| LVar::new(s, LSort::Msg, 0));
    let v = |var| Term::Lit(Lit::Var(var));
    let ac = |l, r| f_app_ac(AcSym::Union, vec![l, r]);
    let (a, b) = (pub_term("a"), pub_term("b"));
    let packed = |map, sum, nested| f_app_list(vec![map, f_app_list(vec![sum, nested])]);
    let lhs = packed(emap(v(x), v(y)), ac(v(x), v(y)), pair(v(z), v(w)));
    let rhs = packed(
        emap(a.clone(), b.clone()),
        ac(b.clone(), a.clone()),
        pair(v(w), v(z)),
    );
    let mut eqs = vec![Equal::new(lhs, rhs)];
    let Outcome::Complete(reference) = unify_modulo_attributes(&sig, &eqs).unwrap() else {
        panic!("declared mixed conjunction was rejected")
    };
    // The handle spells the export's witnesses as the Maude backend does.
    let unnamed = |arms: &crate::lean_unification::Substitutions| {
        let mut arms: Vec<_> = arms
            .iter()
            .map(|arm| {
                LNSubstVFresh::from_list(arm.clone())
                    .remove_renamings()
                    .drop_name_hints()
            })
            .collect();
        arms.sort();
        arms
    };
    assert_eq!(unnamed(&handle.unify(&eqs).unwrap()), unnamed(&reference));
    assert!(handle.unifiable(&eqs).unwrap());
    let mut general = [false; 2];
    for arm in reference {
        let subst = LNSubstVFresh::from_list(arm);
        let (left, right) = (subst.image_of(&x).unwrap(), subst.image_of(&y).unwrap());
        let orientation = if (left, right) == (&a, &b) {
            0
        } else {
            assert_eq!((left, right), (&b, &a));
            1
        };
        let image = subst.image_of(&z).unwrap();
        assert_eq!(Some(image), subst.image_of(&w));
        let Term::Lit(Lit::Var(witness)) = image else {
            panic!("alias was grounded")
        };
        assert_ne!(witness.idx, x.idx);
        general[orientation] |= witness.sort == LSort::Msg;
    }
    assert_eq!(general, [true, true]);
    // Ordinary unification uses only C/AC attributes even though this signature
    // contains the active reduction fst(pair(a,b)) -> a.
    eqs.push(Equal::new(fst(pair(a.clone(), b)), a));
    assert!(handle.unify(&eqs).unwrap().is_empty());
    assert!(!handle.unifiable(&eqs).unwrap());
    assert_eq!(handle.stats().unify_count, 0);
    // Rust composes the unpacking of the tuples with the total export, and
    // each existence question repeats an enumeration.
    let provenance = handle.provenance();
    assert_eq!(provenance.fresh(Command::Unify, Origin::NativeRust), 2);
    assert_eq!(provenance.cached(Command::Unify, Origin::NativeRust), 2);
    assert_eq!(provenance.total(Command::Unify), 4);
    handle.check_backend_status().unwrap();
}

#[test]
fn reference_unifiability_validates_even_reflexive_roots() {
    use crate::algebra_backend::AlgebraBackend;
    use crate::builtin::hash;
    use crate::lean_unification::{unify_modulo_attributes, Outcome};
    use crate::maude_proc::MaudeError;
    use crate::maude_sig::MaudeSig;

    let sig = MaudeSig::default();
    let term = hash(pub_term("a"));
    let eqs = [Equal::new(term.clone(), term)];
    assert_eq!(
        unify_modulo_attributes(&sig, &eqs).unwrap(),
        Outcome::Unsupported
    );
    for reference in [false, true] {
        let mut handle = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::ProvedOnly,
        )
        .unwrap();
        handle.set_reference(reference);
        assert!(matches!(
            handle.unifiable(&eqs),
            Err(MaudeError::UnsupportedOperation(_))
        ));
        assert!(handle.check_backend_status().is_err());
        assert_eq!(handle.stats().unify_count, 0);
    }
}

fn dh_pair_sig() -> MaudeSig {
    crate::maude_sig::dh_maude_sig().merge(crate::maude_sig::pair_maude_sig())
}

/// A native session and a proved-only one, on one signature.
fn native_pair(sig: MaudeSig) -> (MaudeHandle, MaudeHandle) {
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::Native)
            .unwrap();
    (native, native_session(sig))
}

fn unify_tally(handle: &MaudeHandle, origin: Origin) -> (u64, u64) {
    let seen = handle.provenance();
    (
        seen.fresh(Command::Unify, origin),
        seen.cached(Command::Unify, origin),
    )
}

/// A request that the free unifier solves alone is answered by the Rust of
/// the Maude backend, and the proved unifier is not asked.
#[test]
fn native_answers_a_free_request_without_handing_it_off() {
    use crate::builtin::pair;
    let (native, only) = native_pair(dh_pair_sig());
    let var = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
    let mult = |l, r| f_app_ac(AcSym::Mult, vec![l, r]);
    let eqs = [
        Equal::new(var("k", 1), pair(var("n", 2), var("m", 3))),
        Equal::new(var("z", 4), mult(var("n", 2), pub_term("a"))),
    ];
    let answers = native.unify(&eqs).unwrap();
    assert_eq!(answers, only.unify(&eqs).unwrap());
    assert_eq!(answers.len(), 1);
    // A repeat reads the answer from the memo.
    assert_eq!(native.unify(&eqs).unwrap(), answers);
    assert_eq!(unify_tally(&native, Origin::SharedRust), (1, 1));
    assert_eq!(native.provenance().total(Command::Unify), 2);
    assert_eq!(native.stats().lean_unify_count, 0);
    assert_eq!(native.stats().unify_count, 0);
}

/// A request with delayed AC equations hands them to the port of Maude's
/// unification algorithm, and Rust composes its answer with the free
/// unifier's as the Maude backend composes Maude's. The answer is the Maude
/// backend's, witness names included, and a repeat reads the memo.
#[test]
fn native_hands_the_delayed_equations_to_the_port_of_maude() {
    use crate::builtin::pair;
    let (native, _) = native_pair(dh_pair_sig());
    let maude = require_maude_path().map(|path| {
        MaudeHandle::start_with_backend(&path, dh_pair_sig(), AlgebraBackend::Maude).unwrap()
    });
    let var = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
    let mult = |l, r| f_app_ac(AcSym::Mult, vec![l, r]);
    let requests = [
        vec![Equal::new(
            mult(var("x", 1), var("y", 1)),
            mult(pub_term("a"), pub_term("b")),
        )],
        vec![
            Equal::new(var("k", 1), pair(var("n", 2), var("x", 1))),
            Equal::new(
                mult(var("x", 1), var("y", 1)),
                mult(var("c", 5), var("d", 6)),
            ),
        ],
    ];
    for eqs in &requests {
        let answers = native.unify(eqs).unwrap();
        assert!(answers.len() > 1, "{answers:?}");
        if let Some(maude) = &maude {
            assert_eq!(answers, maude.unify(eqs).unwrap());
        }
        assert_eq!(native.unify(eqs).unwrap(), answers);
    }
    assert_eq!(native.caches.stats.maude_port.load(Ordering::Relaxed), 2);
    assert_eq!(unify_tally(&native, Origin::NativeRust), (2, 2));
    assert_eq!(unify_tally(&native, Origin::Proved), (0, 0));
    assert_eq!(unify_tally(&native, Origin::SharedRust), (0, 0));
    assert_eq!(native.stats().lean_unify_count, 2);
    assert_eq!(native.stats().unify_count, 0);
    // The existence question takes the Maude backend's path, through the
    // same hand-off.
    assert!(native.unifiable(&requests[0]).unwrap());
}

/// A request whose free part clashes has no unifier, which Rust answers as
/// on the Maude backend, whatever its delayed equations.
#[test]
fn native_answers_a_free_clash_without_handing_it_off() {
    use crate::builtin::{exp, pair};
    let (native, only) = native_pair(dh_pair_sig());
    let var = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
    let mult = |l, r| f_app_ac(AcSym::Mult, vec![l, r]);
    let eqs = [
        Equal::new(
            pair(var("x", 1), var("y", 1)),
            exp(pub_term("g"), var("z", 1)),
        ),
        Equal::new(
            mult(var("x", 1), var("y", 1)),
            mult(pub_term("a"), pub_term("b")),
        ),
    ];
    assert_eq!(native.unify(&eqs).unwrap(), Vec::<Vec<_>>::new());
    assert_eq!(only.unify(&eqs).unwrap(), Vec::<Vec<_>>::new());
    assert!(!native.unifiable(&eqs).unwrap());
    assert_eq!(unify_tally(&native, Origin::SharedRust), (1, 1));
    assert_eq!(native.stats().lean_unify_count, 0);
}

/// Matching, normalization and variants: the Maude backend's front ends
/// answer what they answer, and what it sends to Maude goes to the proved
/// exports. The answers are proved-only's.
#[test]
fn native_hands_off_matching_normalization_and_variants() {
    use crate::builtin::{exp, pair};
    let (native, only) = native_pair(dh_pair_sig());
    let var = |name, idx| Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, idx)));
    let mult = |l, r| f_app_ac(AcSym::Mult, vec![l, r]);
    let tally = |handle: &MaudeHandle, command, origin| {
        let seen = handle.provenance();
        seen.fresh(command, origin) + seen.cached(command, origin)
    };
    // A match of a rigid subject with no pattern variable is an equality
    // test, which the front end answers.
    let rigid = [Equal::new(pub_term("a"), pub_term("a"))];
    assert_eq!(native.match_eqs(&rigid).unwrap(), vec![Vec::new()]);
    assert_eq!(tally(&native, Command::Match, Origin::SharedRust), 1);
    // A pattern with an AC operator goes to the proved matcher.
    let open = [Equal::new(
        mult(pub_term("a"), pub_term("b")),
        mult(var("x", 1), var("y", 1)),
    )];
    assert_eq!(
        native.match_eqs(&open).unwrap(),
        only.match_eqs(&open).unwrap()
    );
    assert!(native.has_match_eqs(&open).unwrap());
    assert_eq!(tally(&native, Command::Match, Origin::Proved), 2);
    // A term without a reducible operator is its own normal form, which the
    // front end knows; a reducible one goes to the proved normalizer.
    let plain = pair(pub_term("a"), var("x", 1));
    assert_eq!(native.reduce(&plain).unwrap(), plain);
    assert_eq!(tally(&native, Command::Reduce, Origin::SharedRust), 1);
    let reducible = exp(exp(pub_term("g"), var("x", 1)), var("y", 1));
    assert_eq!(
        native.reduce(&reducible).unwrap(),
        only.reduce(&reducible).unwrap()
    );
    assert_eq!(tally(&native, Command::Reduce, Origin::Proved), 1);
    // Every request for variants goes to the checked route.
    let query = exp(var("b", 1), var("e", 2));
    assert_eq!(
        native.variants(&query).unwrap(),
        only.variants(&query).unwrap()
    );
    assert_eq!(native.provenance().total(Command::Variants), 1);
    assert_eq!(tally(&native, Command::Variants, Origin::Proved), 1);
    assert_eq!(native.stats().match_count, 0);
    assert_eq!(native.stats().norm_count, 0);
    assert_eq!(native.stats().var_count, 0);
}

/// The variables and names of the requests below.
fn msg(idx: u64) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, idx)))
}

fn fresh(idx: u64) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, idx)))
}

fn public(idx: u64) -> LNTerm {
    Term::Lit(Lit::Var(LVar::new("p", LSort::Pub, idx)))
}

/// Requests with delayed AC and C equations, on native and on the Maude
/// backend: the answers are the same, in the same order and with the same
/// witnesses. The port answered every one of them on native.
fn assert_native_answers_as_maude(sig: MaudeSig, requests: &[Vec<Equal<LNTerm>>]) {
    let Some(path) = require_maude_path() else {
        return;
    };
    let native =
        MaudeHandle::start_with_backend("/nonexistent", sig.clone(), AlgebraBackend::Native)
            .unwrap();
    let maude = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
    for eqs in requests {
        assert_eq!(
            native.unify(eqs).unwrap(),
            maude.unify(eqs).unwrap(),
            "{eqs:?}"
        );
    }
    let stats = &native.caches.stats;
    assert_eq!(
        stats.maude_port.load(Ordering::Relaxed),
        requests.len() as u64
    );
    assert_eq!(stats.maude_port_gave_up.load(Ordering::Relaxed), 0);
    assert_eq!(stats.maude_port_declined.load(Ordering::Relaxed), 0);
}

#[test]
fn native_lists_maudes_exclusive_or_unifiers() {
    use crate::builtin::{pair, xor};
    let sig = crate::maude_sig::minimal_maude_sig(false)
        .merge(crate::maude_sig::xor_maude_sig())
        .refresh();
    let zero = || {
        Term::App(
            FunSym::NoEq(crate::function_symbols::zero_sym()),
            Vec::new().into(),
        )
    };
    let requests = vec![
        vec![Equal::new(xor(fresh(0), fresh(1)), xor(msg(2), msg(3)))],
        vec![Equal::new(xor(msg(0), msg(1)), xor(msg(2), msg(3)))],
        vec![Equal::new(
            xor(xor(msg(4), pub_term("a")), fresh(1)),
            xor(msg(2), pair(msg(3), msg(4))),
        )],
        vec![
            Equal::new(xor(msg(0), public(1)), xor(msg(2), pub_term("b"))),
            Equal::new(xor(msg(0), msg(2)), xor(zero(), msg(5))),
        ],
        vec![Equal::new(
            xor(xor(msg(9), msg(3)), xor(msg(1), fresh(7))),
            xor(pub_term("c"), xor(msg(8), msg(2))),
        )],
    ];
    assert_native_answers_as_maude(sig, &requests);
}

#[test]
fn native_lists_maudes_bilinear_unifiers() {
    use crate::builtin::{exp, pmult};
    let sig = crate::maude_sig::minimal_maude_sig(false)
        .merge(crate::maude_sig::dh_maude_sig())
        .merge(crate::maude_sig::bp_maude_sig())
        .refresh();
    let mult = |l, r| f_app_ac(AcSym::Mult, vec![l, r]);
    let em = |l, r| crate::term::f_app_c(crate::function_symbols::CSym::EMap, vec![l, r]);
    let requests = vec![
        vec![Equal::new(
            em(pmult(fresh(1), pub_term("P")), msg(2)),
            em(msg(3), pmult(fresh(4), pub_term("Q"))),
        )],
        vec![Equal::new(
            mult(mult(fresh(1), fresh(2)), msg(3)),
            mult(msg(4), mult(fresh(5), msg(6))),
        )],
        vec![
            Equal::new(
                em(msg(1), msg(2)),
                em(pmult(fresh(3), msg(4)), pub_term("R")),
            ),
            Equal::new(mult(msg(1), fresh(5)), mult(fresh(3), msg(6))),
        ],
        vec![Equal::new(
            exp(pub_term("g"), mult(msg(0), mult(fresh(1), public(2)))),
            exp(pub_term("g"), mult(msg(3), msg(4))),
        )],
    ];
    assert_native_answers_as_maude(sig, &requests);
}

#[test]
fn native_lists_maudes_multiset_and_user_ac_unifiers() {
    use crate::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
    let mut sig = mset_maude_sig().merge(crate::maude_sig::pair_maude_sig());
    let op = AcFctSym::new(
        "combine",
        Privacy::Public,
        Constructability::Constructor,
        NdcState::NotNdc,
    );
    sig.st_ac_fun_syms.insert(op);
    let sig = sig.refresh();
    let union = |l, r| f_app_ac(AcSym::Union, vec![l, r]);
    let combine = |l, r| f_app_ac(AcSym::AcFct(op), vec![l, r]);
    let requests = vec![
        vec![Equal::new(
            union(union(msg(0), pub_term("a")), msg(1)),
            union(msg(2), union(pub_term("a"), pub_term("b"))),
        )],
        vec![Equal::new(
            combine(msg(0), fresh(1)),
            combine(combine(msg(2), msg(3)), fresh(4)),
        )],
        vec![
            Equal::new(union(msg(0), msg(1)), union(msg(2), msg(3))),
            Equal::new(combine(msg(0), msg(2)), combine(msg(4), msg(5))),
        ],
    ];
    assert_native_answers_as_maude(sig, &requests);
}

/// A request the port cannot take goes to the proved total unifier: here
/// the whole request, fact wrapper included, because a sum of natural
/// numbers has a message variable.
#[test]
fn native_falls_back_when_the_port_declines() {
    use crate::function_symbols::nat_one_sym;
    let sig = crate::maude_sig::minimal_maude_sig(false)
        .merge(crate::maude_sig::nat_maude_sig())
        .refresh();
    let (native, only) = native_pair(sig);
    let one = || Term::App(FunSym::NoEq(nat_one_sym()), Vec::new().into());
    let plus = |l, r| f_app_ac(AcSym::NatPlus, vec![l, r]);
    let list = |args: Vec<LNTerm>| Term::App(FunSym::List, args.into());
    let eqs = [Equal::new(
        list(vec![plus(msg(0), one()), msg(1)]),
        list(vec![plus(one(), one()), msg(2)]),
    )];
    let answers = native.unify(&eqs).unwrap();
    assert_eq!(answers.len(), only.unify(&eqs).unwrap().len());
    let stats = &native.caches.stats;
    assert_eq!(stats.maude_port.load(Ordering::Relaxed), 0);
    assert_eq!(stats.maude_port_declined.load(Ordering::Relaxed), 1);
    assert_eq!(native.stats().lean_unify_count, 1);
}
