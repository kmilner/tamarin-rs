//! The signed graph packet describes all input and result coordinates of one
//! query together. Each arm has its own parameters, shared across that tuple.
use super::{JoinSearch, Row};
use crate::builtin::{inv, mult, one_const};
use crate::function_symbols::{inv_sym, one_sym, AcSym, FunSym};
use crate::lean_unification::constructor_variants::RuleTable;
use crate::lean_unification::{initialize, residual, Error, MatchRows, WordSlice, LEAN_THREAD};
use crate::lterm::{LNTerm, LSort, LVar};
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app_ac, Term};
use crate::vterm::Lit;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::BTreeSet;
use std::ffi::c_void;

unsafe extern "C" {
    fn tamarin_lean_signed_graph_variants(
        inputs: u64,
        obs: *const WordSlice,
        count: usize,
    ) -> *mut c_void;
}

// The checked candidate also bounds basis enumeration before allocating rows.
pub(super) const MAX_COORDINATES: usize = 8;
// Up to sixteen sign profiles are cheap enough to try before general narrowing.
pub(super) const QUICK_COORDINATES: usize = 4;
const MAX_PROGRAM: usize = 256;
const MAX_RESPONSE: usize = 65_536;

fn program(
    t: &LNTerm,
    input: &mut impl FnMut(LVar) -> Option<usize>,
    code: &mut Vec<u64>,
    depth: usize,
) -> bool {
    if depth == MAX_PROGRAM || code.len() >= MAX_PROGRAM {
        return false;
    }
    let word = match t {
        Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => {
            let Some(i) = input(*v) else {
                return false;
            };
            3 + i as u64
        }
        Term::App(FunSym::NoEq(f), args) if *f == one_sym() && args.is_empty() => 0,
        Term::App(FunSym::NoEq(f), args) if *f == inv_sym() && args.len() == 1 => {
            if !program(&args[0], input, code, depth + 1) {
                return false;
            }
            1
        }
        Term::App(FunSym::Ac(AcSym::Mult), args) if args.len() >= 2 => {
            for (i, arg) in args.iter().enumerate() {
                if !program(arg, input, code, depth + 1) {
                    return false;
                }
                if i != 0 {
                    code.push(2);
                }
            }
            return code.len() <= MAX_PROGRAM;
        }
        _ => return false,
    };
    code.push(word);
    code.len() <= MAX_PROGRAM
}

fn read_packet(inputs: usize, programs: &[Vec<u64>]) -> Result<Option<Vec<u64>>, Error> {
    initialize()?;
    let observations: Vec<_> = programs.iter().map(|p| WordSlice::new(p)).collect();
    LEAN_THREAD.with(|_| {
        // SAFETY: the borrowed program descriptors live through this synchronous
        // call. MatchRows owns the returned Lean reference and checks the bounds.
        let packet = MatchRows::new(unsafe {
            tamarin_lean_signed_graph_variants(
                inputs as u64,
                observations.as_ptr(),
                observations.len(),
            )
        })?;
        if packet.count() != 1 || packet.rows(0) != 1 {
            return Err(Error::InvalidStatus(255));
        }
        let size = packet.row_size(0, 0)?;
        if size > MAX_RESPONSE {
            return Ok(None);
        }
        let mut words = vec![0; size];
        if packet.copy_row(0, 0, &mut words)? != size {
            return Err(Error::InvalidStatus(255));
        }
        Ok(Some(words))
    })
}

fn count(words: &mut &[u64]) -> Result<usize, Error> {
    let (n, rest) = words.split_first().ok_or(Error::InvalidStatus(255))?;
    *words = rest;
    usize::try_from(*n).map_err(|_| Error::InvalidStatus(255))
}

fn bag(
    words: &mut &[u64],
    names: &mut FxHashMap<u64, LVar>,
    fresh: &mut impl Iterator<Item = u64>,
) -> Result<Option<LNTerm>, Error> {
    let n = count(words)?;
    let (ids, rest) = words.split_at_checked(n).ok_or(Error::InvalidStatus(255))?;
    *words = rest;
    if ids.is_empty() {
        return Ok(None);
    }
    let mut factors = Vec::with_capacity(n);
    for id in ids {
        let v = match names.entry(*id) {
            std::collections::hash_map::Entry::Occupied(found) => *found.get(),
            std::collections::hash_map::Entry::Vacant(slot) => *slot.insert(LVar::new(
                "x",
                LSort::Msg,
                fresh.next().ok_or(Error::FreshVariableOverflow)?,
            )),
        };
        factors.push(Term::Lit(Lit::Var(v)));
    }
    Ok(Some(f_app_ac(AcSym::Mult, factors)))
}

fn decode(
    words: &[u64],
    width: usize,
    inputs: usize,
    original: &FxHashSet<u64>,
) -> Result<Option<BTreeSet<Row>>, Error> {
    if words.len() > MAX_RESPONSE || words == [0] {
        return Ok(None);
    }
    let Some((&1, mut words)) = words.split_first() else {
        return Err(Error::InvalidStatus(255));
    };
    let arms = count(&mut words)?;
    if width == 0
        || width > MAX_COORDINATES
        || inputs > width
        || arms == 0
        || arms > words.len() / (2 * width)
    {
        return Err(Error::InvalidStatus(255));
    }
    let mut rows = BTreeSet::new();
    for _ in 0..arms {
        tamarin_utils::cancellation::check().map_err(|_| Error::Cancelled)?;
        let mut names = FxHashMap::default();
        let mut fresh = (0..=u64::MAX).filter(|i| !original.contains(i));
        let mut coordinates = Vec::with_capacity(width);
        for _ in 0..width {
            let pos = bag(&mut words, &mut names, &mut fresh)?;
            let neg = bag(&mut words, &mut names, &mut fresh)?;
            coordinates.push(match (pos, neg) {
                (None, None) => one_const(),
                (Some(p), None) => p,
                (None, Some(n)) => inv(n),
                (Some(p), Some(n)) => mult(p, inv(n)),
            });
        }
        let values = coordinates.split_off(inputs);
        rows.insert(Row {
            images: coordinates,
            values,
        });
    }
    if !words.is_empty() {
        return Err(Error::InvalidStatus(255));
    }
    Ok(Some(rows))
}

impl RuleTable {
    /// An input that is only observed stays independent of the graph. All
    /// occurrences inside signed expressions refer to the same local coordinate.
    pub(super) fn signed_graph_rows(
        &self,
        keys: &[LVar],
        observed: &[LNTerm],
        max_coordinates: usize,
        search: &mut JoinSearch,
    ) -> Result<Option<Vec<Row>>, Error> {
        if !self.builtin_dh || keys.len() > MAX_RESPONSE || observed.len() > MAX_RESPONSE {
            return Ok(None);
        }
        let by_key: FxHashMap<_, _> = keys
            .iter()
            .copied()
            .enumerate()
            .map(|(i, k)| (k, i))
            .collect();
        if by_key.len() != keys.len() {
            return Ok(None);
        }
        let mut programs: Vec<Vec<u64>> = Vec::new();
        let mut active = Vec::new();
        let mut slots = Vec::with_capacity(observed.len());
        for t in observed {
            if let Term::Lit(Lit::Var(v)) = t {
                let Some(&i) = by_key.get(v) else {
                    return Ok(None);
                };
                slots.push(i);
                continue;
            }
            let mut input = |v| {
                let index = *by_key.get(&v)?;
                if let Some(j) = active.iter().position(|&i| i == index) {
                    Some(j)
                } else if active.len() < max_coordinates {
                    active.push(index);
                    Some(active.len() - 1)
                } else {
                    None
                }
            };
            let mut code = Vec::new();
            if !program(t, &mut input, &mut code, 0) || code.len() > search.graph_work {
                return Ok(None);
            }
            search.graph_work -= code.len();
            let slot = match programs.iter().position(|p| p == &code) {
                Some(i) => i,
                None => {
                    programs.push(code);
                    programs.len() - 1
                }
            };
            if active.len() + programs.len() > max_coordinates {
                return Ok(None);
            }
            slots.push(keys.len() + slot);
        }
        if programs.is_empty() {
            return Ok(Some(vec![Row {
                images: keys.iter().map(|&v| Term::Lit(Lit::Var(v))).collect(),
                values: observed.to_vec(),
            }]));
        }
        let original = keys.iter().map(|v| v.idx).collect();
        let Some(packet) = read_packet(active.len(), &programs)? else {
            return Ok(None);
        };
        let Some(local) = decode(
            &packet,
            active.len() + programs.len(),
            active.len(),
            &original,
        )?
        else {
            return Ok(None);
        };
        let mut projected = BTreeSet::new();
        for r in local {
            if keys.len() + slots.len() > search.graph_work {
                return Ok(None);
            }
            let mut coordinates: Vec<_> = keys.iter().map(|&v| Term::Lit(Lit::Var(v))).collect();
            for (&key, image) in active.iter().zip(r.images) {
                coordinates[key] = image;
            }
            coordinates.extend(r.values);
            let visible = coordinates[..keys.len()]
                .iter()
                .chain(slots.iter().map(|&i| &coordinates[i]));
            if !residual::charge_expansion(&mut search.graph_work, visible, None)? {
                return Ok(None);
            }
            projected.insert(
                Row {
                    images: coordinates[..keys.len()].to_vec(),
                    values: slots.iter().map(|&i| coordinates[i].clone()).collect(),
                }
                .rename(&original),
            );
        }
        let Some(kept) = self.prune_specializations(projected, &mut search.graph_matching)? else {
            return Ok(None);
        };
        for row in &kept {
            let subst = Subst::from_list(keys.iter().copied().zip(row.images.iter().cloned()));
            if !residual::charge_expansion(&mut search.graph_work, observed, Some(&subst))? {
                return Ok(None);
            }
            for t in row.iter() {
                if self.canonical_join_normal(t)? != Some(true) {
                    return Ok(None);
                }
            }
            for (t, value) in observed.iter().zip(&row.values) {
                let instance = apply_vterm(&subst, t.clone());
                if self.reduce_native(&instance)?.as_ref() != Some(value) {
                    return Ok(None);
                }
            }
        }
        Ok(Some(kept))
    }

    /// Test the complete typed FFI route, including the explicit output values.
    #[cfg(test)]
    pub(crate) fn signed_graph_probe(
        &self,
        keys: &[LVar],
        observed: &[LNTerm],
    ) -> Result<Option<Vec<Vec<LNTerm>>>, Error> {
        Ok(self
            .signed_graph_rows(keys, observed, MAX_COORDINATES, &mut JoinSearch::new())?
            .map(|rows| {
                rows.into_iter()
                    .map(|mut r| {
                        r.images.extend(r.values);
                        r.images
                    })
                    .collect()
            }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{fresh_var, hash, msg_var};
    use crate::lterm::pub_term;
    use crate::maude_sig::dh_maude_sig;

    #[test]
    fn signed_graph_arity_sorts_and_resource_deferrals() {
        let table = RuleTable::new(&dh_maude_sig()).unwrap();
        let key = LVar::new("g", LSort::Msg, 0);
        let x = Term::Lit(Lit::Var(key));
        for input in [
            hash(x.clone()),
            fresh_var("f", 0),
            pub_term("c"),
            msg_var("other", 1),
            Term::App(FunSym::NoEq(inv_sym()), vec![x.clone(), x.clone()].into()),
            Term::App(FunSym::NoEq(one_sym()), vec![x.clone()].into()),
            Term::App(FunSym::Ac(AcSym::Mult), vec![x.clone()].into()),
            f_app_ac(AcSym::Mult, vec![x.clone(); MAX_PROGRAM]),
        ] {
            assert!(table
                .signed_graph_probe(&[key], &[input])
                .unwrap()
                .is_none());
        }
        assert!(table
            .signed_graph_probe(&[key, key], &[x])
            .unwrap()
            .is_none());
        let restricted = LVar::new("r", LSort::Fresh, 0);
        assert!(table
            .signed_graph_probe(&[restricted], &[inv(Term::Lit(Lit::Var(restricted)))])
            .unwrap()
            .is_none());
        let mut altered = dh_maude_sig();
        let arg = Term::Lit(Lit::Var(key));
        altered
            .st_rules
            .insert(crate::subterm_rule::CtxtStRule::new(
                inv(arg.clone()),
                crate::subterm_rule::StRhs {
                    positions: vec![vec![0]],
                    term: arg.clone(),
                },
            ));
        assert!(RuleTable::new(&altered)
            .unwrap()
            .signed_graph_probe(&[key], &[inv(arg)])
            .unwrap()
            .is_none());
        assert_eq!(read_packet(1, &[vec![4]]).unwrap().unwrap(), [0]);
        assert_eq!(
            read_packet(1, &[vec![3; MAX_PROGRAM + 1]])
                .unwrap()
                .unwrap(),
            [0]
        );
    }

    #[test]
    fn signed_graph_higher_multiplicities_keep_the_same_parameter() {
        let table = RuleTable::new(&dh_maude_sig()).unwrap();
        let key = LVar::new("g", LSort::Msg, 0);
        let x = Term::Lit(Lit::Var(key));
        for n in 4..=8 {
            let input = f_app_ac(AcSym::Mult, vec![x.clone(); n]);
            let rows = table.signed_graph_probe(&[key], &[input]).unwrap().unwrap();
            let p = msg_var("x", 1);
            let q = msg_var("x", 2);
            let pp = f_app_ac(AcSym::Mult, vec![p.clone(); n]);
            let qq = f_app_ac(AcSym::Mult, vec![q.clone(); n]);
            let expected: BTreeSet<_> = [
                vec![one_const(), one_const()],
                vec![p.clone(), pp.clone()],
                vec![inv(p.clone()), inv(pp.clone())],
                vec![mult(p, inv(q)), mult(pp, inv(qq))],
            ]
            .into_iter()
            .collect();
            assert_eq!(rows.into_iter().collect::<BTreeSet<_>>(), expected);
        }
    }

    #[test]
    fn signed_graph_joint_product_and_quotient_share_all_valued_witnesses() {
        use crate::algebra_backend::AlgebraBackend;
        use crate::lean_unification::{open_match, Outcome};
        use crate::maude_proc::MaudeHandle;
        use crate::rewriting::Equal;
        use crate::term::f_app_list;

        if std::env::var_os("TAM_RS_VERIFY_LEAN_UNIFY").is_some() {
            return;
        }
        let Some(path) = tamarin_test_support::require_maude_path() else {
            return;
        };
        let sig = dh_maude_sig();
        let table = RuleTable::new(&sig).unwrap();
        let native = MaudeHandle::start_with_backend(
            "/nonexistent",
            sig.clone(),
            AlgebraBackend::NativeOnly,
        )
        .unwrap();
        let oracle = MaudeHandle::start_with_backend(&path, sig, AlgebraBackend::Maude).unwrap();
        let keys = [LVar::new("x", LSort::Msg, 0), LVar::new("x", LSort::Msg, 1)];
        let [x, y] = keys.map(|v| Term::Lit(Lit::Var(v)));
        let obs = [mult(x.clone(), y.clone()), mult(x, inv(y))];
        let rows = table
            .signed_graph_rows(&keys, &obs, MAX_COORDINATES, &mut JoinSearch::new())
            .unwrap()
            .unwrap();
        assert_eq!(rows.len(), 247);

        // Full live variant enumeration for this conjunction exceeds the
        // oracle's time budget. Check every public substitution and both
        // outputs with ordinary Maude reduction, then test concrete coverage.
        let public = native.variants(&f_app_list(obs.to_vec())).unwrap();
        let mut valued = BTreeSet::new();
        let original = keys.iter().map(|v| v.idx).collect();
        for arm in public {
            let subst = Subst::from_list(arm);
            let images: Vec<_> = keys
                .iter()
                .map(|&v| apply_vterm(&subst, Term::Lit(Lit::Var(v))))
                .collect();
            for image in &images {
                assert_eq!(&oracle.reduce(image).unwrap(), image);
            }
            let values = obs
                .iter()
                .map(|t| oracle.reduce(&apply_vterm(&subst, t.clone())).unwrap())
                .collect();
            valued.insert(Row { images, values }.rename(&original));
        }
        assert!(valued == rows.iter().map(|r| r.rename(&original)).collect());

        let a = pub_term("a");
        let b = pub_term("b");
        let domain = [
            one_const(),
            a.clone(),
            b.clone(),
            inv(a.clone()),
            inv(b.clone()),
            mult(a.clone(), b.clone()),
            inv(mult(a.clone(), b.clone())),
            mult(a.clone(), inv(b.clone())),
            mult(a.clone(), a),
        ];
        for x in &domain {
            for y in &domain {
                let input = [x, y];
                let expected = [
                    oracle.reduce(&mult(x.clone(), y.clone())).unwrap(),
                    oracle.reduce(&mult(x.clone(), inv(y.clone()))).unwrap(),
                ];
                let mut covered = false;
                for row in &rows {
                    let eqs: Vec<_> = row
                        .images
                        .iter()
                        .zip(input)
                        .map(|(p, s)| Equal {
                            lhs: p.clone(),
                            rhs: s.clone(),
                        })
                        .collect();
                    let Outcome::Complete(captures) =
                        open_match::with_captures(&eqs, Vec::new()).unwrap()
                    else {
                        panic!("bounded concrete input match deferred");
                    };
                    for capture in captures {
                        let subst = Subst::from_list(capture);
                        let values: Vec<_> = row
                            .values
                            .iter()
                            .map(|v| apply_vterm(&subst, v.clone()))
                            .collect();
                        if values.iter().all(|v| oracle.reduce(v).unwrap() == *v) {
                            assert_eq!(values, expected, "{x} and {y}");
                            covered = true;
                        }
                    }
                }
                assert!(covered, "{x} and {y}");
            }
        }
    }

    #[test]
    fn signed_graph_packet_preserves_shared_ids_counts_and_scope() {
        let reserved = [0, 1].into_iter().collect();
        for invalid in [
            vec![],
            vec![2],
            vec![0, 0],
            vec![1],
            vec![1, 1, 0],
            vec![1, 1, 0, 0, 0],
            vec![1, 1, 0, 0, 0, 0, 42],
            vec![1, 1, 3, 0, 0, 0],
        ] {
            assert!(decode(&invalid, 2, 1, &reserved).is_err());
        }
        assert!(decode(&[0], 2, 1, &reserved).unwrap().is_none());
        let id = u64::MAX;
        let packet = [1, 1, 2, id, id, 0, 0, 1, id];
        let r = decode(&packet, 2, 1, &reserved)
            .unwrap()
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        let p = msg_var("x", 2);
        let pp = mult(p.clone(), p.clone());
        assert_eq!(r.images, [pp]);
        assert_eq!(r.values, [inv(p)]);
    }
}
