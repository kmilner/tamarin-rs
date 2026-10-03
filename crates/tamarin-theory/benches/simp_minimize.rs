//! `EquationStore::simp_minimize` on one disjunction of `n` distinct
//! substitutions, the state `simp_with_fresh_avoiding` hands it after
//! `sort_disj_substs`.  Duplicate detection is the only work on this input.
//!
//! Each substitution maps four variables to large terms that agree
//! everywhere except the innermost leaf of the last image, so comparing two
//! of them walks almost all of both, as with the AC unifiers of
//! bilinear-pairing theories (`ake/bilinear/Joux.spthy`).  Every term is
//! built from scratch: `Term`'s `Arc::ptr_eq` fast path would otherwise
//! short-circuit the comparisons, which unifiers parsed from Maude never hit.
//!
//! Run with `cargo bench -p tamarin-theory --bench simp_minimize`.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, SamplingMode};
use tamarin_term::function_symbols::{pair_sym, AcSym};
use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::{f_app_ac, f_app_no_eq};
use tamarin_term::vterm::var_term;
use tamarin_theory::tools::EquationStore;

const SIZES: [usize; 4] = [10, 100, 1000, 3000];
/// Nesting depth of each image: `DEPTH` pairs, each holding a 4-factor product.
const DEPTH: u64 = 8;

fn var(name: &str, idx: u64) -> LNTerm {
    var_term(LVar::new(name, LSort::Fresh, idx))
}

/// `<a1*a2*a3*a4, <b1*..*b4, ... leaf>>`, `DEPTH` levels deep.
fn image(leaf: LNTerm) -> LNTerm {
    (0..DEPTH).rev().fold(leaf, |rest, level| {
        let product = f_app_ac(
            AcSym::Mult,
            (0..4).map(|k| var("e", level * 4 + k)).collect(),
        );
        f_app_no_eq(pair_sym(), vec![product, rest])
    })
}

fn subst(i: usize) -> LNSubstVFresh {
    let x = |j| LVar::new("x", LSort::Msg, j);
    LNSubstVFresh::from_list(vec![
        (x(0), image(var("k", 0))),
        (x(1), image(var("k", 1))),
        (x(2), image(var("k", 2))),
        (x(3), image(var("z", i as u64))),
    ])
}

fn store(n: usize) -> EquationStore {
    let mut store = EquationStore::empty();
    store.add_disj((0..n).map(subst).collect());
    assert_eq!(store.conj[0].substs.len(), n);
    store
}

fn bench_simp_minimize(c: &mut Criterion) {
    let mut group = c.benchmark_group("simp_minimize");
    // The quadratic variant needs about a second per call at n = 3000.
    group.sample_size(10).sampling_mode(SamplingMode::Flat);
    for n in SIZES {
        let mut store = store(n);
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, _| {
            b.iter(|| assert!(!black_box(&mut store).simp_minimize(|_| false)))
        });
    }
    group.finish();
}

criterion_group!(benches, bench_simp_minimize);
criterion_main!(benches);
