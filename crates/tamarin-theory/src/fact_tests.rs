// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

use super::*;
use tamarin_term::builtin::msg_var;

/// `Fact::arity` counts the terms. `fact_tag_arity` reads the arity from the
/// tag. For a protocol fact the arity comes from the `Proto` payload. For
/// every built-in tag the arity is a fixed 1 (HS `factTagArity`,
/// Theory/Model/Fact.hs).
#[test]
fn proto_fact_arity() {
    let f = proto_fact(
        Multiplicity::Linear,
        "P",
        vec![msg_var("x", 0), msg_var("y", 0)],
    );
    assert_eq!(f.arity(), 2);
    assert_eq!(fact_tag_arity(&f.tag), 2);
    // The function reads the arity from the tag, and not from a term list.
    assert_eq!(
        fact_tag_arity(&FactTag::Proto(Multiplicity::Linear, "P", 3)),
        3
    );
    for t in [
        FactTag::Fresh,
        FactTag::Out,
        FactTag::In,
        FactTag::Ku,
        FactTag::Kd,
        FactTag::Ded,
        FactTag::Term,
    ] {
        assert_eq!(fact_tag_arity(&t), 1, "built-in tag {t:?} must be unary");
    }
}

/// `is_linear` and `is_persistent` partition every tag (HS
/// `factTagMultiplicity`, Theory/Model/Fact.hs). A `Proto` tag carries
/// its own multiplicity. KU and KD are Persistent. Every other tag is Linear.
/// The test asserts both directions. A predicate that degenerates to a
/// constant therefore cannot pass the test.
#[test]
fn linear_vs_persistent() {
    let lin = proto_fact(Multiplicity::Linear, "P", vec![]);
    let per = proto_fact(Multiplicity::Persistent, "Q", vec![]);
    assert!(lin.is_linear() && !lin.is_persistent());
    assert!(per.is_persistent() && !per.is_linear());
    for k in [ku_fact(msg_var("x", 0)), kd_fact(msg_var("x", 0))] {
        assert!(k.is_persistent() && !k.is_linear(), "{k:?} must be K-fact");
    }
    for f in [
        fresh_fact(msg_var("x", 0)),
        out_fact(msg_var("x", 0)),
        in_fact(msg_var("x", 0)),
    ] {
        assert!(f.is_linear() && !f.is_persistent(), "{f:?} must be linear");
    }
}

/// `lvarToLnterm` re-sorts NAT variables to FRESH ones — the surprising bit
/// of the HS definition (Theory/Model/Fact.hs), since only fresh-sorted variables
/// can be bound by the `Fr`-premise `freesToFresh` builds around them.
#[test]
fn lvar_to_lnterm_resorts_nat_to_fresh() {
    use tamarin_term::lterm::LSort;
    use tamarin_term::vterm::var_term;

    let n = LVar::new("n", LSort::Nat, 1);
    let expected: LNTerm = var_term(LVar::new("n", LSort::Fresh, 1));
    assert_eq!(lvar_to_lnterm(&n), expected);

    let m = LVar::new("m", LSort::Msg, 0);
    assert_eq!(lvar_to_lnterm(&m), var_term(m));

    assert_eq!(fresh_fact(lvar_to_lnterm(&n)), fresh_fact(expected));
}

#[test]
fn trivial_ku_fact_predicates() {
    assert!(is_trivial_ku_fact(&ku_fact(msg_var("x", 0))));
    // A KD-fact of the same term is not a trivial KU-fact.
    assert!(!is_trivial_ku_fact(&kd_fact(msg_var("x", 0))));
    // Neither is a KU-fact whose term is not a plain message variable.
    let pair = tamarin_term::term::f_app_no_eq(
        tamarin_term::function_symbols::pair_sym(),
        vec![msg_var("x", 0), msg_var("y", 0)],
    );
    assert!(!is_trivial_ku_fact(&ku_fact(pair)));
}

// =========================================================================
// Haskell-faithfulness invariants.
//
// Theory/Model/Fact.hs:  `data Multiplicity = Persistent | Linear`
// Theory/Model/Fact.hs:  `data FactTag = ProtoFact ... | FreshFact | OutFact |
//                              InFact | KUFact | KDFact | DedFact |
//                              TermFact`
//
// FactTag Ord matters because BTreeSet<LNFact> is used in injective-fact
// analysis and rule-conclusion sets.  If the tag order drifts, the
// "Proto facts come first" iteration property breaks, which downstream
// injective-fact code assumes.
// =========================================================================

/// Multiplicity: `Persistent < Linear` from Theory/Model/Fact.hs.
#[test]
fn multiplicity_ord_matches_haskell_declaration() {
    assert!(
        Multiplicity::Persistent < Multiplicity::Linear,
        "Persistent must sort before Linear (Theory/Model/Fact.hs)"
    );
}

/// `FactTag`'s derived Ord (Theory/Model/Fact.hs): every protocol fact
/// sorts before every reserved tag, whatever its name, and the reserved tags
/// follow their declaration order `Fresh < Out < In < Ku < Kd < Ded < Term`.
/// Iteration over fact sets (`simpInjectiveFactEqMon`, partial atom
/// valuation) depends on it.  `fact_tag_of` reads the reserved tags from the
/// names the parser canonicalises to (`mkProtoFact`,
/// Theory/Text/Parser/Fact.hs); `K` and `Term` stay protocol facts.
#[test]
fn fact_tag_ord_proto_sorts_before_builtins() {
    let tag = |persistent: bool, name: &str| {
        crate::elaborate::fact_tag_of(&tamarin_parser::ast::Fact {
            persistent,
            name: name.into(),
            args: vec![],
            annotations: vec![],
        })
    };
    let ascending = [
        tag(false, "Zebra"),
        tag(false, "Fr"),
        tag(false, "Out"),
        tag(false, "In"),
        tag(true, "KU"),
        tag(true, "KD"),
        tag(false, "Ded"),
        FactTag::Term,
    ];
    for pair in ascending.windows(2) {
        assert!(pair[0] < pair[1], "{:?} < {:?}", pair[0], pair[1]);
    }
    assert_eq!(
        &ascending[1..7],
        &[
            FactTag::Fresh,
            FactTag::Out,
            FactTag::In,
            FactTag::Ku,
            FactTag::Kd,
            FactTag::Ded,
        ]
    );
    for name in ["Zebra", "K", "Term"] {
        assert!(matches!(tag(false, name), FactTag::Proto(..)), "{name}");
    }
}

/// `Proto` facts compare by the `(multiplicity, name, arity)` triple,
/// `Persistent < Linear` first; and `Ord Fact` compares the tag before the
/// terms, so the arity decides before any argument is looked at.
#[test]
fn proto_fact_tag_compare_by_multiplicity_then_name_then_arity() {
    let lp = FactTag::Proto(Multiplicity::Linear, "P", 1);
    let pp = FactTag::Proto(Multiplicity::Persistent, "P", 1);
    let la = FactTag::Proto(Multiplicity::Linear, "A", 1);
    let lp2 = FactTag::Proto(Multiplicity::Linear, "P", 2);
    assert!(pp < lp);
    assert!(la < lp);
    assert!(lp < lp2);

    // `P(z)` against `P(a, a.1)`: `z` sorts after `a`, but the arity wins.
    let p1 = proto_fact(Multiplicity::Linear, "P", vec![msg_var("z", 0)]);
    let p2 = proto_fact(
        Multiplicity::Linear,
        "P",
        vec![msg_var("a", 0), msg_var("a", 1)],
    );
    assert!(p1 < p2);
}

// =========================================================================
// Cached-bloom fingerprint skip: soundness invariants.
// =========================================================================

use tamarin_term::builtin::{fresh_var, msg_var as mv, pair, pub_var};
use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::subst::Subst;

/// Tiny deterministic PRNG (no external quickcheck dep) for the property
/// tests below.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn range(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Build a pseudo-random `LNTerm` of bounded depth over a small var pool.
fn rand_term(r: &mut Lcg, depth: u32) -> LNTerm {
    if depth == 0 || r.range(3) == 0 {
        let i = r.range(6);
        match r.range(3) {
            0 => mv(&format!("x{i}"), r.range(4)),
            1 => fresh_var(&format!("n{i}"), r.range(4)),
            _ => pub_var(&format!("p{i}"), r.range(4)),
        }
    } else {
        pair(rand_term(r, depth - 1), rand_term(r, depth - 1))
    }
}

fn rand_fact(r: &mut Lcg) -> LNFact {
    let arity = 1 + r.range(4) as usize;
    let terms: Vec<LNTerm> = (0..arity).map(|_| rand_term(r, 3)).collect();
    let tag = match r.range(4) {
        0 => FactTag::Out,
        1 => FactTag::Ku,
        2 => FactTag::Proto(Multiplicity::Linear, "P", arity),
        _ => FactTag::Proto(Multiplicity::Persistent, "Q", arity),
    };
    Fact::fresh(tag, terms)
}

/// Superset property: every var visited by `for_each_free` has its bit
/// set in `fact.bloom()` (`bloom ⊇ frees`), and structurally-equal facts
/// get equal blooms (deterministic function of content).
#[test]
fn bloom_is_superset_of_frees_and_content_deterministic() {
    let mut r = Lcg(0x1234_5678);
    for _ in 0..2000 {
        let fa = rand_fact(&mut r);
        let b = fa.bloom();
        fa.for_each_free(&mut |v| {
            assert_ne!(
                b & var_bit(v),
                0,
                "bloom missing a bit for free var {v:?} — superset invariant broken"
            );
        });
        // Recomputing from the same terms is identical (content-deterministic).
        let b2 = fact_fingerprints(&fa.terms).0;
        assert_eq!(b, b2);
        // A structurally-equal rebuild gets an equal bloom.
        let fa2 = Fact::fresh(fa.tag, fa.terms.to_vec());
        assert_eq!(fa.bloom(), fa2.bloom());
    }
}

/// Skip-equivalence property: `bloom(fact) & dom_bloom == 0` implies
/// the subst changes NO term of the fact (the skip never fires on a fact
/// the subst actually rewrites).
#[test]
fn bloom_miss_implies_no_change() {
    let mut r = Lcg(0xDEAD_BEEF);
    let mut fired = 0u64;
    for _ in 0..4000 {
        let fa = rand_fact(&mut r);
        // Random subst: map a handful of vars to random terms (dropping
        // trivial bindings via `from_list`, as the real eq-store does).
        let ndom = 1 + r.range(4);
        let pairs: Vec<(LVar, LNTerm)> = (0..ndom)
            .map(|_| {
                let i = r.range(6);
                let v = LVar::new(format!("x{i}"), LSort::Msg, r.range(4));
                (v, rand_term(&mut r, 2))
            })
            .collect();
        let subst: Subst<_, _> = Subst::from_list(pairs);
        if subst.is_empty() {
            continue;
        }
        let dom_bloom = subst.dom().fold(0u64, |b, v| b | var_bit(v));
        if fa.bloom() & dom_bloom == 0 {
            fired += 1;
            for t in fa.terms.iter() {
                assert!(
                    t.apply_changed(&subst).is_none(),
                    "skip fired but subst changed a term — UNSOUND: fact={fa:?}"
                );
            }
        }
    }
    assert!(
        fired > 0,
        "test never exercised a real skip — weaken the generator"
    );
}

/// Trait contract: two facts equal-but-for-fingerprints compare `==`,
/// `Ord`-equal and hash equal.  Pins that the manual `Eq`/`Ord`/`Hash` stay
/// blind to BOTH out-of-band caches (`bloom` and `max_var`).
#[test]
fn fingerprints_are_invisible_to_eq_and_ord() {
    let mut a = Fact::fresh(FactTag::Out, vec![mv("x", 0)]);
    let mut b = a.clone();
    a.bloom = 0; // deliberately divergent fingerprints
    b.bloom = u64::MAX;
    a.max_var = 0;
    b.max_var = u64::MAX;
    assert_eq!(a, b, "Eq must ignore the bloom/max_var fields");
    assert_eq!(
        a.cmp(&b),
        std::cmp::Ordering::Equal,
        "Ord must ignore the bloom/max_var fields"
    );
    assert!(a.partial_cmp(&b) == Some(std::cmp::Ordering::Equal));
    assert_eq!(
        tamarin_utils::fx_hash_one(&a),
        tamarin_utils::fx_hash_one(&b),
        "Hash must ignore the bloom/max_var fields"
    );
}

/// `Hash` reads the same fields `Eq` reads, so the annotations stay out of it
/// (HS ignores them in `Eq`/`Ord`, Theory/Model/Fact.hs).
#[test]
fn fact_hash_ignores_annotations() {
    let a = fresh_fact(msg_var("x", 0)).annotate(FactAnnotation::SolveFirst);
    let b = fresh_fact(msg_var("x", 0));
    assert_eq!(a, b);
    assert_eq!(
        tamarin_utils::fx_hash_one(&a),
        tamarin_utils::fx_hash_one(&b)
    );
}

/// The consistency the implied-formula dedup's hash prefilter rests on:
/// every pair of `==` facts hashes equal, so a hash mismatch really does prove
/// the two values differ.
#[test]
fn fact_equal_values_hash_equal() {
    let mut r = Lcg(0x0FF1_CE99);
    let mut equal_pairs = 0u64;
    for _ in 0..2000 {
        let a = rand_fact(&mut r);
        // An independently built structural copy, with the annotations and the
        // fingerprints deliberately drawn differently.
        let b = Fact::new(a.tag, a.terms.to_vec()).annotate(FactAnnotation::SolveLast);
        assert_eq!(a, b);
        assert_eq!(
            tamarin_utils::fx_hash_one(&a),
            tamarin_utils::fx_hash_one(&b),
            "equal facts must hash equal: {a:?}"
        );
        equal_pairs += 1;
    }
    assert!(equal_pairs > 0);
}

/// `var_bit` determinism: two INDEPENDENTLY-constructed content-equal
/// `LVar`s hash to the same bit (guards against a future ptr-hash
/// "optimisation" of `LVar::Hash` that would break the superset invariant).
#[test]
fn var_bit_is_content_deterministic() {
    let a = LVar::new(String::from("foo"), LSort::Msg, 7);
    let b = LVar::new(format!("f{}{}", "o", "o"), LSort::Msg, 7);
    assert_eq!(a, b);
    assert_eq!(
        var_bit(&a),
        var_bit(&b),
        "content-equal LVars must yield the same bloom bit"
    );
    assert_eq!(
        tamarin_utils::fx_hash_one(&a),
        tamarin_utils::fx_hash_one(&b)
    );
}

// =========================================================================
// Per-fact cached max-var-idx: soundness invariants (the `bm_fact`
// fast-path in reduction.rs).
// =========================================================================

/// Manual `bm_term`-style max-idx fold, replicated here so the property
/// test below is independent of reduction.rs's (private) walker.
fn term_max_idx(t: &LNTerm, max: &mut u64) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => {
            if v.idx > *max {
                *max = v.idx;
            }
        }
        Term::Lit(Lit::Con(_)) => {}
        Term::App(_, args) => {
            for a in args.iter() {
                term_max_idx(a, max);
            }
        }
    }
}

/// A fact with no free vars caches `0` (folding it is the same no-op the
/// per-term walk performs on a no-free fact).
#[test]
fn max_var_no_free_caches_zero() {
    let fa = proto_fact(Multiplicity::Linear, "P", vec![]);
    assert_eq!(fa.max_var_cached(), Some(0));
}

/// The no-`HasFrees` constructors store the `u64::MAX` sentinel, so
/// `max_var_cached()` is `None` — `bm_fact` falls back to the per-term walk.
#[test]
fn max_var_new_and_map_are_sentinel() {
    let new_fa: LNFact = Fact::new(FactTag::Out, vec![mv("x", 7)]);
    assert_eq!(new_fa.max_var_cached(), None);
    // `map` drops the cache to the sentinel even from a computed source.
    let mapped: LNFact = Fact::fresh(FactTag::Out, vec![mv("x", 7)]).map(|t| t);
    assert_eq!(mapped.max_var_cached(), None);
}

/// `recompute_bloom` refreshes BOTH fingerprints from the current terms.
#[test]
fn recompute_bloom_refreshes_both_fingerprints() {
    let mut fa = Fact::fresh(FactTag::Out, vec![mv("x", 2)]);
    assert_eq!(fa.max_var_cached(), Some(2));
    fa.terms = vec![mv("y", 11), mv("z", 4)].into();
    fa.recompute_bloom();
    assert_eq!(fa.max_var_cached(), Some(11));
    assert_eq!(fa.bloom(), fact_fingerprints(&fa.terms).0);
}

/// A `map_free_with` rebuild recomputes the max over the RENAMED terms
/// (never copies the stale source max).
#[test]
fn map_free_with_recomputes_the_max() {
    let fa = Fact::fresh(FactTag::Out, vec![mv("x", 3)]);
    let shifted = fa.map_free_with(
        &mut |mut v| {
            v.idx += 10;
            v
        },
        false,
    );
    assert_eq!(shifted.max_var_cached(), Some(13));
}

/// Parity property: the cached max equals a fresh `bm_term`-style fold over
/// the same terms, bit-for-bit — the invariant the `bm_fact` fast-path
/// rests on (a cached max that drifts from the walk would change every
/// `bounds_max` fresh-index seed).
#[test]
fn max_var_equals_the_manual_walk() {
    let mut r = Lcg(0x0BAD_F00D);
    for _ in 0..2000 {
        let fa = rand_fact(&mut r);
        let mut walked = 0u64;
        for t in fa.terms.iter() {
            term_max_idx(t, &mut walked);
        }
        assert_eq!(
            fa.max_var_cached(),
            Some(walked),
            "cached max must equal the per-term walk — fact={fa:?}"
        );
    }
}

// =========================================================================
// `prettyFact` (Theory/Model/Fact.hs)
// =========================================================================

/// `ppAnn` reads `S.toList`, i.e. `FactAnnotation`'s `Ord` order
/// (Theory/Model/Fact.hs), which is the declaration order
/// `SolveFirst < SolveLast < NoSources` (Theory/Model/Fact.hs).  The
/// annotations go in in the opposite order, so the output can only come from
/// the set's iteration order.
#[test]
fn pretty_lnfact_annotations_in_ord_order() {
    let fa = ku_fact(fresh_var("ltk", 0))
        .annotate(FactAnnotation::NoSources)
        .annotate(FactAnnotation::SolveFirst);
    assert_eq!(
        pretty_lnfact(&fa).render(),
        "!KU( ~ltk )[+, no_precomp]",
        "the suffix is `brackets . fsep . punctuate comma` over the set"
    );
}

/// A tag whose arity disagrees with the argument count prints
/// `MALFORMED-` followed by HS's DERIVED `show tag`
/// (Theory/Model/Fact.hs), which spells the constructor and quotes a
/// protocol fact's name, and not the multiplicity-prefix spelling
/// `show_fact_tag` gives.
#[test]
fn pretty_lnfact_malformed_arity() {
    let proto: LNFact = Fact::new(
        FactTag::Proto(Multiplicity::Persistent, "P", 2),
        vec![mv("x", 0)],
    );
    assert_eq!(
        pretty_lnfact(&proto).render(),
        "MALFORMED-ProtoFact Persistent \"P\" 2( x )"
    );
    let builtin: LNFact = Fact::new(FactTag::Fresh, vec![mv("x", 0), mv("y", 0)]);
    assert_eq!(
        pretty_lnfact(&builtin).render(),
        "MALFORMED-FreshFact( x, y )"
    );
    // The annotation suffix hangs off the malformed head as well
    // (Theory/Model/Fact.hs).
    let annotated = builtin.annotate(FactAnnotation::SolveLast);
    assert_eq!(
        pretty_lnfact(&annotated).render(),
        "MALFORMED-FreshFact( x, y )[-]"
    );
}

/// The argument printer is a parameter, exactly as `prettyFact ppTerm`
/// (Theory/Model/Fact.hs) takes one, so a `Fact` over any term type
/// prints through its own leaf renderer.
#[test]
fn pretty_fact_takes_the_argument_printer() {
    let fa: Fact<&str> = Fact::new(FactTag::Proto(Multiplicity::Linear, "F", 2), vec!["a", "b"]);
    let doc = pretty_fact(
        &|s: &&str| crate::pretty_hpj::Doc::text(s.to_uppercase()),
        &fa,
    );
    assert_eq!(doc.render(), "F( A, B )");
}

/// The `Fact arity issues` and `Fact multiplicity issues` blocks render a
/// LEMMA's fact through HS's derived `Show`, not through `prettyLNFact`.
/// Oracle ef3f0468, on a theory whose rules use `B` at arity 1 and at arity 2
/// and whose lemma reads `Ex x #i. B(x, 'c') @ i`, prints the cell
/// `Fact {factTag = ProtoFact Linear "B" 2, factAnnotations = fromList [],
/// factTerms = [Bound 1,'c']}` — record syntax, a bare comma between the
/// terms, and the bound variable as its De Bruijn index.
#[test]
fn show_bl_fact_matches_the_derived_show() {
    use tamarin_term::lterm::{pub_term, BVar};
    use tamarin_term::vterm::var_term;

    let fa = Fact::new(
        FactTag::Proto(Multiplicity::Linear, "B", 2),
        vec![var_term(BVar::Bound(1)), pub_term("c")],
    );
    assert_eq!(
        show_bl_fact(&fa),
        "Fact {factTag = ProtoFact Linear \"B\" 2, factAnnotations = fromList [], \
         factTerms = [Bound 1,'c']}"
    );
}

/// An annotation reaches the derived `Show` as its constructor name, and the
/// set renders in `Ord` order with a bare comma between elements.  Oracle
/// ef3f0468, on the same shape of theory with the lemma action written
/// `A(x)[+, no_precomp] @ i`, prints
/// `factAnnotations = fromList [SolveFirst,NoSources]`.
#[test]
fn show_bl_fact_renders_a_nonempty_annotation_set() {
    use tamarin_term::lterm::BVar;
    use tamarin_term::vterm::var_term;

    let fa = Fact::new(
        FactTag::Proto(Multiplicity::Linear, "A", 1),
        vec![var_term(BVar::Bound(1))],
    )
    .annotate(FactAnnotation::NoSources)
    .annotate(FactAnnotation::SolveFirst);
    assert_eq!(
        show_bl_fact(&fa),
        "Fact {factTag = ProtoFact Linear \"A\" 1, \
         factAnnotations = fromList [SolveFirst,NoSources], factTerms = [Bound 1]}"
    );
}

/// `isKLogFact` is `isProtoFact` narrowed to the name `K`
/// (Theory/Model/Fact.hs), which is the tag [`k_log_fact`] builds.
/// The special tags are not protocol facts at all, and `KU`/`KD` do not
/// qualify despite their names.
#[test]
fn is_k_log_fact_is_the_proto_fact_named_k() {
    let k = k_log_fact(msg_var("m", 0));
    assert!(is_proto_fact(&k) && is_k_log_fact(&k));
    let p = proto_fact(Multiplicity::Linear, "P", vec![msg_var("m", 0)]);
    assert!(is_proto_fact(&p) && !is_k_log_fact(&p));
    for f in [
        fresh_fact(msg_var("m", 0)),
        in_fact(msg_var("m", 0)),
        out_fact(msg_var("m", 0)),
        ku_fact(msg_var("m", 0)),
        kd_fact(msg_var("m", 0)),
    ] {
        assert!(!is_proto_fact(&f) && !is_k_log_fact(&f), "{f:?}");
    }
}

/// HS `newVariables prems concs` (Theory/Model/Fact.hs): the
/// difference of the two lists' variable sets, as terms, in sorted `LVar`
/// order.  Only the two lists given take part — the caller decides whether
/// the actions belong in the second one (`cs ++ as` at the rule parser's
/// sites, the conclusions alone at the SAPIC and intruder sites).
#[test]
fn new_variables_is_the_sorted_conc_minus_prem_difference() {
    let x = msg_var("x", 0);
    let y = msg_var("y", 0);
    let z = msg_var("z", 0);
    let prems = vec![proto_fact(Multiplicity::Linear, "P", vec![x.clone()])];
    let concs = vec![proto_fact(
        Multiplicity::Linear,
        "Q",
        vec![z.clone(), y.clone(), x.clone()],
    )];
    assert_eq!(new_variables(&prems, &concs), vec![y, z]);
    assert_eq!(new_variables(&concs, &prems), Vec::<LNTerm>::new());
}

/// Every arm of the derived `Show FactTag`.  The `isFactName` tactic
/// compares an action goal's tag against this string, and `jgnFactTag`
/// writes it for every non-protocol fact (`jgnFactName` is `showFactTag`,
/// JSON.hs).  A constructor with a wrong spelling therefore breaks the
/// tactic matching and the graph JSON, and nothing reports an error.
#[test]
fn show_fact_tag_derived_covers_every_arm() {
    assert_eq!(
        show_fact_tag_derived(&FactTag::Proto(Multiplicity::Linear, "Foo", 2)),
        "ProtoFact Linear \"Foo\" 2"
    );
    assert_eq!(
        show_fact_tag_derived(&FactTag::Proto(Multiplicity::Persistent, "Foo", 0)),
        "ProtoFact Persistent \"Foo\" 0"
    );
    assert_eq!(show_fact_tag_derived(&FactTag::Fresh), "FreshFact");
    assert_eq!(show_fact_tag_derived(&FactTag::Out), "OutFact");
    assert_eq!(show_fact_tag_derived(&FactTag::In), "InFact");
    assert_eq!(show_fact_tag_derived(&FactTag::Ku), "KUFact");
    assert_eq!(show_fact_tag_derived(&FactTag::Kd), "KDFact");
    assert_eq!(show_fact_tag_derived(&FactTag::Ded), "DedFact");
    assert_eq!(show_fact_tag_derived(&FactTag::Term), "TermFact");
}
