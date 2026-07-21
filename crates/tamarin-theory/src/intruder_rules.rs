// Currently GPL 3.0 until granted permission by the following authors:
//   jdreier, beschmi, meiersi, kevinmorio, arcz, rkunnema, and other
//   minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Maude/Types.hs,
//   lib/term/src/Term/Positions.hs,
//   lib/term/src/Term/Substitution/SubstVFresh.hs,
//   lib/theory/src/Rule.hs, lib/theory/src/Theory/Sapic/Process.hs,
//   lib/theory/src/Theory/Sapic/Term.hs,
//   lib/theory/src/Theory/Tools/IntruderRules.hs,
//   lib/utils/src/Utils/Misc.hs, src/Main/Mode/Intruder.hs,
//   src/Main/TheoryLoader.hs

//! Port of `Theory.Tools.IntruderRules` from
//! `lib/theory/src/Theory/Tools/IntruderRules.hs` — covers the
//! always-included "special" intruder rules plus the DH/XOR/multiset
//! variant generators (`dh_intruder_rules`, `xor_intruder_rules`,
//! `multiset_intruder_rules`) and the `close_intr_rule` /
//! `variants_intruder` / `construction_rules` narrowing pipeline (which
//! drives Maude). Only the BP intruder rules lack a runtime generator
//! here — those are loaded from the cached file via `intruder_variants.rs`.

use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::vterm::var_term;

use crate::fact::{fresh_fact, in_fact, k_log_fact, kd_fact, ku_fact, out_fact, FactTag, LNFact};
use crate::rule::{IntrRuleAC, IntrRuleACInfo, Rule};

/// `specialIntruderRules diff` returns the intruder rules that are
/// included independently of the message theory:
///
/// - `coerce` — `[ KD(x) ] --[ KU(x) ]-> [ KU(x) ]`
/// - `pub` — `[] --[ KU($x) ]-> [ KU($x) ]`
/// - `gen_fresh` — `[ Fr(~x) ] --[ KU(~x) ]-> [ KU(~x) ]`
/// - `isend` — `[ KU(x) ] --[ K(x) ]-> [ In(x) ]`
/// - `irecv` — `[ Out(x) ] --> [ KD(x) ]`
///
/// If `diff` is true the additional `iequality` rule is included:
/// `[ KU(x), KD(x) ] --> []`.
pub fn special_intruder_rules(diff: bool) -> Vec<IntrRuleAC> {
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let x_pub = var_term(LVar::new("x", LSort::Pub, 0));
    let x_fresh = var_term(LVar::new("x", LSort::Fresh, 0));

    let ku_rule = |info: IntrRuleACInfo,
                   prems: Vec<LNFact>,
                   t: tamarin_term::lterm::LNTerm,
                   nvs: Vec<tamarin_term::lterm::LNTerm>|
     -> IntrRuleAC {
        let mut r = Rule::new(info, prems, vec![ku_fact(t.clone())], vec![ku_fact(t)]);
        r.new_vars = nvs;
        r
    };

    let mut out = vec![
        ku_rule(IntrRuleACInfo::Coerce, vec![kd_fact(x.clone())], x.clone(), vec![]),
        ku_rule(IntrRuleACInfo::PubConstr, vec![], x_pub.clone(), vec![x_pub]),
        ku_rule(
            IntrRuleACInfo::FreshConstr,
            vec![fresh_fact(x_fresh.clone())],
            x_fresh,
            vec![],
        ),
        Rule::new(
            IntrRuleACInfo::ISend,
            vec![ku_fact(x.clone())],
            vec![in_fact(x.clone())],
            vec![k_log_fact(x.clone())],
        ),
        Rule::new(
            IntrRuleACInfo::IRecv,
            vec![out_fact(x.clone())],
            vec![kd_fact(x.clone())],
            vec![],
        ),
    ];

    if diff {
        out.push(Rule::new(
            IntrRuleACInfo::IEquality,
            vec![ku_fact(x.clone()), kd_fact(x.clone())],
            vec![],
            vec![],
        ));
    }

    out
}

/// `natIntruderRules` — direct port of
/// `Theory.Tools.IntruderRules.natIntruderRules` (IntruderRules.hs:113-120):
/// when the natural-numbers plugin is enabled, ONE constructor
///
/// ```text
///   rule nat: [ ] --[ KU( x:nat ) ]-> [ KU( x:nat ) ]
/// ```
///
/// built with the same `kuRule` shape as `PubConstr` (`kuRule
/// NatConstrRule [] x_nat_var [x_nat_var]` — the nat variable is a
/// rule-new variable).
pub fn nat_intruder_rules() -> Vec<IntrRuleAC> {
    let x_nat = var_term(LVar::new("x", LSort::Nat, 0));
    let mut r = Rule::new(
        IntrRuleACInfo::NatConstr,
        vec![],
        vec![ku_fact(x_nat.clone())],
        vec![ku_fact(x_nat.clone())],
    );
    r.new_vars = vec![x_nat];
    vec![r]
}

/// `destructionRules diff st` — direct port of
/// `Theory.Tools.IntruderRules.destructionRules`.  Walks the LHS of a
/// context-subterm rewrite rule and emits a destructor `IntrRuleAC`
/// for every level on the path to the RHS position.
///
/// At each public-function step `(NoEq f Public) at index i`, emit:
///
/// ```text
///   [ KD(t_at_pos), KU(siblings)... ] --[]-> [ KD(rhs) ]
/// ```
///
/// where `t_at_pos` is the current sub-term and `siblings` are the
/// other arguments of the parent function (which the intruder must
/// derive in parallel).  Private symbols stop the descent.
pub fn destruction_rules(
    diff: bool,
    rule: &tamarin_term::subterm_rule::CtxtStRule,
) -> Vec<IntrRuleAC> {
    use tamarin_term::lterm::frees;
    use tamarin_term::positions::Position;
    use tamarin_term::function_symbols::{FunSym, Privacy};
    use tamarin_term::term::Term;

    let lhs = &rule.lhs;
    let rhs = &rule.rhs.term;
    let positions: &[Position] = &rule.rhs.positions;
    if positions.is_empty() { return Vec::new(); }

    // `containsPrivate` mirror (shared `tamarin_term::lterm::contains_private`).
    if !(diff || !frees(rhs).is_empty() || tamarin_term::lterm::contains_private(rhs)) {
        return Vec::new();
    }

    // Process the first position; recurse on the rest of `positions`.
    if positions.len() > 1 {
        let mut out = destruction_rules(diff, &tamarin_term::subterm_rule::CtxtStRule {
            lhs: lhs.clone(),
            rhs: tamarin_term::subterm_rule::StRhs {
                positions: vec![positions[0].clone()],
                term: rhs.clone(),
            },
        });
        out.extend(destruction_rules(diff, &tamarin_term::subterm_rule::CtxtStRule {
            lhs: lhs.clone(),
            rhs: tamarin_term::subterm_rule::StRhs {
                positions: positions[1..].to_vec(),
                term: rhs.clone(),
            },
        }));
        return out;
    }

    let pos = &positions[0];
    let mut out: Vec<IntrRuleAC> = Vec::new();
    let mut t = lhs.clone();
    let mut uprems: Vec<tamarin_term::lterm::LNTerm> = Vec::new();
    let mut name_acc: Vec<u8> = Vec::new();
    let mut posname = String::new();
    let pos_iter: Vec<i64> = pos.clone();
    // `rhs` is loop-invariant, so compute `frees(rhs).is_empty()` once.
    let rhs_frees_empty = frees(rhs).is_empty();
    for (step_idx, &i) in pos_iter.iter().enumerate() {
        match &t {
            Term::App(FunSym::NoEq(sym), args) => {
                if sym.privacy == Privacy::Private {
                    return out;
                }
                let public = sym.privacy == Privacy::Public;
                if !public { return out; }
                // Haskell `destructionRules` pattern #2 (IntruderRules.hs:129-157, see line 135):
                //     go _ (viewTerm -> FApp _ _) (_:[]) _ _ | (frees rhs /= []) = []
                // At the LAST position step, if the current term is an
                // FApp AND rhs has free vars, return [] — neither emit
                // nor recurse.  Current `t` is necessarily FApp here
                // (we're inside the Term::App arm).  Without this,
                // Rust emits extra rules at deep positions like
                // d_0_0_0_prefix_enc_pair or d_1_0_prefix_enc — see
                // denning_sacco_symmetric_cbc which has rule
                // `prefix(enc(<X,Y>,k)) = enc(X,k)` (positions [0,0,0]
                // and [0,1]); at the LAST step into pair(X,Y) and
                // enc(X,Y), Haskell skips.
                if pos_iter.len() == step_idx + 1 && !rhs_frees_empty {
                    return out;
                }
                // Build uprems' = uprems ++ siblings.  The pre-sibling
                // `uprems` value is never read again (the next iteration uses
                // the extended one), so extend in place instead of cloning.
                for (j, a) in args.iter().enumerate() {
                    if (j as i64) != i { uprems.push(a.clone()); }
                }
                let t_new = match args.get(i as usize) {
                    Some(t) => t.clone(),
                    None => return out, // invalid position
                };
                // Emit the rule unless the next step's term equals rhs
                // and rhs already in uprems' (Haskell's filter).
                let cond_emit = t_new != *rhs && !uprems.contains(rhs);
                // Next step's position-name prefix `_<i><pd>`; reused both
                // for the (conditional) rule name and to advance `posname`
                // below — neither `i` nor `posname` changes in between.
                let next_posname = format!("_{}{}", i, posname);
                if cond_emit {
                    // Build the rule name: `_<i><pd>` ++ funs.
                    let mut name = next_posname.as_bytes().to_vec();
                    let funs = {
                        let mut f = name_acc.clone();
                        f.extend_from_slice(b"_");
                        f.extend_from_slice(sym.name);
                        f
                    };
                    name.extend_from_slice(&funs);
                    // `rhs == lhs `atPos` pos` (IntruderRules.hs:129-157, see line 145).  Use
                    // the AC-aware `at_pos` (Positions.hs:28-43) so paths
                    // traversing an AC operator index exactly as Haskell.
                    // `pos` is the (valid) walked LHS position, so the
                    // lookup is `Some`; on the impossible invalid case fall
                    // back to `lhs`,
                    // keeping the boolean unchanged rather than panicking.
                    let at = tamarin_term::positions::at_pos(lhs, pos)
                        .unwrap_or_else(|| lhs.clone());
                    let info = IntrRuleACInfo::DestrRule(
                        name,
                        -1,
                        rhs == &at,
                        rhs_frees_empty,
                    );
                    let mut prems = vec![kd_fact(t_new.clone())];
                    for u in &uprems { prems.push(ku_fact(u.clone())); }
                    out.push(Rule::new(info, prems, vec![kd_fact(rhs.clone())], vec![]));
                }
                // Update accumulators and walk down.
                name_acc.extend_from_slice(b"_");
                name_acc.extend_from_slice(sym.name);
                posname = next_posname;
                t = t_new;
            }
            Term::Lit(_) => {
                // Hit a leaf with positions still remaining — invalid.
                return out;
            }
            _ => return out,
        }
    }
    out
}

/// `subtermIntruderRules` — direct port:
/// `minimizeIntruderRules diff $ concatMap (destructionRules diff) (S.toList stRules)`
/// `  ++ constructionRules (stFunSyms maudeSig) ++ privateConstructorRules (S.toList $ stRules maudeSig)`.
///
/// IntruderRules.hs:210-213.  The `minimizeIntruderRules` pass strips
/// subsumed/duplicate destructor rules — without it, a single equation
/// containing multiple variable positions of the same rhs (e.g. chaum's
/// `unblind(sign(blind(m,r),k), r) = sign(m,k)` where m at [0,0,0] and
/// k at [0,1] both walk through position [0]) emits the same `_0_unblind`
/// destructor twice.  Those duplicates then cause `solve_chain_goal` to
/// fan out 2 identical destructor branches (idx-renamed but otherwise
/// equal), inflating source-case counts at saturate time
/// (chaum::unforgeability KU(sign) goes from Haskell's 1 case to Rust's
/// 4 cases).
pub fn subterm_intruder_rules(
    diff: bool,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<IntrRuleAC> {
    let mut out: Vec<IntrRuleAC> = Vec::new();
    for r in &sig.st_rules {
        out.extend(destruction_rules(diff, r));
    }
    out.extend(construction_rules(sig));
    out.extend(private_constructor_rules(&sig.st_rules));
    minimize_intruder_rules(diff, out)
}

/// `privateConstructorRules` — port of IntruderRules.hs:177-184.
///
/// Returns the constructor rules for private constants that are
/// consequences of the subterm rewrite rules in `st_rules`.  A private
/// 0-arity constructor is "derivable" when there exists an equation whose
/// RHS is that constant and whose LHS only mentions public functions (or
/// already-derivable private constants) — computed by the
/// `derivable_private_constants` fixpoint.  For each such constant `s` we
/// emit:
///
/// ```text
///   [] --[ KU(s) ]-> [ KU(s) ]    (ConstrRule "_<s>")
/// ```
///
/// HS:
/// ```haskell
/// privateConstructorRules rules = map createRule $
///     derivablePrivateConstants (privateConstructorEquations rules) []
///   where createRule s = Rule (ConstrRule (append (pack "_") s)) [] [concfact] [concfact] []
///           where m        = fAppNoEq (s,(0,Private,Constructor)) []
///                 concfact = kuFact m
/// ```
fn private_constructor_rules(
    st_rules: &std::collections::BTreeSet<tamarin_term::subterm_rule::CtxtStRule>,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{
        Constructability, FunSym, NoEqSym, Privacy,
    };
    use tamarin_term::term::Term;

    // `privateConstructorEquations` (IntruderRules.hs:160-165): all
    // equations whose RHS is a 0-arity Private constructor, paired with
    // that constructor's name.
    let eqs: Vec<(&LNTerm, Vec<u8>)> = st_rules.iter().filter_map(|r| {
        match &r.rhs.term {
            Term::App(FunSym::NoEq(NoEqSym { name, arity: 0, privacy: Privacy::Private, .. }), _) => {
                Some((&r.lhs, name.to_vec()))
            }
            _ => None,
        }
    }).collect();

    // `containsNoPrivateExcept funs t` (LTerm.hs:373-377): True if `t`
    // contains no private function symbols other than those named in
    // `funs`.
    fn contains_no_private_except(funs: &[Vec<u8>], t: &LNTerm) -> bool {
        match t {
            Term::Lit(_) => true,
            Term::App(FunSym::NoEq(NoEqSym { name, privacy: Privacy::Private, .. }), args) => {
                funs.iter().any(|f| f.as_slice() == &**name) && args.iter().all(|a| contains_no_private_except(funs, a))
            }
            Term::App(_, args) => args.iter().all(|a| contains_no_private_except(funs, a)),
        }
    }

    // `derivablePrivateConstants eqs x` (IntruderRules.hs:169-175):
    // fixpoint adding the RHS-constants of equations whose LHS only
    // contains public functions or already-derivable private constants.
    fn derivable_private_constants(
        mut eqs: Vec<(&LNTerm, Vec<u8>)>,
        mut x: Vec<Vec<u8>>,
    ) -> Vec<Vec<u8>> {
        loop {
            // Both HS filters (drop + collect-names) use the OLD `x`, so
            // snapshot it before augmenting.
            let prev_x = x.clone();
            let any_derivable = eqs.iter().any(|(l, _)| contains_no_private_except(&prev_x, l));
            if !any_derivable {
                return x;
            }
            // `x ++ map snd (filter (containsNoPrivateExcept x . fst) eqs)`.
            for (l, name) in eqs.iter() {
                if contains_no_private_except(&prev_x, l) {
                    x.push(name.clone());
                }
            }
            // `filter (not . containsNoPrivateExcept x . fst) eqs`.
            eqs.retain(|(l, _)| !contains_no_private_except(&prev_x, l));
        }
    }

    derivable_private_constants(eqs, Vec::new()).into_iter().map(|s| {
        let sym = NoEqSym::new(s.clone(), 0, Privacy::Private, Constructability::Constructor);
        let m: LNTerm = Term::App(FunSym::NoEq(sym), Vec::<LNTerm>::new().into());
        let concfact = ku_fact(m);
        Rule::new(
            intr_constr_info(&s),
            vec![],
            vec![concfact.clone()],
            vec![concfact],
        )
    }).collect()
}

/// Port of `minimizeIntruderRules` (IntruderRules.hs:186-206).
///
/// Two-stage filter:
/// 1. **Subsumption** (skipped in `diff` mode): for each rule with
///    `(prems, concs)`, drop it if any OTHER rule has the same `concs`
///    and a premise set that is a subset of this rule's premises.
///    Mirrors Haskell's `go` accumulator iteration; preserves the order
///    of the first-kept duplicate.
/// 2. **Double-premise filter** (always applied): drop rules whose KD
///    first-premise is a msg-var `t` and whose premises also include
///    `KU(t)` of the same term (with all terms private-free).
fn minimize_intruder_rules(
    diff: bool,
    rules: Vec<IntrRuleAC>,
) -> Vec<IntrRuleAC> {
    let after_subsumption = if diff {
        rules
    } else {
        // Haskell `go checked unchecked`: process `unchecked` left-to-right,
        // dropping any rule subsumed by a peer in `checked ++ unchecked`.
        // We mirror exactly: walk by index, and when checking rule i, the
        // peers are { all kept rules so far } ∪ { all rules with index > i }.
        let n = rules.len();
        let mut kept: Vec<usize> = Vec::with_capacity(n);
        for i in 0..n {
            let r_i = &rules[i];
            let subsumed = (0..n).any(|j| {
                if j == i { return false; }
                // Peer eligibility: either already-kept earlier (j < i and j in kept)
                // or still in `unchecked` (j > i).  Haskell's `checked++unchecked`
                // semantics.
                if j < i && !kept.contains(&j) { return false; }
                let r_j = &rules[j];
                r_j.conclusions == r_i.conclusions
                    && is_subset_of(&r_j.premises, &r_i.premises)
            });
            if !subsumed { kept.push(i); }
        }
        kept.into_iter().map(|i| rules[i].clone()).collect()
    };
    after_subsumption.into_iter().filter(|r| !is_double_premise_rule(r)).collect()
}

/// Set-subset check: every distinct element of `a` is `==` to some element of
/// `b`.  Mirrors Haskell's `subsetOf` (Utils/Misc.hs:87-88):
/// `subsetOf xs ys = (S.fromList xs) `S.isSubsetOf` (S.fromList ys)` —
/// `S.fromList` deduplicates BOTH arguments, so multiplicity is ignored on both
/// sides.  This is a SET subset, not a multiset/list subset.
fn is_subset_of(a: &[crate::fact::LNFact], b: &[crate::fact::LNFact]) -> bool {
    a.iter().all(|fa| b.iter().any(|fb| fa == fb))
}

/// `isDoublePremiseRule` (IntruderRules.hs:201-206).
///
/// Drops destructor rules whose first premise is `KD(t)` where `t` is a
/// msg-var, conclusions are ground, no private function symbols appear
/// in premise/conclusion terms, and `KU(t)` also appears among the
/// premises.  These rules are redundant — the intruder can always supply
/// the term directly via the KU premise, so the KD-derivation pathway
/// is never useful.
fn is_double_premise_rule(r: &IntrRuleAC) -> bool {
    use crate::fact::FactTag;
    use tamarin_term::lterm::is_msg_var;
    let (kd_fact_term, rest_prems): (&tamarin_term::lterm::LNTerm, &[crate::fact::LNFact]) =
        match r.premises.split_first() {
            Some((first, rest)) => {
                if first.tag != FactTag::Kd { return false; }
                let t = match first.terms.first() {
                    Some(t) => t,
                    None => return false,
                };
                (t, rest)
            }
            None => return false,
        };
    // Conclusions must be ground.
    let frees_concs = r.conclusions.iter()
        .flat_map(|f| f.terms.iter())
        .any(|t| !tamarin_term::lterm::frees(t).is_empty());
    if frees_concs { return false; }
    // Reject if any term (KD-premise or any prems-term) contains a private
    // symbol (shared `tamarin_term::lterm::contains_private`).
    if tamarin_term::lterm::contains_private(kd_fact_term) { return false; }
    for f in r.premises.iter() {
        for t in f.terms.iter() {
            if tamarin_term::lterm::contains_private(t) { return false; }
        }
    }
    // KD-premise term must be a msg-var.
    if !is_msg_var(kd_fact_term) { return false; }
    // KU(kd_fact_term) must appear among the remaining premises.
    let ku_t = crate::fact::ku_fact(kd_fact_term.clone());
    rest_prems.iter().any(|f| f == &ku_t)
}

/// `multisetIntruderRules` — port of Haskell's
/// `Theory.Tools.IntruderRules.multisetIntruderRules`
/// (`lib/theory/src/Theory/Tools/IntruderRules.hs:327-333`):
///
/// ```haskell
/// multisetIntruderRules = [mkDUnionRule [x_var, y_var] x_var,
///                          mkCUnionRule [x_var, y_var]]
///   where x_var = varTerm (LVar "x"  LSortMsg   0)
///         y_var = varTerm (LVar "y"  LSortMsg   0)
///
/// mkDUnionRule t_prems t_conc =
///     Rule (DestrRule (append (pack "_") unionSymString) 0 True False)
///          [kdFact $ fAppAC Union t_prems]
///          [kdFact t_conc] [] []
///
/// mkCUnionRule terms =
///     Rule (ConstrRule (append (pack "_") unionSymString))
///          (map kuFact terms)
///          [kuFact $ fAppAC Union terms] [kuFact $ fAppAC Union terms] []
/// ```
///
/// Added to the intruder rule pool when `enableMSet` (Main/TheoryLoader.hs:773-791, see line 788).
/// Note budget=0 (NOT -1) — `closeIntrRule` clause 3 passes through without
/// further variant expansion since budget is not -1.  HS computes budget=0
/// at definition time, so we mirror that here.
pub fn multiset_intruder_rules() -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{AcSym, FunSym, UNION_SYM_STRING};
    use tamarin_term::term::Term;
    let x_var = var_term(LVar::new("x", LSort::Msg, 0));
    let y_var = var_term(LVar::new("y", LSort::Msg, 0));
    let xy_union = Term::App(FunSym::Ac(AcSym::Union), vec![x_var.clone(), y_var.clone()].into());
    let name = underscore_prefixed(UNION_SYM_STRING);
    let d_rule = Rule::new(
        IntrRuleACInfo::DestrRule(name.clone(), 0, true, false),
        vec![kd_fact(xy_union.clone())],
        vec![kd_fact(x_var.clone())],
        vec![],
    );
    let c_rule = {
        let mut r = Rule::new(
            IntrRuleACInfo::ConstrRule(name),
            vec![ku_fact(x_var.clone()), ku_fact(y_var)],
            vec![ku_fact(xy_union.clone())],
            vec![ku_fact(xy_union)],
        );
        r.new_vars = vec![];
        r
    };
    vec![d_rule, c_rule]
}

/// `xorIntruderRules` — port of HS `Theory.Tools.IntruderRules.xorIntruderRules`
/// (IntruderRules.hs:345-349):
///
/// ```haskell
/// xorIntruderRules = [
///     mkDXorRule [x, y] [y, z] (x ⊕ z),   -- KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z)
///     mkDXorRule [x, y] [y]    x,         -- KD(x⊕y) ∧ KU(y)   → KD(x)
///     mkCXorRule x y (x ⊕ y),             -- KU(x)   ∧ KU(y)   → KU(x⊕y)
///     zeroConstructor                     -- KU(zero)
/// ]
/// ```
///
/// The two destructor rules let the adversary recover `x` (or `x⊕z`) when
/// they know `x⊕y` (as KD, e.g. from an `Out(x⊕y)`) and can compose `y`
/// (or `y⊕z`) themselves.  The constructor rule lets them XOR two known
/// values together.  `zeroConstructor` makes `zero` always known.
///
/// Wired in `ProofContext::new_with_restrictions_and_pool` when
/// `sig.enable_xor`, after `special_intruder_rules` and before the
/// DH/BP intruder variants — mirroring HS `addMessageDeductionRule
/// Variants` (TheoryLoader.hs:786-789).
pub fn xor_intruder_rules() -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{
        AcSym, FunSym, NoEqSym, Privacy, Constructability,
        XOR_SYM_STRING, ZERO_SYM_STRING,
    };
    use tamarin_term::term::Term;
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let z = var_term(LVar::new("z", LSort::Msg, 0));
    // `Term::App(Ac(Xor), [a, b])`.  Constructed via the AC-flatten/sort
    // smart constructor so the operand order matches HS's `fAppAC` (sorted
    // by Ord).
    let xor2 = |a: LNTerm, b: LNTerm| -> LNTerm {
        tamarin_term::term::f_app_ac(AcSym::Xor, vec![a, b])
    };
    let x_xor_y = xor2(x.clone(), y.clone());
    let x_xor_z = xor2(x.clone(), z.clone());
    let y_xor_z = xor2(y.clone(), z.clone());
    let name = underscore_prefixed(XOR_SYM_STRING);

    // Rule 1: KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z)
    // HS: mkDXorRule [x, y] [y, z] x_xor_z
    let d_rule_1 = Rule::new(
        IntrRuleACInfo::DestrRule(name.clone(), 1, true, false),
        vec![kd_fact(x_xor_y.clone()), ku_fact(y_xor_z)],
        vec![kd_fact(x_xor_z)],
        vec![],
    );
    // Rule 2: KD(x⊕y) ∧ KU(y) → KD(x)
    // HS: mkDXorRule [x, y] [y] x_var — note `fAppAC Xor [y]` is a singleton
    // AC that the smart constructor strips to just `y`.
    let d_rule_2 = Rule::new(
        IntrRuleACInfo::DestrRule(name.clone(), 1, true, false),
        vec![kd_fact(x_xor_y.clone()), ku_fact(y.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    // Rule 3: KU(x) ∧ KU(y) → KU(x⊕y)
    // HS: mkCXorRule x y x_xor_y — constructor, action emits `KU(x⊕y)`.
    let c_rule = {
        let mut r = Rule::new(
            IntrRuleACInfo::ConstrRule(name.clone()),
            vec![ku_fact(x), ku_fact(y)],
            vec![ku_fact(x_xor_y.clone())],
            vec![ku_fact(x_xor_y)],
        );
        r.new_vars = vec![];
        r
    };
    // Rule 4: zero constructor (HS `zeroConstructor`).
    let zero_sym = NoEqSym::new(ZERO_SYM_STRING.to_vec(), 0,
        Privacy::Public, Constructability::Constructor);
    let zero_term: LNTerm = Term::App(FunSym::NoEq(zero_sym), Vec::<LNTerm>::new().into());
    let zero_name = underscore_prefixed(ZERO_SYM_STRING);
    let zero_rule = {
        let mut r = Rule::new(
            IntrRuleACInfo::ConstrRule(zero_name),
            vec![],
            vec![ku_fact(zero_term.clone())],
            vec![ku_fact(zero_term)],
        );
        r.new_vars = vec![];
        r
    };
    vec![d_rule_1, d_rule_2, c_rule, zero_rule]
}

/// `constructionRules`: for every public constructor `f/n` in the
/// signature, emit a KU rule:
///
/// `[KU(x_1), ..., KU(x_n)] --[KU(f(x_1, ..., x_n))]-> [KU(f(x_1, ..., x_n))]`
pub fn construction_rules(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{Constructability, Privacy};
    use tamarin_term::term::f_app_no_eq;
    // HS-faithful: `constructionRules (stFunSyms maudeSig)`
    // (IntruderRules.hs:210-213, see line 213).  `stFunSyms` is the SUBTERM-theory function
    // signature — it EXCLUDES the DH / BP / MSet / Nat / Xor symbols
    // (those are added into `fun_syms` by `refresh`,
    // maude_sig.rs `fn refresh` lines 56-60, exposed as `fun_syms` at line 84).
    // The DH / BP intruder constructors (`c_exp` / `c_inv` / `c_mult`
    // / `c_one` / `c_DH_neutral` / `c_pmult` / `c_emap`) come from the
    // cached `intruder_variants_{dh,bp}.spthy` files via
    // `addMessageDeductionRuleVariants` (TheoryLoader.hs:773-781) —
    // adding them here would duplicate every DH constructor in
    // `intruder_rules`, doubling each `c_exp` / `c_inv` / etc. branch
    // at `solve_action_goal` rule enumeration and causing case-list
    // over-enumeration (e.g. KEA_plus_eCK::eCK_initiator_key
    // `case exp_case_1` vs HS `case exp`).
    let mut out = Vec::new();
    for s in &sig.st_fun_syms {
        // `[ createRule s k | (s,(k,Public,Constructor)) <- ... ]` —
        // only public constructors.
        if s.privacy != Privacy::Public
            || s.constructability != Constructability::Constructor
        {
            continue;
        }
        let arity = s.arity;
        // Build vars x_0 ... x_{n-1} : Msg
        let xs: Vec<tamarin_term::lterm::LNTerm> = (0..arity)
            .map(|i| var_term(LVar::new("x", LSort::Msg, i as u64)))
            .collect();
        let prems: Vec<LNFact> = xs.iter().cloned().map(ku_fact).collect();
        let m = f_app_no_eq(s.clone(), xs);
        let conc = ku_fact(m.clone());
        let act = ku_fact(m);
        // Encode the constructor name in the IntrRuleACInfo.
        let info = intr_constr_info(s.name);
        out.push(Rule::new(info, prems, vec![conc], vec![act]));
    }
    out
}

// =============================================================================
// `closeIntrRule` + `variantsIntruder` — port of `Theory.Tools.IntruderRules`
// and `Rule.closeIntrRule`.
//
// Together these post-process the destructor rules in two ways:
//
//   1. For `DestrRule subterm=True` (the "syntactic-subterm" destructors
//      like `sdec`, `fst`, `snd`) — compute the per-rule
//      `paciRemainingApplications` budget (number of consecutive
//      applications allowed before the loop-breaker fires). Rule.hs:104-114.
//
//   2. For `DestrRule subterm=False` (the convergent-equation
//      destructors `d_0_comb`, `d_1_comb`, `d_0_transform` in issue216 —
//      whose RHS is NOT a subterm of the LHS, e.g.
//      `comb(transform(x, y), y) = x`, where `x` and `y` both appear
//      in the RHS even though the RHS `x` is a sub-position of the LHS)
//      — invoke Maude's `get variants` to enumerate ALL variant rules
//      that the destructor can take.  Each Maude variant substitution is
//      applied to the rule, normalised, and added to the pool.  Without
//      this expansion, chains over `d_0_comb` etc. enumerate only the
//      identity-variant — Haskell expects ~3 extra variant rules
//      bringing the chain pool from `nRules=6` to `nRules=9` on issue216,
//      and the 4 issue216 lemmas all need at least one of these variants
//      to close.
//
// HS pipeline ORDER:
//   intrRulesAC = concatMap (closeIntrRule hnd) intrRules
//                       -- ^ AFTER `minimizeIntruderRules` (run inside
//                       --   `subtermIntruderRules`)
// Mirrors Rule.hs:121-176, see line 160.
// =============================================================================

/// `isPrivateFunction` (Term.hs:203-205): top-level function symbol is Private.
pub fn is_private_function(t: &LNTerm) -> bool {
    use tamarin_term::function_symbols::{FunSym, NoEqSym, Privacy};
    use tamarin_term::term::Term;
    matches!(t, Term::App(FunSym::NoEq(NoEqSym { privacy: Privacy::Private, .. }), _))
}

/// `closeIntrRule` — port of `Rule.closeIntrRule` (lib/theory/src/Rule.hs:103-116).
///
/// HS shape:
/// ```haskell
/// closeIntrRule hnd (Rule (DestrRule name (-1) subterm constant)
///                         prems@((Fact KDFact _ [t]):_)
///                         concs@[Fact KDFact _ [rhs]] acts nvs) =
///   if subterm then [ru] else variantsIntruder hnd id False ru
///     where ru = ...budget-computed...
/// closeIntrRule hnd ir@(Rule (DestrRule _ _ False _) _ _ _ _) =
///     variantsIntruder hnd id False ir
/// closeIntrRule _ ir = [ir]
/// ```
///
/// Note the THREE-way pattern split on Haskell:
///   1. `DestrRule name (-1) subterm constant` + KD-single-fact shape  → compute budget,
///      then either single-rule (subterm) or variantsIntruder (non-subterm).
///   2. ANY `DestrRule _ _ False _` (subterm=False) that didn't match clause 1  → variantsIntruder.
///   3. Default — pass through unchanged.
///
/// Clause 2 catches DestrRules whose shape doesn't match clause 1's narrow
/// pattern (e.g. budget already set, multiple-concs, etc.) AND have
/// subterm=False — these still need variant expansion.
pub fn close_intr_rule(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    ir: &IntrRuleAC,
) -> Vec<IntrRuleAC> {
    use tamarin_term::positions::positions;

    // Clause 1: budget = -1 AND single-KD-conclusion AND first-prem is KD.
    if let IntrRuleACInfo::DestrRule(name, -1, subterm, constant) = &ir.info {
        let kd_prem_t: Option<&LNTerm> = ir.premises.first()
            .filter(|f| f.tag == FactTag::Kd && f.terms.len() == 1)
            .map(|f| &f.terms[0]);
        let single_kd_conc_rhs: Option<&LNTerm> =
            if ir.conclusions.len() == 1
                && ir.conclusions[0].tag == FactTag::Kd
                && ir.conclusions[0].terms.len() == 1 {
                Some(&ir.conclusions[0].terms[0])
            } else { None };
        if let (Some(t), Some(rhs)) = (kd_prem_t, single_kd_conc_rhs) {
            // Compute budget: `if runMaude (unifiableLNTerms rhs t)
            //   then (length (positions t)) - (if (isPrivateFunction t) then 1 else 2)
            //   else 0`.
            use tamarin_term::rewriting::Equal;
            let unifiable = maude.unifiable(&[Equal { lhs: rhs.clone(), rhs: t.clone() }])
                .unwrap_or(false);
            let budget: i64 = if unifiable {
                let np = positions(t).len() as i64;
                let sub = if is_private_function(t) { 1 } else { 2 };
                np - sub
            } else {
                0
            };
            let mut ru = ir.clone();
            ru.info = IntrRuleACInfo::DestrRule(name.clone(), budget, *subterm, *constant);
            return if *subterm {
                vec![ru]
            } else {
                variants_intruder(maude, false, &ru)
            };
        }
    }

    // Clause 2: any DestrRule with subterm=False that didn't match clause 1.
    if matches!(&ir.info, IntrRuleACInfo::DestrRule(_, _, false, _)) {
        return variants_intruder(maude, false, ir);
    }

    // Clause 3: pass through.
    vec![ir.clone()]
}

/// `variantsIntruder` — port of
/// `Theory.Tools.IntruderRules.variantsIntruder` (IntruderRules.hs:288-314).
///
/// HS shape (with `minimizeVariants = id`):
/// ```haskell
/// variantsIntruder hnd id applyFilters ru = go [] $ reverse $ do
///     let ruleTerms = concatMap factTerms (rPrems ru ++ rConcs ru ++ rActs ru)
///     fsigma <- computeVariants (fAppList ruleTerms) `runReader` hnd
///     let sigma     = freshToFree fsigma `evalFreshAvoiding` ruleTerms
///         ruvariant = normRule' (apply sigma ru) `runReader` hnd
///     guard (... filter conditions ...)
///     case concatMap factTerms (rConcs ruvariant) of
///       [viewTerm -> FApp (AC Mult) _] -> fail "Rules with product conclusion redundant"
///       _ -> return ruvariant
///   where
///     go checked [] = checked
///     go checked (r:unchecked) =
///       let checked' = if any (\r' -> equalRuleUpToRenaming r r' ...) (checked++unchecked)
///                      then checked else r:checked
///       in go checked' unchecked
/// ```
///
/// The list-monad `do` enumerates Maude variants of the packed rule-terms
/// list `fAppList ruleTerms`.  For each variant substitution:
///   * convert VFresh → free `Subst`, renaming range vars away from `ruleTerms`
///   * apply to the rule
///   * normalise every rule-term via Maude
///   * if `applyFilters`: drop rules with ground conclusions, identity
///     variants (ruvariant == ru), and rules whose conclusions are subsumed
///     by their premises
///   * drop rules whose single conclusion is an AC-Mult product
///
/// Then `go [] $ reverse $ ...` walks the LIST FROM THE BACK and dedups via
/// `equalRuleUpToRenaming`: if any other rule in `checked++unchecked` is
/// equal-up-to-renaming, this rule is dropped.
pub fn variants_intruder(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    apply_filters: bool,
    ru: &IntrRuleAC,
) -> Vec<IntrRuleAC> {
    // HS hardcodes `minimizeVariants = id` for the DH/pmult call
    // (`variantsIntruder hnd id True ...`, IntruderRules.hs:231-283, see line 242/390).
    variants_intruder_with(maude, &|s| s, apply_filters, ru)
}

/// Core of `variantsIntruder` parameterised by the `minimizeVariants`
/// hook — port of `Theory.Tools.IntruderRules.variantsIntruder`
/// (IntruderRules.hs:288-314).
///
/// HS:
/// ```haskell
/// variantsIntruder :: MaudeHandle -> ([LNSubstVFresh] -> [LNSubstVFresh])
///                  -> Bool -> IntrRuleAC -> [IntrRuleAC]
/// variantsIntruder hnd minimizeVariants applyFilters ru = go [] $ reverse $ do
///     let ruleTerms = concatMap factTerms (rPrems ++ rConcs ++ rActs)
///     fsigma <- minimizeVariants $ computeVariants (fAppList ruleTerms) `runReader` hnd
///     ...
/// ```
///
/// `minimizeVariants` is applied to the WHOLE cleaned variant-subst
/// list before any rule is built (HS `fsigma <- minimizeVariants $
/// computeVariants ...`).  The `id` instance recovers
/// [`variants_intruder`] (the DH / pmult-destructor path) exactly; the
/// BP `emap` destructor passes `nub . map canonize` via
/// [`bp_variants_intruder`].
fn variants_intruder_with(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    minimize_variants: &dyn Fn(Vec<tamarin_term::subst_vfresh::LNSubstVFresh>)
        -> Vec<tamarin_term::subst_vfresh::LNSubstVFresh>,
    apply_filters: bool,
    ru: &IntrRuleAC,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::lterm::frees;
    use tamarin_term::subst::{apply_vterm, Subst};
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    use tamarin_term::term::{f_app_list, Term};

    // `ruleTerms = concatMap factTerms (prems ++ concs ++ acts)`.
    // Note: HS does NOT include `nvs` here (only prems/concs/acts), even
    // though the rest of the pipeline includes nvs.
    let mut rule_terms: Vec<LNTerm> = Vec::new();
    for f in ru.premises.iter()
        .chain(ru.conclusions.iter())
        .chain(ru.actions.iter())
    {
        for t in f.terms.iter() { rule_terms.push(t.clone()); }
    }
    // The free vars of the packed rule-terms list.  Note
    // `frees(packed) == frees(rule_terms)` (packing only wraps the terms in
    // an `fAppList`, introducing no new vars), so this single set serves
    // BOTH roles below: the `restrictVFresh (frees packed)` key-set AND the
    // `freshToFreeAvoiding ruleTerms` avoiding-set.  Computed from
    // `&rule_terms` first so `rule_terms` can then be moved into `f_app_list`
    // without a clone.
    let packed_frees: std::collections::BTreeSet<LVar> = {
        let mut s: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        for t in &rule_terms {
            for v in frees(t) { s.insert(v); }
        }
        s
    };

    let packed = f_app_list(rule_terms);

    let raw_substs = match maude.variants(&packed) {
        Ok(v) => v,
        Err(_) => return vec![ru.clone()],
    };

    // Clean each raw variant subst exactly as HS's `computeVariants`
    // returns them (removeRenamings inside variantsViaMaude), then
    // restrict to the packed free vars.  This is the
    // `computeVariants (fAppList ruleTerms)` list that `minimizeVariants`
    // is applied to.
    // `restrict` key-set is loop-invariant (`packed_frees` never mutates), so
    // materialise the `Vec<LVar>` once rather than per variant subst.
    let packed_frees_vec: Vec<LVar> = packed_frees.iter().cloned().collect();
    let cleaned: Vec<LNSubstVFresh> = raw_substs
        .into_iter()
        .map(|pairs| {
            // HS-faithful `removeRenamings` (Maude/Types.hs:123-127, see line 130): HS's
            // `msubstToLSubstVFresh bindings substMaude` — applied to EVERY
            // variant subst inside `variantsViaMaude` (Process.hs:304-309, see line 312,
            // `map (msubstToLSubstVFresh bindings) <$> parseVariantsReply`) —
            // ends with `removeRenamings $ substFromListVFresh slist`, dropping
            // each entry whose image is a bare fresh Var with no other role in
            // the substitution's range (`isRenamedVar`, SubstVFresh.hs:140-145).
            // RS's `maude.variants()` does NOT clean (the proving caller
            // `abstract_rule_and_variants` cleans it itself,
            // tools/rule_variants.rs:548), so we clean here to match HS.  The IDENTITY
            // variant Maude returns for the `inv`/`exp` destructors is
            // `x0 --> #1` (a fresh witness); `removeRenamings` collapses it to
            // the EMPTY subst, so `freshToFreeAvoiding {}` is the identity and
            // the variant rule equals the base rule — which the `ruvariant /= ru`
            // guard (IntruderRules.hs:288-314, see line 297) then drops.  Without this step the
            // identity variants leak through as `{x0 -> x.N}`, yielding the two
            // extra base-case rules (+1 `d_inv` `KD(x)->KD(inv(x))` and
            // +1 `d_exp`) that over-produce 53 rules instead of HS's 51.
            LNSubstVFresh::from_list(pairs)
                .remove_renamings()
                .restrict(&packed_frees_vec)
        })
        .collect();

    // `fsigma <- minimizeVariants $ computeVariants ...` — apply the
    // minimize hook to the WHOLE cleaned list before building rules.
    let minimized = minimize_variants(cleaned);

    // Build one candidate variant rule per (minimized) variant subst.
    let mut produced: Vec<IntrRuleAC> = Vec::new();
    for s_fresh in minimized {

        // `freshToFreeAvoiding ruleTerms` — convert VFresh → free Subst,
        // allocating fresh idxs that avoid every var in `ruleTerms`.
        let sigma: Subst<tamarin_term::lterm::Name, LVar> = {
            let mut counter = packed_frees.iter().map(|v| v.idx).max()
                .map(|m| m + 1).unwrap_or(0);
            s_fresh.fresh_to_free_avoiding(
                |n| { let b = counter; counter += n; b },
            )
        };

        // Build the variant rule by applying sigma + normalising every term.
        // On Maude-reduce failure fall back to the (un-normalised) applied
        // term — the same lenient fallback `map_facts` uses below — rather
        // than fabricating a bogus `err` var into the rule's new_vars.
        let norm_t = |t: LNTerm| -> LNTerm {
            let applied = apply_vterm(&sigma, t);
            maude.reduce(&applied).unwrap_or(applied)
        };
        let map_facts = |fs: &[LNFact]| -> Vec<LNFact> {
            fs.iter().map(|f| {
                // norm/subst rebuild — frees can change; recompute the bloom.
                let terms: Vec<LNTerm> = f.terms.iter().map(|t| norm_t(t.clone())).collect();
                LNFact::fresh_annotated(f.tag.clone(), f.annotations.clone(), terms)
            }).collect()
        };
        let new_prems = map_facts(&ru.premises);
        let new_concs = map_facts(&ru.conclusions);
        let new_acts = map_facts(&ru.actions);
        let new_nvs: Vec<LNTerm> = ru.new_vars.iter().cloned().map(norm_t).collect();
        let ruvariant: IntrRuleAC = Rule {
            info: ru.info.clone(),
            premises: new_prems,
            conclusions: new_concs,
            actions: new_acts,
            new_vars: new_nvs,
        };

        // Filter conditions (HS IntruderRules.hs:295-301):
        //   guard (not applyFilters || frees (rConcs ruvariant) /= []
        //          && (not applyFilters || ruvariant /= ru)
        //          && (rConcs ruvariant) \\ (rPrems ruvariant) /= [])
        //
        // Note the `\\` is the LAST condition and is NOT gated by
        // `applyFilters` in HS: it's ALWAYS applied.  But the first two
        // are gated.  The expression is `a && b && c` — short-circuits to
        // false if any is false.  When applyFilters=False, a and b are
        // True (trivially) so only c applies.
        if apply_filters {
            // Conclusions must have free vars.
            let concs_have_frees = ruvariant.conclusions.iter()
                .flat_map(|f| f.terms.iter())
                .any(|t| !frees(t).is_empty());
            if !concs_have_frees { continue; }
            // Not the identity variant.
            if &ruvariant == ru { continue; }
        }
        // Always-applied: `(rConcs ruvariant) \\ (rPrems ruvariant) /= []`.
        // `Data.List.(\\)` is multiset difference — it removes ONE matching
        // premise per conclusion (so concs=[A,A], prems=[A] yields [A]).
        let concs_minus_prems_nonempty = {
            let mut prem_avail: Vec<bool> = vec![true; ruvariant.premises.len()];
            let mut any_remaining = false;
            for c in &ruvariant.conclusions {
                let mut matched = false;
                for (j, p) in ruvariant.premises.iter().enumerate() {
                    if prem_avail[j] && p == c {
                        prem_avail[j] = false;
                        matched = true;
                        break;
                    }
                }
                if !matched { any_remaining = true; }
            }
            any_remaining
        };
        if !concs_minus_prems_nonempty { continue; }

        // Drop rules with single product-conclusion (HS lines 303-305).
        let conc_terms: Vec<&LNTerm> = ruvariant.conclusions.iter()
            .flat_map(|f| f.terms.iter())
            .collect();
        if conc_terms.len() == 1
            && matches!(conc_terms[0], Term::App(FunSym::Ac(AcSym::Mult), _)) {
                continue;
            }

        produced.push(ruvariant);
    }

    // `go [] $ reverse $ ...` — HS walks the reversed-produced list and
    // prepends each kept rule via `r:checked`.  At walk-step `p` the peer
    // set is `checked ++ unchecked` = {kept so far} ∪ {rev[p+1..]}; a
    // candidate is dropped iff it is `equalRuleUpToRenaming` to some peer.
    // Because HS prepends each kept rule, `checked` ends up in REVERSE of
    // the (reversed-produced) traversal order — i.e. `produced`'s ORIGINAL
    // order, filtered.  We walk by index (avoiding the O(n) `remove(0)` /
    // `insert(0)` shifts), collect kept indices in encounter order, then
    // reverse once to recover the prepend order.
    produced.reverse();
    let rev = produced;
    let mut kept_idx: Vec<usize> = Vec::new();
    for p in 0..rev.len() {
        let r = &rev[p];
        // peers = {kept so far} ∪ {rev[p+1..]}
        let dup = kept_idx.iter().map(|&k| &rev[k])
            .chain(rev[p + 1..].iter())
            .any(|peer| equal_rule_up_to_renaming(maude, r, peer));
        if !dup {
            kept_idx.push(p);
        }
    }
    // HS `checked' = r:checked` prepend ⇒ reverse the encounter order.
    kept_idx.into_iter().rev().map(|k| rev[k].clone()).collect()
}

/// `equalRuleUpToRenaming` — port of
/// `Theory.Model.Rule.equalRuleUpToRenaming` (Rule.hs:1065-1077).
///
/// Two rules are equal up to variable renaming iff:
///   - Same `info`.
///   - Zipped (premises ++ concs ++ acts) have matching fact tags, and the
///     element-wise term-equalities admit a unifier that is a renaming
///     when restricted to either rule's variable occurrences (sorted).
///   - `new_vars` are also zipped into equalities (in HS, `nvs1` zipped
///     with `nvs2` start the equation list).
///
/// HS `matchFacts` only fails (`Nothing`) on a fact-TAG mismatch; the
/// `zipWith Equal`/`zip` over `(pr1++co1++ac1)`/`(pr2++co2++ac2)` and over
/// `nvs1`/`nvs2` silently TRUNCATE to the shorter list on a count or arity
/// mismatch (they never force False), and the concatenations are zipped
/// across section boundaries.  We mirror that exactly with truncating
/// `zip`s and no length guards.  (In practice every caller compares
/// variants of the same base rule, so counts/arities always agree.)
///
/// HS:
/// ```haskell
/// equalRuleUpToRenaming r1 r2 = reader $ \hnd ->
///   case eqs of
///     Nothing   -> False
///     Just eqs' -> (rn1 == rn2) && any isRenamingPerRule (unifs eqs' hnd)
/// ```
pub fn equal_rule_up_to_renaming(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    r1: &IntrRuleAC,
    r2: &IntrRuleAC,
) -> bool {
    use tamarin_term::lterm::HasFrees;
    use tamarin_term::rewriting::Equal;
    use tamarin_term::subst_vfresh::LNSubstVFresh;

    if r1.info != r2.info { return false; }

    // HS's `eqs` is initialised with `zipWith Equal nvs1 nvs2` (truncating),
    // then each tag-matching fact pair extends it by `zipWith Equal t1 t2`
    // (also truncating).  `matchFacts` only fails on a TAG mismatch — never
    // on a count/arity mismatch — so we use truncating `zip`s with no length
    // guards, and zip the section concatenations across boundaries.
    let mut term_eqs: Vec<Equal<LNTerm>> = Vec::new();
    for (a, b) in r1.new_vars.iter().zip(r2.new_vars.iter()) {
        term_eqs.push(Equal { lhs: a.clone(), rhs: b.clone() });
    }
    let pair_iter = r1.premises.iter().chain(r1.conclusions.iter()).chain(r1.actions.iter())
        .zip(r2.premises.iter().chain(r2.conclusions.iter()).chain(r2.actions.iter()));
    for (f1, f2) in pair_iter {
        if f1.tag != f2.tag { return false; }
        for (a, b) in f1.terms.iter().zip(f2.terms.iter()) {
            term_eqs.push(Equal { lhs: a.clone(), rhs: b.clone() });
        }
    }

    // Collect each rule's vars (occurrences-set).
    let vars_r1: Vec<LVar> = {
        let mut s: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        r1.for_each_free(&mut |v| { s.insert(v.clone()); });
        s.into_iter().collect()
    };
    let vars_r2: Vec<LVar> = {
        let mut s: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        r2.for_each_free(&mut |v| { s.insert(v.clone()); });
        s.into_iter().collect()
    };

    // Trivial case: no constraints → identity unifier is trivially a
    // renaming (empty), so result is True.
    if term_eqs.is_empty() {
        return true;
    }

    let unifs = match maude.unify_at("equal_rule_up_to_renaming", &term_eqs) {
        Ok(u) => u,
        Err(_) => return false,
    };
    // For each unifier `subst`: check `isRenaming (restrictVFresh vars_r1 subst)
    //                       && isRenaming (restrictVFresh vars_r2 subst)`.
    // The unifier comes back as `Vec<(LVar, LNTerm)>` — treat as VFresh.
    for u_pairs in &unifs {
        let s_fresh = LNSubstVFresh::from_list(u_pairs.clone());
        let r1_rest = s_fresh.restrict(&vars_r1);
        let r2_rest = s_fresh.restrict(&vars_r2);
        if r1_rest.is_renaming() && r2_rest.is_renaming() {
            return true;
        }
    }
    false
}

// =============================================================================
// `normRule'` — port of `Theory.Tools.IntruderRules.normRule'`
// (IntruderRules.hs:316-321).
//
// HS shape:
// ```haskell
// normRule' :: IntrRuleAC -> WithMaude IntrRuleAC
// normRule' (Rule i ps cs as nvs) = reader $ \hnd ->
//     let normFactTerms = map (fmap (\t -> norm' t `runReader` hnd)) in
//     let normTerms     = map (\t -> norm' t `runReader` hnd) in
//     Rule i (normFactTerms ps) (normFactTerms cs) (normFactTerms as) (normTerms nvs)
// ```
//
// Walks every fact-term + every new-var term through Maude-backed
// `norm'`.  We use the lenient `tamarin_term::norm::norm` (returns
// Result; on Maude error we fall back to the original term, matching
// the lenient style of the rest of the port — Maude failures during
// variant expansion are recoverable, and propagating them up would
// abort theory load).
// =============================================================================
/// `normRule'` — normalise every term in an intruder rule via Maude.
///
/// Mirrors HS `normRule'` (IntruderRules.hs). Retained as a standalone
/// reusable mirror of `normRule'`; it is intentionally not on the
/// `variants_intruder` hot path, which inlines normalisation via
/// `maude.reduce` rather than going through this function.
// Intentionally retained: faithful HS port; no caller yet.
#[allow(dead_code)]
pub(crate) fn norm_rule(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    ru: &IntrRuleAC,
) -> IntrRuleAC {
    let norm_t = |t: &LNTerm| -> LNTerm {
        tamarin_term::norm::norm(maude, t).unwrap_or_else(|_| t.clone())
    };
    let norm_fact = |f: &LNFact| -> LNFact {
        // norm rebuild — frees can change; recompute the bloom.
        let terms: Vec<LNTerm> = f.terms.iter().map(&norm_t).collect();
        LNFact::fresh_annotated(f.tag.clone(), f.annotations.clone(), terms)
    };
    Rule {
        info: ru.info.clone(),
        premises: ru.premises.iter().map(&norm_fact).collect(),
        conclusions: ru.conclusions.iter().map(&norm_fact).collect(),
        actions: ru.actions.iter().map(&norm_fact).collect(),
        new_vars: ru.new_vars.iter().map(&norm_t).collect(),
    }
}

// =============================================================================
// `dhIntruderRules` — port of
// `Theory.Tools.IntruderRules.dhIntruderRules`
// (IntruderRules.hs:230-283).
//
// HS shape:
// ```haskell
// dhIntruderRules :: Bool -> WithMaude [IntrRuleAC]
// dhIntruderRules diff = reader $ \hnd -> minimizeIntruderRules diff $
//     [ expRule  (ConstrRule (append (pack "_") expSymString))  kuFact return
//     , invRule  (ConstrRule (append (pack "_") invSymString))  kuFact return
//     , dhNeutralRule (ConstrRule (append (pack "_") dhNeutralSymString)) kuFact return
//     , oneRule  (ConstrRule (append (pack "_") oneSymString))  kuFact return
//     , multRule (ConstrRule (append (pack "_") multSymString)) kuFact return
//     ] ++
//     concatMap (variantsIntruder hnd id True)
//       [ expRule (DestrRule (append (pack "_") expSymString) 0 True False) kdFact (const [])
//       , invRule (DestrRule (append (pack "_") invSymString) 0 True False) kdFact (const [])
//       ]
//   where
//     x_var_0 = varTerm (LVar "x" LSortMsg 0)
//     x_var_1 = varTerm (LVar "x" LSortMsg 1)
//     expRule mkInfo kudFact mkAction =
//         Rule mkInfo [bfact, efact] [concfact] (mkAction concfact) []
//       where bfact=kudFact x_var_0; efact=kuFact x_var_1
//             conc=fAppExp(x_var_0,x_var_1); concfact=kudFact conc
//     ... (multRule, invRule, oneRule, dhNeutralRule similarly)
// ```
//
// Note the asymmetry of `mkAction` between constructors and
// destructors:
//   * constructors pass `return :: a -> [a]` (singleton list) — i.e.
//     `[concfact]` as the actions list.
//   * destructors pass `const [] :: a -> [a]` — i.e. empty actions.
//
// We mirror this by passing the `mk_action` argument as an `Fn(&LNFact)
// -> Vec<LNFact>` closure.
// =============================================================================

// Shared `mkInfo`/action plumbing for `dh_intruder_rules` and
// `bp_intruder_rules` (these are inline HS `where`-helpers, not distinct HS
// functions, so a single Rust definition serves both generators).

/// `append (pack "_") xSymString` — the intruder-rule name-mangling primitive.
fn underscore_prefixed(sym: &[u8]) -> Vec<u8> {
    let mut n = b"_".to_vec();
    n.extend_from_slice(sym);
    n
}

/// `ConstrRule (append (pack "_") xSymString)`.
fn intr_constr_info(sym: &[u8]) -> IntrRuleACInfo {
    IntrRuleACInfo::ConstrRule(underscore_prefixed(sym))
}

/// `DestrRule (append (pack "_") xSymString) 0 True False` (IntruderRules.hs:243-244).
/// Note budget=0 (NOT -1), subterm=True, constant=False.  `closeIntrRule` is
/// what assigns the budget=-1 sentinel in our pipeline for subtermIntruderRules'
/// destructors; here HS assigns budget=0 directly because these are
/// convergent-eq destructors for which the budget is irrelevant
/// (variantsIntruder will expand them).
fn intr_destr_info(sym: &[u8]) -> IntrRuleACInfo {
    IntrRuleACInfo::DestrRule(underscore_prefixed(sym), 0, true, false)
}

/// `return :: a -> [a]` — singleton-list action constructor (HS).
fn intr_mk_singleton(f: LNFact) -> Vec<LNFact> { vec![f] }
/// `const [] :: a -> [a]` — empty action constructor (HS destructors).
fn intr_mk_empty(_: LNFact) -> Vec<LNFact> { Vec::new() }

/// `dhIntruderRules` — compute the intruder rules for the Diffie-Hellman
/// theory.  Direct mirror of HS `dhIntruderRules` (IntruderRules.hs:230-283).
///
/// Returns 5 constructor rules (`_exp`, `_inv`, `_DH_neutral`, `_one`,
/// `_mult`) plus the variants-expansion of 2 destructor rules
/// (`_exp`, `_inv`).  The constructors for `one` / `mult` /
/// `DH_neutral` are only really applied in `diff` mode — in trace mode
/// all such constraints are solved directly — but the constructors
/// always appear in the message theory (mirrors HS comment at
/// IntruderRules.hs:235-237).
///
/// # Role: cache REGENERATOR (not the production runtime path)
///
/// HS uses this function only inside `Main.Mode.Intruder.run`
/// (src/Main/Mode/Intruder.hs:43-63, see line 48) to PRODUCE `data/intruder_variants_dh.spthy`:
/// ```haskell
/// let dhRules = dhIntruderRules False `runReader` dhHnd
/// ```
/// The production theory-load path
/// (`Main.TheoryLoader.addMessageDeductionRuleVariants`,
/// TheoryLoader.hs:776-791) parses the CACHED file via
/// `mkDhIntruderVariants` — see [`crate::intruder_variants::mk_dh_intruder_variants`].
///
/// In production the Rust port likewise takes the cached-file path
/// (see `constraint::solver::context::ProofContext::new_with_restrictions`,
/// the `intruder_variants::mk_dh_intruder_variants` call); this
/// function is retained as the regenerator and is exercised by the
/// bridge test
/// `intruder_variants::tests::bridge_runtime_generator_matches_cached_file_on_counts_and_names`,
/// which flags drift between today's Maude and the cached file.
pub fn dh_intruder_rules(
    diff: bool,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Vec<IntrRuleAC> {
    use tamarin_term::builtin::{dh_neutral, exp, inv, mult, one_const};
    use tamarin_term::function_symbols::{
        DH_NEUTRAL_SYM_STRING, EXP_SYM_STRING, INV_SYM_STRING, MULT_SYM_STRING,
        ONE_SYM_STRING,
    };

    // `x_var_0 = varTerm (LVar "x" LSortMsg 0)` etc.
    // IntruderRules.hs:247-248.
    let x_var_0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x_var_1 = var_term(LVar::new("x", LSort::Msg, 1));

    // HS `expRule mkInfo kudFact mkAction`
    //   = Rule mkInfo [kudFact x_var_0, kuFact x_var_1] [kudFact (fAppExp ...)] (mkAction ...) []
    // IntruderRules.hs:250-256.
    let exp_rule = |info: IntrRuleACInfo,
                    kud_fact: fn(LNTerm) -> LNFact,
                    mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = ku_fact(x_var_1.clone());
        let conc = exp(x_var_0.clone(), x_var_1.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // HS `multRule` — IntruderRules.hs:258-264.
    let mult_rule = |info: IntrRuleACInfo,
                     kud_fact: fn(LNTerm) -> LNFact,
                     mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = ku_fact(x_var_1.clone());
        let conc = mult(x_var_0.clone(), x_var_1.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // HS `invRule` — IntruderRules.hs:266-271.
    let inv_rule = |info: IntrRuleACInfo,
                    kud_fact: fn(LNTerm) -> LNFact,
                    mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let conc = inv(x_var_0.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact], vec![concfact], acts)
    };

    // HS `oneRule` — IntruderRules.hs:273-277.
    let one_rule = |info: IntrRuleACInfo,
                    kud_fact: fn(LNTerm) -> LNFact,
                    mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let conc = one_const::<tamarin_term::vterm::Lit<tamarin_term::lterm::Name, LVar>>();
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![], vec![concfact], acts)
    };

    // HS `dhNeutralRule` — IntruderRules.hs:279-283.
    let dh_neutral_rule = |info: IntrRuleACInfo,
                           kud_fact: fn(LNTerm) -> LNFact,
                           mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let conc = dh_neutral::<tamarin_term::vterm::Lit<tamarin_term::lterm::Name, LVar>>();
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![], vec![concfact], acts)
    };

    // Shared `mkInfo`/action plumbing (`intr_constr_info` etc.).
    let constr_info = intr_constr_info;
    let destr_info = intr_destr_info;
    let mk_singleton: &dyn Fn(LNFact) -> Vec<LNFact> = &intr_mk_singleton;
    let mk_empty: &dyn Fn(LNFact) -> Vec<LNFact> = &intr_mk_empty;

    let constrs: Vec<IntrRuleAC> = vec![
        // expRule  (ConstrRule "_exp")        kuFact return
        exp_rule(constr_info(EXP_SYM_STRING), ku_fact, mk_singleton),
        // invRule  (ConstrRule "_inv")        kuFact return
        inv_rule(constr_info(INV_SYM_STRING), ku_fact, mk_singleton),
        // dhNeutralRule (ConstrRule "_DH_neutral") kuFact return
        dh_neutral_rule(constr_info(DH_NEUTRAL_SYM_STRING), ku_fact, mk_singleton),
        // oneRule  (ConstrRule "_one")        kuFact return
        one_rule(constr_info(ONE_SYM_STRING), ku_fact, mk_singleton),
        // multRule (ConstrRule "_mult")       kuFact return
        mult_rule(constr_info(MULT_SYM_STRING), ku_fact, mk_singleton),
    ];

    // Destructor variants: `concatMap (variantsIntruder hnd id True) [exp-destr, inv-destr]`.
    // IntruderRules.hs:241-245.  Note `applyFilters=True` here (NOT False
    // like in closeIntrRule's invocation) — this is the BUILD-time
    // narrowing call, which expects the identity variant and ground-conc
    // variants to be DROPPED.
    let exp_destr = exp_rule(destr_info(EXP_SYM_STRING), kd_fact, mk_empty);
    let inv_destr = inv_rule(destr_info(INV_SYM_STRING), kd_fact, mk_empty);

    let mut destr_variants: Vec<IntrRuleAC> = Vec::new();
    destr_variants.extend(variants_intruder(maude, true, &exp_destr));
    destr_variants.extend(variants_intruder(maude, true, &inv_destr));

    // `minimizeIntruderRules diff $ constrs ++ destr_variants`.
    let mut all = constrs;
    all.extend(destr_variants);
    minimize_intruder_rules(diff, all)
}

// =============================================================================
// `bpIntruderRules` — port of
// `Theory.Tools.IntruderRules.bpIntruderRules` (IntruderRules.hs:384-437).
//
// HS shape:
// ```haskell
// bpIntruderRules :: Bool -> WithMaude [IntrRuleAC]
// bpIntruderRules diff = reader $ \hnd -> minimizeIntruderRules diff $
//     [ pmultRule (ConstrRule "_pmult") kuFact return
//     , emapRule  (ConstrRule "_em")    kuFact return
//     ]
//     ++ (variantsIntruder hnd id True $
//           pmultRule (DestrRule "_pmult" 0 True False) kdFact (const []))
//     ++ (bpVariantsIntruder hnd $
//           emapRule (DestrRule "_em" 0 True False) kdFact (const []))
//   where
//     x_var_0 = varTerm (LVar "x" LSortMsg 0)
//     x_var_1 = varTerm (LVar "x" LSortMsg 1)
//     pmultRule mkInfo kud mkAction =
//         Rule mkInfo [kud x0, kuFact x1] [kud (pmult(x1,x0))] (mkAction conc) []
//     emapRule mkInfo kud mkAction =
//         Rule mkInfo [kud x0, kud x1] [kud (em(x0,x1))] (mkAction conc) []
// ```
//
// NOTE the asymmetries vs `dhIntruderRules`:
//   * `pmultRule`'s conclusion is `pmult(x_var_1, x_var_0)` — the args
//     are SWAPPED relative to the premise order (HS `fAppPMult (x_var_1,
//     x_var_0)`, IntruderRules.hs:384-413, see line 404).
//   * `emapRule` uses `kud` (the KU/KD-fact constructor) for BOTH
//     premises (`bfact = kud x0`, `efact = kud x1`), not `kuFact` for the
//     second (IntruderRules.hs:410-411).
//
// # Role: runtime BP generator for the `variants` command ONLY
//
// HS's `variants` command (Main.Mode.Intruder.run, Intruder.hs:48-53)
// generates `bpIntruderRules False` at RUNTIME against a fresh
// `bpMaudeSig` handle.  On current Maude this differs from the STALE
// cached `data/intruder_variants_bp.spthy`, which production PROVING
// still parses via `mk_bp_intruder_variants`.  This function is the
// runtime generator and is reachable ONLY from `run_variants`; proving
// must keep using the cached file.
// =============================================================================
/// `bpIntruderRules` — compute the bilinear-pairing intruder rules at
/// runtime.  Direct mirror of HS `bpIntruderRules` (IntruderRules.hs:384-437).
///
/// Returns 2 constructor rules (`_pmult`, `_em`) plus the
/// variants-expansion of the `_pmult` destructor (via plain
/// `variants_intruder`, like DH `exp`) and the `_em` destructor (via
/// [`bp_variants_intruder`], which canonicalises + the KD→KU
/// post-process).
///
/// Reachable only from the `variants` command — NOT from proving (which
/// uses the cached [`crate::intruder_variants::mk_bp_intruder_variants`]).
pub fn bp_intruder_rules(
    diff: bool,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> Vec<IntrRuleAC> {
    use tamarin_term::builtin::{emap, pmult};
    use tamarin_term::function_symbols::{EMAP_SYM_STRING, PMULT_SYM_STRING};

    // `x_var_0 = varTerm (LVar "x" LSortMsg 0)` etc. (IntruderRules.hs:396-397).
    let x_var_0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x_var_1 = var_term(LVar::new("x", LSort::Msg, 1));

    // HS `pmultRule mkInfo kud mkAction` (IntruderRules.hs:399-405).
    //   prems = [kud x0, kuFact x1]; conc = kud (pmult(x1, x0)).
    // The conclusion args are SWAPPED: `fAppPMult (x_var_1, x_var_0)`.
    let pmult_rule = |info: IntrRuleACInfo,
                      kud_fact: fn(LNTerm) -> LNFact,
                      mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = ku_fact(x_var_1.clone());
        let conc = pmult(x_var_1.clone(), x_var_0.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // HS `emapRule mkInfo kud mkAction` (IntruderRules.hs:407-413).
    //   prems = [kud x0, kud x1] (BOTH via kud); conc = kud (em(x0, x1)).
    let emap_rule = |info: IntrRuleACInfo,
                     kud_fact: fn(LNTerm) -> LNFact,
                     mk_action: &dyn Fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = kud_fact(x_var_1.clone());
        let conc = emap(x_var_0.clone(), x_var_1.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // Shared `mkInfo`/action plumbing (`intr_constr_info` etc.).
    let constr_info = intr_constr_info;
    let destr_info = intr_destr_info;
    let mk_singleton: &dyn Fn(LNFact) -> Vec<LNFact> = &intr_mk_singleton;
    let mk_empty: &dyn Fn(LNFact) -> Vec<LNFact> = &intr_mk_empty;

    // Constructor rules: `pmultRule (ConstrRule "_pmult") kuFact return`
    // and `emapRule (ConstrRule "_em") kuFact return`.
    let constrs: Vec<IntrRuleAC> = vec![
        pmult_rule(constr_info(PMULT_SYM_STRING), ku_fact, mk_singleton),
        emap_rule(constr_info(EMAP_SYM_STRING), ku_fact, mk_singleton),
    ];

    // pmult destructor variants — `variantsIntruder hnd id True`
    // (like DH `exp`).
    let pmult_destr = pmult_rule(destr_info(PMULT_SYM_STRING), kd_fact, mk_empty);
    let mut all = constrs;
    all.extend(variants_intruder(maude, true, &pmult_destr));

    // em destructor variants — `bpVariantsIntruder hnd` (canonicalised +
    // KD→KU post-process).
    let emap_destr = emap_rule(destr_info(EMAP_SYM_STRING), kd_fact, mk_empty);
    all.extend(bp_variants_intruder(maude, &emap_destr));

    // `minimizeIntruderRules diff $ ...`.
    minimize_intruder_rules(diff, all)
}

/// `bpVariantsIntruder` — port of
/// `Theory.Tools.IntruderRules.bpVariantsIntruder` (IntruderRules.hs:415-437).
///
/// ```haskell
/// bpVariantsIntruder hnd ru = do
///     ruvariant <- variantsIntruder hnd minimizeVariants True ru
///     case ruvariant of
///       Rule i [Fact KDFact an args@[Lit (Var _)], yfact] cs as nvs ->
///         return $ Rule i [Fact KUFact an args, yfact] cs as nvs
///       Rule i [yfact, Fact KDFact an args@[Lit (Var _)]] cs as nvs ->
///         return $ Rule i [yfact, Fact KUFact an args] cs as nvs
///       _ -> return ruvariant
///   where
///     minimizeVariants = nub . map canonize
///     canonize subst = canonizeSubst . substFromListVFresh $ zip doms (sort rngs)
///       where mappings = substToListVFresh subst
///             doms     = map fst mappings
///             rngs     = map snd mappings
/// ```
///
/// `minimizeVariants = nub . map canonize` collapses BP em-destructor
/// variants that differ only by a renaming of their range terms.
/// `canonize` re-zips the domain with the SORTED range terms and then
/// applies [`canonize_subst`] (the occurrence-set canonicalisation).
/// The KD→KU post-process makes the bare-`Var` premise of the
/// `x, pmult(y,z) -> em(x,z)^y` / `pmult(y,z), x -> em(z,x)^y` variants a
/// KU premise (the `x` becomes adversary-known).
fn bp_variants_intruder(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    ru: &IntrRuleAC,
) -> Vec<IntrRuleAC> {
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    use tamarin_term::subsumption::canonize_subst;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // `minimizeVariants = nub . map canonize`.
    //   canonize subst = canonizeSubst . substFromListVFresh $
    //                       zip doms (sort rngs)
    // where (doms, rngs) = unzip (substToListVFresh subst), i.e. the
    // domain keys in `to_list` order zipped with the SORTED range terms.
    let minimize_variants =
        |substs: Vec<LNSubstVFresh>| -> Vec<LNSubstVFresh> {
            let mut out: Vec<LNSubstVFresh> = Vec::new();
            for s in substs {
                let mappings = s.to_list();
                let doms: Vec<LVar> = mappings.iter().map(|(d, _)| d.clone()).collect();
                let mut rngs: Vec<LNTerm> =
                    mappings.iter().map(|(_, t)| t.clone()).collect();
                // `sort rngs` — `Ord LNTerm`.
                rngs.sort();
                let rezipped = LNSubstVFresh::from_list(
                    doms.into_iter().zip(rngs).collect::<Vec<_>>(),
                );
                let canon = canonize_subst(&rezipped);
                // `nub` — keep first occurrence, drop later duplicates
                // (structural `Eq` on the canonicalised subst).
                if !out.iter().any(|existing| existing == &canon) {
                    out.push(canon);
                }
            }
            out
        };

    let variants = variants_intruder_with(maude, &minimize_variants, true, ru);

    // KD→KU post-process (IntruderRules.hs:424-429): if the first premise
    // is a KD-fact whose single arg is a bare Var, rewrite that premise's
    // tag KD→KU (keeping the same args/annotations); else the symmetric
    // case where the SECOND premise is the bare-Var KD-fact.
    let is_bare_var_kd = |f: &LNFact| -> bool {
        f.tag == FactTag::Kd
            && f.terms.len() == 1
            && matches!(f.terms[0], Term::Lit(Lit::Var(_)))
    };
    variants
        .into_iter()
        .map(|mut rv| {
            if rv.premises.len() == 2 {
                if is_bare_var_kd(&rv.premises[0]) {
                    rv.premises[0].tag = FactTag::Ku;
                } else if is_bare_var_kd(&rv.premises[1]) {
                    rv.premises[1].tag = FactTag::Ku;
                }
            }
            rv
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Pins HS `subsetOf` (Utils/Misc.hs:87-88, see line 88) as a SET subset:
    // `(S.fromList xs) `S.isSubsetOf` (S.fromList ys)` deduplicates BOTH
    // sides, so `is_subset_of` must ignore multiplicity entirely.
    #[test]
    fn is_subset_of_ignores_multiplicity() {
        use tamarin_term::vterm::var_term;
        let y = var_term(LVar::new("y", LSort::Msg, 0));
        let z = var_term(LVar::new("z", LSort::Msg, 0));
        // {KU(y)} ⊆ {KU(y), KU(z)}: as a SET subset (HS `subsetOf`) this holds
        // even though a=[KU(y),KU(y)] has higher multiplicity than the single
        // KU(y) in b — a multiset-subset check would reject it (no second
        // KU(y) in b to consume).
        let a = vec![ku_fact(y.clone()), ku_fact(y.clone())];
        let b = vec![ku_fact(y.clone()), ku_fact(z.clone())];
        assert!(is_subset_of(&a, &b));
        // A distinct element of `a` not in `b` ⇒ not a subset.
        assert!(!is_subset_of(&b, &a));
    }

    // minimize_intruder_rules subsumption uses the SET-subset `is_subset_of`
    // (HS `prems' `subsetOf` prems`), so a peer whose DISTINCT premise set is a
    // subset subsumes this rule even at higher multiplicity.  Pins HS
    // IntruderRules.hs:195-197.
    #[test]
    fn minimize_drops_set_subsumed_rule() {
        use tamarin_term::vterm::var_term;
        let x = var_term(LVar::new("x", LSort::Msg, 0));
        let y = var_term(LVar::new("y", LSort::Msg, 0));
        let z = var_term(LVar::new("z", LSort::Msg, 1));
        let name = b"_subsume_test".to_vec();
        // r_j (subsumer): premises [KU(y), KU(y)], conclusion KD(x).
        let r_j = Rule::new(
            IntrRuleACInfo::DestrRule(name.clone(), -1, true, false),
            vec![ku_fact(y.clone()), ku_fact(y.clone())],
            vec![kd_fact(x.clone())],
            vec![],
        );
        // r_i (subsumed): premises [KU(y), KU(z)], same conclusion KD(x).
        // Distinct premises of r_j ({KU(y)}) ⊆ distinct premises of r_i
        // ({KU(y), KU(z)}), so r_j subsumes r_i → r_i dropped.  r_j itself is
        // not dropped: KU(z) of r_i is absent from r_j's premise set.
        let r_i = Rule::new(
            IntrRuleACInfo::DestrRule(name.clone(), -1, true, false),
            vec![ku_fact(y.clone()), ku_fact(z.clone())],
            vec![kd_fact(x.clone())],
            vec![],
        );
        let out = minimize_intruder_rules(false, vec![r_j.clone(), r_i.clone()]);
        // Set-subset: r_i is dropped; only r_j survives.  (Multiset bookkeeping
        // would have kept both, since r_j has two KU(y) but r_i only one.)
        assert_eq!(out.len(), 1);
        assert_eq!(out[0].premises, r_j.premises);
    }

    #[test]
    fn special_rules_count_excluding_diff() {
        let r = special_intruder_rules(false);
        assert_eq!(r.len(), 5);
        assert!(matches!(r[0].info, IntrRuleACInfo::Coerce));
        assert!(matches!(r[1].info, IntrRuleACInfo::PubConstr));
        assert!(matches!(r[2].info, IntrRuleACInfo::FreshConstr));
        assert!(matches!(r[3].info, IntrRuleACInfo::ISend));
        assert!(matches!(r[4].info, IntrRuleACInfo::IRecv));
    }

    #[test]
    fn special_rules_count_with_diff() {
        let r = special_intruder_rules(true);
        assert_eq!(r.len(), 6);
        assert!(matches!(r[5].info, IntrRuleACInfo::IEquality));
    }

    #[test]
    fn pub_constr_has_x_pub_in_new_vars() {
        let r = &special_intruder_rules(false)[1];
        assert_eq!(r.new_vars.len(), 1);
    }

    #[test]
    fn fresh_constr_has_fresh_premise() {
        let r = &special_intruder_rules(false)[2];
        assert_eq!(r.premises.len(), 1);
        assert!(matches!(
            r.premises[0].tag,
            crate::fact::FactTag::Fresh
        ));
    }

    #[test]
    fn isend_emits_in_conclusion() {
        let r = &special_intruder_rules(false)[3];
        assert!(matches!(r.conclusions[0].tag, crate::fact::FactTag::In));
    }

    // =========================================================================
    // construction_rules: per-symbol KU constructor generation.
    //
    // Direct Haskell-spec mirror — Theory.Tools.IntruderRules.hs:
    //
    //     constructionRules fSig =
    //         [ createRule s k | (s, (k, Public, Constructor)) <- S.toList fSig ]
    //       where
    //         createRule s k = Rule (ConstrRule (append (pack "_") s))
    //                              (map kuFact vars) [concfact] [concfact] []
    //           where vars = take k [varTerm (LVar "x" LSortMsg i) | i <- [0..]]
    //                 m = fAppNoEq (s, (k, Public, Constructor)) vars
    //                 concfact = kuFact m
    // =========================================================================

    #[test]
    fn construction_rules_pair_signature_emits_pair_rule() {
        // The default pair-only signature has `pair/2`, `fst/1`, `snd/1`.
        // pair is Public+Constructor → emits a KU rule;
        // fst, snd are Public+Destructor → no construction rule.
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules = construction_rules(&sig);
        // Find the pair rule.
        let pair_rule = rules.iter().find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule(name) => name == b"_pair",
            _ => false,
        });
        let pair_rule = pair_rule.expect("expected pair construction rule");
        // pair/2 → 2 KU premises, 1 KU conclusion, 1 KU action.
        assert_eq!(pair_rule.premises.len(), 2);
        assert_eq!(pair_rule.conclusions.len(), 1);
        assert_eq!(pair_rule.actions.len(), 1);
        // All facts have KU tag.
        for f in pair_rule.premises.iter()
            .chain(&pair_rule.conclusions)
            .chain(&pair_rule.actions)
        {
            assert_eq!(f.tag, crate::fact::FactTag::Ku);
        }
    }

    #[test]
    fn construction_rules_only_emits_constructor_info() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules = construction_rules(&sig);
        // Every emitted rule should have `ConstrRule` info — never
        // a `DestrRule` (we filter on Constructability).
        for r in &rules {
            match &r.info {
                IntrRuleACInfo::ConstrRule(_) => {}
                other => panic!("expected ConstrRule, got {:?}", other),
            }
        }
        assert!(!rules.is_empty(), "default pair sig has at least one constructor");
    }

    /// Symmetric-encryption signature should emit one destructor rule
    /// for `sdec(senc(x, y), y) = x`.  The rule must have:
    ///   - First premise: KD(senc(x, y)).
    ///   - Second premise: KU(y).
    ///   - Conclusion: KD(x).
    #[test]
    fn destruction_rules_sym_enc_emits_decryption() {
        let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        // We expect exactly one destructor: the outermost decryption.
        assert!(!rules.is_empty(),
            "expected at least one sdec destructor; got {:?}", rules);
        // Inspect: first rule should have KD as first premise + at least one KU.
        let first = &rules[0];
        assert_eq!(first.premises[0].tag, crate::fact::FactTag::Kd);
        assert!(first.premises.iter().skip(1).all(|p| p.tag == crate::fact::FactTag::Ku),
            "follow-on premises must be KU; got {:?}", first.premises);
        assert_eq!(first.conclusions[0].tag, crate::fact::FactTag::Kd);
    }

    /// Pair signature emits `fst` / `snd` destructors.
    #[test]
    fn destruction_rules_pair_emits_fst_snd_destructors() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        // One destructor per rule; pair has fst + snd → 2 destructor rules.
        assert!(rules.len() >= 2,
            "expected >= 2 pair destructors (fst + snd); got {}", rules.len());
    }

    /// `subtermIntruderRules` on a sym-enc signature should combine
    /// construction (senc) + destruction (sdec).
    #[test]
    fn subterm_intruder_rules_combines_construction_and_destruction() {
        let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
        let rules = subterm_intruder_rules(false, &sig);
        let any_destr = rules.iter().any(|r|
            matches!(r.info, IntrRuleACInfo::DestrRule(..)));
        let any_constr = rules.iter().any(|r|
            matches!(r.info, IntrRuleACInfo::ConstrRule(_)));
        assert!(any_destr, "expected at least one DestrRule");
        assert!(any_constr, "expected at least one ConstrRule");
    }

    #[test]
    fn construction_rules_premise_count_equals_arity() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        for r in construction_rules(&sig) {
            // Pull the symbol's arity from the rule's KU action term.
            let conc_term = &r.conclusions[0].terms[0];
            let arity = match conc_term {
                tamarin_term::term::Term::App(_, args) => args.len(),
                tamarin_term::term::Term::Lit(_) => 0,
            };
            assert_eq!(r.premises.len(), arity,
                "premise count must equal symbol arity");
            assert_eq!(r.conclusions.len(), 1);
            assert_eq!(r.actions.len(), 1);
        }
    }

    // =========================================================================
    // Haskell-faithfulness invariants for `destruction_rules`.
    //
    // Mirrors IntruderRules.hs:129-157.  Two easy-to-break patterns:
    //
    //   1. Pattern #1 line 135: at the LAST position step, if the
    //      current term is an FApp AND rhs has free vars, return [].
    //      (The "skip-last" case.)
    //
    //   2. Private-symbol stop (line 149): descending through a Private
    //      constructor terminates the loop early.
    // =========================================================================

    /// `destructionRules` for the sym-enc rule `sdec(senc(x, y), y) = x`
    /// must emit EXACTLY ONE destructor, not two.
    ///
    /// The rule has rhs position [0, 0] — two steps.  Without the
    /// skip-last guard, Rust emits a second (degenerate) destructor at
    /// the inner step, producing `KD(x) + KU(...) → KD(x)` — a
    /// self-loop that explodes the chain search on denning_sacco.
    #[test]
    fn destruction_rules_sym_enc_emits_exactly_one_destructor() {
        let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        assert_eq!(rules.len(), 1,
            "sym-enc rule `sdec(senc(x, y), y) = x` must yield EXACTLY ONE \
             destructor — the skip-last pattern (IntruderRules.hs:135) \
             elides the inner step.  Got {} rules.  If this regresses, \
             denning_sacco-class chain explosion will silently reappear.",
            rules.len());
        let r = &rules[0];
        // Premise[0] = KD(senc(x, y)); follow-on premises = KU(y).
        assert_eq!(r.premises[0].tag, crate::fact::FactTag::Kd);
        // Inner step was elided, so no `KD(x) KU(x) → KD(x)` self-loop.
        for p in &r.premises[1..] {
            assert_eq!(p.tag, crate::fact::FactTag::Ku);
        }
    }

    /// `destructionRules` for the asym-enc rule
    /// `adec(aenc(x, pk(y)), y) = x` likewise emits EXACTLY ONE
    /// destructor (position [0, 0], rhs free var x).
    #[test]
    fn destruction_rules_asym_enc_emits_exactly_one_destructor() {
        let sig = tamarin_term::maude_sig::asym_enc_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        assert_eq!(rules.len(), 1,
            "asym-enc rule must yield EXACTLY ONE destructor; got {} rules. \
             Skip-last pattern was probably regressed.", rules.len());
    }

    /// `destructionRules` for pair `fst(<x,y>) = x` and `snd(<x,y>) = y`
    /// each yield EXACTLY ONE destructor.  Pair is a one-step rule
    /// (position [0]), but skip-last doesn't apply to the FIRST step
    /// because step_idx == 0 and pos_iter.len() == 1 → step_idx+1 == len,
    /// and `t` is `pair(x,y)` (FApp) and rhs is a var (free) — so
    /// skip-last DOES fire.  This means the destructor must be emitted
    /// at the WRAPPING-step (the outer match arm where we step from
    /// the destructor's lhs into pair), NOT at the inner step.
    ///
    /// (This is subtle and worth pinning explicitly.)
    #[test]
    fn destruction_rules_pair_emits_exactly_two_destructors() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        assert_eq!(rules.len(), 2,
            "pair signature must yield exactly fst + snd destructors \
             (2 total); got {} rules.  Pair rules are `fst(<x,y>) = x` \
             and `snd(<x,y>) = y` at position [0] each.", rules.len());
    }

    // =========================================================================
    // `equal_rule_up_to_renaming` (Rule.hs:1065-1077).  Mirrors HS:
    //
    //   equalRuleUpToRenaming r1 r2 = reader $ \hnd ->
    //     case eqs of
    //       Nothing   -> False
    //       Just eqs' -> (rn1 == rn2) && any isRenamingPerRule (unifs eqs' hnd)
    //
    // Pin both ends of the predicate: a positive (two rules differing only
    // in variable names) and a negative (structurally different).
    // =========================================================================
    /// Locate the Maude binary (`MAUDE_PATH` env override, else the common
    /// install paths).  `None` skips the Maude-backed tests below.
    fn maude_bin_path() -> Option<String> {
        std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        })
    }

    fn maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
        tamarin_term::maude_proc::MaudeHandle::start(
            &maude_bin_path()?, tamarin_term::maude_sig::pair_maude_sig()).ok()
    }

    /// Build a rule `[ KU(a) ] --[ KU(pair(a, a)) ]-> [ KU(pair(a, a)) ]`
    /// (a constructor-shape rule with one var `a`).  Used to test
    /// `equal_rule_up_to_renaming` with two alpha-equivalent rules.
    fn ku_pair_rule_with_var(var_name: &str, idx: u64) -> IntrRuleAC {
        use tamarin_term::builtin::pair;
        use tamarin_term::lterm::{LSort, LVar};
        let a = var_term(LVar::new(var_name, LSort::Msg, idx));
        let p = pair(a.clone(), a.clone());
        Rule::new(
            IntrRuleACInfo::ConstrRule(b"_pair".to_vec()),
            vec![ku_fact(a.clone())],
            vec![ku_fact(p.clone())],
            vec![ku_fact(p)],
        )
    }

    /// Positive: two rules that differ ONLY in their bound variable's
    /// name (and possibly idx) must compare equal-up-to-renaming.
    ///
    /// HS: `unifyLNTerm` produces a renaming `[x.0 ~> y.7]`; its
    /// restriction to each rule's vars (each is the singleton `{x.0}`
    /// vs `{y.7}`) is a renaming, so `isRenamingPerRule` holds.
    #[test]
    fn equal_rule_up_to_renaming_alpha_equivalent_pair_rules() {
        let maude = match maude_handle() { Some(m) => m, None => return };
        let r1 = ku_pair_rule_with_var("x", 0);
        let r2 = ku_pair_rule_with_var("y", 7);
        assert!(equal_rule_up_to_renaming(&maude, &r1, &r2),
            "two rules differing only in their bound var's name+idx \
             must be equal-up-to-renaming.  HS: `unifyLNTerm` yields a \
             renaming `[x.0 ~> y.7]`, isRenaming on each rule's restricted \
             var set holds.  See Rule.hs:1065-1077.");
        // Symmetric: r2 vs r1.
        assert!(equal_rule_up_to_renaming(&maude, &r2, &r1),
            "equal_rule_up_to_renaming must be symmetric");
        // Reflexive: r1 vs r1.
        assert!(equal_rule_up_to_renaming(&maude, &r1, &r1),
            "equal_rule_up_to_renaming must be reflexive");
    }

    /// Negative: two rules with structurally different conclusions
    /// (different fact shapes) must NOT be equal-up-to-renaming.
    ///
    /// HS: `matchFacts` returns `Nothing` because tags differ → False.
    #[test]
    fn equal_rule_up_to_renaming_structurally_different_rules_diverge() {
        use tamarin_term::lterm::{LSort, LVar};
        let maude = match maude_handle() { Some(m) => m, None => return };
        let r1 = ku_pair_rule_with_var("x", 0);
        // r2 has a single KU premise but a DIFFERENT conclusion shape:
        // it concludes KU(x) (the variable directly) instead of
        // KU(pair(x, x)).  No renaming can make `KU(x)` == `KU(pair(x, x))`.
        let a = var_term(LVar::new("x", LSort::Msg, 0));
        let r2 = Rule::new(
            IntrRuleACInfo::ConstrRule(b"_pair".to_vec()),
            vec![ku_fact(a.clone())],
            vec![ku_fact(a.clone())],
            vec![ku_fact(a)],
        );
        assert!(!equal_rule_up_to_renaming(&maude, &r1, &r2),
            "rules with structurally distinct conclusions (KU(pair(x,x)) \
             vs KU(x)) cannot be equal-up-to-renaming — no unifier \
             matches `pair(x,x) =? x`.  HS: matchFacts builds the eqs, \
             unifyLNTerm fails or yields a non-renaming.");
        // Different info also makes them unequal even when terms match.
        let r3 = Rule::new(
            IntrRuleACInfo::ConstrRule(b"_OTHER".to_vec()),
            r1.premises.clone(),
            r1.conclusions.clone(),
            r1.actions.clone(),
        );
        assert!(!equal_rule_up_to_renaming(&maude, &r1, &r3),
            "differing info field (rule names) must short-circuit to False \
             — HS: `if r1.info /= r2.info then False else ...`");
    }

    // =========================================================================
    // `variants_intruder` (IntruderRules.hs:288-314).
    //
    // Pin: a `DestrRule subterm=False` rule whose argument terms have
    // Maude variants under the AC theory produces MORE than one variant.
    // =========================================================================

    /// `variants_intruder` on a constructor rule whose argument is a
    /// pair (i.e. has multiple Maude variants under AC) produces at
    /// least two variants — the identity variant plus at least one
    /// substitution that reorders / splits the pair structure.
    ///
    /// We don't assert an exact count because it is Maude-version
    /// dependent (and minor signature differences affect the variant
    /// enumeration), but `len() >= 1` is invariant.
    #[test]
    fn variants_intruder_emits_at_least_the_identity_variant() {
        let maude = match maude_handle() { Some(m) => m, None => return };
        // The pair-construction rule from the basic sig.  Apply
        // `variants_intruder` to it; Maude should produce at least the
        // identity variant.  More may appear depending on the
        // signature loaded.
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let cs = construction_rules(&sig);
        let pair_rule = cs.iter().find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule(name) => name == b"_pair",
            _ => false,
        }).expect("expected pair constructor rule");
        let variants = variants_intruder(&maude, false, pair_rule);
        assert!(!variants.is_empty(),
            "variants_intruder must emit at least one rule (the identity \
             variant if no Maude variants exist).  HS \
             `variantsIntruder` (IntruderRules.hs:288-314) wraps the \
             rule in a list-monad enumeration that includes the original \
             via the identity Maude variant.");
    }

    /// `destructionRules` short-circuits when the rhs is a closed term
    /// (no free vars) AND `diff=false` AND rhs has no Private symbol.
    /// This is the outer guard at IntruderRules.hs:129-157, see line 130 — the function
    /// returns [] before even starting the position walk.
    ///
    /// Pin this by constructing a CtxtStRule whose rhs is a public
    /// constant (no free vars).
    #[test]
    fn destruction_rules_returns_empty_for_closed_rhs_in_non_diff_mode() {
        use tamarin_term::lterm::{LSort, LVar, Name, NameId, NameTag, LNTerm};
        use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        use tamarin_term::builtin::{pair, senc};

        // Build: lhs = senc(x, pair($a, $b)), rhs = $a (pub const, no frees).
        // Position [1, 0] — into senc's arg 1 (the pair), then into pair's
        // arg 0 ($a).
        let x = LVar::new("x", LSort::Msg, 1);
        let pub_a = Name { tag: NameTag::Pub, id: NameId::new("a") };
        let pub_b = Name { tag: NameTag::Pub, id: NameId::new("b") };
        let pa: LNTerm = Term::Lit(Lit::Con(pub_a.clone()));
        let pb: LNTerm = Term::Lit(Lit::Con(pub_b));
        let lhs = senc(Term::Lit(Lit::Var(x)), pair(pa.clone(), pb));
        let rhs_st = StRhs { positions: vec![vec![1, 0]], term: pa };
        let rule = CtxtStRule::new(lhs, rhs_st);

        // diff=false, rhs has no free vars, rhs has no private symbol →
        // outer guard returns [].
        let out = destruction_rules(false, &rule);
        assert!(out.is_empty(),
            "diff=false + closed rhs (no frees, no private) must short-\
             circuit to empty.  Mirrors IntruderRules.hs:130 outer guard. \
             Got {} rules.", out.len());

        // BUT in diff mode, the guard is bypassed and we DO descend.
        let out_diff = destruction_rules(true, &rule);
        assert!(!out_diff.is_empty(),
            "diff=true must bypass the closed-rhs guard and emit destructors");
    }

    // =========================================================================
    // `dh_intruder_rules` (IntruderRules.hs:230-283 — definition above).
    //
    // The expected output for `dh_intruder_rules(false)` is exactly the
    // contents of `data/intruder_variants_dh.spthy`, which the HS
    // production pipeline embeds and parses (TheoryLoader.hs:746-759).
    // That file has:
    //   * 5 ConstrRules: `_exp` `_inv` `_DH_neutral` `_one` `_mult`
    //   * 45 `d_exp` (DestrRule "_exp")  destructor variants
    //   * 1  `d_inv` (DestrRule "_inv")  destructor variant
    //   = 51 rules total.
    //
    // We measured this directly:
    //   $ grep -c "^rule" data/intruder_variants_dh.spthy
    //   51
    //   $ grep -c "^rule (modulo AC) c_" data/intruder_variants_dh.spthy → 5
    //   $ grep -c "^rule (modulo AC) d_exp" data/intruder_variants_dh.spthy → 45
    //   $ grep -c "^rule (modulo AC) d_inv" data/intruder_variants_dh.spthy → 1
    //
    // The variants enumeration depends on Maude's narrowing
    // implementation; the exact count is Maude-version-sensitive.  We
    // assert structural invariants (constructor count, name shapes,
    // KU/KD wiring) and let a slightly-looser bound check the variants
    // count, deferring exact byte parity to the corpus probe.
    // =========================================================================

    fn dh_maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
        tamarin_term::maude_proc::MaudeHandle::start(
            &maude_bin_path()?, tamarin_term::maude_sig::dh_maude_sig()).ok()
    }

    fn bp_maude_handle() -> Option<tamarin_term::maude_proc::MaudeHandle> {
        tamarin_term::maude_proc::MaudeHandle::start(
            &maude_bin_path()?, tamarin_term::maude_sig::bp_maude_sig()).ok()
    }

    /// `bp_intruder_rules(false)` yields exactly 75 bilinear-pairing
    /// intruder rules (2 constructors `_pmult`/`_em` + the pmult- and
    /// em-destructor variant expansions), matching HS `bpIntruderRules
    /// False` on current Maude — the count the `variants` command emits
    /// for the BP block (75 of the 126 total = 51 DH + 75 BP).
    #[test]
    fn bp_intruder_rules_yields_75() {
        let maude = match bp_maude_handle() { Some(m) => m, None => return };
        let rules = bp_intruder_rules(false, &maude);
        assert_eq!(
            rules.len(),
            75,
            "bp_intruder_rules(false) must produce exactly 75 rules; got {}",
            rules.len()
        );
        // Sanity: the two construction rules are present and named.
        let constr_names: Vec<&[u8]> = rules
            .iter()
            .filter_map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => Some(n.as_slice()),
                _ => None,
            })
            .collect();
        assert!(constr_names.contains(&b"_pmult".as_slice()));
        assert!(constr_names.contains(&b"_em".as_slice()));
    }

    /// Helper: extract the bytestring name of a ConstrRule or DestrRule.
    fn rule_name(info: &IntrRuleACInfo) -> Option<&[u8]> {
        match info {
            IntrRuleACInfo::ConstrRule(n) => Some(n.as_slice()),
            IntrRuleACInfo::DestrRule(n, _, _, _) => Some(n.as_slice()),
            _ => None,
        }
    }

    /// `dh_intruder_rules(false)` returns the 5 hard-coded constructor
    /// rules (`_exp`, `_inv`, `_DH_neutral`, `_one`, `_mult`) plus a
    /// non-empty list of destructor variants.  The 5 ConstrRules are
    /// the immediately-known core; the variant count depends on Maude's
    /// narrowing enumeration but is at minimum 1 (the identity variant
    /// of `_exp` or `_inv` survives `applyFilters=True` filters when
    /// the variant has non-ground conclusions).
    ///
    /// HS reference: IntruderRules.hs:230-245.  The cached output at
    /// `data/intruder_variants_dh.spthy` shows the expected shape (5
    /// constr + 45 d_exp + 1 d_inv = 51 rules total).
    #[test]
    fn dh_intruder_rules_emits_five_constructors_and_some_destructors() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules = dh_intruder_rules(false, &maude);

        // 5 ConstrRules with the known names.
        let names: Vec<&[u8]> = rules.iter()
            .filter_map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => Some(n.as_slice()),
                _ => None,
            }).collect();
        assert_eq!(names.len(), 5,
            "expected exactly 5 ConstrRules (_exp/_inv/_DH_neutral/_one/_mult); \
             got: {:?}",
            names.iter().map(|n| String::from_utf8_lossy(n).to_string()).collect::<Vec<_>>()
        );
        // All constructor names start with `_` (HS pack "_" prefix).
        for n in &names {
            assert!(n.starts_with(b"_"),
                "constructor rule name must start with `_` (HS appends pack \"_\" — \
                 IntruderRules.hs:233-240); got {}",
                String::from_utf8_lossy(n));
        }
        // Specific names present.
        let name_strings: Vec<&[u8]> = names.to_vec();
        for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
            assert!(name_strings.contains(expected),
                "missing constructor rule named {}; got names {:?}",
                String::from_utf8_lossy(expected),
                name_strings.iter().map(|n| String::from_utf8_lossy(n).to_string())
                    .collect::<Vec<_>>());
        }

        // Destructor rules also present (variants of _exp and _inv).
        let destrs: Vec<&IntrRuleAC> = rules.iter()
            .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule(..)))
            .collect();
        assert!(!destrs.is_empty(),
            "expected at least one DestrRule variant (HS \
             `variantsIntruder (exp-destr|inv-destr)` produces several); \
             got 0 destructors out of {} total rules", rules.len());
        for d in &destrs {
            let n = rule_name(&d.info).expect("DestrRule has name");
            assert!(n.starts_with(b"_"),
                "destructor rule name must start with `_`; got {}",
                String::from_utf8_lossy(n));
        }

        // EXACT byte-faithful shape vs HS `dhIntruderRules False`
        // (data/intruder_variants_dh.spthy): 5 constr + 45 `d_exp` +
        // 1 `d_inv` = 51 rules.  The lone `d_inv` is the swap variant
        // `[KD(inv(x))] -> [KD(x)]`; the IDENTITY variants of the `_exp`
        // and `_inv` destructors (`KD(x)->KD(inv(x))`, `[KD(x),KU(y)]->
        // [KD(x^y)]`) MUST be dropped — Maude returns them as `x0 --> #N`
        // fresh-witness renamings which HS's `removeRenamings`
        // (Maude/Types.hs:123-127, see line 130) collapses to the empty subst, so the
        // `ruvariant /= ru` guard (IntruderRules.hs:288-314, see line 297) discards them.
        // A regression here (53 rules: +1 d_exp, +1 d_inv) means the
        // `remove_renamings` step in `variants_intruder` was lost.
        let (n_exp, n_inv) = destrs.iter().fold((0usize, 0usize), |(e, i), d| {
            let n = rule_name(&d.info).unwrap();
            let s = String::from_utf8_lossy(n);
            if s.contains("inv") { (e, i + 1) }
            else if s.contains("exp") { (e + 1, i) }
            else { (e, i) }
        });
        assert_eq!(rules.len(), 51,
            "dhIntruderRules must yield exactly 51 rules (5 constr + 45 d_exp \
             + 1 d_inv) byte-identically to HS; got {} (n_exp={}, n_inv={}). \
             53 indicates the dropped-identity-variant `remove_renamings` \
             step regressed.", rules.len(), n_exp, n_inv);
        assert_eq!(n_exp, 45, "expected exactly 45 d_exp destructors; got {}", n_exp);
        assert_eq!(n_inv, 1, "expected exactly 1 d_inv destructor (the swap \
             variant); got {} (2 means the identity variant KD(x)->KD(inv(x)) \
             leaked)", n_inv);
    }

    /// The 5 ConstrRules MUST have the HS-specified shape:
    /// - `_exp` premises: `[KU(x.0), KU(x.1)]`, conc: `KU(exp(x.0, x.1))`
    /// - `_inv` premises: `[KU(x.0)]`, conc: `KU(inv(x.0))`
    /// - `_DH_neutral` premises: `[]`, conc: `KU(DH_neutral)`
    /// - `_one` premises: `[]`, conc: `KU(one)`
    /// - `_mult` premises: `[KU(x.0), KU(x.1)]`, conc: `KU(x.0 * x.1)`
    ///
    /// HS: see expRule/invRule/multRule/oneRule/dhNeutralRule helpers at
    /// IntruderRules.hs:250-283 — each is `Rule mkInfo prems [concfact]
    /// (mkAction concfact) []` where `concfact = kudFact conc`.
    #[test]
    fn dh_intruder_rules_constructors_have_expected_shape() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules = dh_intruder_rules(false, &maude);
        let find = |name: &[u8]| -> &IntrRuleAC {
            rules.iter().find(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => n.as_slice() == name,
                _ => false,
            }).unwrap_or_else(|| panic!("no constructor rule named {}",
                String::from_utf8_lossy(name)))
        };

        // All constructor rules emit a single action equal to the conclusion
        // (HS: `mkAction = return`, so `acts = [concfact]`).
        for name in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
            let r = find(name);
            assert_eq!(r.conclusions.len(), 1, "{}: must have 1 conclusion",
                String::from_utf8_lossy(name));
            assert_eq!(r.actions.len(), 1, "{}: HS `return concfact` ⇒ 1 action",
                String::from_utf8_lossy(name));
            assert_eq!(r.actions[0], r.conclusions[0],
                "{}: action must equal conclusion (HS `mkAction concfact` ⇒ \
                 `[concfact]`)", String::from_utf8_lossy(name));
            // No `new_vars`.
            assert!(r.new_vars.is_empty(),
                "{}: constructors have empty new_vars (HS Rule mkInfo prems concs acts [])",
                String::from_utf8_lossy(name));
            // Every fact tag is KU (HS `kudFact = kuFact`).
            for f in r.premises.iter().chain(&r.conclusions).chain(&r.actions) {
                assert_eq!(f.tag, FactTag::Ku,
                    "{}: all facts must be KU (HS `kudFact = kuFact`)",
                    String::from_utf8_lossy(name));
            }
        }

        // Premise counts match HS shape.
        assert_eq!(find(b"_exp").premises.len(), 2, "_exp: 2 KU premises (HS expRule)");
        assert_eq!(find(b"_inv").premises.len(), 1, "_inv: 1 KU premise (HS invRule)");
        assert_eq!(find(b"_DH_neutral").premises.len(), 0, "_DH_neutral: 0 premises");
        assert_eq!(find(b"_one").premises.len(), 0, "_one: 0 premises");
        assert_eq!(find(b"_mult").premises.len(), 2, "_mult: 2 KU premises");
    }

    /// `dh_intruder_rules(true)` (diff mode) skips the subsumption phase
    /// of `minimizeIntruderRules` — see IntruderRules.hs:188-190:
    /// ```haskell
    /// minimizeIntruderRules diff rules =
    ///     filter (not . isDoublePremiseRule)
    ///        $ if diff then rules else go [] rules
    /// ```
    ///
    /// Concretely: diff=true should produce AT LEAST as many rules as
    /// diff=false (the diff filter is weaker — only the double-premise
    /// filter still applies).
    #[test]
    fn dh_intruder_rules_diff_mode_is_at_least_as_large() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules_no_diff = dh_intruder_rules(false, &maude);
        let rules_diff = dh_intruder_rules(true, &maude);
        assert!(rules_diff.len() >= rules_no_diff.len(),
            "diff=true skips the subsumption filter (HS IntruderRules.hs:188-190) \
             — must produce >= rules.  Got diff={}, no-diff={}",
            rules_diff.len(), rules_no_diff.len());
        // The 5 constructor rules must still be present in diff mode.
        let constr_names: Vec<&[u8]> = rules_diff.iter()
            .filter_map(|r| match &r.info {
                IntrRuleACInfo::ConstrRule(n) => Some(n.as_slice()),
                _ => None,
            }).collect();
        for expected in &[&b"_exp"[..], b"_inv", b"_DH_neutral", b"_one", b"_mult"] {
            assert!(constr_names.contains(expected),
                "diff-mode dh_intruder_rules missing constructor named {}",
                String::from_utf8_lossy(expected));
        }
    }

    /// Destructor rules in `dh_intruder_rules` are KD-rules: their
    /// first premise (the term-being-deconstructed) has KD tag, the
    /// conclusion is KD, and actions are empty (HS `mkAction = const []`
    /// for destructors).
    #[test]
    fn dh_intruder_rules_destructors_have_kd_shape() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules = dh_intruder_rules(false, &maude);
        let destrs: Vec<&IntrRuleAC> = rules.iter()
            .filter(|r| matches!(r.info, IntrRuleACInfo::DestrRule(..)))
            .collect();
        assert!(!destrs.is_empty(), "expected at least one destructor variant");
        for d in &destrs {
            assert!(!d.premises.is_empty(),
                "destructor must have premises; got rule with 0 prems");
            assert_eq!(d.premises[0].tag, FactTag::Kd,
                "destructor's first premise must be KD (HS `kudFact = kdFact`)");
            assert_eq!(d.conclusions.len(), 1,
                "destructor must have exactly 1 KD conclusion");
            assert_eq!(d.conclusions[0].tag, FactTag::Kd,
                "destructor conclusion must be KD");
            assert!(d.actions.is_empty(),
                "destructor actions must be empty (HS `mkAction = const []`)");
            assert!(d.new_vars.is_empty(),
                "destructor new_vars must be empty");
        }
    }

    /// Every rule produced by `dh_intruder_rules` has a name starting
    /// with `_` — the HS `append (pack "_") ...SymString` prefix.  This
    /// is how HS distinguishes intruder rules from user-defined rules
    /// with the same name (e.g. user-defined `exp` vs intruder `_exp`).
    /// Mirrors IntruderRules.hs:233-244, 182, etc.
    #[test]
    fn dh_intruder_rules_all_names_have_underscore_prefix() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules = dh_intruder_rules(false, &maude);
        for r in &rules {
            let n = rule_name(&r.info).expect("DH intruder rule must have a name");
            assert!(n.starts_with(b"_"),
                "DH intruder rule name must start with `_` (HS `append (pack \"_\") \
                 ...SymString`); got {}.  This prefix is how HS distinguishes \
                 the intruder `_exp` from a user-defined `exp` function.",
                String::from_utf8_lossy(n));
        }
    }

    /// `norm_rule` is the identity on a DH constructor rule whose
    /// terms are already in normal form (KU(x.0), KU(x.1), KU(exp(x.0, x.1))).
    /// Mirrors HS `normRule'` (IntruderRules.hs:317-321) — for already-normal
    /// terms, `norm'` returns the input.
    #[test]
    fn norm_rule_identity_on_already_normal_rule() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules = dh_intruder_rules(false, &maude);
        let exp_constr = rules.iter().find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule(n) => n.as_slice() == b"_exp",
            _ => false,
        }).expect("_exp constructor rule must be present");
        let normalised = norm_rule(&maude, exp_constr);
        assert_eq!(&normalised, exp_constr,
            "norm_rule must be the identity on a rule whose terms are \
             already in normal form (`x.0`, `x.1`, `exp(x.0, x.1)` — no \
             reducible top-level shapes).  HS: `normRule' = mapTerms norm'`, \
             and `norm' (x.0) = x.0`.");
    }

    /// `dh_intruder_rules` rule list is well-formed: every rule has at
    /// least one conclusion, every fact's terms is non-empty, etc.
    #[test]
    fn dh_intruder_rules_well_formed() {
        let maude = match dh_maude_handle() { Some(m) => m, None => return };
        let rules = dh_intruder_rules(false, &maude);
        assert!(!rules.is_empty(), "dh_intruder_rules must produce > 0 rules");
        for r in &rules {
            assert!(!r.conclusions.is_empty(),
                "every dh intruder rule must have at least one conclusion");
            for f in r.premises.iter().chain(&r.conclusions).chain(&r.actions) {
                assert!(!f.terms.is_empty(),
                    "every fact in a dh intruder rule must have non-empty terms");
            }
        }
    }
}
