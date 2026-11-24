// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Theory.Tools.IntruderRules` from
//! `lib/theory/src/Theory/Tools/IntruderRules.hs` — covers the
//! always-included "special" intruder rules, the DH/XOR/multiset
//! variant generators (`dh_intruder_rules`, `xor_intruder_rules`,
//! `multiset_intruder_rules`), the constructor generators
//! (`subterm_constructor_rules` / `construction_rules`), and the
//! narrowing-based destruction-rule generators for user-defined
//! function symbols (`destruction_rules_no_eq` / `destruction_rules_ac`,
//! all built on the `variants_intruder` pipeline that drives Maude).
//! The production BP intruder rules are loaded from the cached file via
//! `intruder_variants.rs`.
//!
//! Diff mode is not ported, so every generator is HS's with `diff = False`:
//! no `iequality` rule, the closed-rhs and conclusion-frees filters always
//! apply, and minimisation always uses subset subsumption.

use tamarin_term::function_symbols::FunSym;
use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::vterm::var_term;

use crate::fact::{fresh_fact, in_fact, k_log_fact, kd_fact, ku_fact, out_fact, FactTag, LNFact};
use crate::rule::{
    equal_duplicate_rule_up_to_renaming, equal_rule_up_to_renaming,
    equal_subset_rule_up_to_renaming, IntrRuleAC, IntrRuleACInfo, Rule,
};

/// `specialIntruderRules False` returns the intruder rules that are
/// included independently of the message theory:
///
/// - `coerce` — `[ KD(x) ] --[ KU(x) ]-> [ KU(x) ]`
/// - `pub` — `[] --[ KU($x) ]-> [ KU($x) ]`
/// - `gen_fresh` — `[ Fr(~x) ] --[ KU(~x) ]-> [ KU(~x) ]`
/// - `isend` — `[ KU(x) ] --[ K(x) ]-> [ In(x) ]`
/// - `irecv` — `[ Out(x) ] --> [ KD(x) ]`
pub fn special_intruder_rules() -> Vec<IntrRuleAC> {
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

    vec![
        ku_rule(
            IntrRuleACInfo::Coerce,
            vec![kd_fact(x.clone())],
            x.clone(),
            vec![],
        ),
        ku_rule(
            IntrRuleACInfo::PubConstr,
            vec![],
            x_pub.clone(),
            vec![x_pub],
        ),
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
    ]
}

/// `destructionRules False st` — direct port of
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
pub fn destruction_rules(rule: &tamarin_term::subterm_rule::CtxtStRule) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{AcFctSym, AcSym, NoEqSym, Privacy};
    use tamarin_term::lterm::frees;
    use tamarin_term::positions::Position;
    use tamarin_term::term::Term;

    let lhs = &rule.lhs;
    let rhs = &rule.rhs.term;
    let positions: &[Position] = &rule.rhs.positions;
    if positions.is_empty() {
        return Vec::new();
    }

    // `containsPrivate` mirror (shared `tamarin_term::lterm::contains_private`).
    if frees(rhs).is_empty() && !tamarin_term::lterm::contains_private(rhs) {
        return Vec::new();
    }

    // Process the first position; recurse on the rest of `positions`.
    if positions.len() > 1 {
        let mut out = destruction_rules(&tamarin_term::subterm_rule::CtxtStRule {
            lhs: lhs.clone(),
            rhs: tamarin_term::subterm_rule::StRhs {
                positions: vec![positions[0].clone()],
                term: rhs.clone(),
            },
        });
        out.extend(destruction_rules(&tamarin_term::subterm_rule::CtxtStRule {
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
    let mut funs_acc: Vec<FunSym> = Vec::new();
    let mut posname = String::new();
    let pos_iter: Vec<i64> = pos.clone();
    // `rhs` is loop-invariant, so compute `frees(rhs).is_empty()` once.
    let rhs_frees_empty = frees(rhs).is_empty();
    for (step_idx, &i) in pos_iter.iter().enumerate() {
        // A descent step applies at public NoEq and public user-AC
        // applications alike (IntruderRules.hs `go` NoEq + ACfct cases).
        // Everything else stops the walk: a private symbol, any other
        // function symbol, or a leaf hit with positions still remaining
        // (invalid).
        let (fun, args) = match &t {
            Term::App(f, args)
                if matches!(
                    f,
                    FunSym::NoEq(NoEqSym {
                        privacy: Privacy::Public,
                        ..
                    }) | FunSym::Ac(AcSym::AcFct(AcFctSym {
                        privacy: Privacy::Public,
                        ..
                    }))
                ) =>
            {
                (*f, args.clone())
            }
            _ => return out,
        };
        // Haskell `destructionRules` pattern #2 (IntruderRules.hs `go`):
        //     go _ (viewTerm -> FApp _ _) (_:[]) _ _ | (frees rhs /= []) = []
        // At the LAST position step, if the current term is an
        // FApp AND rhs has free vars, return [] — neither emit
        // nor recurse.  Current `t` is necessarily FApp here.
        // Without this, Rust emits extra rules at deep positions like
        // d_0_0_0_prefix_enc_pair or d_1_0_prefix_enc — see
        // denning_sacco_symmetric_cbc which has rule
        // `prefix(enc(<X,Y>,k)) = enc(X,k)` (positions [0,0,0]
        // and [0,1]); at the LAST step into pair(X,Y) and
        // enc(X,Y), Haskell skips.
        if pos_iter.len() == step_idx + 1 && !rhs_frees_empty {
            return out;
        }
        // Build uprems' = uprems ++ siblings in place: the pre-sibling
        // `uprems` value is never read again (the next iteration uses
        // the extended one).
        for (j, a) in args.iter().enumerate() {
            if (j as i64) != i {
                uprems.push(a.clone());
            }
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
        // funs' = funs ++ [fun] — the symbol chain walked so far,
        // carried both in the rule name and in the DestrRule metadata.
        funs_acc.push(fun);
        if cond_emit {
            // `name i pd n fun`: `_<i><pd>` ++ concatMap ("_" ++
            // showFunSymName) funs'.
            let mut name = next_posname.as_bytes().to_vec();
            for f in &funs_acc {
                name.push(b'_');
                name.extend_from_slice(show_fun_sym_name(f).as_bytes());
            }
            // `rhs == lhs `atPos` pos`.  Use the AC-aware `at_pos`
            // (Positions.hs) so paths traversing an AC operator index
            // exactly as Haskell.  `pos` is the (valid) walked LHS
            // position, so the lookup is `Some`; on the impossible
            // invalid case fall back to `lhs`, keeping the boolean
            // unchanged rather than panicking.
            let at = tamarin_term::positions::at_pos(lhs, pos).unwrap_or_else(|| lhs.clone());
            let info = IntrRuleACInfo::DestrRule {
                name,
                remaining_applications: -1,
                rhs_is_proper_subterm: rhs == &at,
                rhs_is_constant: rhs_frees_empty,
                funs: funs_acc.clone(),
            };
            let mut prems = vec![kd_fact(t_new.clone())];
            for u in &uprems {
                prems.push(ku_fact(u.clone()));
            }
            out.push(Rule::new(info, prems, vec![kd_fact(rhs.clone())], vec![]));
        }
        // Walk down into argument `i`.
        posname = next_posname;
        t = t_new;
    }
    out
}

/// `showFunSymName` (Term/Term.hs) — the plain-name rendering used for
/// intruder rule names and case names: user symbols print their own name; the
/// builtin AC/C operators print their `*SymString` names.  Note `Union`
/// renders as HS's `munSymString` ("mun"), NOT `unionSymString` ("union") —
/// the two are distinct upstream, and `multiset_intruder_rules` names its
/// rules from the latter.
///
/// Every arm reads the name out of `tamarin_term::function_symbols`, the one
/// source of truth these names have: the builtin operators from the same
/// `*SymString` constants HS's arms name, `List` from `LIST_SYM_STRING`
/// (HS spells that one arm's literal inline — it has no `listSymString`).
/// The names reach intruder-rule names, `close_rule.rs` case names and
/// `reduction.rs` term rendering, so a literal spelled here could silently
/// rename cases when a constant changes.
pub fn show_fun_sym_name(f: &FunSym) -> std::borrow::Cow<'static, str> {
    use tamarin_term::function_symbols::{
        AcSym, CSym, EMAP_SYM_STRING, LIST_SYM_STRING, MULT_SYM_STRING, MUN_SYM_STRING,
        NAT_PLUS_SYM_STRING, XOR_SYM_STRING,
    };
    // Every name is `&'static [u8]`, so the lossy conversion is already a
    // `Cow<'static, str>` — borrowed, with no allocation, whenever the name is
    // valid UTF-8 (the six constants below are ASCII, so always).
    match f {
        FunSym::NoEq(s) => String::from_utf8_lossy(s.name),
        FunSym::Ac(AcSym::AcFct(s)) => String::from_utf8_lossy(s.name),
        FunSym::Ac(AcSym::Union) => String::from_utf8_lossy(MUN_SYM_STRING),
        FunSym::Ac(AcSym::Mult) => String::from_utf8_lossy(MULT_SYM_STRING),
        FunSym::Ac(AcSym::Xor) => String::from_utf8_lossy(XOR_SYM_STRING),
        FunSym::Ac(AcSym::NatPlus) => String::from_utf8_lossy(NAT_PLUS_SYM_STRING),
        FunSym::C(CSym::EMap) => String::from_utf8_lossy(EMAP_SYM_STRING),
        FunSym::List => String::from_utf8_lossy(LIST_SYM_STRING),
    }
}

/// `subtermConstructorRules` — direct port:
///
/// ```haskell
/// subtermConstructorRules :: Bool -> MaudeHandle -> MaudeSig -> [IntrRuleAC]
/// subtermConstructorRules diff hnd maudeSig =
///     minimizeIntruderRules diff hnd
///       (constructionRules (userDefinedSTFunSyms maudeSig)
///          ++ privateConstructorRules (S.toList $ stRules maudeSig))
/// ```
///
/// CONSTRUCTOR rules only: the per-symbol construction rules for the
/// user-defined subterm signature plus the derivable-private-constant
/// constructors.  The destruction rules for user-defined symbols are
/// generated separately by the narrowing-based [`destruction_rules_no_eq`]
/// / [`destruction_rules_ac`].
pub fn subterm_constructor_rules(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<IntrRuleAC> {
    let mut out = construction_rules(&sig.user_defined_st_fun_syms());
    out.extend(private_constructor_rules(&sig.st_rules));
    minimize_intruder_rules(maude, out)
}

/// `privateConstructorRules` — port of IntruderRules.hs.
///
/// Returns the constructor rules for private constants that are
/// consequences of the subterm rewrite rules in `st_rules`.  A private
/// 0-arity constructor is "derivable" when there exists an equation whose
/// RHS is that constant and whose LHS only mentions public functions (or
/// already-derivable private constants) — computed by the
/// `derivable_private_constants` fixpoint.  For each such constant we
/// emit:
///
/// ```text
///   [] --[ KU(s) ]-> [ KU(s) ]    (ConstrRule "_<s>" f)
/// ```
///
/// HS:
/// ```haskell
/// privateConstructorRules rules = map createRule $
///     derivablePrivateConstants (privateConstructorEquations rules) []
///   where createRule f@(NoEq (s, _)) = Rule (ConstrRule (append (pack "_") s) f) [] [concfact] [concfact] []
///           where m         = fApp f []
///                 concfact  = kuFact m
/// ```
fn private_constructor_rules(
    st_rules: &std::collections::BTreeSet<tamarin_term::subterm_rule::CtxtStRule>,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{NoEqSym, Privacy};
    use tamarin_term::lterm::contains_no_private_except;
    use tamarin_term::term::Term;

    // `privateConstructorEquations` (IntruderRules.hs): all equations
    // whose RHS is a 0-arity Private constructor, paired with that
    // constructor's function symbol.
    let eqs: Vec<(&LNTerm, FunSym)> = st_rules
        .iter()
        .filter_map(|r| match &r.rhs.term {
            Term::App(
                f @ FunSym::NoEq(NoEqSym {
                    arity: 0,
                    privacy: Privacy::Private,
                    ..
                }),
                _,
            ) => Some((&r.lhs, *f)),
            _ => None,
        })
        .collect();

    // `derivablePrivateConstants eqs except` (IntruderRules.hs):
    // fixpoint adding the RHS-constants of equations whose LHS only
    // contains public functions or already-derivable private constants.
    // The exemption test (`containsNoPrivateExcept`, LTerm.hs) is on
    // whole `FunSym`s, not names.
    fn derivable_private_constants(
        mut eqs: Vec<(&LNTerm, FunSym)>,
        mut except: Vec<FunSym>,
    ) -> Vec<FunSym> {
        loop {
            // Both HS filters (drop + collect-syms) use the OLD `except`,
            // so snapshot it before augmenting.
            let prev = except.clone();
            let any_derivable = eqs
                .iter()
                .any(|(l, _)| contains_no_private_except(&prev, l));
            if !any_derivable {
                return except;
            }
            // `except ++ map snd (filter (containsNoPrivateExcept except . fst) eqs)`.
            for (l, f) in eqs.iter() {
                if contains_no_private_except(&prev, l) {
                    except.push(*f);
                }
            }
            // `filter (not . containsNoPrivateExcept except . fst) eqs`.
            eqs.retain(|(l, _)| !contains_no_private_except(&prev, l));
        }
    }

    derivable_private_constants(eqs, Vec::new())
        .into_iter()
        .map(|f| {
            // HS `createRule f@(NoEq (s, _))` — the equations above only
            // ever yield NoEq symbols.
            let name = match f {
                FunSym::NoEq(s) => s.name,
                _ => unreachable!("privateConstructorRules: non-NoEq private constant"),
            };
            let m: LNTerm = Term::App(f, Vec::<LNTerm>::new().into());
            let concfact = ku_fact(m);
            Rule::new(
                IntrRuleACInfo::ConstrRule {
                    name: underscore_prefixed(name),
                    fun: f,
                },
                vec![],
                vec![concfact.clone()],
                vec![concfact],
            )
        })
        .collect()
}

/// HS `minimizeIntruderRules` (IntruderRules.hs):
///
/// ```haskell
/// minimizeIntruderRules diff hnd rules =
///     filter (not . isDoublePremiseRule) $ go [] rules
///   where
///     go checked [] = reverse checked
///     go checked (r:unchecked) = go checked' unchecked
///       where
///         checked' = if any (\r' -> (equalDuplicateRuleUpToRenaming r r' `runReader` hnd)
///                                || ((not diff) && equalSubsetRuleUpToRenaming r r' `runReader` hnd))
///                           (checked++unchecked)
///                    then checked
///                    else r:checked
/// ```
///
/// Walking by index, rule `i`'s peers are the kept rules before it and every
/// rule after it; keeping the survivors in index order is `reverse checked`.
/// Every generator feeding this pass emits rules with one conclusion, which
/// HS's `head co` in `equalSubsetRuleUpToRenaming` needs.
fn minimize_intruder_rules(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    rules: Vec<IntrRuleAC>,
) -> Vec<IntrRuleAC> {
    debug_assert!(rules.iter().all(|r| !r.conclusions.is_empty()));
    let mut kept: Vec<bool> = vec![false; rules.len()];
    for (i, r) in rules.iter().enumerate() {
        let dropped = rules.iter().enumerate().any(|(j, peer)| {
            (j > i || (j < i && kept[j]))
                && (equal_duplicate_rule_up_to_renaming(maude, r, peer)
                    || equal_subset_rule_up_to_renaming(maude, r, peer))
        });
        kept[i] = !dropped;
    }
    rules
        .into_iter()
        .zip(kept)
        .filter(|(r, keep)| *keep && !is_double_premise_rule(r))
        .map(|(r, _)| r)
        .collect()
}

/// `isDoublePremiseRule` (IntruderRules.hs).
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
                if first.tag != FactTag::Kd {
                    return false;
                }
                let t = match first.terms.first() {
                    Some(t) => t,
                    None => return false,
                };
                (t, rest)
            }
            None => return false,
        };
    // Conclusions must be ground.
    let frees_concs = r
        .conclusions
        .iter()
        .flat_map(|f| f.terms.iter())
        .any(|t| !tamarin_term::lterm::frees(t).is_empty());
    if frees_concs {
        return false;
    }
    // Reject if any term (KD-premise or any prems-term) contains a private
    // symbol (shared `tamarin_term::lterm::contains_private`).
    if tamarin_term::lterm::contains_private(kd_fact_term) {
        return false;
    }
    for f in r.premises.iter() {
        for t in f.terms.iter() {
            if tamarin_term::lterm::contains_private(t) {
                return false;
            }
        }
    }
    // KD-premise term must be a msg-var.
    if !is_msg_var(kd_fact_term) {
        return false;
    }
    // KU(kd_fact_term) must appear among the remaining premises.
    let ku_t = crate::fact::ku_fact(kd_fact_term.clone());
    rest_prems.iter().any(|f| f == &ku_t)
}

/// `multisetIntruderRules` — port of Haskell's
/// `Theory.Tools.IntruderRules.multisetIntruderRules`
/// (`lib/theory/src/Theory/Tools/IntruderRules.hs`, with
/// `mkDUnionRule` and `mkCUnionRule`):
///
/// ```haskell
/// multisetIntruderRules = [mkDUnionRule [x_var, y_var] x_var,
///                          mkCUnionRule [x_var, y_var]]
///   where x_var = varTerm (LVar "x"  LSortMsg   0)
///         y_var = varTerm (LVar "y"  LSortMsg   0)
///
/// mkDUnionRule t_prems t_conc =
///     Rule (DestrRule (append (pack "_") unionSymString) 0 True False [AC Union])
///          [kdFact $ fAppAC Union t_prems]
///          [kdFact t_conc] [] []
///
/// mkCUnionRule terms =
///     Rule (ConstrRule (append (pack "_") unionSymString) (AC Union))
///          (map kuFact terms)
///          [kuFact $ fAppAC Union terms] [kuFact $ fAppAC Union terms] []
/// ```
///
/// Added to the intruder rule pool when `enableMSet` (Main/TheoryLoader.hs).
/// Note budget=0 (NOT -1) — HS computes budget=0 at definition time, so
/// we mirror that here.
pub fn multiset_intruder_rules() -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{AcSym, UNION_SYM_STRING};
    use tamarin_term::term::Term;
    let x_var = var_term(LVar::new("x", LSort::Msg, 0));
    let y_var = var_term(LVar::new("y", LSort::Msg, 0));
    let xy_union = Term::App(
        FunSym::Ac(AcSym::Union),
        vec![x_var.clone(), y_var.clone()].into(),
    );
    let name = underscore_prefixed(UNION_SYM_STRING);
    let d_rule = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: 0,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![FunSym::Ac(AcSym::Union)],
        },
        vec![kd_fact(xy_union.clone())],
        vec![kd_fact(x_var.clone())],
        vec![],
    );
    let c_rule = {
        let mut r = Rule::new(
            IntrRuleACInfo::ConstrRule {
                name,
                fun: FunSym::Ac(AcSym::Union),
            },
            vec![ku_fact(x_var.clone()), ku_fact(y_var)],
            vec![ku_fact(xy_union.clone())],
            vec![ku_fact(xy_union)],
        );
        r.new_vars = vec![];
        r
    };
    vec![d_rule, c_rule]
}

/// `xorIntruderRules` — port of HS `Theory.Tools.IntruderRules.xorIntruderRules`:
///
/// ```haskell
/// xorIntruderRules = [
///     mkDXorRule [x, y] [y, z] (x ⊕ z),          -- KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z)
///     mkDXorRuleSubterm [x, y] [y]    x,         -- KD(x⊕y) ∧ KU(y)   → KD(x)
///     mkCXorRule x y (x ⊕ y),                    -- KU(x)   ∧ KU(y)   → KU(x⊕y)
///     zeroConstructor                            -- KU(zero)
/// ]
/// ```
///
/// The two destructor rules let the adversary recover `x` (or `x⊕z`) when
/// they know `x⊕y` (as KD, e.g. from an `Out(x⊕y)`) and can compose `y`
/// (or `y⊕z`) themselves.  The constructor rule lets them XOR two known
/// values together.  `zeroConstructor` makes `zero` always known.
///
/// `mkDXorRule` (the 2-composed-premise rule) carries subterm=FALSE —
/// `x⊕z` is not a syntactic subterm of `x⊕y`; only `mkDXorRuleSubterm`
/// (the `[x,y] [y] → x` rule) is a true subterm destructor.
///
/// Wired in `ProofContext::with_options` when
/// `sig.enable_xor`, after `special_intruder_rules` and before the
/// DH/BP intruder variants — mirroring HS `addMessageDeductionRule
/// Variants` (TheoryLoader.hs).
pub fn xor_intruder_rules() -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{zero_sym, AcSym, XOR_SYM_STRING, ZERO_SYM_STRING};
    use tamarin_term::term::Term;
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let y = var_term(LVar::new("y", LSort::Msg, 0));
    let z = var_term(LVar::new("z", LSort::Msg, 0));
    // `Term::App(Ac(Xor), [a, b])`.  Constructed via the AC-flatten/sort
    // smart constructor so the operand order matches HS's `fAppAC` (sorted
    // by Ord).
    let xor2 =
        |a: LNTerm, b: LNTerm| -> LNTerm { tamarin_term::term::f_app_ac(AcSym::Xor, vec![a, b]) };
    let x_xor_y = xor2(x.clone(), y.clone());
    let x_xor_z = xor2(x.clone(), z.clone());
    let y_xor_z = xor2(y.clone(), z.clone());
    let name = underscore_prefixed(XOR_SYM_STRING);

    // Rule 1: KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z)
    // HS: mkDXorRule [x, y] [y, z] x_xor_z — subterm=False.
    let d_rule_1 = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: 1,
            rhs_is_proper_subterm: false,
            rhs_is_constant: false,
            funs: vec![FunSym::Ac(AcSym::Xor)],
        },
        vec![kd_fact(x_xor_y.clone()), ku_fact(y_xor_z)],
        vec![kd_fact(x_xor_z)],
        vec![],
    );
    // Rule 2: KD(x⊕y) ∧ KU(y) → KD(x)
    // HS: mkDXorRuleSubterm [x, y] [y] x_var — subterm=True; note
    // `fAppAC Xor [y]` is a singleton AC that the smart constructor
    // strips to just `y`.
    let d_rule_2 = Rule::new(
        IntrRuleACInfo::DestrRule {
            name: name.clone(),
            remaining_applications: 1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: false,
            funs: vec![FunSym::Ac(AcSym::Xor)],
        },
        vec![kd_fact(x_xor_y.clone()), ku_fact(y.clone())],
        vec![kd_fact(x.clone())],
        vec![],
    );
    // Rule 3: KU(x) ∧ KU(y) → KU(x⊕y)
    // HS: mkCXorRule x y x_xor_y — constructor, action emits `KU(x⊕y)`.
    let c_rule = {
        let mut r = Rule::new(
            IntrRuleACInfo::ConstrRule {
                name: name.clone(),
                fun: FunSym::Ac(AcSym::Xor),
            },
            vec![ku_fact(x), ku_fact(y)],
            vec![ku_fact(x_xor_y.clone())],
            vec![ku_fact(x_xor_y)],
        );
        r.new_vars = vec![];
        r
    };
    // Rule 4: zero constructor (HS `zeroConstructor`,
    // `ConstrRule "_zero" (NoEq zeroSym)`).
    let zero_term: LNTerm = Term::App(FunSym::NoEq(zero_sym()), Vec::<LNTerm>::new().into());
    let zero_name = underscore_prefixed(ZERO_SYM_STRING);
    let zero_rule = {
        let mut r = Rule::new(
            IntrRuleACInfo::ConstrRule {
                name: zero_name,
                fun: FunSym::NoEq(zero_sym()),
            },
            vec![],
            vec![ku_fact(zero_term.clone())],
            vec![ku_fact(zero_term)],
        );
        r.new_vars = vec![];
        r
    };
    vec![d_rule_1, d_rule_2, c_rule, zero_rule]
}

/// `constructionRules fSig` — port of IntruderRules.hs:
///
/// ```haskell
/// constructionRules :: UserDefinedSig -> [IntrRuleAC]
/// constructionRules fSig =
///     [ createRuleNoEq s f k | NoEqUser f@(s,(k,Public,Constructor,_)) <- S.toList fSig ] ++
///     [ createRuleAC s f | ACfctUser f@(s,(Public,Constructor,_)) <- S.toList fSig ]
/// ```
///
/// For every public NoEq constructor `f/k`, a KU rule
/// `[KU(x_0), ..., KU(x_{k-1})] --[KU(f(..))]-> [KU(f(..))]`; for every
/// public AC constructor `f`, the 2-premise rule
/// `[KU(x_0), KU(x_1)] --[KU(f(x_0, x_1))]-> [KU(f(x_0, x_1))]` with the
/// term built via the AC smart constructor.  The two list comprehensions
/// run separately over `fSig`, so ALL NoEq rules precede ALL AC rules.
///
/// `fSig` is the USER-DEFINED subterm signature (`userDefinedSTFunSyms`)
/// — it excludes the DH / BP / MSet / Nat / Xor builtins, whose intruder
/// constructors come from the cached `intruder_variants_{dh,bp}.spthy`
/// files / the builtin generators instead.
pub fn construction_rules(
    f_sig: &tamarin_term::function_symbols::UserDefinedSig,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{AcSym, Constructability, Privacy, UserDefinedSym};
    use tamarin_term::term::{f_app_ac, f_app_no_eq};

    // `vars = take k [ varTerm (LVar "x" LSortMsg i) | i <- [0..] ]`.
    let msg_vars = |k: usize| -> Vec<LNTerm> {
        (0..k)
            .map(|i| var_term(LVar::new("x", LSort::Msg, i as u64)))
            .collect()
    };
    // Shared body of `createRuleNoEq` / `createRuleAC`:
    // `(map kuFact vars) --[kuFact m]-> [kuFact m]`, named after the symbol.
    let ku_constr_rule = |name: &[u8], fun: FunSym, prems: Vec<LNFact>, m: LNTerm| {
        let concfact = ku_fact(m);
        Rule::new(
            IntrRuleACInfo::ConstrRule {
                name: underscore_prefixed(name),
                fun,
            },
            prems,
            vec![concfact.clone()],
            vec![concfact],
        )
    };

    let mut out = Vec::new();
    // `createRuleNoEq` comprehension — public NoEq constructors.
    for u in f_sig {
        let s = match u {
            UserDefinedSym::NoEqUser(s) => s,
            _ => continue,
        };
        if s.privacy != Privacy::Public || s.constructability != Constructability::Constructor {
            continue;
        }
        let xs = msg_vars(s.arity);
        let prems: Vec<LNFact> = xs.iter().cloned().map(ku_fact).collect();
        out.push(ku_constr_rule(
            s.name,
            FunSym::NoEq(*s),
            prems,
            f_app_no_eq(*s, xs),
        ));
    }
    // `createRuleAC` comprehension — public AC constructors (arity 2).
    for u in f_sig {
        let s = match u {
            UserDefinedSym::AcFctUser(s) => s,
            _ => continue,
        };
        if s.privacy != Privacy::Public || s.constructability != Constructability::Constructor {
            continue;
        }
        let xs = msg_vars(2);
        let prems: Vec<LNFact> = xs.iter().cloned().map(ku_fact).collect();
        out.push(ku_constr_rule(
            s.name,
            FunSym::Ac(AcSym::AcFct(*s)),
            prems,
            f_app_ac(AcSym::AcFct(*s), xs),
        ));
    }
    out
}

// =============================================================================
// User-defined destruction rules — port of
// `Theory.Tools.IntruderRules.destructionRulesNoEq` / `destructionRulesAC` /
// `decomposeNotSubterm` / `maxApplications`.
//
// For every public user-defined function symbol a generic destructor
//
//   [ KD(x_{k-1}), KU(x_0), .., KU(x_{k-2}) ] --[ KD(f(..)) ]-> [ KD(f(..)) ]
//
// is narrowed via `variants_intruder` (Maude `get variants`); each variant
// is rebuilt into the rewrite rule `f(kd-term, prem-terms..) → conclusion`
// and — when that is a context subterm rule — expanded into concrete
// destructor rules via `rrule_to_ctxt_st_rule` + `destruction_rules`
// (`decompose_not_subterm`).  NoEq destructors additionally get their
// consecutive-application budget from `max_applications` (N12).  Intruder
// rules therefore arrive at the rule cache fully processed.
// =============================================================================

/// `isPrivateFunction` (Term/Term.hs): top-level function symbol is Private.
pub fn is_private_function(t: &LNTerm) -> bool {
    matches!(t, tamarin_term::term::Term::App(f, _) if f.is_private())
}

/// `destructionRulesAC diff fSig` — port of
/// `Theory.Tools.IntruderRules.destructionRulesAC`:
///
/// ```haskell
/// destructionRulesAC :: Bool -> ACfctFunSig -> WithMaude [IntrRuleAC]
/// destructionRulesAC diff fSig = reader $ \hnd -> minimizeIntruderRules diff hnd $
///     concatMap (decomposeNotSubterm diff . variantsIntruderAux hnd id True diff)
///       [ (AC (ACfct f), createRule s f)
///       | f@(s,(Public,_,_)) <- S.toList fSig, s `notElem` builtInDestrRule ]
///   where
///     createRule s f = Rule (DestrRule (append (pack "_") s) (-1) True True [AC (ACfct f)])
///                           [kdFact x_0, kuFact x_1] [concfact] [concfact] []
///       where concfact = kdFact (fAppACfct f [x_0, x_1])
/// ```
///
/// One generic 2-premise destructor per public user-defined AC symbol
/// (the built-in destructor names are skipped), narrowed and decomposed
/// into concrete destructor rules.
pub fn destruction_rules_ac(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    f_sig: &tamarin_term::function_symbols::AcFctFunSig,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{AcSym, Privacy};
    use tamarin_term::term::f_app_ac;

    let x_0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x_1 = var_term(LVar::new("x", LSort::Msg, 1));
    let mut generated: Vec<IntrRuleAC> = Vec::new();
    for f in f_sig {
        if f.privacy != Privacy::Public {
            continue;
        }
        if crate::rule::built_in_destr_rule().contains(&f.name) {
            continue;
        }
        let fun = FunSym::Ac(AcSym::AcFct(*f));
        let concfact = kd_fact(f_app_ac(AcSym::AcFct(*f), vec![x_0.clone(), x_1.clone()]));
        let base = Rule::new(
            IntrRuleACInfo::DestrRule {
                name: underscore_prefixed(f.name),
                remaining_applications: -1,
                rhs_is_proper_subterm: true,
                rhs_is_constant: true,
                funs: vec![fun],
            },
            vec![kd_fact(x_0.clone()), ku_fact(x_1.clone())],
            vec![concfact.clone()],
            vec![concfact],
        );
        let variants = variants_intruder(maude, &base);
        generated.extend(decompose_not_subterm(fun, &variants));
    }
    minimize_intruder_rules(maude, generated)
}

/// `decomposeNotSubterm` — port of
/// `Theory.Tools.IntruderRules.decomposeNotSubterm`:
///
/// ```haskell
/// decomposeNotSubterm bool (f, (Rule (DestrRule _ _ _ _ _)
///                                    ((Fact KDFact _ (lhs:_)) : other_prems)
///                                    [Fact KDFact _ [tc]] _ _) : rq) =
///   case rRuleToCtxtStRule (flhs `RRule` tc) of
///     Just context -> destructionRules bool context ++ decomposeNotSubterm bool (f, rq)
///     Nothing      -> decomposeNotSubterm bool (f, rq)
///   where flhs = FAPP f (lhs : foldMap getFactTerms other_prems)
/// decomposeNotSubterm _ (_, []) = []
/// ```
///
/// Rebuilds each destructor variant into the rewrite rule
/// `f(kd-term, prem-terms..) → tc` and, when that forms a context subterm
/// rule, expands it back into concrete destructor rules.  `FAPP` is the
/// RAW term constructor — the rebuilt LHS is NOT AC-normalised here.
fn decompose_not_subterm(f: FunSym, rules: &[IntrRuleAC]) -> Vec<IntrRuleAC> {
    use tamarin_term::rewriting::RRule;
    use tamarin_term::subterm_rule::rrule_to_ctxt_st_rule;
    use tamarin_term::term::Term;

    let mut out: Vec<IntrRuleAC> = Vec::new();
    for r in rules {
        // Variants of the generic destructors always match this shape
        // (DestrRule info, leading single-term KD premise, single KD
        // conclusion); anything else is skipped.
        if !matches!(r.info, IntrRuleACInfo::DestrRule { .. }) {
            continue;
        }
        let (first, other_prems) = match r.premises.split_first() {
            Some((first, rest)) if first.tag == FactTag::Kd && !first.terms.is_empty() => {
                (first, rest)
            }
            _ => continue,
        };
        let lhs = &first.terms[0];
        let tc = match r.conclusions.as_slice() {
            [c] if c.tag == FactTag::Kd && c.terms.len() == 1 => &c.terms[0],
            _ => continue,
        };
        // `flhs = FAPP f (lhs : foldMap getFactTerms other_prems)`.
        let args: Vec<LNTerm> = std::iter::once(lhs.clone())
            .chain(other_prems.iter().flat_map(|p| p.terms.iter().cloned()))
            .collect();
        let flhs: LNTerm = Term::App(f, args.into());
        if let Some(context) = rrule_to_ctxt_st_rule(&RRule::new(flhs, tc.clone())) {
            out.extend(destruction_rules(&context));
        }
    }
    out
}

/// `destructionRulesNoEq diff fSig` — port of
/// `Theory.Tools.IntruderRules.destructionRulesNoEq` (the non-AC cases):
///
/// ```haskell
/// destructionRulesNoEq :: Bool -> NoEqFunSig -> WithMaude [IntrRuleAC]
/// destructionRulesNoEq diff fSig = reader $ \hnd ->
///     map (maxApplications hnd) . minimizeIntruderRules diff hnd $
///     concatMap (decomposeNotSubterm diff . variantsIntruderAux hnd id True diff)
///       [ (NoEq f, createRule s f k)
///       | f@(s,(k,Public,_,_)) <- S.toList fSig, s `notElem` builtInDestrRule ]
///   where
///     createRule s f k | k /= 0 =
///         Rule (DestrRule (append (pack "_") s) (-1) True True [NoEq f])
///              ((kdFact x_{k-1}) : take (k-1) (map kuFact vars))
///              [concfact] [concfact] []
///     -- the two booleans are set by default to True: the budget is computed just after
///       where vars     = take k [ varTerm (LVar "x" LSortMsg i) | i <- [0..] ]
///             concfact = kdFact (fAppNoEq f (reverse vars))
///     createRule s f 0 = Rule (DestrRule (append (pack "_") s) (-1) True True [NoEq f])
///                             [] [concfact] [concfact] []
///       where concfact = kdFact (fAppNoEq f [])
/// ```
///
/// Note the generic rule's shapes: the KD premise carries `x_{k-1}`, the
/// KU premises carry `x_0 .. x_{k-2}`, and the conclusion applies `f` to
/// the REVERSED variable list `f(x_{k-1}, .., x_0)`.
pub fn destruction_rules_no_eq(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    f_sig: &tamarin_term::function_symbols::NoEqFunSig,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::Privacy;
    use tamarin_term::term::f_app_no_eq;

    let mut generated: Vec<IntrRuleAC> = Vec::new();
    for f in f_sig {
        if f.privacy != Privacy::Public {
            continue;
        }
        if crate::rule::built_in_destr_rule().contains(&f.name) {
            continue;
        }
        let k = f.arity;
        let info = IntrRuleACInfo::DestrRule {
            name: underscore_prefixed(f.name),
            remaining_applications: -1,
            rhs_is_proper_subterm: true,
            rhs_is_constant: true,
            funs: vec![FunSym::NoEq(*f)],
        };
        let base = if k != 0 {
            let vars: Vec<LNTerm> = (0..k)
                .map(|i| var_term(LVar::new("x", LSort::Msg, i as u64)))
                .collect();
            let mut prems = vec![kd_fact(vars[k - 1].clone())];
            prems.extend(vars.iter().take(k - 1).cloned().map(ku_fact));
            // `concfact = kdFact (fAppNoEq f (reverse vars))`.
            let concfact = kd_fact(f_app_no_eq(*f, vars.into_iter().rev().collect()));
            Rule::new(info, prems, vec![concfact.clone()], vec![concfact])
        } else {
            let concfact = kd_fact(f_app_no_eq(*f, vec![]));
            Rule::new(info, vec![], vec![concfact.clone()], vec![concfact])
        };
        let variants = variants_intruder(maude, &base);
        generated.extend(decompose_not_subterm(FunSym::NoEq(*f), &variants));
    }
    minimize_intruder_rules(maude, generated)
        .into_iter()
        .map(|r| max_applications(maude, r))
        .collect()
}

/// `maxApplications` — compute the maximum number of consecutive
/// applications of a deconstruction rule (implements N12):
///
/// ```haskell
/// maxApplications hnd (Rule (DestrRule name (-1) subterm constant funs)
///                           prems@((Fact KDFact _ [t]):_) concs@[Fact KDFact _ [rhs]] acts nvs) =
///    Rule (DestrRule name (if containsOnlyNoEq rhs && containsOnlyNoEq t
///                             && runMaude (unifiableLNTerms rhs t)
///                          then length (positions t) - (if isPrivateFunction t then 1 else 2)
///                          else 0) subterm constant funs) prems concs acts nvs
/// maxApplications _ ir@(Rule (DestrRule name _ _ _ _) _ _ _ _)
///     | any (`isSuffixOf` name) builtInDestrRuleInclPair = ir
/// maxApplications _ (Rule (DestrRule _ _ False _ _) _ _ _ _) =
///     error "maxApplications: This case should not happen, ..."
/// maxApplications _ ir = ir
/// ```
///
/// Clause order matters: the budget computation fires for ANY budget=-1
/// destructor with the KD-premise/KD-conclusion shape (built-in-named or
/// not); only rules failing that pattern reach the built-in-suffix
/// passthrough and the subterm=False error clause.
fn max_applications(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    mut ir: IntrRuleAC,
) -> IntrRuleAC {
    use tamarin_term::lterm::contains_only_no_eq;
    use tamarin_term::positions::positions;
    use tamarin_term::rewriting::Equal;

    // Clause 1: budget = -1 AND leading single-term KD premise AND single
    // KD conclusion.
    if matches!(
        ir.info,
        IntrRuleACInfo::DestrRule {
            remaining_applications: -1,
            ..
        }
    ) {
        let kd_prem_t: Option<&LNTerm> = ir
            .premises
            .first()
            .filter(|f| f.tag == FactTag::Kd && f.terms.len() == 1)
            .map(|f| &f.terms[0]);
        let kd_conc_rhs: Option<&LNTerm> = match ir.conclusions.as_slice() {
            [c] if c.tag == FactTag::Kd && c.terms.len() == 1 => Some(&c.terms[0]),
            _ => None,
        };
        if let (Some(t), Some(rhs)) = (kd_prem_t, kd_conc_rhs) {
            let budget: i64 = if contains_only_no_eq(rhs)
                && contains_only_no_eq(t)
                && maude
                    .unifiable(&[Equal {
                        lhs: rhs.clone(),
                        rhs: t.clone(),
                    }])
                    .unwrap_or(false)
            {
                // We do not need to count t itself, hence - 1.
                // If t is a private function symbol we need to permit one
                // more rule application as there is no associated
                // constructor.
                positions(t).len() as i64 - (if is_private_function(t) { 1 } else { 2 })
            } else {
                0
            };
            if let IntrRuleACInfo::DestrRule {
                remaining_applications,
                ..
            } = &mut ir.info
            {
                *remaining_applications = budget;
            }
            return ir;
        }
    }
    if let IntrRuleACInfo::DestrRule {
        name,
        rhs_is_proper_subterm,
        ..
    } = &ir.info
    {
        // Clause 2: built-in deconstruction rules pass through untouched.
        if crate::rule::has_builtin_suffix(name, &crate::rule::built_in_destr_rule_incl_pair()) {
            return ir;
        }
        // Clause 3: non-subterm destructors must have been budgeted above.
        if !*rhs_is_proper_subterm {
            panic!(
                "maxApplications: This case should not happen, please report it on the github page"
            );
        }
    }
    // Clause 4: pass through.
    ir
}

/// `variantsIntruder` — port of
/// `Theory.Tools.IntruderRules.variantsIntruder`.
///
/// HS shape (with `minimizeVariants = id`):
/// ```haskell
/// variantsIntruder hnd id applyFilters diff ru = go [] $ reverse $ do
///     let ruleTerms = concatMap factTerms (rPrems ru ++ rConcs ru ++ rActs ru)
///     fsigma <- computeVariants (fAppList ruleTerms) `runReader` hnd
///     let sigma     = freshToFree fsigma `evalFreshAvoiding` ruleTerms
///         ruvariant = normRule' (apply sigma ru) `runReader` hnd
///     guard (not applyFilters || (frees (get rConcs ruvariant) /= [] || diff) &&
///            (not applyFilters || ruvariant /= ru) &&
///            (get rConcs ruvariant) \\ (get rPrems ruvariant) /= [])
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
///   * drop rules with ground conclusions, identity variants
///     (ruvariant == ru), and rules whose
///     conclusions are subsumed by their premises
///   * drop rules whose single conclusion is an AC-Mult product
///
/// Then `go [] $ reverse $ ...` walks the LIST FROM THE BACK and dedups via
/// `equalRuleUpToRenaming`: if any other rule in `checked++unchecked` is
/// equal-up-to-renaming, this rule is dropped.
///
/// Every HS caller passes `applyFilters = True`, so the filters always apply
/// here.
pub fn variants_intruder(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    ru: &IntrRuleAC,
) -> Vec<IntrRuleAC> {
    // HS hardcodes `minimizeVariants = id` for every call except the BP
    // `em` destructor (`variantsIntruder hnd id True diff ...`).
    variants_intruder_with(maude, &|s| s, ru)
}

/// Core of `variantsIntruder` parameterised by the `minimizeVariants`
/// hook — port of `Theory.Tools.IntruderRules.variantsIntruder`.
///
/// HS:
/// ```haskell
/// variantsIntruder :: MaudeHandle -> ([LNSubstVFresh] -> [LNSubstVFresh])
///                  -> Bool -> Bool -> IntrRuleAC -> [IntrRuleAC]
/// variantsIntruder hnd minimizeVariants applyFilters diff ru = go [] $ reverse $ do
///     let ruleTerms = concatMap factTerms (rPrems ++ rConcs ++ rActs)
///     fsigma <- minimizeVariants $ computeVariants (fAppList ruleTerms) `runReader` hnd
///     ...
/// ```
///
/// `minimizeVariants` is applied to the WHOLE cleaned variant-subst
/// list before any rule is built (HS `fsigma <- minimizeVariants $
/// computeVariants ...`).  The `id` instance recovers
/// [`variants_intruder`] (the DH / pmult / user-destructor paths)
/// exactly; the BP `emap` destructor passes `nub . map canonize` via
/// [`bp_variants_intruder`].
fn variants_intruder_with(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    minimize_variants: &dyn Fn(
        Vec<tamarin_term::subst_vfresh::LNSubstVFresh>,
    ) -> Vec<tamarin_term::subst_vfresh::LNSubstVFresh>,
    ru: &IntrRuleAC,
) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::lterm::frees;
    use tamarin_term::subst::{apply_vterm, Subst};
    use tamarin_term::subst_vfresh::LNSubstVFresh;
    use tamarin_term::term::{f_app_list, Term};

    // `ruleTerms = concatMap factTerms (prems ++ concs ++ acts)`.
    // Note: HS does NOT include `nvs` here (only prems/concs/acts), even
    // though the rest of the pipeline includes nvs.
    let mut rule_terms: Vec<LNTerm> = Vec::new();
    for f in ru
        .premises
        .iter()
        .chain(ru.conclusions.iter())
        .chain(ru.actions.iter())
    {
        for t in f.terms.iter() {
            rule_terms.push(t.clone());
        }
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
            for v in frees(t) {
                s.insert(v);
            }
        }
        s
    };

    let packed = f_app_list(rule_terms);

    let raw_substs = match maude.variants(&packed) {
        Ok(v) => v,
        Err(_) => return vec![ru.clone()],
    };

    // `restrictVFresh (frees packed)`: the key-set is loop-invariant, so
    // materialise it once.
    let packed_frees_vec: Vec<LVar> = packed_frees.iter().copied().collect();
    let cleaned: Vec<LNSubstVFresh> = raw_substs
        .into_iter()
        .map(|pairs| LNSubstVFresh::from_list(pairs).restrict(&packed_frees_vec))
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
            let mut counter = packed_frees
                .iter()
                .map(|v| v.idx)
                .max()
                .map(|m| m + 1)
                .unwrap_or(0);
            s_fresh.fresh_to_free_avoiding(|n| {
                let b = counter;
                counter += n;
                b
            })
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
            fs.iter()
                .map(|f| {
                    // norm/subst rebuild — frees can change; recompute the bloom.
                    let terms: Vec<LNTerm> = f.terms.iter().map(|t| norm_t(t.clone())).collect();
                    LNFact::fresh_annotated(f.tag, f.annotations.clone(), terms)
                })
                .collect()
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

        // HS `guard`, at `applyFilters = True`: the conclusions have free
        // variables, the variant is not the rule itself, and
        // `rConcs \\ rPrems /= []`.
        let concs_have_frees = ruvariant
            .conclusions
            .iter()
            .flat_map(|f| f.terms.iter())
            .any(|t| !frees(t).is_empty());
        if !concs_have_frees {
            continue;
        }
        // Not the identity variant.
        if &ruvariant == ru {
            continue;
        }
        // `(rConcs ruvariant) \\ (rPrems ruvariant) /= []`.
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
                if !matched {
                    any_remaining = true;
                }
            }
            any_remaining
        };
        if !concs_minus_prems_nonempty {
            continue;
        }

        // Drop rules with single product-conclusion (IntruderRules.hs).
        let conc_terms: Vec<&LNTerm> = ruvariant
            .conclusions
            .iter()
            .flat_map(|f| f.terms.iter())
            .collect();
        if conc_terms.len() == 1 && matches!(conc_terms[0], Term::App(FunSym::Ac(AcSym::Mult), _)) {
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
        let dup = kept_idx
            .iter()
            .map(|&k| &rev[k])
            .chain(rev[p + 1..].iter())
            .any(|peer| equal_rule_up_to_renaming(maude, r, peer));
        if !dup {
            kept_idx.push(p);
        }
    }
    // HS `checked' = r:checked` prepend ⇒ reverse the encounter order.
    kept_idx.into_iter().rev().map(|k| rev[k].clone()).collect()
}

// =============================================================================
// `dhIntruderRules` / `bpIntruderRules` (IntruderRules.hs) and their shared
// `where`-helpers.  Constructors take `mkAction = return` (the conclusion as
// the action), destructors `const []`.
// =============================================================================

/// `append (pack "_") xSymString` — the intruder-rule name-mangling primitive.
fn underscore_prefixed(sym: &[u8]) -> Vec<u8> {
    let mut n = b"_".to_vec();
    n.extend_from_slice(sym);
    n
}

/// `ConstrRule (append (pack "_") xSymString) f`.
fn intr_constr_info(sym: &[u8], f: FunSym) -> IntrRuleACInfo {
    IntrRuleACInfo::ConstrRule {
        name: underscore_prefixed(sym),
        fun: f,
    }
}

/// `DestrRule (append (pack "_") xSymString) 0 True False funs`.
/// Note budget=0 (NOT -1), subterm=True, constant=False — these are the
/// builtin DH/BP destructors whose budget is irrelevant (variantsIntruder
/// expands them at build time).
fn intr_destr_info(sym: &[u8], funs: Vec<FunSym>) -> IntrRuleACInfo {
    IntrRuleACInfo::DestrRule {
        name: underscore_prefixed(sym),
        remaining_applications: 0,
        rhs_is_proper_subterm: true,
        rhs_is_constant: false,
        funs,
    }
}

/// `return :: a -> [a]` — singleton-list action constructor (HS).
fn intr_mk_singleton(f: LNFact) -> Vec<LNFact> {
    vec![f]
}
/// `const [] :: a -> [a]` — empty action constructor (HS destructors).
fn intr_mk_empty(_: LNFact) -> Vec<LNFact> {
    Vec::new()
}

/// HS `dhIntruderRules` (IntruderRules.hs): the `_exp`, `_inv`,
/// `_DH_neutral`, `_one` and `_mult` constructors plus the variants of the
/// `_exp` and `_inv` destructors, minimised.
///
/// Like HS, proving reads the cached `data/intruder_variants_dh.spthy`
/// ([`crate::intruder_variants::mk_dh_intruder_variants`]); this generator
/// serves the `variants` command, which regenerates that file.
pub fn dh_intruder_rules(maude: &tamarin_term::maude_proc::MaudeHandle) -> Vec<IntrRuleAC> {
    use tamarin_term::builtin::{dh_neutral, exp, inv, mult, one_const};
    use tamarin_term::function_symbols::{
        dh_neutral_sym, exp_sym, inv_sym, one_sym, AcSym, DH_NEUTRAL_SYM_STRING, EXP_SYM_STRING,
        INV_SYM_STRING, MULT_SYM_STRING, ONE_SYM_STRING,
    };

    // `x_var_0 = varTerm (LVar "x" LSortMsg 0)` etc.
    // IntruderRules.hs.
    let x_var_0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x_var_1 = var_term(LVar::new("x", LSort::Msg, 1));

    // HS `expRule mkInfo kudFact mkAction`
    //   = Rule mkInfo [kudFact x_var_0, kuFact x_var_1] [kudFact (fAppExp ...)] (mkAction ...) []
    // IntruderRules.hs.
    let exp_rule = |info: IntrRuleACInfo,
                    kud_fact: fn(LNTerm) -> LNFact,
                    mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = ku_fact(x_var_1.clone());
        let conc = exp(x_var_0.clone(), x_var_1.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // HS `multRule` — IntruderRules.hs.
    let mult_rule = |info: IntrRuleACInfo,
                     kud_fact: fn(LNTerm) -> LNFact,
                     mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = ku_fact(x_var_1.clone());
        let conc = mult(x_var_0.clone(), x_var_1.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // HS `invRule` — IntruderRules.hs.
    let inv_rule = |info: IntrRuleACInfo,
                    kud_fact: fn(LNTerm) -> LNFact,
                    mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let conc = inv(x_var_0.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact], vec![concfact], acts)
    };

    // HS `oneRule` — IntruderRules.hs.
    let one_rule = |info: IntrRuleACInfo,
                    kud_fact: fn(LNTerm) -> LNFact,
                    mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let conc = one_const::<tamarin_term::vterm::Lit<tamarin_term::lterm::Name, LVar>>();
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![], vec![concfact], acts)
    };

    // HS `dhNeutralRule` — IntruderRules.hs.
    let dh_neutral_rule = |info: IntrRuleACInfo,
                           kud_fact: fn(LNTerm) -> LNFact,
                           mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let conc = dh_neutral::<tamarin_term::vterm::Lit<tamarin_term::lterm::Name, LVar>>();
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![], vec![concfact], acts)
    };

    let constrs: Vec<IntrRuleAC> = vec![
        // expRule  (ConstrRule "_exp" (NoEq expSym))        kuFact return
        exp_rule(
            intr_constr_info(EXP_SYM_STRING, FunSym::NoEq(exp_sym())),
            ku_fact,
            intr_mk_singleton,
        ),
        // invRule  (ConstrRule "_inv" (NoEq invSym))        kuFact return
        inv_rule(
            intr_constr_info(INV_SYM_STRING, FunSym::NoEq(inv_sym())),
            ku_fact,
            intr_mk_singleton,
        ),
        // dhNeutralRule (ConstrRule "_DH_neutral" (NoEq dhNeutralSym)) kuFact return
        dh_neutral_rule(
            intr_constr_info(DH_NEUTRAL_SYM_STRING, FunSym::NoEq(dh_neutral_sym())),
            ku_fact,
            intr_mk_singleton,
        ),
        // oneRule  (ConstrRule "_one" (NoEq oneSym))        kuFact return
        one_rule(
            intr_constr_info(ONE_SYM_STRING, FunSym::NoEq(one_sym())),
            ku_fact,
            intr_mk_singleton,
        ),
        // multRule (ConstrRule "_mult" (AC Mult))           kuFact return
        mult_rule(
            intr_constr_info(MULT_SYM_STRING, FunSym::Ac(AcSym::Mult)),
            ku_fact,
            intr_mk_singleton,
        ),
    ];

    // `concatMap (variantsIntruder hnd id True diff) [exp-destr, inv-destr]`.
    let exp_destr = exp_rule(
        intr_destr_info(EXP_SYM_STRING, vec![FunSym::NoEq(exp_sym())]),
        kd_fact,
        intr_mk_empty,
    );
    let inv_destr = inv_rule(
        intr_destr_info(INV_SYM_STRING, vec![FunSym::NoEq(inv_sym())]),
        kd_fact,
        intr_mk_empty,
    );

    let mut destr_variants: Vec<IntrRuleAC> = Vec::new();
    destr_variants.extend(variants_intruder(maude, &exp_destr));
    destr_variants.extend(variants_intruder(maude, &inv_destr));

    // `minimizeIntruderRules diff hnd $ constrs ++ destr_variants`.
    let mut all = constrs;
    all.extend(destr_variants);
    minimize_intruder_rules(maude, all)
}

/// HS `bpIntruderRules` (IntruderRules.hs): the `_pmult` and `_em`
/// constructors plus the variants of the `_pmult` destructor and, through
/// [`bp_variants_intruder`], of the `_em` destructor, minimised.  Note
/// `pmultRule` concludes `pmult(x1, x0)`, swapping its premises' order, and
/// `emapRule` takes both premises through `kud`.
///
/// Serves the `variants` command only; proving reads the cached
/// `data/intruder_variants_bp.spthy`
/// ([`crate::intruder_variants::mk_bp_intruder_variants`]).
pub fn bp_intruder_rules(maude: &tamarin_term::maude_proc::MaudeHandle) -> Vec<IntrRuleAC> {
    use tamarin_term::builtin::{emap, pmult};
    use tamarin_term::function_symbols::{pmult_sym, CSym, EMAP_SYM_STRING, PMULT_SYM_STRING};

    // `x_var_0 = varTerm (LVar "x" LSortMsg 0)` etc. (IntruderRules.hs).
    let x_var_0 = var_term(LVar::new("x", LSort::Msg, 0));
    let x_var_1 = var_term(LVar::new("x", LSort::Msg, 1));

    // HS `pmultRule mkInfo kud mkAction` (IntruderRules.hs).
    //   prems = [kud x0, kuFact x1]; conc = kud (pmult(x1, x0)).
    // The conclusion args are SWAPPED: `fAppPMult (x_var_1, x_var_0)`.
    let pmult_rule = |info: IntrRuleACInfo,
                      kud_fact: fn(LNTerm) -> LNFact,
                      mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = ku_fact(x_var_1.clone());
        let conc = pmult(x_var_1.clone(), x_var_0.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // HS `emapRule mkInfo kud mkAction` (IntruderRules.hs).
    //   prems = [kud x0, kud x1] (BOTH via kud); conc = kud (em(x0, x1)).
    let emap_rule = |info: IntrRuleACInfo,
                     kud_fact: fn(LNTerm) -> LNFact,
                     mk_action: fn(LNFact) -> Vec<LNFact>|
     -> IntrRuleAC {
        let bfact = kud_fact(x_var_0.clone());
        let efact = kud_fact(x_var_1.clone());
        let conc = emap(x_var_0.clone(), x_var_1.clone());
        let concfact = kud_fact(conc);
        let acts = mk_action(concfact.clone());
        Rule::new(info, vec![bfact, efact], vec![concfact], acts)
    };

    // Constructor rules: `pmultRule (ConstrRule "_pmult" (NoEq pmultSym))
    // kuFact return` and `emapRule (ConstrRule "_em" (C EMap)) kuFact return`.
    let constrs: Vec<IntrRuleAC> = vec![
        pmult_rule(
            intr_constr_info(PMULT_SYM_STRING, FunSym::NoEq(pmult_sym())),
            ku_fact,
            intr_mk_singleton,
        ),
        emap_rule(
            intr_constr_info(EMAP_SYM_STRING, FunSym::C(CSym::EMap)),
            ku_fact,
            intr_mk_singleton,
        ),
    ];

    // pmult destructor variants — `variantsIntruder hnd id True diff`
    // (like DH `exp`).
    let pmult_destr = pmult_rule(
        intr_destr_info(PMULT_SYM_STRING, vec![FunSym::NoEq(pmult_sym())]),
        kd_fact,
        intr_mk_empty,
    );
    let mut all = constrs;
    all.extend(variants_intruder(maude, &pmult_destr));

    // em destructor variants — `bpVariantsIntruder diff hnd`
    // (canonicalised + KD→KU post-process).
    let emap_destr = emap_rule(
        intr_destr_info(EMAP_SYM_STRING, vec![FunSym::C(CSym::EMap)]),
        kd_fact,
        intr_mk_empty,
    );
    all.extend(bp_variants_intruder(maude, &emap_destr));

    // `minimizeIntruderRules diff hnd $ ...`.
    minimize_intruder_rules(maude, all)
}

/// `bpVariantsIntruder` — port of
/// `Theory.Tools.IntruderRules.bpVariantsIntruder`.
///
/// ```haskell
/// bpVariantsIntruder diff hnd ru = do
///     ruvariant <- variantsIntruder hnd minimizeVariants True diff ru
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
    let minimize_variants = |substs: Vec<LNSubstVFresh>| -> Vec<LNSubstVFresh> {
        let mut out: Vec<LNSubstVFresh> = Vec::new();
        for s in substs {
            let mappings = s.to_list();
            let doms: Vec<LVar> = mappings.iter().map(|(d, _)| *d).collect();
            let mut rngs: Vec<LNTerm> = mappings.iter().map(|(_, t)| t.clone()).collect();
            // `sort rngs` — `Ord LNTerm`.
            rngs.sort();
            let rezipped = LNSubstVFresh::from_list(doms.into_iter().zip(rngs).collect::<Vec<_>>());
            let canon = canonize_subst(&rezipped);
            // `nub` — keep first occurrence, drop later duplicates
            // (structural `Eq` on the canonicalised subst).
            if !out.iter().any(|existing| existing == &canon) {
                out.push(canon);
            }
        }
        out
    };

    let variants = variants_intruder_with(maude, &minimize_variants, ru);

    // KD→KU post-process (IntruderRules.hs): if the first premise
    // is a KD-fact whose single arg is a bare Var, rewrite that premise's
    // tag KD→KU (keeping the same args/annotations); else the symmetric
    // case where the SECOND premise is the bare-Var KD-fact.
    let is_bare_var_kd = |f: &LNFact| -> bool {
        f.tag == FactTag::Kd && f.terms.len() == 1 && matches!(f.terms[0], Term::Lit(Lit::Var(_)))
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
#[path = "intruder_rules_tests.rs"]
mod tests;
