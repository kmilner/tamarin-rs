// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Sapic.Basetranslation` (`lib/sapic/src/Sapic/Basetranslation.hs`):
//!   - `baseInit`       (Basetranslation.hs)
//!   - `baseTransNull`  (Basetranslation.hs)
//!   - `baseTransAction` — every `SapicAction` arm
//!   - `baseTransComb`   — every `ProcessCombinator` arm
//!   - the hardcoded restrictions `baseRestr` selects from:
//!     `single_session`, state, predicate, event and locking restrictions are
//!     built directly in the theory's internal formula representation.
//!
//! `baseRestr`'s selection logic itself lives in `translate`, which owns the
//! process-shape predicates (`contains isLookup` etc.) it dispatches on.

use std::collections::BTreeSet;

use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::vterm::var_term;

use tamarin_theory::atom::ProtoAtom;
use tamarin_theory::formula::{
    formula_frees, lift_free, quantify_vars, ProtoFormula, Quantifier, SyntacticLNFormula,
};
use tamarin_theory::sapic::{
    to_lformula, to_ln_fact, to_ln_term, ProcessPosition, SapicAction, SapicLVar, SapicTerm,
};

use crate::annotation::ProcessAnnotation;
use crate::facts::{
    lstate, AnnotatedRule, RulePosition, SpecialPosition, StateKind, TransAction, TransFact,
};

/// A single translation "rule body": `(prems, acts, concs, restr)`.
/// HS `([TransFact],[TransAction],[TransFact],[SyntacticLNFormula])`; the
/// 4th element carries the rule's embedded restriction formulas.
pub(crate) type RuleBody = (
    Vec<TransFact>,
    Vec<TransAction>,
    Vec<TransFact>,
    Vec<SyntacticLNFormula>,
);

/// `baseTransNull` (Basetranslation.hs):
///   `[([State LState p tildex], [], [], [])]`
pub(crate) fn base_trans_null(p: &ProcessPosition, tildex: &BTreeSet<LVar>) -> Vec<RuleBody> {
    vec![(vec![lstate(p, &[], tildex)], vec![], vec![], vec![])]
}

/// `Data.List.union xs ys = xs ++ filter (`notElem` xs) (nub ys)`: keep `xs` in
/// order (duplicates preserved), then append each element of `ys` that is not
/// already present (deduped within the appended tail too, via the growing
/// membership check).  Generic over any `PartialEq` element, matching HS's
/// `Eq`-based `union`.
pub(crate) fn list_union<T: PartialEq + Clone>(xs: &[T], ys: &[T]) -> Vec<T> {
    let mut out = xs.to_vec();
    for y in ys {
        if !out.contains(y) {
            out.push(y.clone());
        }
    }
    out
}

/// `Data.List.intersect xs ys`: keep every element of `xs` (in `xs`-order,
/// duplicates preserved) that is an `Eq`-member of `ys`.  Generic over any
/// `PartialEq` element.
pub(crate) fn list_intersect<T: PartialEq + Clone>(xs: &[T], ys: &[T]) -> Vec<T> {
    xs.iter().filter(|x| ys.contains(x)).cloned().collect()
}

/// `baseTransAction` (Basetranslation.hs).  Returns the rule bodies and
/// the updated `tildex`.  `needs_ass_immediate` is the `needsInEvRes` flag;
/// when false, `Event` emits NO extra `EventEmpty` action.
pub(crate) fn base_trans_action(
    async_channels: bool,
    needs_ass_immediate: bool,
    ac: &SapicAction<SapicLVar>,
    an: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<(Vec<RuleBody>, BTreeSet<LVar>), String> {
    // `def_state = State LState p tildex`, `def_state' tx = State LState (p++[1]) tx`
    let mut p1 = p.clone();
    p1.push(1);
    // `channelIn t = [ChannelIn t | needsAssImmediate]`.
    let channel_in = |t: &LNTerm| -> Vec<TransAction> {
        if needs_ass_immediate {
            vec![TransAction::ChannelIn(t.clone())]
        } else {
            vec![]
        }
    };

    match ac {
        // (Rep): replication (Basetranslation.hs).  Two rules:
        //   [([def_state], [], [State PSemiState (p++[1]) tildex], []),
        //    ([State PSemiState (p++[1]) tildex], [], [def_state' tildex], [])]
        // The first consumes the entering linear state and produces a
        // PERSISTENT semistate (so it can fire arbitrarily often); the second
        // turns each persistent-semistate instance back into a fresh linear
        // `def_state'` for the replicated body.  `tildex` is unchanged.
        SapicAction::Rep => {
            let semistate = TransFact::State(StateKind::PSemiState, p1.clone(), tildex.clone());
            let body1: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![semistate.clone()],
                vec![],
            );
            let body2: RuleBody = (
                vec![semistate],
                vec![],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body1, body2], tildex.clone()))
        }
        // (New v): `tx' = toLVar v `insert` tildex`
        //   [([def_state, Fr (toLVar v)], [], [def_state' tx'], [])]
        SapicAction::New(v) => {
            let lv = v.to_lvar();
            let mut tx2 = tildex.clone();
            tx2.insert(lv);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex), TransFact::Fr(lv)],
                vec![],
                vec![lstate(p, &[1], &tx2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Event f): `[([def_state], TamarinAct f : [EventEmpty | needsAss], [def_state' tildex], [])]`
        SapicAction::Event(f) => {
            let lnf = to_ln_fact(f);
            let mut acts = vec![TransAction::TamarinAct(lnf)];
            if needs_ass_immediate {
                acts.push(TransAction::EventEmpty);
            }
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                acts,
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (ChIn channel t' matchVar) (Basetranslation.hs): handle channel
        // input `in(c,pat); P` like `in(c,x); let pat = x in P`.  Mint a fresh
        // message variable `x` avoiding `tildex`, build the Let combinator rules
        // for `let pat = x`, then append the channel facts via
        // `mergeWithStateRule` (only onto rules that have a State premise).
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => {
            // `x = evalFreshAvoiding (freshLVar "x" LSortMsg) tildex`.
            let x = fresh_msg_var_avoiding("x", tildex);
            let xt: LNTerm = var_term(x);
            // `xTerm = varTerm (SapicLVar { slvar = x, stype = Nothing })`.
            let x_sapic: SapicTerm = var_term(SapicLVar::untyped(x));
            // `(rules, tx', _) = baseTransComb (Let t' xTerm matchVar) (an {elseBranch=False}) p tildex`.
            let let_comb = tamarin_theory::sapic::ProcessCombinator::Let {
                left: msg.clone(),
                right: x_sapic,
                match_vars: match_vars.clone(),
            };
            let mut an_let = an.clone();
            an_let.else_branch = false;
            let (rules, tx_prime, _) = base_trans_comb(&let_comb, &an_let, p, tildex)?;
            // `t = toLNTerm t'`.
            let t = to_ln_term(msg);
            match chan {
                None => {
                    if needs_ass_immediate {
                        // delay matching: `mergeWithStateRule ([In x], channelIn x, []) rules`.
                        let merged = merge_with_state_rule(
                            (vec![TransFact::In(xt.clone())], channel_in(&xt), vec![]),
                            rules,
                        );
                        Ok((merged, tx_prime))
                    } else {
                        // `tx2' = freeset t `union` tildex`; single direct In rule.
                        let mut tx2 = tildex.clone();
                        tx2.extend(ln_term_vars(&t));
                        let body: RuleBody = (
                            vec![lstate(p, &[], tildex), TransFact::In(t)],
                            vec![],
                            vec![lstate(p, &[1], &tx2)],
                            vec![],
                        );
                        Ok((vec![body], tx2))
                    }
                }
                Some(tc_term) => {
                    // `tc = toLNTerm tc'`; `ts = fAppPair (tc, varTerm x)`.
                    let tc = to_ln_term(tc_term);
                    let ts = tamarin_term::builtin::pair(tc.clone(), xt.clone());
                    // `ack = [Ack tc xt | not asyncChannels]`.
                    let ack: Vec<TransFact> = if async_channels {
                        vec![]
                    } else {
                        vec![TransFact::Ack(tc.clone(), xt.clone())]
                    };
                    // `mergeWithStateRule ([Message tc xt], [], ack) rules`.
                    let mut out = merge_with_state_rule(
                        (
                            vec![TransFact::Message(tc.clone(), xt.clone())],
                            vec![],
                            ack,
                        ),
                        rules.clone(),
                    );
                    // only add adversary rule if channel is not guaranteed secret.
                    if an.secret_channel.is_none() {
                        out.extend(merge_with_state_rule(
                            (vec![TransFact::In(ts.clone())], channel_in(&ts), vec![]),
                            rules,
                        ));
                    }
                    Ok((out, tx_prime))
                }
            }
        }
        // (ChOut (Just tc') t') (Basetranslation.hs): the two guards differ
        // only in the adversary-injected output rule `([def_state, In tc],
        // channelIn tc, [Out t, def_state' tildex], [])`, which comes first
        // and is emitted only when `secretChannel = Nothing`.  Then the
        // `Message` rule, plus the semistate/`Ack` rule for sync channels.
        SapicAction::ChOut {
            chan: Some(tc_term),
            msg,
        } => {
            let tc = to_ln_term(tc_term);
            let t = to_ln_term(msg);
            let mut rules: Vec<RuleBody> = Vec::new();
            if an.secret_channel.is_none() {
                rules.push((
                    vec![lstate(p, &[], tildex), TransFact::In(tc.clone())],
                    channel_in(&tc),
                    vec![TransFact::Out(t.clone()), lstate(p, &[1], tildex)],
                    vec![],
                ));
            }
            if async_channels {
                // `([def_state], [], [Message tc t, def_state' tildex], [])`.
                rules.push((
                    vec![lstate(p, &[], tildex)],
                    vec![],
                    vec![TransFact::Message(tc, t), lstate(p, &[1], tildex)],
                    vec![],
                ));
            } else {
                // `semistate = State LSemiState (p++[1]) tildex`.
                let semistate = TransFact::State(StateKind::LSemiState, p1.clone(), tildex.clone());
                rules.push((
                    vec![lstate(p, &[], tildex)],
                    vec![],
                    vec![TransFact::Message(tc.clone(), t.clone()), semistate.clone()],
                    vec![],
                ));
                rules.push((
                    vec![semistate, TransFact::Ack(tc, t)],
                    vec![],
                    vec![lstate(p, &[1], tildex)],
                    vec![],
                ));
            }
            Ok((rules, tildex.clone()))
        }
        // (ChOut Nothing t): `[([def_state], [], [def_state' tildex, Out t], [])]`
        SapicAction::ChOut { chan: None, msg } => {
            let t = to_ln_term(msg);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[1], tildex), TransFact::Out(t)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // === Pure cell translation (Basetranslation.hs) ===
        // Gated on `an.pure_state`, which is only ever set when the
        // state-channel optimisation is enabled (`--translation-state-optimisation`
        // / `_stateChannelOpt`).  These guards MUST be checked BEFORE the classical
        // `Insert`/`Lock`/`Unlock` cases (HS guard order).
        //
        // (Insert t1 t2) | pureState, Just (AnVar v) <- an.unlock
        //   let tx' = v `insert` tildex in
        //   [([def_state, CellLocked t1 (varTerm v)], [],
        //     [def_state' tx', PureCell t1 t2], [])]
        SapicAction::Insert(t1, t2) if an.pure_state && an.unlock.is_some() => {
            let v = an.unlock.as_ref().unwrap().0;
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let mut tx2 = tildex.clone();
            tx2.insert(v);
            let body: RuleBody = (
                vec![
                    lstate(p, &[], tildex),
                    TransFact::CellLocked(lt1.clone(), var_term(v)),
                ],
                vec![],
                vec![lstate(p, &[1], &tx2), TransFact::PureCell(lt1, lt2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Insert t1 t2) | pureState  (no unlock annotation — lone insert)
        //   [([def_state], [], [def_state' tildex, PureCell t1 t2], [])]
        SapicAction::Insert(t1, t2) if an.pure_state => {
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[1], tildex), TransFact::PureCell(lt1, lt2)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Lock _) | pureState and (Unlock _) | pureState -> silent
        // passthrough (Basetranslation.hs gives both the same rule):
        //   [([def_state], [], [def_state' tildex], [])]
        SapicAction::Lock(_) | SapicAction::Unlock(_) if an.pure_state => {
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }

        // === Classical state translation (Basetranslation.hs) ===
        //
        // (Insert t1 t2): `[([def_state], [InsertA t1 t2], [def_state' tildex], [])]`
        SapicAction::Insert(t1, t2) => {
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![TransAction::InsertA(lt1, lt2)],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Delete t): `[([def_state], [DeleteA t], [def_state' tildex], [])]`
        SapicAction::Delete(t) => {
            let lt = to_ln_term(t);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![TransAction::DeleteA(lt)],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Lock t) | Just (AnVar v) <- an.lock (Basetranslation.hs):
        //   let tx' = v `insert` tildex in
        //   [([def_state, Fr v], [LockNamed t v, LockUnnamed t v], [def_state' tx'], [])]
        // (Lock _) | Nothing <- an.lock -> "Unannotated lock" error
        //   (Basetranslation.hs).
        SapicAction::Lock(t) => {
            let Some(an_v) = &an.lock else {
                return Err("baseTransAction: Unannotated lock".to_string());
            };
            let v = an_v.0;
            let lt = to_ln_term(t);
            let mut tx2 = tildex.clone();
            tx2.insert(v);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex), TransFact::Fr(v)],
                vec![
                    TransAction::LockNamed(lt.clone(), v),
                    TransAction::LockUnnamed(lt, v),
                ],
                vec![lstate(p, &[1], &tx2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Unlock t) | Just (AnVar v) <- an.unlock (Basetranslation.hs):
        //   [([def_state], [UnlockNamed t v, UnlockUnnamed t v], [def_state' tildex], [])]
        // (Unlock _) | Nothing <- an.lock -> "Unannotated unlock" error
        //   (Basetranslation.hs).
        SapicAction::Unlock(t) => {
            let Some(an_v) = &an.unlock else {
                return Err(
                    "This feature is not implemented yet. Sorry! Unannotated unlock".to_string(),
                );
            };
            let v = an_v.0;
            let lt = to_ln_term(t);
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![
                    TransAction::UnlockNamed(lt.clone(), v),
                    TransAction::UnlockUnnamed(lt, v),
                ],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (ProcessCall ..): a pure inlining marker (Basetranslation.hs).
        //   [([def_state], [], [def_state' tildex], [])]
        // The substituted body that follows the marker carries the real
        // behaviour; this rule just threads the state on by one position.
        SapicAction::ProcessCall(_, _) => {
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (MSR l' a' r' res' _): an embedded multiset-rewrite rule inside the
        // process (Basetranslation.hs). Match-vars do not affect this step.
        //   (l,a,r,res) = (map toLNFact l', map toLNFact a', map toLNFact r',
        //                  map toLFormula res')
        //   tx' = freeset' l ∪ tildex          (freeset' = vars of all premises)
        //   [( def_state : map TamarinFact l
        //    , map TamarinAct a ++ [EventEmpty | needsAss]
        //    , def_state' tx' : map TamarinFact r
        //    , res )]
        SapicAction::Msr {
            prems,
            acts,
            concs,
            rest,
            ..
        } => {
            let l: Vec<tamarin_theory::fact::LNFact> = prems.iter().map(to_ln_fact).collect();
            let a: Vec<tamarin_theory::fact::LNFact> = acts.iter().map(to_ln_fact).collect();
            let r: Vec<tamarin_theory::fact::LNFact> = concs.iter().map(to_ln_fact).collect();
            // `tx' = freeset' l ∪ tildex`, `freeset' = fromList . concatMap getFactVariables`.
            let mut tx2 = tildex.clone();
            for f in &l {
                tx2.extend(fact_vars(f));
            }
            // premises: def_state : map TamarinFact l
            let mut prems_facts: Vec<TransFact> = vec![lstate(p, &[], tildex)];
            prems_facts.extend(l.into_iter().map(TransFact::TamarinFact));
            // actions: map TamarinAct a ++ [EventEmpty | needsAss]
            let mut act_facts: Vec<TransAction> =
                a.into_iter().map(TransAction::TamarinAct).collect();
            if needs_ass_immediate {
                act_facts.push(TransAction::EventEmpty);
            }
            // conclusions: def_state' tx' : map TamarinFact r
            let mut conc_facts: Vec<TransFact> = vec![lstate(p, &[1], &tx2)];
            conc_facts.extend(r.into_iter().map(TransFact::TamarinFact));
            // restrictions: `map toLFormula res'` (Theory/Sapic/Term.hs
            // drops the type tags).
            let restr: Vec<SyntacticLNFormula> = rest.iter().map(to_lformula).collect();
            let body: RuleBody = (prems_facts, act_facts, conc_facts, restr);
            Ok((vec![body], tx2))
        }
    }
}

/// The result of translating a combinator: `(rules, tildex_l, Option<tildex_r>)`
/// — HS `TranslationResultComb` (Basetranslation.hs).  `tildex_r` is `None`
/// when the combinator has no right child to translate (e.g. `let` without an
/// else branch).
pub(crate) type CombResult = (Vec<RuleBody>, BTreeSet<LVar>, Option<BTreeSet<LVar>>);

/// `baseTransComb` (Basetranslation.hs): `Parallel`, `NDC`, `CondEq`,
/// `Cond` (with a formula), `Lookup` and `Let`.
pub(crate) fn base_trans_comb(
    c: &tamarin_theory::sapic::ProcessCombinator<SapicLVar>,
    an: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<CombResult, String> {
    use tamarin_theory::sapic::ProcessCombinator as PC;

    // `def_state = State LState p tildex`, `def_stateN tx = State LState (p++[N]) tx`

    match c {
        // Parallel (Basetranslation.hs):
        //   ([([def_state], [], [def_state1 tildex, def_state2 tildex], [])],
        //    tildex, Just tildex)
        PC::Parallel => {
            let body: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[1], tildex), lstate(p, &[2], tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone(), Some(tildex.clone())))
        }
        // NDC (Basetranslation.hs): no rules of its own; both children
        // share the parent's position (handled by `substStatePos` in `gen`).
        //   ([], tildex, Just tildex)
        PC::Ndc => Ok((vec![], tildex.clone(), Some(tildex.clone()))),
        // CondEq (Basetranslation.hs):
        //   let fa = toLNFact (protoFact Linear "Eq" [t1, t2]) in
        //   if vars_f ⊆ tildex then
        //     ([([def_state], [PredicateA fa], [def_state1 tildex], []),
        //       ([def_state], [NegPredicateA fa], [def_state2 tildex], [])],
        //      tildex, Just tildex)
        //   else throw (WFUnbound (vars_f \\ tildex))
        PC::CondEq(t1, t2) => {
            let fa = eq_fact(t1, t2);
            // `vars_f = fromList $ getFactVariables fa` — the variables in the
            // (untyped) Eq fact.
            let vars_f = fact_vars(&fa);
            if !vars_f.is_subset(tildex) {
                return Err(wf_unbound(vars_f.difference(tildex).copied()));
            }
            let body_eq: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![TransAction::PredicateA(fa.clone())],
                vec![lstate(p, &[1], tildex)],
                vec![],
            );
            let body_neq: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![TransAction::NegPredicateA(fa)],
                vec![lstate(p, &[2], tildex)],
                vec![],
            );
            Ok((
                vec![body_eq, body_neq],
                tildex.clone(),
                Some(tildex.clone()),
            ))
        }
        // Cond f' (Basetranslation.hs):
        //   f <- toLFormula f'
        //   let freevars_f = fromList (freesList f)
        //   if freevars_f ⊆ tildex then
        //     ([([def_state], [], [def_state1 tildex], [f]),
        //       ([def_state], [], [def_state2 tildex], [Not f])],
        //      tildex, Just tildex)
        //   else throw (WFUnbound (freevars_f \\ tildex))
        PC::Cond(f) => {
            let f = to_lformula(f);
            // `fromList (freesList f)` — the formula's free message and
            // timepoint variables, compared against `tildex :: Set LVar`.
            let freevars_f: BTreeSet<LVar> = formula_frees(&f).into_iter().collect();
            if !freevars_f.is_subset(tildex) {
                return Err(wf_unbound(freevars_f.difference(tildex).copied()));
            }
            // then-arm carries `[f]`; else-arm carries `[Not f]`.
            let body_then: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[1], tildex)],
                vec![f.clone()],
            );
            let body_else: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![lstate(p, &[2], tildex)],
                vec![f.not()],
            );
            Ok((
                vec![body_then, body_else],
                tildex.clone(),
                Some(tildex.clone()),
            ))
        }
        // Pure cell Lookup (Basetranslation.hs), gated on
        //   pureState && Just (AnVar vs) <- an.unlock:
        //   let tx' = vs `insert` (v `insert` tildex) in
        //   ([([def_state, PureCell t (varTerm v), Fr vs], [],
        //      [def_state1 tx', CellLocked t (varTerm vs)], [])],
        //    tx', Nothing)
        // Pure lookups emit only the success arm.
        PC::Lookup(t, v) if an.pure_state && an.unlock.is_some() => {
            let vs = an.unlock.as_ref().unwrap().0;
            let lt = to_ln_term(t);
            let lv = v.to_lvar();
            let mut tx_prime = tildex.clone();
            tx_prime.insert(lv);
            tx_prime.insert(vs);
            let body: RuleBody = (
                vec![
                    lstate(p, &[], tildex),
                    TransFact::PureCell(lt.clone(), var_term(lv)),
                    TransFact::Fr(vs),
                ],
                vec![],
                vec![
                    lstate(p, &[1], &tx_prime),
                    TransFact::CellLocked(lt, var_term(vs)),
                ],
                vec![],
            );
            // Pure lookups cannot fail; do not translate an unreachable branch.
            Ok((vec![body], tx_prime, None))
        }
        // Classical Lookup (Basetranslation.hs):
        //   let tx' = v `insert` tildex
        //   ([([def_state], [IsIn t v], [def_state1 tx'], []),
        //     ([def_state], [IsNotSet t], [def_state2 tildex], [])],
        //    tx', Just tildex)
        PC::Lookup(t, v) => {
            let lt = to_ln_term(t);
            let lv = v.to_lvar();
            let mut tx_prime = tildex.clone();
            tx_prime.insert(lv);
            let body_in: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![TransAction::IsIn(lt.clone(), lv)],
                vec![lstate(p, &[1], &tx_prime)],
                vec![],
            );
            let body_notset: RuleBody = (
                vec![lstate(p, &[], tildex)],
                vec![TransAction::IsNotSet(lt)],
                vec![lstate(p, &[2], tildex)],
                vec![],
            );
            Ok((vec![body_in, body_notset], tx_prime, Some(tildex.clone())))
        }
        // Strict plans retain shared source continuations. Backwards liveness
        // drops generated intermediates as soon as they are dead, but keeps
        // caller variables through every success/failure boundary.
        PC::Let { left, right, .. } => {
            use crate::annotation::{let_stage_position, LetStage};
            let lhs = to_ln_term(left);
            let mut result_vars = tildex.clone();
            result_vars.extend(ln_term_vars(&lhs));
            let fallback;
            let stages = if an.let_plan.is_empty() {
                fallback = vec![LetStage {
                    input: to_ln_term(right),
                    alternatives: vec![(lhs, None)],
                    bound: result_vars.clone(),
                }];
                &fallback
            } else {
                &an.let_plan
            };
            let mut live = result_vars.clone();
            let mut live_after = vec![BTreeSet::new(); stages.len()];
            for (i, stage) in stages.iter().enumerate().rev() {
                live_after[i] = live.clone();
                live = live.difference(&stage.bound).copied().collect();
                live.extend(ln_term_vars(&stage.input));
            }
            let mut bodies = vec![(
                vec![lstate(p, &[], tildex)],
                vec![],
                vec![TransFact::FLet(
                    let_stage_position(p, 0),
                    stages[0].input.clone(),
                    tildex.clone(),
                )],
                vec![],
            )];
            let mut vars = tildex.clone();
            for (i, stage) in stages.iter().enumerate() {
                let available: BTreeSet<_> = vars.union(&stage.bound).copied().collect();
                let mut next_vars = tildex.clone();
                next_vars.extend(available.intersection(&live_after[i]).copied());
                for (pattern, reduct) in &stage.alternatives {
                    let destination = if let Some(next) = stages.get(i + 1) {
                        TransFact::FLet(
                            let_stage_position(p, i + 1),
                            reduct.as_ref().unwrap_or(&next.input).clone(),
                            next_vars.clone(),
                        )
                    } else {
                        lstate(p, &[1], &result_vars)
                    };
                    let body: RuleBody = (
                        vec![TransFact::FLet(
                            let_stage_position(p, i),
                            pattern.clone(),
                            vars.clone(),
                        )],
                        vec![],
                        vec![destination],
                        vec![],
                    );
                    bodies.push(body);
                }
                if an.else_branch {
                    let failures = stage
                        .alternatives
                        .iter()
                        .map(|(pattern, _)| {
                            let freevars =
                                ln_term_vars(pattern).difference(&vars).copied().collect();
                            let_else_restriction(pattern, &stage.input, &freevars)
                        })
                        .collect();
                    let failure = (
                        vec![TransFact::FLet(
                            let_stage_position(p, i),
                            stage.input.clone(),
                            vars.clone(),
                        )],
                        vec![],
                        vec![lstate(p, &[2], tildex)],
                        failures,
                    );
                    bodies.push(failure);
                }
                vars = next_vars;
            }
            Ok((bodies, result_vars, an.else_branch.then(|| tildex.clone())))
        }
    }
}

/// `mergeWithStateRule' (l',a',r') (l,a,r,f)` (Basetranslation.hs):
/// append the channel facts `(l',a',r')` to a rule body `(l,a,r,f)` ONLY
/// when the rule's premise list `l` contains a `State` fact (`List.find
/// isState l`); otherwise the rule is left unchanged.  `mergeWithStateRule`
/// maps this over a list of rule bodies.
fn merge_with_state_rule(
    extra: (Vec<TransFact>, Vec<TransAction>, Vec<TransFact>),
    rules: Vec<RuleBody>,
) -> Vec<RuleBody> {
    let (extra_l, extra_a, extra_r) = extra;
    rules
        .into_iter()
        .map(|(l, a, r, f)| {
            let has_state = l.iter().any(|fact| matches!(fact, TransFact::State(..)));
            if has_state {
                // HS appends: `(l ++ l', a ++ a', r ++ r', f)`.
                let mut nl = l;
                nl.extend(extra_l.clone());
                let mut na = a;
                na.extend(extra_a.clone());
                let mut nr = r;
                nr.extend(extra_r.clone());
                (nl, na, nr, f)
            } else {
                (l, a, r, f)
            }
        })
        .collect()
}

/// `evalFreshAvoiding (freshLVar name LSortMsg) tildex` (Basetranslation.hs):
/// mint a fresh `LSortMsg` variable named `name` whose index avoids every
/// variable index already present in `tildex`.  HS `avoid` = `maybe 0 (succ .
/// snd) . boundsVarIdx` — i.e. (max index in `tildex`) + 1, or 0 if empty.
fn fresh_msg_var_avoiding(name: &str, tildex: &BTreeSet<LVar>) -> LVar {
    let idx = tildex
        .iter()
        .map(|v| v.idx)
        .max()
        .map(|m| m + 1)
        .unwrap_or(0);
    LVar::new(name, LSort::Msg, idx)
}

/// `freeset = fromList . frees` over an `LNTerm` — its variables.
pub(crate) fn ln_term_vars(t: &LNTerm) -> BTreeSet<LVar> {
    tamarin_term::vterm::vars_vterm(t).into_iter().collect()
}

/// The else-arm restriction for a kept `let` (Basetranslation.hs):
///   `fa  = Conn Imp (Ato (EqE (fmapTerm (fmap Free) t1) (fmapTerm (fmap Free) t2))) (TF False)`
///   `faN = fold (hinted forAll) fa freevars`
/// = `∀ freevars. ((t1 = t2) ⇒ ⊥)`.  `fold` is `Data.Set.fold` (the module
/// imports `Data.Set` unqualified, Basetranslation.hs), which is `foldr`
/// over the ascending set, so the SMALLEST free variable carries the
/// OUTERMOST binder.  `hinted forAll` takes the binder hint from the variable
/// (`hint (LVar n s _) = (n, s)`, Theory/Model/Formula.hs).
fn let_else_restriction(t1: &LNTerm, t2: &LNTerm, freevars: &BTreeSet<LVar>) -> SyntacticLNFormula {
    let eq = ProtoFormula::Atom(ProtoAtom::EqE(lift_free(t1), lift_free(t2)));
    let fa = eq.implies(ProtoFormula::lfalse());
    let vs: Vec<LVar> = freevars.iter().copied().collect();
    quantify_vars(Quantifier::All, &vs, fa)
}

/// `toLNFact (protoFact Linear "Eq" [t1, t2])` (Basetranslation.hs): build
/// the `Eq( t1, t2 )` linear fact over the type-erased terms.
fn eq_fact(t1: &SapicTerm, t2: &SapicTerm) -> tamarin_theory::fact::LNFact {
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    let terms = vec![to_ln_term(t1), to_ln_term(t2)];
    Fact::new(FactTag::Proto(Multiplicity::Linear, "Eq", 2), terms)
}

/// `fromList $ getFactVariables fa` — the set of variables occurring in a fact.
fn fact_vars(f: &tamarin_theory::fact::LNFact) -> BTreeSet<LVar> {
    f.terms()
        .iter()
        .flat_map(tamarin_term::vterm::vars_vterm)
        .collect()
}

/// `throw $ WFUnbound vars` (Basetranslation.hs).  A pure `throw`, so it
/// is raised outside `gen`'s `catch` and the oracle prints it bare.
fn wf_unbound(vars: impl Iterator<Item = LVar>) -> String {
    crate::exceptions::WfError::Unbound(vars.collect()).to_string()
}

/// `baseInit` (Basetranslation.hs): the `Init` rule plus the empty
/// initial `tildex`.
///   `[AnnotatedRule (Just "Init") anP (Right InitPosition) [] [InitEmpty]
///       [State LState [] empty] [] 0]`
pub(crate) fn base_init(
    an_proc: &tamarin_theory::sapic::Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> (Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>) {
    let rule = AnnotatedRule {
        process_name: Some("Init".to_string()),
        process: an_proc.clone(),
        position: RulePosition::Special(SpecialPosition::InitPosition),
        prems: vec![],
        acts: vec![TransAction::InitEmpty],
        concs: vec![TransFact::State(StateKind::LState, vec![], BTreeSet::new())],
        restr: vec![],
        index: 0,
        matches_destructor_equation: false,
    };
    (vec![rule], BTreeSet::new())
}

// =============================================================================
// baseRestr — the hard-coded restrictions (Basetranslation.hs)
// =============================================================================

/// The `single_session` restriction `resSingleSession`
/// (Basetranslation.hs), one of the hard-coded restrictions
/// `baseRestr` assembles (Basetranslation.hs).  The
/// formula body is HS's hardcoded formula.
pub(crate) fn single_session_restriction() -> tamarin_theory::restriction::Restriction {
    use crate::restriction_builder as rb;
    let i = rb::node("i");
    let j = rb::node("j");
    rb::restriction(
        "single_session",
        rb::all(
            &[i, j],
            rb::action("Init", &[], i)
                .and(rb::action("Init", &[], j))
                .implies(rb::eq(i, j)),
        ),
    )
}

/// The two conditional-equality restrictions `resEq` / `resNotEq`
/// (Basetranslation.hs), added by `baseRestr` when the process
/// `contains isEq` (a `CondEq` combinator).  The formula bodies are HS's
/// hardcoded strings, parsed as HS's `toEx`/`parseRestriction` parses them.
pub(crate) fn predicate_restrictions() -> Vec<tamarin_theory::restriction::Restriction> {
    use crate::restriction_builder as rb;
    let i = rb::node("i");
    let a = rb::msg("a");
    let b = rb::msg("b");
    vec![
        rb::restriction(
            "predicate_eq",
            rb::all(
                &[i, a, b],
                rb::action("Pred_Eq", &[a, b], i).implies(rb::eq(a, b)),
            ),
        ),
        rb::restriction(
            "predicate_not_eq",
            rb::all(
                &[i, a, b],
                rb::action("Pred_Not_Eq", &[a, b], i).implies(rb::eq(a, b).not()),
            ),
        ),
    ]
}

/// The `set_in` / `set_notin` restrictions (Basetranslation.hs), added
/// by `baseRestr` when the process `contains isLookup`. `has_delete` selects
/// the full variants (the process also `contains isDelete`) over the
/// NoDelete variants. The builders preserve the binder order and connective
/// associativity of the formulas parsed by Haskell's `toEx`/`parseRestriction`.
pub(crate) fn state_restrictions(
    has_delete: bool,
) -> Vec<tamarin_theory::restriction::Restriction> {
    use crate::restriction_builder as rb;
    let x = rb::msg("x");
    let y = rb::msg("y");
    let yp = rb::msg("yp");
    let t1 = rb::node("t1");
    let t2 = rb::node("t2");
    let t3 = rb::node("t3");

    let later_insert = rb::all(
        &[t1, yp],
        rb::action("Insert", &[x, yp], t1)
            .implies(rb::less(t1, t2).or(rb::eq(t1, t2)).or(rb::less(t3, t1))),
    );
    let mut set_in_body = rb::action("Insert", &[x, y], t2).and(rb::less(t2, t3));
    if has_delete {
        set_in_body = set_in_body.and(rb::all(
            &[t1],
            rb::action("Delete", &[x], t1).implies(rb::less(t1, t2).or(rb::less(t3, t1))),
        ));
    }
    set_in_body = set_in_body.and(later_insert);
    let set_in = rb::restriction(
        "set_in",
        rb::all(
            &[x, y, t3],
            rb::action("IsIn", &[x, y], t3).implies(rb::exists(&[t2], set_in_body)),
        ),
    );

    let future_insert = rb::all(
        &[t1, y],
        rb::action("Insert", &[x, y], t1).implies(rb::less(t3, t1)),
    );
    let set_notin_body = if has_delete {
        future_insert.or(rb::exists(
            &[t1],
            rb::action("Delete", &[x], t1)
                .and(rb::less(t1, t3))
                .and(rb::all(
                    &[t2, y],
                    rb::action("Insert", &[x, y], t2)
                        .and(rb::less(t2, t3))
                        .implies(rb::less(t2, t1)),
                )),
        ))
    } else {
        future_insert
    };
    let set_notin = rb::restriction(
        "set_notin",
        rb::all(
            &[x, t3],
            rb::action("IsNotSet", &[x], t3).implies(set_notin_body),
        ),
    );

    vec![set_in, set_notin]
}

/// The `in_event` restriction `resInEv` (Basetranslation.hs), added by
/// `baseRestr` when `needsInEvRes` (a lemma needs the in-event axiom), built
/// with the binder order and implication structure of Haskell's
/// `parseRestriction` result.
pub(crate) fn in_event_restriction() -> tamarin_theory::restriction::Restriction {
    use crate::restriction_builder as rb;
    let x = rb::msg("x");
    let xp = rb::msg("xp");
    let t1 = rb::node("t1");
    let t2 = rb::node("t2");
    let t3 = rb::node("t3");
    let rhs = rb::action("K", &[x], t2)
        .and(rb::less(t2, t3))
        .and(rb::all(
            &[t1],
            rb::action("Event", &[], t1).implies(rb::less(t1, t2).or(rb::less(t3, t1))),
        ))
        .and(rb::all(
            &[t1, xp],
            rb::action("K", &[xp], t1)
                .implies(rb::less(t1, t2).or(rb::eq(t1, t2)).or(rb::less(t3, t1))),
        ));
    rb::restriction(
        "in_event",
        rb::all(
            &[x, t3],
            rb::action("ChannelIn", &[x], t3).implies(rb::exists(&[t2], rhs)),
        ),
    )
}

// =============================================================================
// resLocking (Basetranslation.hs)
// =============================================================================

/// `resLockingPOS` (Basetranslation.hs): the per-lock locking
/// restriction.  `LockPOS`/`UnlockPOS` are placeholder fact names that
/// `resLocking` rewrites to `Lock_<idx>`/`Unlock_<idx>` for the given lock var.
/// `resLocking hasUnlock v` (Basetranslation.hs): produce the
/// `locking_<idx v>` restriction with `Lock_<idx>`/`Unlock_<idx>` action facts
/// (HS `mapAtoms subst`, with
/// `hardcode s = s ++ "_" ++ show (lvarIdx v)`).
pub(crate) fn res_locking(has_unlock: bool, v: &LVar) -> tamarin_theory::restriction::Restriction {
    use crate::restriction_builder as rb;
    let idx = v.idx;
    let p = rb::msg("p");
    let pp = rb::msg("pp");
    let l = rb::msg("l");
    let lpp = rb::msg("lpp");
    let x = rb::msg("x");
    let lp = rb::msg("lp");
    let t0 = rb::node("t0");
    let t1 = rb::node("t1");
    let t2 = rb::node("t2");
    let t3 = rb::node("t3");
    let lock_pos = format!("Lock_{idx}");
    let unlock_pos = format!("Unlock_{idx}");

    let rhs = if has_unlock {
        let between = rb::action(&unlock_pos, &[p, l, x], t2)
            .and(rb::less(t1, t2))
            .and(rb::less(t2, t3))
            .and(rb::all(
                &[t0, pp],
                rb::action("Unlock", &[pp, l, x], t0).implies(rb::eq(t0, t2)),
            ))
            .and(rb::all(
                &[pp, lpp, t0],
                rb::action("Lock", &[pp, lpp, x], t0)
                    .implies(rb::less(t0, t1).or(rb::eq(t0, t1)).or(rb::less(t2, t0))),
            ))
            .and(rb::all(
                &[pp, lpp, t0],
                rb::action("Unlock", &[pp, lpp, x], t0)
                    .implies(rb::less(t0, t1).or(rb::less(t2, t0)).or(rb::eq(t2, t0))),
            ));
        rb::less(t1, t3)
            .and(rb::exists(&[t2], between))
            .or(rb::less(t3, t1))
            .or(rb::eq(t1, t3))
    } else {
        rb::less(t3, t1).or(rb::eq(t1, t3))
    };
    rb::restriction(
        format!("locking_{idx}"),
        rb::all(
            &[p, pp, l, x, lp, t1, t3],
            rb::action(&lock_pos, &[p, l, x], t1)
                .and(rb::action("Lock", &[pp, lp, x], t3))
                .implies(rhs),
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    /// Direct builders and parsed formulas agree on connective associativity,
    /// quantifier order and shadowed binders in state and locking restrictions.
    #[test]
    fn direct_restriction_builders_match_parsed_formulas() {
        use tamarin_theory::formula::{from_parser, to_lnformula, LNFormula};

        let msig = tamarin_term::maude_sig::pair_maude_sig();
        let lower = |src: &str| -> LNFormula {
            let parsed = tamarin_parser::parser::parse_formula_str(src, &msig)
                .expect("restriction formula parses");
            to_lnformula(&from_parser(&parsed, &msig).expect("restriction lowers"))
                .expect("hard-coded restriction contains no predicate sugar")
        };
        let same = |restriction: tamarin_theory::restriction::Restriction, src: &str| {
            assert_eq!(restriction.formula, lower(src), "{}", restriction.name);
        };

        same(
            single_session_restriction(),
            "All #i #j. Init()@i & Init()@j ==> #i=#j",
        );
        let predicates = predicate_restrictions();
        assert_eq!(
            predicates[0].formula,
            lower("All #i a b. Pred_Eq(a,b)@i ==> a = b")
        );
        assert_eq!(
            predicates[1].formula,
            lower("All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)")
        );

        let with_delete = state_restrictions(true);
        assert_eq!(
            with_delete[0].formula,
            lower(
                "All x y #t3 . IsIn(x,y)@t3 ==>\n\
                 (Ex #t2 . Insert(x,y)@t2 & #t2<#t3\n\
                 & ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 | #t3<#t1))\n\
                 & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1))\n\
                 )"
            )
        );
        assert_eq!(
            with_delete[1].formula,
            lower(
                "All x #t3 . IsNotSet(x)@t3 ==>\n\
                 (All #t1 y . Insert(x,y)@t1 ==> #t3<#t1)\n\
                 | (Ex #t1 . Delete(x)@t1 & #t1<#t3\n\
                 & (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==> #t2<#t1))"
            )
        );

        let without_delete = state_restrictions(false);
        assert_eq!(
            without_delete[0].formula,
            lower(
                "All x y #t3 . IsIn(x,y)@t3 ==>\n\
                 (Ex #t2 . Insert(x,y)@t2 & #t2<#t3\n\
                 & (All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1)))"
            )
        );
        assert_eq!(
            without_delete[1].formula,
            lower(
                "All x #t3 . IsNotSet(x)@t3 ==>\n\
                 (All #t1 y . Insert(x,y)@t1 ==> #t3<#t1)"
            )
        );

        same(
            in_event_restriction(),
            "All x #t3. ChannelIn(x)@t3 ==> (Ex #t2. K(x)@t2 & #t2 < #t3\n\
             & (All #t1. Event()@t1 ==> #t1 < #t2 | #t3 < #t1)\n\
             & (All #t1 xp. K(xp)@t1 ==> #t1 < #t2 | #t1 = #t2 | #t3 < #t1))",
        );

        let lock = LVar::new("lock", LSort::Msg, 7);
        same(
            res_locking(true, &lock),
            "All p pp l x lp #t1 #t3. Lock_7(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>\n\
             (#t1<#t3 & (Ex #t2. Unlock_7(p, l, x)@t2 & #t1 < #t2 & #t2 < #t3\n\
             & (All #t0 pp. Unlock(pp, l, x)@t0 ==> #t0 = #t2)\n\
             & (All pp lpp #t0. Lock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t0 = #t1 | #t2 < #t0)\n\
             & (All pp lpp #t0. Unlock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t2 < #t0 | #t2 = #t0)))\n\
             | #t3<#t1 | #t1=#t3",
        );
        same(
            res_locking(false, &lock),
            "All p pp l x lp #t1 #t3. Lock_7(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>\n\
             #t3<#t1 | #t1=#t3",
        );
    }
}
