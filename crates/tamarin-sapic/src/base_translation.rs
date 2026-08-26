// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.Basetranslation` (`lib/sapic/src/Sapic/Basetranslation.hs`):
//!   - `baseInit`       (Basetranslation.hs:312-318)
//!   - `baseTransNull`  (Basetranslation.hs:81-82)
//!   - `baseTransAction` (94-214) — every `SapicAction` arm
//!   - `baseTransComb`   (226-306) — every `ProcessCombinator` arm
//!   - the hardcoded restrictions `baseRestr` (449-485) selects from:
//!     `single_session` and `predicate_eq`/`predicate_not_eq` are built
//!     directly as parser-AST restrictions, while `set_in`/`set_notin`,
//!     `in_event` and `locking_<idx>` go through `parse_formula_str` on HS's
//!     verbatim restriction text (as HS's own `toEx`/`parseRestriction` does).
//!
//! `baseRestr`'s selection logic itself lives in `translate`, which owns the
//! process-shape predicates (`contains isLookup` etc.) it dispatches on.

use std::collections::BTreeSet;

use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::vterm::{Lit, VTerm};

use tamarin_theory::atom::ProtoAtom;
use tamarin_theory::formula::{
    for_all_var, formula_frees, lift_free, ProtoFormula, SyntacticLNFormula,
};
use tamarin_theory::sapic::{to_lformula, ProcessPosition, SapicAction, SapicLVar, SapicTerm};

use crate::annotation::ProcessAnnotation;
use crate::facts::{
    AnnotatedRule, RulePosition, SpecialPosition, StateKind, TransAction, TransFact,
};

/// A single translation "rule body": `(prems, acts, concs, restr)`.
/// HS `([TransFact],[TransAction],[TransFact],[SyntacticLNFormula])`; the
/// 4th element carries the rule's embedded restriction formulas.
pub type RuleBody = (
    Vec<TransFact>,
    Vec<TransAction>,
    Vec<TransFact>,
    Vec<SyntacticLNFormula>,
);

/// `baseTransNull` (Basetranslation.hs:81-82):
///   `[([State LState p tildex], [], [], [])]`
pub fn base_trans_null(p: &ProcessPosition, tildex: &BTreeSet<LVar>) -> Vec<RuleBody> {
    let st = TransFact::State(
        StateKind::LState,
        p.clone(),
        tildex.iter().copied().collect(),
    );
    vec![(vec![st], vec![], vec![], vec![])]
}

/// Type-erase: HS works over `LNTerm` (untyped) for the rule facts; the
/// translation calls `toLNTerm` / `toLVar` on SAPIC terms.  Convert a typed
/// SAPIC term to a plain `LNTerm` (drop the type tag).
pub fn to_ln_term(t: &SapicTerm) -> LNTerm {
    match t {
        VTerm::Lit(Lit::Var(sv)) => VTerm::Lit(Lit::Var(sv.var)),
        VTerm::Lit(Lit::Con(c)) => VTerm::Lit(Lit::Con(*c)),
        VTerm::App(sym, args) => {
            let new_args: Vec<LNTerm> = args.iter().map(to_ln_term).collect();
            use tamarin_term::function_symbols::FunSym;
            match sym {
                FunSym::Ac(o) => tamarin_term::term::f_app_ac(*o, new_args),
                FunSym::C(o) => tamarin_term::term::f_app_c(*o, new_args),
                FunSym::NoEq(o) => tamarin_term::term::f_app_no_eq(*o, new_args),
                FunSym::List => tamarin_term::term::f_app_list(new_args),
            }
        }
    }
}

/// `toLNFact` over a SAPIC fact (drop type tags from every term).
pub fn to_ln_fact(f: &tamarin_theory::sapic::SapicLNFact) -> tamarin_theory::fact::LNFact {
    f.map_ref(to_ln_term)
}

/// Apply a SAPIC substitution to a SAPIC term.
pub(crate) fn subst_term(
    subst: &tamarin_term::subst::Subst<tamarin_term::lterm::Name, SapicLVar>,
    t: &SapicTerm,
) -> SapicTerm {
    tamarin_term::subst::apply_vterm(subst, t.clone())
}

/// Apply a SAPIC substitution to a SAPIC fact (tag + annotations preserved).
pub(crate) fn subst_fact(
    subst: &tamarin_term::subst::Subst<tamarin_term::lterm::Name, SapicLVar>,
    f: &tamarin_theory::sapic::SapicLNFact,
) -> tamarin_theory::sapic::SapicLNFact {
    f.map_ref(|t| subst_term(subst, t))
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

/// `toLVar v = slvar v`.
pub fn to_lvar(v: &SapicLVar) -> LVar {
    v.var
}

/// `baseTransAction` (Basetranslation.hs:94-205).  Returns the rule bodies and
/// the updated `tildex`.  `needs_ass_immediate` is the `needsInEvRes` flag;
/// when false, `Event` emits NO extra `EventEmpty` action.
pub fn base_trans_action(
    async_channels: bool,
    needs_ass_immediate: bool,
    ac: &SapicAction<SapicLVar>,
    an: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<(Vec<RuleBody>, BTreeSet<LVar>), String> {
    // `def_state = State LState p tildex`
    let def_state = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p.clone(), tx.iter().copied().collect())
    };
    // `def_state' tx = State LState (p++[1]) tx`
    let mut p1 = p.clone();
    p1.push(1);
    let def_state_next = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p1.clone(), tx.iter().copied().collect())
    };

    match ac {
        // (Rep): replication (Basetranslation.hs:99-102).  Two rules:
        //   [([def_state], [], [State PSemiState (p++[1]) tildex], []),
        //    ([State PSemiState (p++[1]) tildex], [], [def_state' tildex], [])]
        // The first consumes the entering linear state and produces a
        // PERSISTENT semistate (so it can fire arbitrarily often); the second
        // turns each persistent-semistate instance back into a fresh linear
        // `def_state'` for the replicated body.  `tildex` is unchanged.
        SapicAction::Rep => {
            let semistate = TransFact::State(
                StateKind::PSemiState,
                p1.clone(),
                tildex.iter().copied().collect(),
            );
            let body1: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![semistate.clone()],
                vec![],
            );
            let body2: RuleBody = (
                vec![semistate],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body1, body2], tildex.clone()))
        }
        // (New v): `tx' = toLVar v `insert` tildex`
        //   [([def_state, Fr (toLVar v)], [], [def_state' tx'], [])]
        SapicAction::New(v) => {
            let lv = to_lvar(v);
            let mut tx2 = tildex.clone();
            tx2.insert(lv);
            let body: RuleBody = (
                vec![def_state(tildex), TransFact::Fr(lv)],
                vec![],
                vec![def_state_next(&tx2)],
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
                vec![def_state(tildex)],
                acts,
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (ChIn channel t' matchVar) (Basetranslation.hs:105-127): handle channel
        // input `in(c,pat); P` like `in(c,x); let pat = x in P`.  Mint a fresh
        // message variable `x` avoiding `tildex`, build the Let combinator rules
        // for `let pat = x`, then prepend the channel facts via
        // `mergeWithStateRule` (only onto rules that have a State premise).
        SapicAction::ChIn {
            chan,
            msg,
            match_vars,
        } => {
            // `x = evalFreshAvoiding (freshLVar "x" LSortMsg) tildex`.
            let x = fresh_msg_var_avoiding("x", tildex);
            let xt: LNTerm = VTerm::Lit(Lit::Var(x));
            // `xTerm = varTerm (SapicLVar { slvar = x, stype = Nothing })`.
            let x_sapic: SapicTerm = VTerm::Lit(Lit::Var(SapicLVar::untyped(x)));
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
            // `channelIn ts = [ChannelIn ts | needsAssImmediate]`.
            let channel_in = |ts: &LNTerm| -> Vec<TransAction> {
                if needs_ass_immediate {
                    vec![TransAction::ChannelIn(ts.clone())]
                } else {
                    vec![]
                }
            };
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
                            vec![def_state(tildex), TransFact::In(t)],
                            vec![],
                            vec![def_state_next(&tx2)],
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
        // (ChOut (Just tc') t') | secretChannel = Just (AnVar _)
        // (Basetranslation.hs:128-137): the private secret-channel output.
        SapicAction::ChOut {
            chan: Some(tc_term),
            msg,
        } if an.secret_channel.is_some() => {
            let tc = to_ln_term(tc_term);
            let t = to_ln_term(msg);
            if async_channels {
                // `[([def_state], [], [Message tc t, def_state' tildex], [])]`.
                let body: RuleBody = (
                    vec![def_state(tildex)],
                    vec![],
                    vec![TransFact::Message(tc, t), def_state_next(tildex)],
                    vec![],
                );
                Ok((vec![body], tildex.clone()))
            } else {
                // `semistate = State LSemiState (p++[1]) tildex`.
                let semistate = TransFact::State(
                    StateKind::LSemiState,
                    p1.clone(),
                    tildex.iter().copied().collect(),
                );
                let body1: RuleBody = (
                    vec![def_state(tildex)],
                    vec![],
                    vec![TransFact::Message(tc.clone(), t.clone()), semistate.clone()],
                    vec![],
                );
                let body2: RuleBody = (
                    vec![semistate, TransFact::Ack(tc, t)],
                    vec![],
                    vec![def_state_next(tildex)],
                    vec![],
                );
                Ok((vec![body1, body2], tildex.clone()))
            }
        }
        // (ChOut (Just tc') t') | secretChannel = Nothing
        // (Basetranslation.hs:138-149): the public-channel output.
        SapicAction::ChOut {
            chan: Some(tc_term),
            msg,
        } => {
            let tc = to_ln_term(tc_term);
            let t = to_ln_term(msg);
            // The adversary-injected output rule: `([def_state, In tc],
            // channelIn tc, [Out t, def_state' tildex], [])`, with
            // `channelIn tc = [ChannelIn tc | needsAssImmediate]`.
            let in_acts: Vec<TransAction> = if needs_ass_immediate {
                vec![TransAction::ChannelIn(tc.clone())]
            } else {
                vec![]
            };
            let in_rule: RuleBody = (
                vec![def_state(tildex), TransFact::In(tc.clone())],
                in_acts,
                vec![TransFact::Out(t.clone()), def_state_next(tildex)],
                vec![],
            );
            if async_channels {
                let msg_rule: RuleBody = (
                    vec![def_state(tildex)],
                    vec![],
                    vec![TransFact::Message(tc, t), def_state_next(tildex)],
                    vec![],
                );
                Ok((vec![in_rule, msg_rule], tildex.clone()))
            } else {
                let semistate = TransFact::State(
                    StateKind::LSemiState,
                    p1.clone(),
                    tildex.iter().copied().collect(),
                );
                let msg_rule: RuleBody = (
                    vec![def_state(tildex)],
                    vec![],
                    vec![TransFact::Message(tc.clone(), t.clone()), semistate.clone()],
                    vec![],
                );
                let ack_rule: RuleBody = (
                    vec![semistate, TransFact::Ack(tc, t)],
                    vec![],
                    vec![def_state_next(tildex)],
                    vec![],
                );
                Ok((vec![in_rule, msg_rule, ack_rule], tildex.clone()))
            }
        }
        // (ChOut Nothing t): `[([def_state], [], [def_state' tildex, Out t], [])]`
        SapicAction::ChOut { chan: None, msg } => {
            let t = to_ln_term(msg);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex), TransFact::Out(t)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // === Pure cell translation (Basetranslation.hs:155-174) ===
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
                    def_state(tildex),
                    TransFact::CellLocked(lt1.clone(), VTerm::Lit(Lit::Var(v))),
                ],
                vec![],
                vec![def_state_next(&tx2), TransFact::PureCell(lt1, lt2)],
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
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex), TransFact::PureCell(lt1, lt2)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Lock _) | pureState -> silent passthrough.
        //   [([def_state], [], [def_state' tildex], [])]
        SapicAction::Lock(_) if an.pure_state => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Unlock _) | pureState -> silent passthrough.
        SapicAction::Unlock(_) if an.pure_state => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }

        // === Classical state translation (Basetranslation.hs:177-194) ===
        //
        // (Insert t1 t2): `[([def_state], [InsertA t1 t2], [def_state' tildex], [])]`
        SapicAction::Insert(t1, t2) => {
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::InsertA(lt1, lt2)],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Delete t): `[([def_state], [DeleteA t], [def_state' tildex], [])]`
        SapicAction::Delete(t) => {
            let lt = to_ln_term(t);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::DeleteA(lt)],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Lock t) | Just (AnVar v) <- an.lock (Basetranslation.hs:185-189):
        //   let tx' = v `insert` tildex in
        //   [([def_state, Fr v], [LockNamed t v, LockUnnamed t v], [def_state' tx'], [])]
        // (Lock _) | Nothing <- an.lock -> "Unannotated lock" error
        //   (Basetranslation.hs:94-214, see line 190).
        SapicAction::Lock(t) => {
            let Some(an_v) = &an.lock else {
                return Err("baseTransAction: Unannotated lock".to_string());
            };
            let v = an_v.0;
            let lt = to_ln_term(t);
            let mut tx2 = tildex.clone();
            tx2.insert(v);
            let body: RuleBody = (
                vec![def_state(tildex), TransFact::Fr(v)],
                vec![
                    TransAction::LockNamed(lt.clone(), v),
                    TransAction::LockUnnamed(lt, v),
                ],
                vec![def_state_next(&tx2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Unlock t) | Just (AnVar v) <- an.unlock (Basetranslation.hs:191-193):
        //   [([def_state], [UnlockNamed t v, UnlockUnnamed t v], [def_state' tildex], [])]
        // (Unlock _) | Nothing <- an.lock -> "Unannotated unlock" error
        //   (Basetranslation.hs:94-214, see line 194).
        SapicAction::Unlock(t) => {
            let Some(an_v) = &an.unlock else {
                return Err("baseTransAction: Unannotated unlock".to_string());
            };
            let v = an_v.0;
            let lt = to_ln_term(t);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![
                    TransAction::UnlockNamed(lt.clone(), v),
                    TransAction::UnlockUnnamed(lt, v),
                ],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (ProcessCall ..): a pure inlining marker (Basetranslation.hs:204-207).
        //   [([def_state], [], [def_state' tildex], [])]
        // The substituted body that follows the marker carries the real
        // behaviour; this rule just threads the state on by one position.
        SapicAction::ProcessCall(_, _) => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (MSR l' a' r' res' _): an embedded multiset-rewrite rule inside the
        // process (Basetranslation.hs:200-203).  Match-vars are ignored here
        // (they were consumed at parse time).
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
            let mut prems_facts: Vec<TransFact> = vec![def_state(tildex)];
            prems_facts.extend(l.into_iter().map(TransFact::TamarinFact));
            // actions: map TamarinAct a ++ [EventEmpty | needsAss]
            let mut act_facts: Vec<TransAction> =
                a.into_iter().map(TransAction::TamarinAct).collect();
            if needs_ass_immediate {
                act_facts.push(TransAction::EventEmpty);
            }
            // conclusions: def_state' tx' : map TamarinFact r
            let mut conc_facts: Vec<TransFact> = vec![def_state_next(&tx2)];
            conc_facts.extend(r.into_iter().map(TransFact::TamarinFact));
            // restrictions: `map toLFormula res'` (Theory/Sapic/Term.hs:152-154
            // drops the type tags).
            let restr: Vec<SyntacticLNFormula> = rest.iter().map(to_lformula).collect();
            let body: RuleBody = (prems_facts, act_facts, conc_facts, restr);
            Ok((vec![body], tx2))
        }
    }
}

/// The result of translating a combinator: `(rules, tildex_l, Option<tildex_r>)`
/// — HS `TranslationResultComb` (Basetranslation.hs:51-51).  `tildex_r` is `None`
/// when the combinator has no right child to translate (e.g. `let` without an
/// else branch).
pub type CombResult = (Vec<RuleBody>, BTreeSet<LVar>, Option<BTreeSet<LVar>>);

/// `baseTransComb` (Basetranslation.hs:226-306): `Parallel`, `NDC`, `CondEq`,
/// `Cond` (with a formula), `Lookup` and `Let`.
pub fn base_trans_comb(
    c: &tamarin_theory::sapic::ProcessCombinator<SapicLVar>,
    an: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<CombResult, String> {
    use tamarin_theory::sapic::ProcessCombinator as PC;

    // `def_state = State LState p tildex`
    let def_state = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p.clone(), tx.iter().copied().collect())
    };
    // `def_state1 tx = State LState (p++[1]) tx`
    let mut p1 = p.clone();
    p1.push(1);
    let def_state1 = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p1.clone(), tx.iter().copied().collect())
    };
    // `def_state2 tx = State LState (p++[2]) tx`
    let mut p2 = p.clone();
    p2.push(2);
    let def_state2 = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p2.clone(), tx.iter().copied().collect())
    };

    match c {
        // Parallel (Basetranslation.hs:228-230):
        //   ([([def_state], [], [def_state1 tildex, def_state2 tildex], [])],
        //    tildex, Just tildex)
        PC::Parallel => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state1(tildex), def_state2(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone(), Some(tildex.clone())))
        }
        // NDC (Basetranslation.hs:231-233): no rules of its own; both children
        // share the parent's position (handled by `substStatePos` in `gen`).
        //   ([], tildex, Just tildex)
        PC::Ndc => Ok((vec![], tildex.clone(), Some(tildex.clone()))),
        // CondEq (Basetranslation.hs:243-251):
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
                let unbound: Vec<LVar> = vars_f.difference(tildex).copied().collect();
                return Err(format!(
                    "process not well-formed: unbound variables in conditional: {unbound:?}"
                ));
            }
            let body_eq: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::PredicateA(fa.clone())],
                vec![def_state1(tildex)],
                vec![],
            );
            let body_neq: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::NegPredicateA(fa)],
                vec![def_state2(tildex)],
                vec![],
            );
            Ok((
                vec![body_eq, body_neq],
                tildex.clone(),
                Some(tildex.clone()),
            ))
        }
        // Cond f' (Basetranslation.hs:234-242):
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
                let unbound: Vec<LVar> = freevars_f.difference(tildex).copied().collect();
                return Err(format!(
                    "process not well-formed: unbound variables in conditional: {unbound:?}"
                ));
            }
            // then-arm carries `[f]`; else-arm carries `[Not f]`.
            let body_then: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state1(tildex)],
                vec![f.clone()],
            );
            let body_else: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state2(tildex)],
                vec![f.not()],
            );
            Ok((
                vec![body_then, body_else],
                tildex.clone(),
                Some(tildex.clone()),
            ))
        }
        // Pure cell Lookup (Basetranslation.hs:280-289), gated on
        //   pureState && Just (AnVar vs) <- an.unlock:
        //   let tx' = vs `insert` (v `insert` tildex) in
        //   ([([def_state, PureCell t (varTerm v), Fr vs], [],
        //      [def_state1 tx', CellLocked t (varTerm vs)], [])],
        //    tx', Just tildex)
        // (The right `IsNotSet` arm is commented out in HS — pure lookups have a
        // single arm.)
        PC::Lookup(t, v) if an.pure_state && an.unlock.is_some() => {
            let vs = an.unlock.as_ref().unwrap().0;
            let lt = to_ln_term(t);
            let lv = to_lvar(v);
            let mut tx_prime = tildex.clone();
            tx_prime.insert(lv);
            tx_prime.insert(vs);
            let body: RuleBody = (
                vec![
                    def_state(tildex),
                    TransFact::PureCell(lt.clone(), VTerm::Lit(Lit::Var(lv))),
                    TransFact::Fr(vs),
                ],
                vec![],
                vec![
                    def_state1(&tx_prime),
                    TransFact::CellLocked(lt, VTerm::Lit(Lit::Var(vs))),
                ],
                vec![],
            );
            Ok((vec![body], tx_prime, Some(tildex.clone())))
        }
        // Classical Lookup (Basetranslation.hs:293-299):
        //   let tx' = v `insert` tildex
        //   ([([def_state], [IsIn t v], [def_state1 tx'], []),
        //     ([def_state], [IsNotSet t], [def_state2 tildex], [])],
        //    tx', Just tildex)
        PC::Lookup(t, v) => {
            let lt = to_ln_term(t);
            let lv = to_lvar(v);
            let mut tx_prime = tildex.clone();
            tx_prime.insert(lv);
            let body_in: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::IsIn(lt.clone(), lv)],
                vec![def_state1(&tx_prime)],
                vec![],
            );
            let body_notset: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::IsNotSet(lt)],
                vec![def_state2(tildex)],
                vec![],
            );
            Ok((vec![body_in, body_notset], tx_prime, Some(tildex.clone())))
        }
        // Let (Basetranslation.hs:252-277).  Match-vars are ignored in the
        // translation (they are bound in the def_state).  The RHS / matched LHS
        // are threaded through a `Let_<pos>` (FLet) fact:
        //   t1or = toLNTerm left
        //   (t1, t2, freevars) = case an.destructor_equation of
        //       None        -> (t1or, toLNTerm right, frees t1or)
        //       Some(tl1,tl2) -> (tl1, tl2, frees tl1 \ tildex)
        //   fa  = (t1 = t2) ⇒ ⊥          (the else-arm restriction body)
        //   faN = ∀ freevars. fa
        //   tildexl = frees t1or ∪ tildex
        //   pos = p++[1]
        //   if elseBranch:
        //     [ ([def_state], [], [FLet pos t2 tildex], []),
        //       ([FLet pos t1 tildex], [], [def_state1 tildexl], []),
        //       ([FLet pos t2 tildex], [], [def_state2 tildex], [faN]) ],
        //      tildexl, Just tildex
        //   else:
        //     [ ([def_state], [], [FLet pos t2 tildex], []),
        //       ([FLet pos t1 tildex], [], [def_state1 tildexl], []) ],
        //      tildexl, Nothing
        PC::Let { left, right, .. } => {
            let t1or = to_ln_term(left);
            let (t1, t2, freevars): (LNTerm, LNTerm, BTreeSet<LVar>) = match &an.destructor_equation
            {
                None => {
                    let fv = ln_term_vars(&t1or);
                    (t1or.clone(), to_ln_term(right), fv)
                }
                Some((tl1, tl2)) => {
                    let mut fv = ln_term_vars(tl1);
                    for v in tildex {
                        fv.remove(v);
                    }
                    (tl1.clone(), tl2.clone(), fv)
                }
            };
            // `tildexl = frees t1or ∪ tildex`
            let mut tildexl = tildex.clone();
            tildexl.extend(ln_term_vars(&t1or));
            // `faN = ∀ freevars. ((t1 = t2) ⇒ ⊥)`
            let fa_n = let_else_restriction(&t1, &t2, &freevars);
            // `pos = p ++ [1]`
            let pos = p1.clone();
            let body0: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![TransFact::FLet(
                    pos.clone(),
                    t2.clone(),
                    tildex.iter().copied().collect(),
                )],
                vec![],
            );
            let body1: RuleBody = (
                vec![TransFact::FLet(
                    pos.clone(),
                    t1,
                    tildex.iter().copied().collect(),
                )],
                vec![],
                vec![def_state1(&tildexl)],
                vec![],
            );
            if an.else_branch {
                let body2: RuleBody = (
                    vec![TransFact::FLet(pos, t2, tildex.iter().copied().collect())],
                    vec![],
                    vec![def_state2(tildex)],
                    vec![fa_n],
                );
                Ok((vec![body0, body1, body2], tildexl, Some(tildex.clone())))
            } else {
                Ok((vec![body0, body1], tildexl, None))
            }
        }
    }
}

/// `mergeWithStateRule' (l',a',r') (l,a,r,f)` (Basetranslation.hs:84-92):
/// prepend the channel facts `(l',a',r')` onto a rule body `(l,a,r,f)` ONLY
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

/// `evalFreshAvoiding (freshLVar name LSortMsg) tildex` (Basetranslation.hs:94-214, see line 106):
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

/// The else-arm restriction for a kept `let` (Basetranslation.hs:261-263):
///   `fa  = Conn Imp (Ato (EqE (fmapTerm (fmap Free) t1) (fmapTerm (fmap Free) t2))) (TF False)`
///   `faN = fold (hinted forAll) fa freevars`
/// = `∀ freevars. ((t1 = t2) ⇒ ⊥)`.  `fold` is `Data.Set.fold` (the module
/// imports `Data.Set` unqualified, Basetranslation.hs:36), which is `foldr`
/// over the ascending set, so the SMALLEST free variable carries the
/// OUTERMOST binder.  `hinted forAll` takes the binder hint from the variable
/// (`hint (LVar n s _) = (n, s)`, Theory/Model/Formula.hs:227-228).
fn let_else_restriction(t1: &LNTerm, t2: &LNTerm, freevars: &BTreeSet<LVar>) -> SyntacticLNFormula {
    let eq = ProtoFormula::Atom(ProtoAtom::EqE(lift_free(t1), lift_free(t2)));
    let fa = eq.implies(ProtoFormula::lfalse());
    freevars.iter().rev().fold(fa, |body, v| {
        for_all_var((v.name.to_string(), v.sort), v, body)
    })
}

/// `toLNFact (protoFact Linear "Eq" [t1, t2])` (Basetranslation.hs:226-306, see line 244): build
/// the `Eq( t1, t2 )` linear fact over the type-erased terms.
fn eq_fact(t1: &SapicTerm, t2: &SapicTerm) -> tamarin_theory::fact::LNFact {
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    let terms = vec![to_ln_term(t1), to_ln_term(t2)];
    Fact::new(FactTag::Proto(Multiplicity::Linear, "Eq", 2), terms)
}

/// `fromList $ getFactVariables fa` — the set of variables occurring in a fact.
fn fact_vars(f: &tamarin_theory::fact::LNFact) -> BTreeSet<LVar> {
    f.terms
        .iter()
        .flat_map(tamarin_term::vterm::vars_vterm)
        .collect()
}

/// `baseInit` (Basetranslation.hs:312-318): the `Init` rule plus the empty
/// initial `tildex`.
///   `[AnnotatedRule (Just "Init") anP (Right InitPosition) [] [InitEmpty]
///       [State LState [] empty] [] 0]`
pub fn base_init(
    an_proc: &tamarin_theory::sapic::Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> (Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>) {
    let rule = AnnotatedRule {
        process_name: Some("Init".to_string()),
        process: an_proc.clone(),
        position: RulePosition::Special(SpecialPosition::InitPosition),
        prems: vec![],
        acts: vec![TransAction::InitEmpty],
        concs: vec![TransFact::State(StateKind::LState, vec![], vec![])],
        restr: vec![],
        index: 0,
    };
    (vec![rule], BTreeSet::new())
}

// =============================================================================
// baseRestr — the hard-coded restrictions (Basetranslation.hs)
// =============================================================================

/// The `single_session` restriction `resSingleSession`
/// (Basetranslation.hs:361-364), one of the hard-coded restrictions
/// `baseRestr` assembles (Basetranslation.hs:449-479, see line 459).  The
/// formula body is HS's hardcoded string, parsed as HS's
/// `toEx`/`parseRestriction` parses it.
pub fn single_session_restriction() -> tamarin_parser::ast::Restriction {
    parse_restriction("single_session", "All #i #j. Init()@i & Init()@j ==> #i=#j")
}

/// The two conditional-equality restrictions `resEq` / `resNotEq`
/// (Basetranslation.hs:427-436), added by `baseRestr` when the process
/// `contains isEq` (a `CondEq` combinator).  The formula bodies are HS's
/// hardcoded strings, parsed as HS's `toEx`/`parseRestriction` parses them.
pub fn predicate_restrictions() -> Vec<tamarin_parser::ast::Restriction> {
    vec![
        parse_restriction("predicate_eq", "All #i a b. Pred_Eq(a,b)@i ==> a = b"),
        parse_restriction(
            "predicate_not_eq",
            "All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)",
        ),
    ]
}

/// Parse one of the hard-coded restriction strings (`parseRestriction`'s job in
/// HS) and wrap it in a named `Restriction`.  Shared by every hard-coded
/// restriction builder so the parse+panic+wrap shape lives in one place.
///
/// HS `parseRestriction = parseString [] …` (Theory/Text/Parser/Restriction.hs:65-66)
/// and `parseString` seeds the parser state with `pairMaudeSig`
/// (Theory/Text/Parser/Token.hs:250-258), not the theory's signature, so
/// these strings are read against the pair signature alone.
fn parse_restriction(name: &str, src: &str) -> tamarin_parser::ast::Restriction {
    use tamarin_parser::ast as p;
    let formula =
        tamarin_parser::parser::parse_formula_str(src, &tamarin_term::maude_sig::pair_maude_sig())
            .unwrap_or_else(|e| panic!("Error parsing hard-coded restriction {name}: {e:?}"));
    p::Restriction {
        name: name.to_string(),
        formula,
        attributes: vec![],
    }
}

/// The `set_in` / `set_notin` restrictions (Basetranslation.hs:332-359), added
/// by `baseRestr` (449-457) when the process `contains isLookup`.  HS hardcodes
/// these as restriction strings and parses them with `toEx`/`parseRestriction`;
/// we do the same with the RS `parse_formula_str` (so the rendered output is
/// byte-identical to HS's hand-written strings, and AC/sort handling matches the
/// parser path).  `has_delete` selects the full variants (the process also
/// `contains isDelete`) over the NoDelete variants.
pub fn state_restrictions(has_delete: bool) -> Vec<tamarin_parser::ast::Restriction> {
    // `parseRestriction`'s formula body, verbatim from Basetranslation.hs.
    let (set_in_src, set_notin_src) = if has_delete {
        (
            // resSetIn (Basetranslation.hs:333-338)
            "All x y #t3 . IsIn(x,y)@t3 ==>\n\
             (Ex #t2 . Insert(x,y)@t2 & #t2<#t3\n\
             & ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1))\n\
             & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1))\n\
             )",
            // resSetNotIn (Basetranslation.hs:341-345)
            "All x #t3 . IsNotSet(x)@t3 ==>\n\
             (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )\n\
             | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3\n\
             &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))",
        )
    } else {
        (
            // resSetInNoDelete (Basetranslation.hs:349-353)
            "All x y #t3 . IsIn(x,y)@t3 ==>\n\
             (Ex #t2 . Insert(x,y)@t2 & #t2<#t3\n\
             & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1))\n\
             )",
            // resSetNotInNoDelete (Basetranslation.hs:356-358)
            "All x #t3 . IsNotSet(x)@t3 ==>\n\
             (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )",
        )
    };
    vec![
        parse_restriction("set_in", set_in_src),
        parse_restriction("set_notin", set_notin_src),
    ]
}

/// The `in_event` restriction `resInEv` (Basetranslation.hs:439-444), added by
/// `baseRestr` when `needsInEvRes` (a lemma needs the in-event axiom).  As with
/// the other hardcoded restrictions, HS parses the string with
/// `parseRestriction`; we parse the same formula body so the rendered output is
/// byte-identical to HS.
pub fn in_event_restriction() -> tamarin_parser::ast::Restriction {
    let src = "All x #t3. ChannelIn(x)@t3 ==> (Ex #t2. K(x)@t2 & #t2 < #t3\n\
               & (All #t1. Event()@t1  ==> #t1 < #t2 | #t3 < #t1)\n\
               & (All #t1 xp. K(xp)@t1 ==> #t1 < #t2 | #t1 = #t2 | #t3 < #t1))";
    parse_restriction("in_event", src)
}

// =============================================================================
// resLocking (Basetranslation.hs:366-425)
// =============================================================================

/// `resLockingPOS` (Basetranslation.hs:368-376): the per-lock locking
/// restriction.  `LockPOS`/`UnlockPOS` are placeholder fact names that
/// `resLocking` rewrites to `Lock_<idx>`/`Unlock_<idx>` for the given lock var.
const RES_LOCKING_POS: &str = "All p pp l x lp #t1 #t3. LockPOS(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>\n\
        (#t1<#t3 & (Ex #t2. UnlockPOS(p, l, x)@t2 & #t1 < #t2 & #t2 < #t3\n\
                   & (All #t0 pp. Unlock(pp, l, x)@t0 ==> #t0 = #t2)\n\
                   & (All pp lpp #t0. Lock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t0 = #t1 | #t2 < #t0)\n\
                   & (All pp lpp #t0. Unlock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t2 < #t0 | #t2 = #t0 )))\n\
      | #t3<#t1 | #t1=#t3";

/// `resLockingPOSNoUnlock` (Basetranslation.hs:379-383): the locking
/// restriction for a lock with no matching unlock.
const RES_LOCKING_POS_NO_UNLOCK: &str =
    "All p pp l x lp #t1 #t3. LockPOS(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>\n\
        #t3<#t1 | #t1=#t3";

/// `resLocking hasUnlock v` (Basetranslation.hs:406-425): produce the
/// `locking_<idx v>` restriction by parsing `resLockingPOS` (or the NoUnlock
/// variant) and rewriting the `LockPOS`/`UnlockPOS` action facts to
/// `Lock_<idx>`/`Unlock_<idx>` (HS `mapAtoms subst`, with
/// `hardcode s = s ++ "_" ++ show (lvarIdx v)`).
pub fn res_locking(has_unlock: bool, v: &LVar) -> tamarin_parser::ast::Restriction {
    let src = if has_unlock {
        RES_LOCKING_POS
    } else {
        RES_LOCKING_POS_NO_UNLOCK
    };
    let idx = v.idx;
    let mut restr = parse_restriction(&format!("locking_{idx}"), src);
    rename_lock_pos_atoms(&mut restr.formula, idx);
    restr
}

/// HS `subst` inside `resLocking` (Basetranslation.hs:414-422): rewrite the
/// `LockPOS` 3-ary action fact name to `Lock_<idx>` and `UnlockPOS` to
/// `Unlock_<idx>`.  Non-POS `Lock`/`Unlock` facts are left untouched.
fn rename_lock_pos_atoms(f: &mut tamarin_parser::ast::Formula, idx: u64) {
    use tamarin_parser::ast as p;
    fn walk_atom(a: &mut p::Atom, idx: u64) {
        if let p::Atom::Action(fact, _) = a {
            if fact.name == "LockPOS" && fact.args.len() == 3 {
                fact.name = format!("Lock_{idx}");
            } else if fact.name == "UnlockPOS" && fact.args.len() == 3 {
                fact.name = format!("Unlock_{idx}");
            }
        }
    }
    fn walk(f: &mut p::Formula, idx: u64) {
        use p::Formula::*;
        match f {
            True | False => {}
            Atom(a) => walk_atom(a, idx),
            Not(g) => walk(g, idx),
            And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
                walk(a, idx);
                walk(b, idx);
            }
            Forall(_, body) | Exists(_, body) => walk(body, idx),
        }
    }
    walk(f, idx);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;
    use tamarin_theory::sapic::ProcessCombinator;

    fn lv(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }
    fn svar(name: &str) -> SapicTerm {
        VTerm::Lit(Lit::Var(SapicLVar::untyped(lv(name, 0))))
    }

    /// The hard-coded restriction strings lower to the internal formulas the
    /// oracle prints (pinned build ef3f0468; `restriction single_session` /
    /// `predicate_eq` / `predicate_not_eq` blocks of any translated theory).
    /// The unsigiled `@i` references must resolve to the node variables the
    /// `All #i` binders introduce.
    #[test]
    fn hardcoded_restrictions_lower_to_the_oracle_formulas() {
        use tamarin_theory::formula::{from_parser, to_lnformula};
        use tamarin_theory::pretty_formula::pretty_lnformula;
        let msig = tamarin_term::maude_sig::pair_maude_sig();
        let lower = |r: &tamarin_parser::ast::Restriction| {
            pretty_lnformula(&to_lnformula(&from_parser(&r.formula, &msig).unwrap()).unwrap())
        };
        assert_eq!(
            lower(&single_session_restriction()),
            "\u{2200} #i #j. ((Init( ) @ #i) \u{2227} (Init( ) @ #j)) \u{21d2} (#i = #j)"
        );
        let preds = predicate_restrictions();
        assert_eq!(
            preds
                .iter()
                .map(|r| (r.name.as_str(), lower(r)))
                .collect::<Vec<_>>(),
            [
                (
                    "predicate_eq",
                    "\u{2200} #i a b. (Pred_Eq( a, b ) @ #i) \u{21d2} (a = b)".to_string()
                ),
                (
                    "predicate_not_eq",
                    "\u{2200} #i a b. (Pred_Not_Eq( a, b ) @ #i) \u{21d2} (\u{ac}(a = b))"
                        .to_string()
                ),
            ]
        );
    }

    #[test]
    fn rep_emits_two_rules_with_persistent_semistate() {
        // pos = [1], tildex = {}.  baseTransAction Rep:
        //   [([State LState [1] {}], [], [State PSemiState [1,1] {}], []),
        //    ([State PSemiState [1,1] {}], [], [State LState [1,1] {}], [])]
        let an = ProcessAnnotation::<LVar>::empty();
        let p = vec![1i64];
        let tx = BTreeSet::new();
        let (bodies, tx2) =
            base_trans_action(false, false, &SapicAction::Rep, &an, &p, &tx).unwrap();
        assert_eq!(bodies.len(), 2);
        assert_eq!(tx2, tx); // tildex unchanged
                             // First rule conclusion is a PERSISTENT semistate at [1,1].
        let (_, _, concs0, _) = &bodies[0];
        match &concs0[0] {
            TransFact::State(kind, pos, _) => {
                assert!(kind.is_semi_state());
                assert_eq!(
                    kind.multiplicity(),
                    tamarin_theory::fact::Multiplicity::Persistent
                );
                assert_eq!(pos, &vec![1, 1]);
            }
            _ => panic!("expected semistate conclusion"),
        }
        // Second rule premise is that same persistent semistate.
        let (prems1, _, concs1, _) = &bodies[1];
        assert!(matches!(&prems1[0], TransFact::State(k, _, _) if k.is_semi_state()));
        // ...and its conclusion is the linear def_state' at [1,1].
        match &concs1[0] {
            TransFact::State(kind, pos, _) => {
                assert!(!kind.is_semi_state());
                assert_eq!(pos, &vec![1, 1]);
            }
            _ => panic!("expected linear def_state' conclusion"),
        }
    }

    #[test]
    fn parallel_splits_into_two_states() {
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let tx = BTreeSet::new();
        let (bodies, txl, txr) =
            base_trans_comb(&ProcessCombinator::Parallel, &an, &p, &tx).unwrap();
        assert_eq!(bodies.len(), 1);
        assert_eq!(txl, tx);
        assert_eq!(txr, Some(tx));
        let (_, _, concs, _) = &bodies[0];
        // Two conclusions: State_1 and State_2.
        assert_eq!(concs.len(), 2);
        assert!(matches!(&concs[0], TransFact::State(_, p, _) if p == &vec![1]));
        assert!(matches!(&concs[1], TransFact::State(_, p, _) if p == &vec![2]));
    }

    #[test]
    fn ndc_emits_no_rule() {
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let tx = BTreeSet::new();
        let (bodies, txl, txr) = base_trans_comb(&ProcessCombinator::Ndc, &an, &p, &tx).unwrap();
        assert!(bodies.is_empty());
        assert_eq!(txl, tx);
        assert_eq!(txr, Some(tx));
    }

    #[test]
    fn condeq_emits_pred_and_negpred_arms() {
        // tildex must contain a and b for the wellformedness check to pass.
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let mut tx = BTreeSet::new();
        tx.insert(lv("a", 0));
        tx.insert(lv("b", 0));
        let c = ProcessCombinator::CondEq(svar("a"), svar("b"));
        let (bodies, _, _) = base_trans_comb(&c, &an, &p, &tx).unwrap();
        assert_eq!(bodies.len(), 2);
        // Arm 0: PredicateA, conclusion State_1; arm 1: NegPredicateA, State_2.
        let (_, acts0, concs0, _) = &bodies[0];
        assert!(matches!(&acts0[0], TransAction::PredicateA(_)));
        assert!(matches!(&concs0[0], TransFact::State(_, p, _) if p == &vec![1]));
        let (_, acts1, concs1, _) = &bodies[1];
        assert!(matches!(&acts1[0], TransAction::NegPredicateA(_)));
        assert!(matches!(&concs1[0], TransFact::State(_, p, _) if p == &vec![2]));
    }

    #[test]
    fn condeq_unbound_var_errors() {
        // tildex is empty, so a and b are unbound.  The result is a
        // WFUnbound error that names both of them.  The failure therefore
        // comes from the unbound-variable check and not from another
        // rejection.
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let tx = BTreeSet::new();
        let c = ProcessCombinator::CondEq(svar("a"), svar("b"));
        let err = base_trans_comb(&c, &an, &p, &tx).unwrap_err();
        assert!(err.contains('a') && err.contains('b'), "got {err}");
        // When both variables are bound, the same combinator translates.
        let mut tx2 = BTreeSet::new();
        tx2.insert(lv("a", 0));
        tx2.insert(lv("b", 0));
        assert!(base_trans_comb(&c, &an, &p, &tx2).is_ok());
    }

    /// A bare token naming a declared 0-arity function symbol is a CONSTANT in
    /// the conditional, not a free variable, so it never trips `WFUnbound`.
    /// HS's term parser resolves it against the signature while parsing
    /// (`nullaryApp`), leaving an `FApp` leaf that `freesList` ignores.
    ///
    /// Oracle bytes (pinned build, Git revision ef3f0468): `functions: nil/0` +
    /// `predicates: Eq(a, b) <=> a = b` +
    /// `in(k); if Eq(nil, k) then out('yes') else out('no')` LOADS, emitting
    /// `process="if Eq( nil, k.1 )"`.
    #[test]
    fn cond_nullary_constant_is_not_an_unbound_var() {
        let cond = |decl: &str| {
            let thy =
                tamarin_parser::parse_theory(&format!("theory T begin\n{decl}\nend"), &[]).unwrap();
            let msig = tamarin_theory::elaborate::elaborate(&thy)
                .unwrap()
                .signature
                .maude_sig;
            // `Eq(nil, k)` — the predicate atom the surface `if Eq(nil, k)`
            // parses to.
            let f = tamarin_parser::parser::parse_formula_str("Eq(nil, k)", &msig).unwrap();
            ProcessCombinator::Cond(tamarin_theory::formula::sapic_from_parser(&f, &msig).unwrap())
        };
        let an = ProcessAnnotation::<LVar>::empty();
        let pos: Vec<i64> = vec![];
        // tildex binds only `k`.
        let mut tx = BTreeSet::new();
        tx.insert(lv("k", 0));

        // Undeclared, `nil` is an ordinary variable and is (correctly)
        // unbound — this is what makes the assertion below discriminating.
        let err = base_trans_comb(&cond(""), &an, &pos, &tx).unwrap_err();
        assert!(
            err.contains("nil"),
            "expected WFUnbound over nil, got {err}"
        );

        let (bodies, txl, txr) =
            base_trans_comb(&cond("functions: nil/0"), &an, &pos, &tx).unwrap();
        assert_eq!(bodies.len(), 2);
        assert_eq!(txl, tx);
        assert_eq!(txr, Some(tx));
    }

    /// `faN = fold (hinted forAll) fa freevars` (Basetranslation.hs:261-263).
    /// `fold` is `Data.Set.fold` = `foldr` over the ASCENDING set, so the
    /// smallest free variable is the last binder applied and therefore the
    /// OUTERMOST one, while the largest sits next to the body and carries De
    /// Bruijn index 0.
    #[test]
    fn let_else_restriction_binds_the_smallest_free_variable_outermost() {
        use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
        use tamarin_term::lterm::BVar;
        use tamarin_term::term::f_app_no_eq;
        use tamarin_term::vterm::var_term;
        use tamarin_theory::formula::{Connective, Quantifier};

        let x = lv("x", 0);
        let y = lv("y", 0);
        let pair = NoEqSym::new(
            b"pair".to_vec(),
            2,
            Privacy::Public,
            Constructability::Constructor,
        );
        // `<y, x>`: the two variables occur in the order that is NOT the set
        // order, so the assertion below reads the binder depth and not the
        // argument position.
        let t1: LNTerm = f_app_no_eq(pair, vec![var_term(y), var_term(x)]);
        let t2: LNTerm = tamarin_term::lterm::pub_term("c");
        let fv: BTreeSet<LVar> = [x, y].into_iter().collect();

        let f = let_else_restriction(&t1, &t2, &fv);

        let ProtoFormula::Qua(Quantifier::All, outer, body) = &f else {
            panic!("expected a universal binder, got {f:?}");
        };
        assert_eq!(outer, &("x".to_string(), LSort::Msg));
        let ProtoFormula::Qua(Quantifier::All, inner, body) = body.as_ref() else {
            panic!("expected a second universal binder, got {body:?}");
        };
        assert_eq!(inner, &("y".to_string(), LSort::Msg));
        let ProtoFormula::Conn(Connective::Imp, lhs, rhs) = body.as_ref() else {
            panic!("expected `(t1 = t2) ⇒ ⊥`, got {body:?}");
        };
        assert_eq!(**rhs, ProtoFormula::lfalse());
        let ProtoFormula::Atom(ProtoAtom::EqE(a, b)) = lhs.as_ref() else {
            panic!("expected the equality atom, got {lhs:?}");
        };
        // `y` is the inner binder, so it is `Bound(0)`; `x` is one binder
        // further out.
        assert_eq!(
            *a,
            f_app_no_eq(
                pair,
                vec![var_term(BVar::Bound(0)), var_term(BVar::Bound(1))]
            )
        );
        assert_eq!(*b, lift_free(&t2));
    }

    /// A quantifier binder in a SAPIC condition is read by `sapicvar` and
    /// carries no type tag (Theory/Text/Parser/Token.hs:506-510#sapicvar),
    /// while a timepoint operand is read by `sapicnodevar` and is tagged
    /// `node` (Theory/Text/Parser/Token.hs:522-525#sapicnodevar,
    /// Theory/Sapic/Term.hs:99-100#defaultSapicNodeType).  `quantify`
    /// compares the WHOLE variable (Theory/Model/Formula.hs:346-352), so the
    /// binder closes nothing and the timepoint reaches the `⊆ tildex` check.
    ///
    /// Oracle (pinned build, Git revision ef3f0468) on
    /// `in(x); event Foo(x); if (Ex #j. Foo(x)@#j) then out('yes') else out('no')`:
    /// `tamarin-prover: The variable(s) #j are not bound.`, exit 1
    /// (probe `S2_cond_quantified_timepoint`).
    #[test]
    fn a_quantified_timepoint_in_a_cond_is_not_bound_by_its_binder() {
        let msig = tamarin_term::maude_sig::pair_maude_sig();
        let cond = |src: &str| {
            let f = tamarin_parser::parser::parse_formula_str(src, &msig).unwrap();
            ProcessCombinator::Cond(tamarin_theory::formula::sapic_from_parser(&f, &msig).unwrap())
        };
        let an = ProcessAnnotation::<LVar>::empty();
        let pos: Vec<i64> = vec![];
        // tildex binds only `x`.
        let mut tx = BTreeSet::new();
        tx.insert(lv("x", 0));

        // A message binder does close its occurrences — both the binder and
        // the occurrence take `sapicvar`.  That is what makes the assertion
        // below discriminating.
        assert!(base_trans_comb(&cond("Ex y. Eq(y, x)"), &an, &pos, &tx).is_ok());

        let err = base_trans_comb(&cond("Ex #j. Foo(x) @ #j"), &an, &pos, &tx).unwrap_err();
        assert!(
            err.contains("name: \"j\"") && err.contains("Node"),
            "expected the timepoint to stay free, got {err}"
        );
    }

    // A user-`[AC]` symbol prints INFIX, as HS `prettyTerm` renders it
    // (Term/Term.hs:305): the translation's restriction bodies carry these
    // terms into emitted bytes, so a prefix `add(…)` here would diverge from
    // the oracle in both the rendered predicate and the derived
    // rule/restriction names.  No corpus theory combines SAPIC with a user
    // `[AC]` symbol, so this shape is only pinned here.
    #[test]
    fn user_ac_terms_print_infix() {
        use tamarin_term::function_symbols::{AcFctSym, Constructability, NdcState, Privacy};
        use tamarin_term::pretty::pretty_nterm;
        use tamarin_term::term::f_app_acfct;

        let add = AcFctSym::new(
            b"add".to_vec(),
            Privacy::Public,
            Constructability::Constructor,
            NdcState::NotNdc,
        );
        let leaf = |n: &str| tamarin_term::term::Term::Lit(Lit::Var(lv(n, 0)));

        for arity in [2usize, 3] {
            let t = f_app_acfct(add, (0..arity).map(|i| leaf(&format!("x{i}"))).collect());
            // Read the expectation off the smart constructor's own
            // (flattened, sorted) argument list so the test pins the infix
            // spelling, not the AC argument order.
            let tamarin_term::term::Term::App(_, args) = &t else {
                panic!("f_app_acfct built a non-App term");
            };
            assert_eq!(args.len(), arity);
            let operands: Vec<String> = args.iter().map(|a| pretty_nterm(a).render()).collect();
            assert_eq!(
                pretty_nterm(&t).render(),
                format!("({})", operands.join(" add "))
            );
        }
    }

    /// The terms the SAPIC translation builds print through HS `prettyTerm`,
    /// so `exp` comes out infix and a `pair` chain is split down the RIGHT
    /// spine only (Term/Term.hs:310,313,323-324).  Both shapes reach emitted
    /// bytes through `let_else_restriction`: on
    /// `let <x, y> = <'g'^k, <<'a','b'>,'c'>> in … else …` the pinned oracle
    /// (ef3f0468) renders the generated action as
    /// `Restr_letxygkabc_2_1_1( <'g'^k.1, <'a', 'b'>, 'c'> )`.
    #[test]
    fn exp_and_nested_pairs_print_like_prettyterm() {
        use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
        use tamarin_term::pretty::pretty_nterm;
        use tamarin_term::term::{f_app_list, f_app_no_eq, Term as TTerm};

        let sym = |n: &[u8], k| {
            NoEqSym::new(
                n.to_vec(),
                k,
                Privacy::Public,
                Constructability::Constructor,
            )
        };
        let leaf = |n: &str| TTerm::Lit(Lit::Var(lv(n, 0)));
        let pair = |a: LNTerm, b: LNTerm| f_app_no_eq(sym(b"pair", 2), vec![a, b]);
        let render = |t: &LNTerm| pretty_nterm(t).render();

        // `exp(a, b)` is the infix `a^b`, not a prefix application.
        let e = f_app_no_eq(sym(b"exp", 2), vec![leaf("a"), leaf("b")]);
        assert_eq!(render(&e), "a^b");

        // `<'g'^k, <<'a','b'>,'c'>>` = pair(exp, pair(pair(a,b), c)): the right
        // spine flattens, the LEFT-nested inner pair stays a 2-tuple.
        let inner = pair(pair(leaf("a"), leaf("b")), leaf("c"));
        assert_eq!(render(&pair(e.clone(), inner.clone())), "<a^b, <a, b>, c>");
        assert_eq!(render(&inner), "<<a, b>, c>");

        // `List` is HS `ppFun "LIST" ts` (Term/Term.hs:317), not a tuple.
        assert_eq!(
            render(&f_app_list(vec![leaf("a"), leaf("b")])),
            "LIST(a, b)"
        );
    }
}
