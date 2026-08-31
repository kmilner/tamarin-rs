// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Port of `Sapic.ReliableChannelTranslation`
//! (`lib/sapic/src/Sapic/ReliableChannelTranslation.hs`).
//!
//! Reliable (`'r'`) and asynchronous-private (`'c'`) channel handling:
//!   - `reliable_channel_init`  (HS `reliableChannelInit`):  the `MessageIDRule`
//!     that mints `MID_Sender`/`MID_Receiver` facts.
//!   - `reliable_channel_trans_act` (HS `reliableChannelTransAct`):  rewrites
//!     `in('c'/'r', ..)` / `out('c'/'r', ..)` actions into the channel rules.
//!   - `reliable_channel_restr` (HS `reliableChannelRestr`):  the `reliable`
//!     restriction (Send ⇒ later Receive), iff a reliable OUT exists.

use std::collections::BTreeSet;

use tamarin_term::lterm::{LVar, NameTag};
use tamarin_term::vterm::{Lit, VTerm};
use tamarin_theory::restriction::Restriction;
use tamarin_theory::sapic::{
    process_contains, Process, ProcessPosition, SapicAction, SapicLVar, SapicTerm,
};

use crate::annotation::ProcessAnnotation;
use crate::base_translation::{ln_term_vars as freeset, to_ln_term, RuleBody};
use crate::facts::{StateKind, TransAction, TransFact};

type AProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// Whether a SAPIC channel term is the public constant `'<id>'`.
fn pub_name_is(t: &SapicTerm, id: &str) -> bool {
    matches!(
        t,
        VTerm::Lit(Lit::Con(n)) if n.tag == NameTag::Pub && n.id.0 == id
    )
}

/// `reliableChannelInit anP (initrules, initTx)` (ReliableChannelTranslation.hs:27-35):
/// prepend the `MessageIDRule`.
pub(crate) fn reliable_channel_init(
    an_proc: &AProc,
    init_rules: Vec<crate::facts::AnnotatedRule<ProcessAnnotation<LVar>>>,
    init_tx: BTreeSet<LVar>,
) -> (
    Vec<crate::facts::AnnotatedRule<ProcessAnnotation<LVar>>>,
    BTreeSet<LVar>,
) {
    use crate::facts::{AnnotatedRule, RulePosition, SpecialPosition};
    let empty: ProcessPosition = Vec::new();
    let message_id_rule = AnnotatedRule {
        process_name: Some("MessageIDRule".to_string()),
        process: an_proc.clone(),
        position: RulePosition::Special(SpecialPosition::NoPosition),
        prems: vec![TransFact::Fr(crate::facts::var_mid(&empty))],
        acts: vec![],
        concs: vec![
            TransFact::MessageIDReceiver(empty.clone()),
            TransFact::MessageIDSender(empty),
        ],
        restr: vec![],
        index: 0,
    };
    let mut out = vec![message_id_rule];
    out.extend(init_rules);
    (out, init_tx)
}

/// `reliableChannelTransAct tAct ac an p tx` (ReliableChannelTranslation.hs:38-84).
///
/// Returns `Some((rules, tx'))` when the action is a `'c'`/`'r'`-channel
/// in/out (the channel-specific translation overrides the base translation), or
/// an `Err(WFReliable)` for a malformed reliable channel action.  `None` falls
/// through to the base translation (`tAct`).
#[allow(clippy::type_complexity)]
pub(crate) fn reliable_channel_trans_act(
    ac: &SapicAction<SapicLVar>,
    p: &ProcessPosition,
    tx: &BTreeSet<LVar>,
) -> Result<Option<(Vec<RuleBody>, BTreeSet<LVar>)>, String> {
    // `def_state = State LState p tx`; `def_state1 tx' = State LState (p++[1]) tx'`.
    let def_state = || TransFact::State(StateKind::LState, p.clone(), tx.iter().copied().collect());
    let mut p1 = p.clone();
    p1.push(1);
    let def_state1 = |tx2: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p1.clone(), tx2.iter().copied().collect())
    };

    match ac {
        // ChIn (Just 'c') t — async private channel input.
        SapicAction::ChIn {
            chan: Some(v), msg, ..
        } if pub_name_is(v, "c") => {
            let vt = to_ln_term(v);
            let t = to_ln_term(msg);
            // `tx' = freeset v ∪ freeset t ∪ tx`
            let mut tx2 = tx.clone();
            tx2.extend(freeset(&vt));
            tx2.extend(freeset(&t));
            // `ts = fAppPair (v,t)`
            let ts = tamarin_term::builtin::pair(vt.clone(), t.clone());
            let body: RuleBody = (
                vec![def_state(), TransFact::In(ts.clone())],
                vec![TransAction::ChannelIn(ts)],
                vec![def_state1(&tx2)],
                vec![],
            );
            Ok(Some((vec![body], tx2)))
        }
        // ChOut (Just 'c') t — async private channel output.
        SapicAction::ChOut { chan: Some(v), msg } if pub_name_is(v, "c") => {
            let vt = to_ln_term(v);
            let t = to_ln_term(msg);
            let mut tx2 = tx.clone();
            tx2.extend(freeset(&vt));
            tx2.extend(freeset(&t));
            let body: RuleBody = (
                vec![def_state(), TransFact::In(vt.clone())],
                vec![TransAction::ChannelIn(vt)],
                vec![def_state1(&tx2), TransFact::Out(t)],
                vec![],
            );
            Ok(Some((vec![body], tx2)))
        }
        // ChIn (Just 'r') t — reliable channel input.
        SapicAction::ChIn {
            chan: Some(r), msg, ..
        } if pub_name_is(r, "r") => {
            let rt = to_ln_term(r);
            let t = to_ln_term(msg);
            let mut tx2 = tx.clone();
            tx2.extend(freeset(&rt));
            tx2.extend(freeset(&t));
            let body: RuleBody = (
                vec![
                    def_state(),
                    TransFact::In(t.clone()),
                    TransFact::MessageIDReceiver(p.clone()),
                ],
                vec![TransAction::Receive(p.clone(), t)],
                vec![def_state1(&tx2)],
                vec![],
            );
            Ok(Some((vec![body], tx2)))
        }
        // ChOut (Just 'r') t — reliable channel output.
        SapicAction::ChOut { chan: Some(r), msg } if pub_name_is(r, "r") => {
            let rt = to_ln_term(r);
            let t = to_ln_term(msg);
            let mut tx2 = tx.clone();
            tx2.extend(freeset(&rt));
            tx2.extend(freeset(&t));
            let body: RuleBody = (
                vec![TransFact::MessageIDSender(p.clone()), def_state()],
                vec![TransAction::Send(p.clone(), t.clone())],
                vec![TransFact::Out(t), def_state1(&tx2)],
                vec![],
            );
            Ok(Some((vec![body], tx2)))
        }
        // `throwM WFReliable` for every remaining channel action
        // (ReliableChannelTranslation.hs:75-78, four guards with one body): the
        // `'c'`/`'r'` arms above already consumed the well-formed cases.
        SapicAction::ChOut { .. } | SapicAction::ChIn { .. } => {
            Err("process not well-formed: reliable channel".to_string())
        }
        // Otherwise: fall through to the base translation.
        _ => Ok(None),
    }
}

/// `reliableChannelRestr anP restrictions` (ReliableChannelTranslation.hs:103-115):
/// add the `reliable` restriction iff the process contains a reliable OUT.
pub(crate) fn reliable_channel_restr(
    an_proc: &AProc,
    mut restrictions: Vec<Restriction>,
) -> Vec<Restriction> {
    // `isReliableTrans (ProcessAction (ChOut (Just 'r') _) _ _) = True`
    let has_reliable_out = process_contains(an_proc, |proc| {
        matches!(
            proc,
            Process::Action(SapicAction::ChOut { chan: Some(tr), .. }, _, _)
                if pub_name_is(tr, "r")
        )
    });
    if has_reliable_out {
        restrictions.push(res_reliable());
    }
    restrictions
}

/// `resReliable` (ReliableChannelTranslation.hs:97-100):
///   `∀ #i x y. Send(x,y)@#i ⇒ ∃ #j. Receive(x,y)@#j ∧ #i < #j`
fn res_reliable() -> Restriction {
    use crate::restriction_builder as rb;
    let i = rb::node("i");
    let j = rb::node("j");
    let x = rb::msg("x");
    let y = rb::msg("y");
    let body = rb::action("Send", &[x, y], i).implies(rb::exists(
        &[j],
        rb::action("Receive", &[x, y], j).and(rb::less(i, j)),
    ));
    rb::restriction("reliable", rb::all(&[i, x, y], body))
}
