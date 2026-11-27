// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Sapic.Facts` (`lib/sapic/src/Sapic/Facts.hs`) — the
//! translation-specific fact/action types (`TransFact` / `TransAction`), their
//! conversion to real `LNFact`s (`factToFact` / `actionToFact`), the
//! `AnnotatedRule` carrier, and the final `toRule` that produces a
//! `ProtoRuleE` with HS-exact name / color / process / role attributes.

use std::collections::BTreeSet;

use tamarin_term::lterm::{LNTerm, LVar};
use tamarin_term::vterm::var_term;
use tamarin_utils::color::{hsv_to_rgb, rgb_to_hsv, Hsv, Rgb};

use tamarin_theory::fact::{fresh_fact, in_fact, out_fact, proto_fact, LNFact, Multiplicity};
use tamarin_theory::formula::SyntacticLNFormula;
use tamarin_theory::pretty_sapic::pretty_sapic_top_level;
use tamarin_theory::rule::{ProtoRuleE, ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes};
use tamarin_theory::sapic::{
    pretty_position, GoodAnnotation, PlainProcess, Process, ProcessPosition, SapicLVar,
};

use crate::annotation::{to_parsed, ProcessAnnotation};

// =============================================================================
// StateKind (Facts.hs) / TransFact / TransAction
// =============================================================================

// `pub` keeps the dead-code lint off `PState`: HS declares the variant
// (Facts.hs) but never constructs it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateKind {
    LState,
    PState,
    LSemiState,
    PSemiState,
}

impl StateKind {
    /// `isSemiState` (Facts.hs).
    pub(crate) fn is_semi_state(self) -> bool {
        matches!(self, StateKind::LSemiState | StateKind::PSemiState)
    }
    /// `multiplicity` (Facts.hs).
    pub(crate) fn multiplicity(self) -> Multiplicity {
        match self {
            StateKind::LState | StateKind::LSemiState => Multiplicity::Linear,
            StateKind::PState | StateKind::PSemiState => Multiplicity::Persistent,
        }
    }
}

/// `TransFact` (Facts.hs) — premise/conclusion facts.  Every
/// constructor is wired through `factToFact`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TransFact {
    Fr(LVar),
    In(LNTerm),
    Out(LNTerm),
    State(StateKind, ProcessPosition, BTreeSet<LVar>),
    /// A literal user MSR fact (`TamarinFact`).
    TamarinFact(LNFact),
    /// `PureCell t1 t2` (Facts.hs): `L_PureState( t1, t2 )` — the pure-state
    /// cell content (used only when the state-channel optimisation is enabled).
    PureCell(LNTerm, LNTerm),
    /// `CellLocked t1 t2` (Facts.hs): `L_CellLocked( t1, t2 )` — the
    /// pure-state lock token.
    CellLocked(LNTerm, LNTerm),
    /// `FLet p t vars` (Facts.hs): `Let_<pos>( t, v1, .., vn )` — the
    /// intermediate fact a `let` combinator threads its RHS / matched LHS
    /// through (Basetranslation.hs).  `vars` are the bound variables in
    /// scope.
    FLet(ProcessPosition, LNTerm, BTreeSet<LVar>),
    /// `Message t t'` (Facts.hs): `Message( c, m )` — a message in transit
    /// on a private channel (Basetranslation.hs ChIn/ChOut with a channel).
    Message(LNTerm, LNTerm),
    /// `Ack t t'` (Facts.hs): `Ack( c, m )` — the synchronous acknowledgement
    /// for a private-channel message (non-async-channels case).
    Ack(LNTerm, LNTerm),
    /// `MessageIDSender p` (Facts.hs): `MID_Sender( ~mid_<pos> )` — the
    /// reliable-channel sender message-id fact.
    MessageIDSender(ProcessPosition),
    /// `MessageIDReceiver p` (Facts.hs): `MID_Receiver( ~mid_<pos> )` —
    /// the reliable-channel receiver message-id fact.
    MessageIDReceiver(ProcessPosition),
}

/// `TransAction` (Facts.hs) — action facts.  Every constructor is wired
/// through `actionToFact`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TransAction {
    InitEmpty,
    EventEmpty,
    /// A literal user action fact (`TamarinAct`).
    TamarinAct(LNFact),
    /// `PredicateA f` (Facts.hs): renders `f` with its name prefixed by
    /// `Pred_` (used by the positive arm of `if t1 = t2`).
    PredicateA(LNFact),
    /// `NegPredicateA f` (Facts.hs): renders `f` with its name prefixed by
    /// `Pred_Not_` (the negative arm of `if t1 = t2`).
    NegPredicateA(LNFact),
    // --- mutable state (Facts.hs) ---
    /// `IsIn t v` (Facts.hs): `IsIn( t, v )` — the lookup-found action.
    IsIn(LNTerm, LVar),
    /// `IsNotSet t` (Facts.hs): `IsNotSet( t )` — the lookup-not-found action.
    IsNotSet(LNTerm),
    /// `InsertA t1 t2` (Facts.hs): `Insert( t1, t2 )`.
    InsertA(LNTerm, LNTerm),
    /// `DeleteA t` (Facts.hs): `Delete( t )`.
    DeleteA(LNTerm),
    // --- locks (Facts.hs) ---
    /// `LockNamed t v` (Facts.hs): `Lock_<idx v>( '<idx v>', v, t )`.
    LockNamed(LNTerm, LVar),
    /// `LockUnnamed t v` (Facts.hs): `Lock( '<idx v>', v, t )`.
    LockUnnamed(LNTerm, LVar),
    /// `UnlockNamed t v` (Facts.hs): `Unlock_<idx v>( '<idx v>', v, t )`.
    UnlockNamed(LNTerm, LVar),
    /// `UnlockUnnamed t v` (Facts.hs): `Unlock( '<idx v>', v, t )`.
    UnlockUnnamed(LNTerm, LVar),
    /// `ChannelIn t` (Facts.hs): `ChannelIn( t )` — emitted by `in`
    /// actions when the theory has a lemma needing the `in_event` restriction
    /// (`needsAssImmediate`).
    ChannelIn(LNTerm),
    /// `ProgressFrom p` (Facts.hs): `ProgressFrom_<pos>( ~prog_<pos> )`.
    ProgressFrom(ProcessPosition),
    /// `ProgressTo p pf` (Facts.hs): `ProgressTo_<pos>( ~prog_<pf> )` —
    /// the action is named for `p` but carries the progress variable of `pf`
    /// (the inverse position, for verification speedup).
    ProgressTo(ProcessPosition, ProcessPosition),
    /// `Send p t` (Facts.hs): `Send( ~mid_<pos>, t )` — reliable-channel
    /// send action.
    Send(ProcessPosition, LNTerm),
    /// `Receive p t` (Facts.hs): `Receive( ~mid_<pos>, t )` —
    /// reliable-channel receive action.
    Receive(ProcessPosition, LNTerm),
}

/// `SpecialPosition` (Facts.hs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpecialPosition {
    InitPosition,
    NoPosition,
}

/// `Either ProcessPosition SpecialPosition`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum RulePosition {
    Pos(ProcessPosition),
    Special(SpecialPosition),
}

// =============================================================================
// actionToFact (Facts.hs) / factToFact
// =============================================================================

/// `factToFact` (Facts.hs).
pub(crate) fn fact_to_fact(f: &TransFact) -> LNFact {
    match f {
        TransFact::Fr(v) => fresh_fact(var_term(*v)),
        TransFact::In(t) => in_fact(t.clone()),
        TransFact::Out(t) => out_fact(t.clone()),
        TransFact::State(kind, p, vars) => {
            let name = if kind.is_semi_state() {
                "Semistate"
            } else {
                "State"
            };
            let full = format!("{}_{}", name, pretty_position(p));
            let ts: Vec<LNTerm> = vars.iter().copied().map(var_term).collect();
            // multiplicity from the state kind.
            proto_fact_mult(kind.multiplicity(), &full, ts)
        }
        TransFact::TamarinFact(f) => f.clone(),
        TransFact::PureCell(t1, t2) => proto_fact(
            Multiplicity::Linear,
            "L_PureState",
            vec![t1.clone(), t2.clone()],
        ),
        TransFact::CellLocked(t1, t2) => proto_fact(
            Multiplicity::Linear,
            "L_CellLocked",
            vec![t1.clone(), t2.clone()],
        ),
        TransFact::FLet(p, t, vars) => {
            let full = format!("Let_{}", pretty_position(p));
            let mut ts: Vec<LNTerm> = vec![t.clone()];
            ts.extend(vars.iter().copied().map(var_term));
            proto_fact(Multiplicity::Linear, &full, ts)
        }
        TransFact::Message(t1, t2) => proto_fact(
            Multiplicity::Linear,
            "Message",
            vec![t1.clone(), t2.clone()],
        ),
        TransFact::Ack(t1, t2) => {
            proto_fact(Multiplicity::Linear, "Ack", vec![t1.clone(), t2.clone()])
        }
        TransFact::MessageIDSender(p) => proto_fact(
            Multiplicity::Linear,
            "MID_Sender",
            vec![var_term(var_mid(p))],
        ),
        TransFact::MessageIDReceiver(p) => proto_fact(
            Multiplicity::Linear,
            "MID_Receiver",
            vec![var_term(var_mid(p))],
        ),
    }
}

/// `actionToFact` (Facts.hs).
pub(crate) fn action_to_fact(a: &TransAction) -> LNFact {
    match a {
        TransAction::InitEmpty => proto_fact(Multiplicity::Linear, "Init", vec![]),
        TransAction::EventEmpty => proto_fact(Multiplicity::Linear, "Event", vec![]),
        TransAction::TamarinAct(f) => f.clone(),
        TransAction::PredicateA(f) => map_fact_name(f, "Pred_"),
        TransAction::NegPredicateA(f) => map_fact_name(f, "Pred_Not_"),
        TransAction::IsIn(t, v) => {
            proto_fact(Multiplicity::Linear, "IsIn", vec![t.clone(), var_term(*v)])
        }
        TransAction::IsNotSet(t) => proto_fact(Multiplicity::Linear, "IsNotSet", vec![t.clone()]),
        TransAction::InsertA(t1, t2) => {
            proto_fact(Multiplicity::Linear, "Insert", vec![t1.clone(), t2.clone()])
        }
        TransAction::DeleteA(t) => proto_fact(Multiplicity::Linear, "Delete", vec![t.clone()]),
        TransAction::LockNamed(t, v) => proto_fact(
            Multiplicity::Linear,
            &lock_fact_name(v),
            vec![lock_pub_term(v), var_term(*v), t.clone()],
        ),
        TransAction::LockUnnamed(t, v) => proto_fact(
            Multiplicity::Linear,
            "Lock",
            vec![lock_pub_term(v), var_term(*v), t.clone()],
        ),
        TransAction::UnlockNamed(t, v) => proto_fact(
            Multiplicity::Linear,
            &unlock_fact_name(v),
            vec![lock_pub_term(v), var_term(*v), t.clone()],
        ),
        TransAction::UnlockUnnamed(t, v) => proto_fact(
            Multiplicity::Linear,
            "Unlock",
            vec![lock_pub_term(v), var_term(*v), t.clone()],
        ),
        TransAction::ChannelIn(t) => proto_fact(Multiplicity::Linear, "ChannelIn", vec![t.clone()]),
        TransAction::ProgressFrom(p) => proto_fact(
            Multiplicity::Linear,
            &format!("ProgressFrom_{}", pretty_position(p)),
            vec![var_term(var_progress(p))],
        ),
        TransAction::ProgressTo(p, pf) => proto_fact(
            Multiplicity::Linear,
            &format!("ProgressTo_{}", pretty_position(p)),
            vec![var_term(var_progress(pf))],
        ),
        TransAction::Send(p, t) => proto_fact(
            Multiplicity::Linear,
            "Send",
            vec![var_term(var_mid(p)), t.clone()],
        ),
        TransAction::Receive(p, t) => proto_fact(
            Multiplicity::Linear,
            "Receive",
            vec![var_term(var_mid(p)), t.clone()],
        ),
    }
}

/// `varNameProgress p = "prog_" ++ prettyPosition p` (Facts.hs).
pub(crate) fn var_name_progress(p: &ProcessPosition) -> String {
    format!("prog_{}", pretty_position(p))
}

/// `varProgress p = LVar (varNameProgress p) LSortFresh 0` (Facts.hs):
/// the fresh progress variable used in the rule premise/conclusion/action.
pub(crate) fn var_progress(p: &ProcessPosition) -> LVar {
    LVar::new(var_name_progress(p), tamarin_term::lterm::LSort::Fresh, 0)
}

/// `msgVarProgress p = LVar (varNameProgress p) LSortMsg 0` (Facts.hs):
/// the message-sort progress variable used in the progress RESTRICTION
/// quantifier (`∀ prog_<pos>. ..`).
pub(crate) fn msg_var_progress(p: &ProcessPosition) -> LVar {
    LVar::new(var_name_progress(p), tamarin_term::lterm::LSort::Msg, 0)
}

/// `varMID p = LVar ("mid_" ++ prettyPosition p) LSortFresh 0` (Facts.hs).
/// (HS also has the identical `varMsgId`, Facts.hs.)
pub(crate) fn var_mid(p: &ProcessPosition) -> LVar {
    LVar::new(
        format!("mid_{}", pretty_position(p)),
        tamarin_term::lterm::LSort::Fresh,
        0,
    )
}

/// `State LState (p ++ suffix) tx`, the linear state fact Basetranslation.hs
/// calls `def_state` (empty suffix) and `def_state'`/`def_state1`/`def_state2`.
pub(crate) fn lstate(p: &[i64], suffix: &[i64], tx: &BTreeSet<LVar>) -> TransFact {
    TransFact::State(StateKind::LState, [p, suffix].concat(), tx.clone())
}

/// `isNonSemiState` (Facts.hs): a non-semi `State` fact.
pub(crate) fn is_non_semi_state(f: &TransFact) -> bool {
    matches!(f, TransFact::State(kind, _, _) if !kind.is_semi_state())
}

/// `isOutFact` (Facts.hs).
pub(crate) fn is_out_fact(f: &LNFact) -> bool {
    matches!(f.tag, tamarin_theory::fact::FactTag::Out)
}

/// `isLetFact` (Facts.hs): name starts with `Let`.
pub(crate) fn is_let_fact(f: &LNFact) -> bool {
    proto_name_starts_with(f, &["Let"])
}

/// `isStateFact` (Facts.hs): name starts with `State` or `Semistate`.
pub(crate) fn is_state_fact(f: &LNFact) -> bool {
    proto_name_starts_with(f, &["State", "Semistate"])
}

/// `isLockFact` (Facts.hs): name starts with `L_CellLocked`.
pub(crate) fn is_lock_fact(f: &LNFact) -> bool {
    proto_name_starts_with(f, &["L_CellLocked"])
}

/// True when `f` is a proto fact whose name starts with one of `prefixes`.
fn proto_name_starts_with(f: &LNFact, prefixes: &[&str]) -> bool {
    match &f.tag {
        tamarin_theory::fact::FactTag::Proto(_, name, _) => {
            prefixes.iter().any(|p| name.starts_with(p))
        }
        _ => false,
    }
}

/// `addVarToState v' (State kind pos vs) = State kind pos (v' `S.insert` vs)`
/// (Facts.hs): insert a variable into a `State` fact's variable set;
/// other facts unchanged.
pub(crate) fn add_var_to_state(v: &LVar, f: &TransFact) -> TransFact {
    match f {
        TransFact::State(kind, pos, vs) => {
            let mut nvs = vs.clone();
            nvs.insert(*v);
            TransFact::State(*kind, pos.clone(), nvs)
        }
        other => other.clone(),
    }
}

/// `lockFactName v = "Lock_" ++ show (lvarIdx v)` (Facts.hs).
pub(crate) fn lock_fact_name(v: &LVar) -> String {
    format!("Lock_{}", v.idx)
}

/// `unlockFactName v = "Unlock_" ++ show (lvarIdx v)` (Facts.hs).
pub(crate) fn unlock_fact_name(v: &LVar) -> String {
    format!("Unlock_{}", v.idx)
}

/// `lockPubTerm v = pubTerm (show (lvarIdx v))` (Facts.hs): the public
/// constant `'<idx v>'` used as the first argument of the lock/unlock facts.
fn lock_pub_term(v: &LVar) -> LNTerm {
    tamarin_term::lterm::pub_term(v.idx.to_string())
}

/// `mapFactName (prefix ++)` (Facts.hs): prepend `prefix` to a
/// `ProtoFact` name (other tags are left unchanged).
fn map_fact_name(f: &LNFact, prefix: &str) -> LNFact {
    use tamarin_theory::fact::FactTag;
    let tag = match &f.tag {
        FactTag::Proto(m, s, i) => FactTag::Proto(
            *m,
            tamarin_term::intern::intern_str(&format!("{prefix}{s}")),
            *i,
        ),
        other => *other,
    };
    tamarin_theory::fact::Fact::new(tag, f.terms().to_vec()).with_annotations(f.annotations.clone())
}

/// `proto_fact` is fixed to `Linear`; the state fact needs an explicit
/// multiplicity, so build the tag directly.
fn proto_fact_mult(mult: Multiplicity, name: &str, terms: Vec<LNTerm>) -> LNFact {
    use tamarin_theory::fact::{Fact, FactTag};
    Fact::new(
        FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()),
        terms,
    )
}

// =============================================================================
// crc32 / colorForProcessName (Facts.hs)
// =============================================================================

/// `crc32` (Facts.hs).
fn crc32(s: &str) -> u32 {
    fn inner(c: u32) -> u32 {
        (c >> 1) ^ (0xedb8_8329u32 & 0u32.wrapping_sub(c & 1))
    }
    let mut acc: u32 = 0xffff_ffff;
    for ch in s.chars() {
        let m = ch as u32;
        let mut c = acc ^ m;
        for _ in 0..8 {
            c = inner(c);
        }
        acc = c;
    }
    acc
}

/// `colorHash` (Facts.hs): per-channel byte of the CRC, scaled to [0,1].
fn color_hash(s: &str) -> Rgb {
    let h = crc32(s);
    let nth = |n: u32| -> f64 { (((h >> (8 * n)) & 0xff) as f64) / 255.0 };
    Rgb::new(nth(0), nth(1), nth(2))
}

fn interpolate(a: Hsv, b: Hsv, t: f64) -> Hsv {
    Hsv::new(
        (b.h - a.h) * t + a.h,
        (b.s - a.s) * t + a.s,
        (b.v - a.v) * t + a.v,
    )
}

/// `colorForProcessName` (Facts.hs).
pub(crate) fn color_for_process_name(names: &[String]) -> Rgb {
    if names.is_empty() {
        // HS `RGB 255 255 255` — `rgbToHex` clamps `floor(256*255)` to 255 →
        // `#ffffff`.  Mirror with the same out-of-[0,1] value.
        return Rgb::new(255.0, 255.0, 255.0);
    }
    let palette: Vec<Hsv> = names.iter().map(|n| rgb_to_hsv(color_hash(n))).collect();
    let mut acc = palette[0];
    for (i, v) in palette[1..].iter().enumerate() {
        let t = 2f64.powi(-(i as i32));
        acc = interpolate(acc, *v, t);
    }
    // normalize (HSV h _ _) = HSV h 0.5 0.5
    let normalized = Hsv::new(acc.h, 0.5, 0.5);
    hsv_to_rgb(normalized)
}

// =============================================================================
// AnnotatedRule + toRule (Facts.hs)
// =============================================================================

/// `AnnotatedRule` (Facts.hs).  `process` is the subprocess this rule
/// was generated for (used for naming / color / `process=` attribute).
#[derive(Debug, Clone)]
pub(crate) struct AnnotatedRule<Ann> {
    pub process_name: Option<String>,
    pub process: Process<Ann, SapicLVar>,
    pub position: RulePosition,
    pub prems: Vec<TransFact>,
    pub acts: Vec<TransAction>,
    pub concs: Vec<TransFact>,
    /// Embedded restrictions (HS `restr :: [SyntacticLNFormula]`, Facts.hs).
    /// [`to_rule`] stores them as the rule's `_preRestriction`, which the
    /// `_restrict` expansion turns into `Restr_<rule>_<i>` restrictions plus
    /// actions on the rule.
    pub restr: Vec<SyntacticLNFormula>,
    pub matches_destructor_equation: bool,
    pub index: usize,
}

/// `prettyEitherPositionOrSpecial` (Facts.hs).
fn pretty_position_or_special(pos: &RulePosition) -> String {
    match pos {
        RulePosition::Pos(p) => pretty_position(p),
        RulePosition::Special(SpecialPosition::InitPosition) => "Init".to_string(),
        RulePosition::Special(SpecialPosition::NoPosition) => String::new(),
    }
}

/// `getTopLevelName` (Facts.hs) — the process-name list from the
/// (already-name-propagated) annotation of the subprocess.
fn get_top_level_name<Ann: GoodAnnotation>(p: &Process<Ann, SapicLVar>) -> &[String] {
    &p.annotation().parsed().process_names
}

/// `roleFromProcessNameList` (Facts.hs).
fn role_from_process_name_list(names: &[String]) -> String {
    if names.is_empty() {
        "Process".to_string()
    } else {
        names.join("_")
    }
}

/// `stripNonAlphanumerical = filter isAlpha` (Sapic/Facts.hs#stripNonAlphanumerical).
fn strip_non_alphabetic(s: &str) -> String {
    s.chars().filter(|c| c.is_alphabetic()).collect()
}

/// The `Nothing` arm of `toRule`'s `name` (Facts.hs):
/// `unNull (stripNonAlphanumerical (prettySapicTopLevel process)) ++ "_" ++
/// show index ++ "_" ++ prettyEitherPositionOrSpecial position`.
///
/// Takes the already-erased process so [`to_rule`] can share one
/// [`crate::annotation::to_parsed`] with the `process=` attribute it also
/// builds from it.
fn generated_rule_name(plain: &PlainProcess, index: usize, position: &RulePosition) -> String {
    let stripped = strip_non_alphabetic(&pretty_sapic_top_level(plain));
    // `unNull s = if null s then "p" else s`
    let un_null = if stripped.is_empty() { "p" } else { &stripped };
    format!("{un_null}_{index}_{}", pretty_position_or_special(position))
}

/// `toRule` (Facts.hs): build the final `ProtoRuleE` with HS-exact
/// `name`, `color`, `process`, `role`, `issapicrule` attributes.
///
/// `ignoreDerivChecks = isLookup process` (Facts.hs): the lookup rules
/// carry the `no_derivcheck` attribute so the message-derivation check skips
/// them (the bound lookup variable is unconstrained at that point).
pub(crate) fn to_rule(r: AnnotatedRule<ProcessAnnotation<LVar>>) -> ProtoRuleE {
    // Both the generated name and the `process=` attribute read the erased
    // process, so erase once.
    let plain = to_parsed(&r.process);
    let name = match &r.process_name {
        Some(s) => s.clone(),
        None => generated_rule_name(&plain, r.index, &r.position),
    };
    // HS reaches this list twice, as `getTopLevelName process` (for the colour)
    // and as `getProcessNames $ processGetAnnotation process` (for the role);
    // `getTopLevelName` IS that second expression, so one binding serves both.
    let names = get_top_level_name(&r.process);
    // HS `isLookup (ProcessComb (Lookup _ _) _ _ _) = True; isLookup _ = False`
    // (Facts.hs) — the LITERAL process node this rule was generated for.
    let is_lookup_proc = matches!(
        &r.process,
        Process::Comb(
            tamarin_theory::sapic::ProcessCombinator::Lookup(_, _),
            _,
            _,
            _
        )
    );
    let attr = RuleAttributes {
        color: Some(color_for_process_name(names)),
        process: Some(std::sync::Arc::new(
            tamarin_theory::sapic::SharedProcess::new(plain),
        )),
        ignore_deriv_checks: is_lookup_proc || r.matches_destructor_equation,
        is_sapic_rule: true,
        role: Some(role_from_process_name_list(names)),
    };
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(&name)),
        attributes: attr,
        restrictions: r.restr,
    };
    let prems: Vec<LNFact> = r.prems.iter().map(fact_to_fact).collect();
    let acts: Vec<LNFact> = r.acts.iter().map(action_to_fact).collect();
    let concs: Vec<LNFact> = r.concs.iter().map(fact_to_fact).collect();
    // HS `newVariables l r` (Facts.hs): the premises against the
    // conclusions alone — the actions do not contribute new variables here.
    let new_vars = tamarin_theory::fact::new_variables(&prems, &concs);
    Rule::new(info, prems, concs, acts).with_new_vars(new_vars)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The rendered `color=` hex value for a process-name list — what the rule
    /// printer emits for `RuleAttributes::color`.
    fn color_hex_for_process_name(names: &[String]) -> String {
        tamarin_utils::color::rgb_to_hex(color_for_process_name(names))
    }

    #[test]
    fn crc32_known_values() {
        // CRC32 (HS's non-standard 0xedb88329 variant of the reflected CRC32
        // polynomial, matching `crc32` above) of "" is 0xFFFFFFFF before
        // final-xor; HS does NOT apply the final xor, so for the empty string
        // `crc32 "" == 0xffffffff`.  The empty string never enters the digest
        // loop.  The non-empty cases below are therefore the ones that check
        // the polynomial, the `ord` feed for each `Char`, and the 8 bit-steps.
        assert_eq!(crc32(""), 0xffff_ffff);
        // The next two words come from the port itself.  No external
        // reference exists for upstream's 0xedb88329 mistyping of the
        // reflected CRC-32 polynomial.  The test
        // `color_hex_matches_oracle_rule_attribute` corroborates the two
        // words.  Its expectations are oracle bytes, and it consumes bytes 0,
        // 1 and 2 of exactly these words.
        assert_eq!(crc32("A"), 0xe02a_16e8);
        assert_eq!(crc32("B"), 0xc728_5741);
    }

    /// `color=` is a rendered rule attribute, so `colorForProcessName` must
    /// agree with upstream byte for byte.  The values below are oracle bytes
    /// from the pinned build at Git revision ef3f0468.  The input is
    /// `let B = out('t')  let A = B  process: A`:
    ///   `rule (modulo E) A_0_[color=#ffffff, …]`     — no enclosing def
    ///   `rule (modulo E) B_0_1[color=#804046, …]`    — processnames ["A"]
    ///   `rule (modulo E) outt_0_11[color=#628040, …]` — processnames ["A","B"]
    /// `propagate_names` puts the ancestors before a node's own names, so the
    /// innermost rule sees the outer def first.  The case with one name and
    /// the case with two names cover the whole chain: `crc32` → `colorHash` →
    /// `rgbToHsv` → `interpolate` (two names only) → `normalize` →
    /// `hsvToRgb` → `rgbToHex`.
    #[test]
    fn color_hex_matches_oracle_rule_attribute() {
        assert_eq!(color_hex_for_process_name(&[]), "#ffffff");
        assert_eq!(color_hex_for_process_name(&["A".to_string()]), "#804046");
        assert_eq!(
            color_hex_for_process_name(&["A".to_string(), "B".to_string()]),
            "#628040"
        );
        // The interpolation depends on the order.  A swap of the two names
        // gives a different colour, so the code does not treat the list as a
        // set.
        assert_ne!(
            color_hex_for_process_name(&["B".to_string(), "A".to_string()]),
            "#628040"
        );
    }

    /// `toRule` computes `newVariables l r` (Facts.hs): premises against
    /// conclusions alone.  A variable occurring only in an action is not a
    /// new variable of the generated rule; a conclusion-only variable is.
    #[test]
    fn to_rule_new_vars_ignore_action_only_variables() {
        use tamarin_term::lterm::LSort;

        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let z = LVar::new("z", LSort::Msg, 0);
        let r = AnnotatedRule {
            process_name: Some("t".to_string()),
            process: Process::Null(ProcessAnnotation::default()),
            position: RulePosition::Pos(vec![]),
            prems: vec![TransFact::In(var_term(x))],
            acts: vec![TransAction::TamarinAct(proto_fact(
                Multiplicity::Linear,
                "A",
                vec![var_term(y)],
            ))],
            concs: vec![TransFact::Out(var_term(z))],
            restr: Vec::new(),
            index: 0,
            matches_destructor_equation: false,
        };
        let rule = to_rule(r);
        assert_eq!(rule.new_vars, vec![var_term(z)]);
    }
}
