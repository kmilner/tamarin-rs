// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, rkunnema, jdreier, kevinmorio, charlie-j, arcz, yavivanov,
//   Hong-Thai, beschmi, PhilipLukertWork, rsasse, ValentinYuri,
//   xaDxelA, and other minor contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/Basetranslation.hs,
//   lib/sapic/src/Sapic/Facts.hs, lib/theory/src/Rule.hs,
//   lib/theory/src/Theory/Model/Rule.hs,
//   lib/theory/src/Theory/Text/Parser/Rule.hs

//! Port of `Sapic.Facts` (`lib/sapic/src/Sapic/Facts.hs`) — the
//! translation-specific fact/action types (`TransFact` / `TransAction`), their
//! conversion to real `LNFact`s (`factToFact` / `actionToFact`), the
//! `AnnotatedRule` carrier, and the final `toRule` that produces a
//! `ProtoRuleE` with HS-exact name / color / process / role attributes.

use tamarin_term::lterm::{LVar, LNTerm};
use tamarin_term::vterm::{Lit, VTerm};
use tamarin_utils::color::{rgb_to_hex, rgb_to_hsv, hsv_to_rgb, Hsv, Rgb};

use tamarin_theory::fact::{proto_fact, fresh_fact, out_fact, in_fact, LNFact, Multiplicity};
use tamarin_theory::rule::{ProtoRuleE, ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes};
use tamarin_theory::sapic::{
    pretty_position, GoodAnnotation, PlainProcess, Process, ProcessPosition, SapicLVar,
};
use tamarin_theory::pretty_sapic::pretty_sapic_top_level;

use crate::annotation::ProcessAnnotation;

// =============================================================================
// StateKind / TransFact / TransAction (Facts.hs:90-127, 53-77)
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateKind {
    LState,
    PState,
    LSemiState,
    PSemiState,
}

impl StateKind {
    /// `isSemiState` (Facts.hs:147-151).
    pub fn is_semi_state(self) -> bool {
        matches!(self, StateKind::LSemiState | StateKind::PSemiState)
    }
    /// `multiplicity` (Facts.hs:153-157).
    pub fn multiplicity(self) -> Multiplicity {
        match self {
            StateKind::LState | StateKind::LSemiState => Multiplicity::Linear,
            StateKind::PState | StateKind::PSemiState => Multiplicity::Persistent,
        }
    }
}

/// `TransFact` (Facts.hs:96-108) — premise/conclusion facts.  Every
/// constructor is wired through `factToFact`.
#[derive(Debug, Clone, PartialEq)]
pub enum TransFact {
    Fr(LVar),
    In(LNTerm),
    Out(LNTerm),
    State(StateKind, ProcessPosition, Vec<LVar>),
    /// A literal user MSR fact (`TamarinFact`).
    TamarinFact(LNFact),
    /// `PureCell t1 t2` (Facts.hs:96-109, see line 108): `L_PureState( t1, t2 )` — the pure-state
    /// cell content (used only when the state-channel optimisation is enabled).
    PureCell(LNTerm, LNTerm),
    /// `CellLocked t1 t2` (Facts.hs:96-109, see line 109): `L_CellLocked( t1, t2 )` — the
    /// pure-state lock token.
    CellLocked(LNTerm, LNTerm),
    /// `FLet p t vars` (Facts.hs:96-109, see line 100): `Let_<pos>( t, v1, .., vn )` — the
    /// intermediate fact a `let` combinator threads its RHS / matched LHS
    /// through (Basetranslation.hs:252-277).  `vars` are the bound variables in
    /// scope (rendered sorted, like `State`).
    FLet(ProcessPosition, LNTerm, Vec<LVar>),
    /// `Message t t'` (Facts.hs:96-109, see line 101): `Message( c, m )` — a message in transit
    /// on a private channel (Basetranslation.hs ChIn/ChOut with a channel).
    Message(LNTerm, LNTerm),
    /// `Ack t t'` (Facts.hs:96-109, see line 102): `Ack( c, m )` — the synchronous acknowledgement
    /// for a private-channel message (non-async-channels case).
    Ack(LNTerm, LNTerm),
    /// `MessageIDSender p` (Facts.hs:96-109, see line 104, 262): `MID_Sender( ~mid_<pos> )` — the
    /// reliable-channel sender message-id fact.
    MessageIDSender(ProcessPosition),
    /// `MessageIDReceiver p` (Facts.hs:96-109, see line 105, 263): `MID_Receiver( ~mid_<pos> )` —
    /// the reliable-channel receiver message-id fact.
    MessageIDReceiver(ProcessPosition),
}

/// `TransAction` (Facts.hs:43-77) — action facts.  Every constructor is wired
/// through `actionToFact`.
#[derive(Debug, Clone, PartialEq)]
pub enum TransAction {
    InitEmpty,
    EventEmpty,
    /// A literal user action fact (`TamarinAct`).
    TamarinAct(LNFact),
    /// `PredicateA f` (Facts.hs:55-81, see line 74): renders `f` with its name prefixed by
    /// `Pred_` (used by the positive arm of `if t1 = t2`).
    PredicateA(LNFact),
    /// `NegPredicateA f` (Facts.hs:55-81, see line 75): renders `f` with its name prefixed by
    /// `Pred_Not_` (the negative arm of `if t1 = t2`).
    NegPredicateA(LNFact),
    // --- mutable state (Facts.hs) ---
    /// `IsIn t v` (Facts.hs:213-234, see line 220): `IsIn( t, v )` — the lookup-found action.
    IsIn(LNTerm, LVar),
    /// `IsNotSet t` (Facts.hs:213-234, see line 221): `IsNotSet( t )` — the lookup-not-found action.
    IsNotSet(LNTerm),
    /// `InsertA t1 t2` (Facts.hs:213-234, see line 222): `Insert( t1, t2 )`.
    InsertA(LNTerm, LNTerm),
    /// `DeleteA t` (Facts.hs:213-234, see line 223): `Delete( t )`.
    DeleteA(LNTerm),
    // --- locks (Facts.hs) ---
    /// `LockNamed t v` (Facts.hs:213-234, see line 228): `Lock_<idx v>( '<idx v>', v, t )`.
    LockNamed(LNTerm, LVar),
    /// `LockUnnamed t v` (Facts.hs:213-234, see line 229): `Lock( '<idx v>', v, t )`.
    LockUnnamed(LNTerm, LVar),
    /// `UnlockNamed t v` (Facts.hs:213-234, see line 230): `Unlock_<idx v>( '<idx v>', v, t )`.
    UnlockNamed(LNTerm, LVar),
    /// `UnlockUnnamed t v` (Facts.hs:213-234, see line 231): `Unlock( '<idx v>', v, t )`.
    UnlockUnnamed(LNTerm, LVar),
    /// `ChannelIn t` (Facts.hs:55-81, see line 69, 224): `ChannelIn( t )` — emitted by `in`
    /// actions when the theory has a lemma needing the `in_event` restriction
    /// (`needsAssImmediate`).
    ChannelIn(LNTerm),
    /// `ProgressFrom p` (Facts.hs:55-81, see line 77, 232): `ProgressFrom_<pos>( ~prog_<pos> )`.
    ProgressFrom(ProcessPosition),
    /// `ProgressTo p pf` (Facts.hs:55-81, see line 78, 233): `ProgressTo_<pos>( ~prog_<pf> )` —
    /// the action is named for `p` but carries the progress variable of `pf`
    /// (the inverse position, for verification speedup).
    ProgressTo(ProcessPosition, ProcessPosition),
    /// `Send p t` (Facts.hs:55-81, see line 80, 218): `Send( ~mid_<pos>, t )` — reliable-channel
    /// send action.
    Send(ProcessPosition, LNTerm),
    /// `Receive p t` (Facts.hs:55-81, see line 81, 219): `Receive( ~mid_<pos>, t )` —
    /// reliable-channel receive action.
    Receive(ProcessPosition, LNTerm),
}

/// `SpecialPosition` (Facts.hs:110-112).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialPosition {
    InitPosition,
    NoPosition,
}

/// `Either ProcessPosition SpecialPosition`.
#[derive(Debug, Clone, PartialEq)]
pub enum RulePosition {
    Pos(ProcessPosition),
    Special(SpecialPosition),
}

// =============================================================================
// State variable set: HS stores `tildex` as a `Set LVar`; `factToFact`
// renders it via `S.toList` (sorted, deduplicated).  We model it as a sorted,
// deduped `Vec<LVar>` to match the rendered order.
// =============================================================================

fn sorted_unique(mut vs: Vec<LVar>) -> Vec<LVar> {
    vs.sort();
    vs.dedup();
    vs
}

// =============================================================================
// factToFact / actionToFact (Facts.hs:213-271)
// =============================================================================

/// `factToFact` (Facts.hs:253-271).
pub fn fact_to_fact(f: &TransFact) -> LNFact {
    match f {
        TransFact::Fr(v) => fresh_fact(VTerm::Lit(Lit::Var(v.clone()))),
        TransFact::In(t) => in_fact(t.clone()),
        TransFact::Out(t) => out_fact(t.clone()),
        TransFact::State(kind, p, vars) => {
            let name = if kind.is_semi_state() { "Semistate" } else { "State" };
            let full = format!("{}_{}", name, pretty_position(p));
            let ts: Vec<LNTerm> = sorted_unique(vars.clone())
                .into_iter()
                .map(|v| VTerm::Lit(Lit::Var(v)))
                .collect();
            // multiplicity from the state kind.
            proto_fact_mult(kind.multiplicity(), &full, ts)
        }
        TransFact::TamarinFact(f) => f.clone(),
        // `factToFact (PureCell t1 t2) = protoFact Linear "L_PureState" [t1, t2]`
        // (Facts.hs:253-270, see line 269).
        TransFact::PureCell(t1, t2) => {
            proto_fact(Multiplicity::Linear, "L_PureState", vec![t1.clone(), t2.clone()])
        }
        // `factToFact (CellLocked t1 t2) = protoFact Linear "L_CellLocked" [t1, t2]`
        // (Facts.hs:253-270, see line 270).
        TransFact::CellLocked(t1, t2) => {
            proto_fact(Multiplicity::Linear, "L_CellLocked", vec![t1.clone(), t2.clone()])
        }
        // `factToFact (FLet p t vars) = protoFact Linear ("Let_" ++ pos) (t : vars)`
        // (Facts.hs:257-259).  `vars` rendered as `S.toList` (sorted unique).
        TransFact::FLet(p, t, vars) => {
            let full = format!("Let_{}", pretty_position(p));
            let mut ts: Vec<LNTerm> = vec![t.clone()];
            ts.extend(
                sorted_unique(vars.clone())
                    .into_iter()
                    .map(|v| VTerm::Lit(Lit::Var(v))),
            );
            proto_fact(Multiplicity::Linear, &full, ts)
        }
        // `factToFact (Message t t') = protoFact Linear "Message" [t, t']`
        // (Facts.hs:253-270, see line 260) — the private-channel message-in-transit fact.
        TransFact::Message(t1, t2) => {
            proto_fact(Multiplicity::Linear, "Message", vec![t1.clone(), t2.clone()])
        }
        // `factToFact (Ack t t') = protoFact Linear "Ack" [t, t']` (Facts.hs:253-270, see line 261)
        // — the private-channel acknowledgement fact.
        TransFact::Ack(t1, t2) => {
            proto_fact(Multiplicity::Linear, "Ack", vec![t1.clone(), t2.clone()])
        }
        // `factToFact (MessageIDSender p) = protoFact Linear "MID_Sender" [varTerm $ varMID p]`
        // (Facts.hs:253-270, see line 262).
        TransFact::MessageIDSender(p) => proto_fact(
            Multiplicity::Linear,
            "MID_Sender",
            vec![VTerm::Lit(Lit::Var(var_mid(p)))],
        ),
        // `factToFact (MessageIDReceiver p) = protoFact Linear "MID_Receiver" [varTerm $ varMID p]`
        // (Facts.hs:253-270, see line 263).
        TransFact::MessageIDReceiver(p) => proto_fact(
            Multiplicity::Linear,
            "MID_Receiver",
            vec![VTerm::Lit(Lit::Var(var_mid(p)))],
        ),
    }
}

/// `actionToFact` (Facts.hs:213-234).
pub fn action_to_fact(a: &TransAction) -> LNFact {
    match a {
        TransAction::InitEmpty => proto_fact(Multiplicity::Linear, "Init", vec![]),
        TransAction::EventEmpty => proto_fact(Multiplicity::Linear, "Event", vec![]),
        TransAction::TamarinAct(f) => f.clone(),
        // `actionToFact (PredicateA f) = mapFactName ("Pred_" ++) f`
        // (Facts.hs:213-234, see line 226).
        TransAction::PredicateA(f) => map_fact_name(f, "Pred_"),
        // `actionToFact (NegPredicateA f) = mapFactName ("Pred_Not_" ++) f`
        // (Facts.hs:213-234, see line 227).
        TransAction::NegPredicateA(f) => map_fact_name(f, "Pred_Not_"),
        // `actionToFact (IsIn t v) = protoFact Linear "IsIn" [t, varTerm v]`
        // (Facts.hs:213-234, see line 220).
        TransAction::IsIn(t, v) => proto_fact(
            Multiplicity::Linear,
            "IsIn",
            vec![t.clone(), VTerm::Lit(Lit::Var(v.clone()))],
        ),
        // `actionToFact (IsNotSet t) = protoFact Linear "IsNotSet" [t]` (Facts.hs:213-234, see line 221).
        TransAction::IsNotSet(t) => proto_fact(Multiplicity::Linear, "IsNotSet", vec![t.clone()]),
        // `actionToFact (InsertA t1 t2) = protoFact Linear "Insert" [t1, t2]`
        // (Facts.hs:213-234, see line 222).
        TransAction::InsertA(t1, t2) => {
            proto_fact(Multiplicity::Linear, "Insert", vec![t1.clone(), t2.clone()])
        }
        // `actionToFact (DeleteA t) = protoFact Linear "Delete" [t]` (Facts.hs:213-234, see line 223).
        TransAction::DeleteA(t) => proto_fact(Multiplicity::Linear, "Delete", vec![t.clone()]),
        // `actionToFact (LockNamed t v) =
        //    protoFact Linear (lockFactName v) [lockPubTerm v, varTerm v, t]`
        // (Facts.hs:213-234, see line 228).
        TransAction::LockNamed(t, v) => proto_fact(
            Multiplicity::Linear,
            &lock_fact_name(v),
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (LockUnnamed t v) =
        //    protoFact Linear "Lock" [lockPubTerm v, varTerm v, t]` (Facts.hs:213-234, see line 229).
        TransAction::LockUnnamed(t, v) => proto_fact(
            Multiplicity::Linear,
            "Lock",
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (UnlockNamed t v) =
        //    protoFact Linear (unlockFactName v) [lockPubTerm v, varTerm v, t]`
        // (Facts.hs:213-234, see line 230).
        TransAction::UnlockNamed(t, v) => proto_fact(
            Multiplicity::Linear,
            &unlock_fact_name(v),
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (UnlockUnnamed t v) =
        //    protoFact Linear "Unlock" [lockPubTerm v, varTerm v, t]` (Facts.hs:213-234, see line 231).
        TransAction::UnlockUnnamed(t, v) => proto_fact(
            Multiplicity::Linear,
            "Unlock",
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (ChannelIn t) = protoFact Linear "ChannelIn" [t]`
        // (Facts.hs:213-234, see line 224).
        TransAction::ChannelIn(t) => proto_fact(Multiplicity::Linear, "ChannelIn", vec![t.clone()]),
        // `actionToFact (ProgressFrom p) =
        //    protoFact Linear ("ProgressFrom_" ++ prettyPosition p) [varTerm $ varProgress p]`
        // (Facts.hs:213-234, see line 232).
        TransAction::ProgressFrom(p) => proto_fact(
            Multiplicity::Linear,
            &format!("ProgressFrom_{}", pretty_position(p)),
            vec![VTerm::Lit(Lit::Var(var_progress(p)))],
        ),
        // `actionToFact (ProgressTo p pf) =
        //    protoFact Linear ("ProgressTo_" ++ prettyPosition p) [varTerm $ varProgress pf]`
        // (Facts.hs:213-234, see line 233).  NOTE: name uses `p`, but the term is `varProgress pf`.
        TransAction::ProgressTo(p, pf) => proto_fact(
            Multiplicity::Linear,
            &format!("ProgressTo_{}", pretty_position(p)),
            vec![VTerm::Lit(Lit::Var(var_progress(pf)))],
        ),
        // `actionToFact (Send p t) = protoFact Linear "Send" [varTerm $ varMsgId p, t]`
        // (Facts.hs:213-234, see line 218).
        TransAction::Send(p, t) => proto_fact(
            Multiplicity::Linear,
            "Send",
            vec![VTerm::Lit(Lit::Var(var_mid(p))), t.clone()],
        ),
        // `actionToFact (Receive p t) = protoFact Linear "Receive" [varTerm $ varMsgId p, t]`
        // (Facts.hs:213-234, see line 219).
        TransAction::Receive(p, t) => proto_fact(
            Multiplicity::Linear,
            "Receive",
            vec![VTerm::Lit(Lit::Var(var_mid(p))), t.clone()],
        ),
    }
}

/// `varNameProgress p = "prog_" ++ prettyPosition p` (Facts.hs:189-190).
pub fn var_name_progress(p: &ProcessPosition) -> String {
    format!("prog_{}", pretty_position(p))
}

/// `varProgress p = LVar (varNameProgress p) LSortFresh 0` (Facts.hs:192-197):
/// the fresh progress variable used in the rule premise/conclusion/action.
pub fn var_progress(p: &ProcessPosition) -> LVar {
    LVar::new(var_name_progress(p), tamarin_term::lterm::LSort::Fresh, 0)
}

/// `msgVarProgress p = LVar (varNameProgress p) LSortMsg 0` (Facts.hs:199-204):
/// the message-sort progress variable used in the progress RESTRICTION
/// quantifier (`∀ prog_<pos>. ..`).
pub fn msg_var_progress(p: &ProcessPosition) -> LVar {
    LVar::new(var_name_progress(p), tamarin_term::lterm::LSort::Msg, 0)
}

/// `varMID p = LVar ("mid_" ++ prettyPosition p) LSortFresh 0` (Facts.hs:244-251).
/// (HS also has the identical `varMsgId`, Facts.hs:206-211.)
pub fn var_mid(p: &ProcessPosition) -> LVar {
    LVar::new(
        format!("mid_{}", pretty_position(p)),
        tamarin_term::lterm::LSort::Fresh,
        0,
    )
}

/// `isState` (Facts.hs `isState`).
// Intentionally retained: faithful HS port; no caller yet (the predicate is
// inlined as `matches!(.., TransFact::State(..))` at the merge-with-state site).
#[allow(dead_code)]
pub(crate) fn is_state(f: &TransFact) -> bool {
    matches!(f, TransFact::State(..))
}

/// `isNonSemiState` (Facts.hs:154-156): a non-semi `State` fact.
pub fn is_non_semi_state(f: &TransFact) -> bool {
    matches!(f, TransFact::State(kind, _, _) if !kind.is_semi_state())
}

/// `addVarToState v' (State kind pos vs) = State kind pos (v' `S.insert` vs)`
/// (Facts.hs:162-164): insert a variable into a `State` fact's variable set;
/// other facts unchanged.
pub fn add_var_to_state(v: &LVar, f: &TransFact) -> TransFact {
    match f {
        TransFact::State(kind, pos, vs) => {
            let mut nvs = vs.clone();
            if !nvs.contains(v) {
                nvs.push(v.clone());
            }
            TransFact::State(*kind, pos.clone(), nvs)
        }
        other => other.clone(),
    }
}

/// `lockFactName v = "Lock_" ++ show (lvarIdx v)` (Facts.hs:180-181).
pub fn lock_fact_name(v: &LVar) -> String {
    format!("Lock_{}", v.idx)
}

/// `unlockFactName v = "Unlock_" ++ show (lvarIdx v)` (Facts.hs:183-184).
pub fn unlock_fact_name(v: &LVar) -> String {
    format!("Unlock_{}", v.idx)
}

/// `lockPubTerm v = pubTerm (show (lvarIdx v))` (Facts.hs:186-187): the public
/// constant `'<idx v>'` used as the first argument of the lock/unlock facts.
fn lock_pub_term(v: &LVar) -> LNTerm {
    tamarin_term::lterm::pub_term(v.idx.to_string())
}

/// `mapFactName (prefix ++)` (Facts.hs:173-177): prepend `prefix` to a
/// `ProtoFact` name (other tags are left unchanged).
fn map_fact_name(f: &LNFact, prefix: &str) -> LNFact {
    use tamarin_theory::fact::FactTag;
    let tag = match &f.tag {
        FactTag::Proto(m, s, i) => FactTag::Proto(*m, tamarin_term::intern::intern_str(&format!("{prefix}{s}")), *i),
        other => other.clone(),
    };
    tamarin_theory::fact::Fact::new(tag, f.terms.clone()).with_annotations(f.annotations.clone())
}

/// `proto_fact` is fixed to `Linear`; the state fact needs an explicit
/// multiplicity, so build the tag directly.
fn proto_fact_mult(mult: Multiplicity, name: &str, terms: Vec<LNTerm>) -> LNFact {
    use tamarin_theory::fact::{Fact, FactTag};
    Fact::new(FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()), terms)
}

// =============================================================================
// crc32 / colorForProcessName (Facts.hs:327-374)
// =============================================================================

/// `crc32` (Facts.hs:327-331).
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

/// `colorHash` (Facts.hs:347-351): per-channel byte of the CRC, scaled to [0,1].
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

/// `colorForProcessName` (Facts.hs:360-374).
pub fn color_for_process_name(names: &[String]) -> Rgb {
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

/// The rendered `color=` hex value for a process-name list.
// Test convenience only (no production caller; `to_rule` uses
// `color_for_process_name` directly and the rule printer renders the hex).
#[allow(dead_code)]
pub(crate) fn color_hex_for_process_name(names: &[String]) -> String {
    rgb_to_hex(color_for_process_name(names))
}

// =============================================================================
// AnnotatedRule + toRule (Facts.hs:114-127, 376-403)
// =============================================================================

/// `AnnotatedRule` (Facts.hs:114-127).  `process` is the subprocess this rule
/// was generated for (used for naming / color / `process=` attribute).
#[derive(Debug, Clone)]
pub struct AnnotatedRule<Ann> {
    pub process_name: Option<String>,
    pub process: Process<Ann, SapicLVar>,
    pub position: RulePosition,
    pub prems: Vec<TransFact>,
    pub acts: Vec<TransAction>,
    pub concs: Vec<TransFact>,
    /// Embedded restrictions (HS `restr :: [SyntacticLNFormula]`, Facts.hs:116-125, see line 123).
    /// Carried as parser-AST formulas so they flow through the existing
    /// `_restrict` expansion (`rule_restriction::lift_rule_restrictions`).
    /// Non-empty only for `if <formula>` arms (the `Cond` combinator).
    pub restr: Vec<tamarin_parser::ast::Formula>,
    pub index: usize,
}

/// `prettyEitherPositionOrSpecial` (Facts.hs:319-322).
fn pretty_position_or_special(pos: &RulePosition) -> String {
    match pos {
        RulePosition::Pos(p) => pretty_position(p),
        RulePosition::Special(SpecialPosition::InitPosition) => "Init".to_string(),
        RulePosition::Special(SpecialPosition::NoPosition) => String::new(),
    }
}

/// `getTopLevelName` (Facts.hs:295-298) — the process-name list from the
/// (already-name-propagated) annotation of the subprocess.
fn get_top_level_name<Ann: GoodAnnotation>(p: &Process<Ann, SapicLVar>) -> Vec<String> {
    p.annotation().parsed().process_names.clone()
}

/// `roleFromProcessNameList` (Facts.hs:399-400).
fn role_from_process_name_list(names: &[String]) -> String {
    if names.is_empty() {
        "Process".to_string()
    } else {
        names.join("_")
    }
}

/// `stripNonAlphanumerical = filter isAlpha` (Facts.hs:376-404, see line 401).
fn strip_non_alphabetic(s: &str) -> String {
    s.chars().filter(|c| c.is_alphabetic()).collect()
}

/// Erase the rich annotation back to a `PlainProcess` for printing (HS
/// `toProcess`).
fn to_plain<Ann: GoodAnnotation + Clone>(p: &Process<Ann, SapicLVar>) -> PlainProcess {
    match p {
        Process::Null(a) => Process::Null(a.parsed().clone()),
        Process::Action(ac, a, body) => {
            Process::Action(ac.clone(), a.parsed().clone(), Box::new(to_plain(body)))
        }
        Process::Comb(c, a, l, r) => Process::Comb(
            c.clone(),
            a.parsed().clone(),
            Box::new(to_plain(l)),
            Box::new(to_plain(r)),
        ),
    }
}

/// The HS-faithful rule name (Facts.hs:380-388).
pub fn rule_name<Ann: GoodAnnotation + Clone>(r: &AnnotatedRule<Ann>) -> String {
    match &r.process_name {
        Some(s) => s.clone(),
        None => {
            let plain = to_plain(&r.process);
            let base = pretty_sapic_top_level(&plain);
            let stripped = strip_non_alphabetic(&base);
            let un_null = if stripped.is_empty() { "p".to_string() } else { stripped };
            format!(
                "{}_{}_{}",
                un_null,
                r.index,
                pretty_position_or_special(&r.position)
            )
        }
    }
}

/// `toRule` (Facts.hs:376-403): build the final `ProtoRuleE` with HS-exact
/// `name`, `color`, `process`, `role`, `issapicrule` attributes.
///
/// `ignoreDerivChecks = isLookup process` (Facts.hs:404-405): the lookup rules
/// carry the `no_derivcheck` attribute so the message-derivation check skips
/// them (the bound lookup variable is unconstrained at that point).
pub fn to_rule(r: &AnnotatedRule<ProcessAnnotation<LVar>>) -> ProtoRuleE {
    let name = rule_name(r);
    let names = get_top_level_name(&r.process);
    // HS `isLookup (ProcessComb (Lookup _ _) _ _ _) = True; isLookup _ = False`
    // (Facts.hs:404-405) — the LITERAL process node this rule was generated for.
    let is_lookup_proc = matches!(
        &r.process,
        Process::Comb(tamarin_theory::sapic::ProcessCombinator::Lookup(_, _), _, _, _)
    );
    let attr = RuleAttributes {
        color: Some(color_for_process_name(&names)),
        process: Some(to_plain(&r.process)),
        ignore_deriv_checks: is_lookup_proc,
        is_sapic_rule: true,
        role: Some(role_from_process_name_list(
            &r.process.annotation().parsed().process_names,
        )),
    };
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(tamarin_term::intern::intern_str(&name)),
        attributes: attr,
        restrictions: Vec::new(),
    };
    let prems: Vec<LNFact> = r.prems.iter().map(fact_to_fact).collect();
    let acts: Vec<LNFact> = r.acts.iter().map(action_to_fact).collect();
    let concs: Vec<LNFact> = r.concs.iter().map(fact_to_fact).collect();
    let new_vars = compute_new_vars(&prems, &concs, &acts);
    Rule::new(info, prems, concs, acts).with_new_vars(new_vars)
}

/// `newVariables l r` (Rule.hs): variables in conclusions/actions not bound by
/// the premises.  Mirrors `elaborate.rs::compute_new_vars`.
pub fn compute_new_vars(prems: &[LNFact], concs: &[LNFact], acts: &[LNFact]) -> Vec<LNTerm> {
    use std::collections::BTreeSet;
    fn collect(t: &LNTerm, out: &mut BTreeSet<LVar>) {
        match t {
            VTerm::Lit(Lit::Var(v)) => {
                out.insert(v.clone());
            }
            VTerm::Lit(_) => {}
            VTerm::App(_, args) => {
                for a in args.iter() {
                    collect(a, out);
                }
            }
        }
    }
    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        for t in &f.terms {
            collect(t, &mut prem_vars);
        }
    }
    let mut new_set: BTreeSet<LVar> = BTreeSet::new();
    for f in concs.iter().chain(acts) {
        for t in &f.terms {
            let mut here = BTreeSet::new();
            collect(t, &mut here);
            for v in here {
                if !prem_vars.contains(&v) {
                    new_set.insert(v);
                }
            }
        }
    }
    new_set.into_iter().map(|v| VTerm::Lit(Lit::Var(v))).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crc32_known_values() {
        // CRC32 (HS's non-standard 0xedb88329 variant of the reflected CRC32
        // polynomial, matching `crc32` above) of "" is 0xFFFFFFFF before
        // final-xor; HS does NOT apply the final xor, so for the empty string
        // `crc32 "" == 0xffffffff`.
        assert_eq!(crc32(""), 0xffff_ffff);
    }

    #[test]
    fn empty_names_is_white() {
        assert_eq!(color_hex_for_process_name(&[]), "#ffffff");
    }

    #[test]
    fn state_fact_name_and_mult() {
        let f = TransFact::State(StateKind::LState, vec![1], vec![]);
        let lnf = fact_to_fact(&f);
        match &lnf.tag {
            tamarin_theory::fact::FactTag::Proto(m, n, _) => {
                assert_eq!(&**n, "State_1");
                assert_eq!(*m, Multiplicity::Linear);
            }
            _ => panic!("expected proto fact"),
        }
    }

    #[test]
    fn empty_position_state_renders_state_underscore() {
        let f = TransFact::State(StateKind::LState, vec![], vec![]);
        let lnf = fact_to_fact(&f);
        if let tamarin_theory::fact::FactTag::Proto(_, n, _) = &lnf.tag {
            assert_eq!(&**n, "State_");
        } else {
            panic!();
        }
    }
}
