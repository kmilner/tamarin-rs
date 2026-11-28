// Currently GPL 3.0; see README.md for licensing details.
// Derived from the upstream tamarin-prover sources referenced below.

//! Port of `Sapic.ProgressTranslation`
//! (`lib/sapic/src/Sapic/ProgressTranslation.hs`).
//!
//! Wraps the base translation with the local-progress events and
//! restrictions; [`Progress`] holds the progress function the passes share.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_term::lterm::LVar;
use tamarin_theory::formula::LNFormula;
use tamarin_theory::restriction::Restriction;
use tamarin_theory::sapic::{pretty_position, Process, SapicLVar};

use crate::annotation::ProcessAnnotation;
use crate::base_translation::RuleBody;
use crate::facts::{
    add_var_to_state, is_non_semi_state, msg_var_progress, var_progress, AnnotatedRule, StateKind,
    TransAction, TransFact,
};
use crate::progress_function::{pf, pf_from, pf_inv};

type Pos = Vec<i64>;
type PosSet = BTreeSet<Pos>;
type AProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// The progress function's domain `pfFrom anP` and inverse `pfInv anP`
/// (ProgressFunction.hs).  Haskell recomputes both at every use; they depend
/// only on the annotated process, so the translation computes them once.
pub(crate) struct Progress {
    dom: PosSet,
    inv: BTreeMap<Pos, Pos>,
}

impl Progress {
    pub(crate) fn new(an_proc: &AProc) -> Result<Self, String> {
        let dom = pf_from(an_proc)?;
        let inv = pf_inv(an_proc, &dom)?;
        Ok(Progress { dom, inv })
    }

    /// `addProgressFrom domPF child (l,a,r,res)` (ProgressTranslation.hs):
    /// add a `Fr (varProgress child)` premise, a `ProgressFrom child` action,
    /// and thread the progress variable into every conclusion state, if a
    /// conclusion is a non-semi state and `child ∈ domPF`.
    fn add_progress_from(
        &self,
        child: &Pos,
        prems: &mut Vec<TransFact>,
        acts: &mut Vec<TransAction>,
        concs: &mut [TransFact],
    ) {
        if concs.iter().any(is_non_semi_state) && self.dom.contains(child) {
            let vp = var_progress(child);
            prems.insert(0, TransFact::Fr(vp));
            acts.insert(0, TransAction::ProgressFrom(child.clone()));
            for fact in concs {
                *fact = add_var_to_state(&vp, fact);
            }
        }
    }

    /// `addProgressTo invPF child (l,a,r,res)` (ProgressTranslation.hs): add a
    /// `ProgressTo child posFrom` action if a conclusion is an `LState` /
    /// `PState` at `child` and `child` has an inverse.
    fn add_progress_to(&self, child: &Pos, acts: &mut Vec<TransAction>, concs: &[TransFact]) {
        let is_target_state = |fct: &TransFact| {
            matches!(
                fct,
                TransFact::State(kind, next_pos, _)
                    if next_pos == child
                        && matches!(kind, StateKind::PState | StateKind::LState)
            )
        };
        if concs.iter().any(is_target_state)
            && let Some(pos_from) = self.inv.get(child)
        {
            acts.insert(0, TransAction::ProgressTo(child.clone(), pos_from.clone()));
        }
    }

    /// The rule half of `progressTransAct` / `progressTransComb`
    /// (ProgressTranslation.hs): `addProgressItems domPF invPF pos` =
    /// `addProgressFrom domPF (lhsP pos) . addProgressTo invPF (lhsP pos) .
    /// addProgressTo invPF (rhsP pos)` on every rule.
    pub(crate) fn trans_rules(&self, pos: &[i64], rules: Vec<RuleBody>) -> Vec<RuleBody> {
        let lhs = child(pos, 1);
        let rhs = child(pos, 2);
        rules
            .into_iter()
            .map(|(mut prems, mut acts, mut concs, restr)| {
                self.add_progress_to(&rhs, &mut acts, &concs);
                self.add_progress_to(&lhs, &mut acts, &concs);
                self.add_progress_from(&lhs, &mut prems, &mut acts, &mut concs);
                (prems, acts, concs, restr)
            })
            .collect()
    }

    /// `extendVars domPF pos tx` (ProgressTranslation.hs): add `varProgress
    /// (lhsP pos)` to `tx` if `lhsP pos ∈ domPF`.  `progressTransComb` applies
    /// it to both continuations' variables.
    pub(crate) fn extend_vars(&self, pos: &[i64], tx: &mut BTreeSet<LVar>) {
        let lhs = child(pos, 1);
        if self.dom.contains(&lhs) {
            tx.insert(var_progress(&lhs));
        }
    }

    /// `progressInit anP (initrules, initTx)` (ProgressTranslation.hs).
    pub(crate) fn init(
        &self,
        init_rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>>,
        mut init_tx: BTreeSet<LVar>,
    ) -> (Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>) {
        let empty: Pos = Vec::new();
        // `initTx' = if [] ∈ domPF then {varProgress []} else {}`
        if self.dom.contains(&empty) {
            init_tx.insert(var_progress(&empty));
        }
        // `initrules' = map (mapAct $ addProgressFrom domPF []) initrules`
        let rules = init_rules
            .into_iter()
            .map(|mut r| {
                self.add_progress_from(&empty, &mut r.prems, &mut r.acts, &mut r.concs);
                r
            })
            .collect();
        (rules, init_tx)
    }

    /// `progressRestr anP restrictions` (ProgressTranslation.hs): one
    /// `Progress_<pos>_to_<...>` restriction per element of `pf anP pos`, over
    /// the ascending domain, then `progressInit`.
    pub(crate) fn restr(
        &self,
        an_proc: &AProc,
        mut restrictions: Vec<Restriction>,
    ) -> Result<Vec<Restriction>, String> {
        for pos in &self.dom {
            for tos in &pf(an_proc, pos)? {
                restrictions.push(make_restriction(pos, tos));
            }
        }
        restrictions.push(res_progress_init());
        Ok(restrictions)
    }
}

/// `lhsP pos` / `rhsP pos`: `pos ++ [i]`.
fn child(pos: &[i64], i: i64) -> Pos {
    [pos, &[i]].concat()
}

/// `resProgressInit` (ProgressTranslation.hs): `∃ #t. Init( ) @ #t`.
fn res_progress_init() -> Restriction {
    use crate::restriction_builder as rb;
    let t = rb::node("t");
    rb::restriction("progressInit", rb::exists(&[t], rb::action("Init", &[], t)))
}

/// Build one `Progress_<pos>_to_<t1>_or_<t2>...` restriction.
///   `name = "Progress_" ++ prettyPosition pos ++ "_to_" ++ intercalate "_or_" (map prettyPosition (toList tos))`
///   `formula = ∀ prog_<pos>. ∀ #t. ProgressFrom_<pos>(prog_<pos>)@#t ⇒ bigOr [∃ #t.2. ProgressTo_<to>(prog_<pos>)@#t.2 | to ∈ tos]`
fn make_restriction(pos: &[i64], tos: &PosSet) -> Restriction {
    use crate::restriction_builder as rb;
    let pos_v = pos.to_vec();
    let name = format!(
        "Progress_{}_to_{}",
        pretty_position(&pos_v),
        tos.iter()
            .map(pretty_position)
            .collect::<Vec<_>>()
            .join("_or_")
    );

    // `pvar = msgVarProgress pos` — the message-sort progress var (rendered
    // without the `~`), quantified universally.
    let pvar = msg_var_progress(&pos_v);
    // `t1var = LVar "t" LSortNode 1`, `t2var = LVar "t" LSortNode 2`.
    let t1var = rb::indexed_node("t", 1);
    let t2var = rb::indexed_node("t", 2);

    // antecedent = ProgressFrom_<pos>( prog_<pos> ) @ #t.1
    let antecedent = rb::action(
        &format!("ProgressFrom_{}", pretty_position(&pos_v)),
        &[pvar],
        t1var,
    );

    // progressTo to = ∃ #t.2. ProgressTo_<to>( prog_<pos> ) @ #t.2
    let progress_to = |to: &Pos| -> LNFormula {
        let act = rb::action(
            &format!("ProgressTo_{}", pretty_position(to)),
            &[pvar],
            t2var,
        );
        rb::exists(&[t2var], act)
    };

    // bigOr over `toList tos` (ascending), right-nested as in HS
    // `bigOr (to:tos) = to .||. bigOr tos`.
    let tos_list: Vec<&Pos> = tos.iter().collect();
    let conclusion = big_or(&tos_list, &progress_to);

    let body = antecedent.implies(conclusion);
    // `hinted forAll pvar $ hinted forAll t1var $ ...`
    rb::restriction(name, rb::all(&[pvar, t1var], body))
}

/// `bigOr` (ProgressTranslation.hs): right-nested disjunction.  The
/// empty case never occurs (`tos` is always non-empty here).
fn big_or(tos: &[&Pos], progress_to: &impl Fn(&Pos) -> LNFormula) -> LNFormula {
    match tos {
        [] => LNFormula::lfalse(),
        [to] => progress_to(to),
        [to, rest @ ..] => progress_to(to).or(big_or(rest, progress_to)),
    }
}
