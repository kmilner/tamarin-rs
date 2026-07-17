// Currently GPL 3.0 until granted permission by the following authors:
//   Robert Künnemann, Artur Cygan, Charlie Jacomme, and other minor
//   contributors (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/sapic/src/Sapic/ProgressTranslation.hs

//! Port of `Sapic.ProgressTranslation`
//! (`lib/sapic/src/Sapic/ProgressTranslation.hs`).
//!
//! Wraps the base translation with the local-progress events/restrictions:
//!   - `progress_init`   (HS `progressInit`):  adds `ProgressFrom_` to the init
//!     rules if `[] ∈ dom(pf)`, and extends the initial `~x`.
//!   - `progress_trans_*` (HS `progressTransAct`/`progressTransComb`):  adds
//!     `ProgressFrom`/`ProgressTo` events + extends `~x` per action/combinator.
//!   - `progress_restr`  (HS `progressRestr`):  the `Progress_<pos>_to_<...>`
//!     restrictions + `resProgressInit`.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_term::lterm::LVar;
use tamarin_theory::sapic::{pretty_position, Process, SapicLVar};

use crate::annotation::ProcessAnnotation;
use crate::base_translation::RuleBody;
use crate::facts::{
    add_var_to_state, is_non_semi_state, msg_var_progress, var_progress, AnnotatedRule, StateKind,
    TransAction, TransFact,
};
use crate::progress_function::{pf, pf_from};

type Pos = Vec<i64>;
type PosSet = BTreeSet<Pos>;
type AProc = Process<ProcessAnnotation<LVar>, SapicLVar>;

/// `lhsP pos` / `rhsP pos`: append 1 / 2.
fn lhs_p(pos: &[i64]) -> Pos {
    let mut v = pos.to_vec();
    v.push(1);
    v
}
fn rhs_p(pos: &[i64]) -> Pos {
    let mut v = pos.to_vec();
    v.push(2);
    v
}

/// `addProgressFrom domPF child (l,a,r,res)` (ProgressTranslation.hs:39-49):
/// add a `Fr (varProgress child)` premise, a `ProgressFrom child` action, and
/// thread the progress var into every rhs state fact — IF any rhs fact is a
/// non-semi state AND `child ∈ domPF`.
fn add_progress_from(dom_pf: &PosSet, child: &[i64], body: RuleBody) -> RuleBody {
    let (l, a, r, res) = body;
    let any_non_semi = r.iter().any(is_non_semi_state);
    if any_non_semi && dom_pf.contains(child) {
        let vp = var_progress(&child.to_vec());
        let mut nl = vec![TransFact::Fr(vp.clone())];
        nl.extend(l);
        let mut na = vec![TransAction::ProgressFrom(child.to_vec())];
        na.extend(a);
        let nr: Vec<TransFact> = r.iter().map(|f| add_var_to_state(&vp, f)).collect();
        (nl, na, nr, res)
    } else {
        (l, a, r, res)
    }
}

/// `addProgressTo invPF child (l,a,r,res)` (ProgressTranslation.hs:93-102): add a
/// `ProgressTo child posFrom` action IF any rhs fact is a "target state" whose
/// next-position is `child` (an `LState`/`PState`), and `child` has an inverse.
fn add_progress_to<F: Fn(&[i64]) -> Option<Pos>>(
    inv_pf: &F,
    child: &[i64],
    body: RuleBody,
) -> RuleBody {
    let (l, a, r, res) = body;
    let is_target_state = |fct: &TransFact| -> bool {
        matches!(
            fct,
            TransFact::State(kind, next_pos, _)
                if next_pos.as_slice() == child
                    && matches!(kind, StateKind::PState | StateKind::LState)
        )
    };
    if r.iter().any(is_target_state) {
        if let Some(pos_from) = inv_pf(child) {
            let mut na = vec![TransAction::ProgressTo(child.to_vec(), pos_from)];
            na.extend(a);
            return (l, na, r, res);
        }
    }
    (l, a, r, res)
}

/// `addProgressItems domPF invPF pos` (ProgressTranslation.hs:73-80):
///   addProgressFrom domPF (lhsP pos) . addProgressTo invPF (lhsP pos) . addProgressTo invPF (rhsP pos)
fn add_progress_items<F: Fn(&[i64]) -> Option<Pos>>(
    dom_pf: &PosSet,
    inv_pf: &F,
    pos: &[i64],
    body: RuleBody,
) -> RuleBody {
    let b = add_progress_to(inv_pf, &rhs_p(pos), body);
    let b = add_progress_to(inv_pf, &lhs_p(pos), b);
    add_progress_from(dom_pf, &lhs_p(pos), b)
}

/// `extendVars domPF pos tx` (ProgressTranslation.hs:66-69): add `varProgress
/// (lhsP pos)` to `tx` if `lhsP pos ∈ domPF`.
fn extend_vars(dom_pf: &PosSet, pos: &[i64], tx: &mut BTreeSet<LVar>) {
    let lhs = lhs_p(pos);
    if dom_pf.contains(&lhs) {
        tx.insert(var_progress(&lhs));
    }
}

/// `progressInit anP (initrules, initTx)` (ProgressTranslation.hs:54-62).
pub fn progress_init(
    an_proc: &AProc,
    init_rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>>,
    init_tx: BTreeSet<LVar>,
) -> Result<(Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>), String> {
    let dom_pf = pf_from(an_proc)?;
    let empty: Pos = Vec::new();
    // `initTx' = if [] ∈ domPF then {varProgress []} else {}`
    let mut new_tx = init_tx;
    if dom_pf.contains(&empty) {
        new_tx.insert(var_progress(&empty));
    }
    // `initrules' = map (mapAct $ addProgressFrom domPF []) initrules`
    let new_rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>> = init_rules
        .into_iter()
        .map(|mut r| {
            let body: RuleBody = (r.prems, r.acts, r.concs, r.restr);
            let (l, a, c, res) = add_progress_from(&dom_pf, &empty, body);
            r.prems = l;
            r.acts = a;
            r.concs = c;
            r.restr = res;
            r
        })
        .collect();
    Ok((new_rules, new_tx))
}

/// `progressTransAct` (ProgressTranslation.hs:111-119): post-process the base
/// action translation result.  `dom_pf` / the inverse are computed once and
/// threaded in.
pub fn progress_trans_act(
    dom_pf: &PosSet,
    inv_pf: &impl Fn(&[i64]) -> Option<Pos>,
    pos: &[i64],
    rules: Vec<RuleBody>,
    mut tx1: BTreeSet<LVar>,
) -> (Vec<RuleBody>, BTreeSet<LVar>) {
    let new_rules = rules
        .into_iter()
        .map(|b| add_progress_items(dom_pf, inv_pf, pos, b))
        .collect();
    extend_vars(dom_pf, pos, &mut tx1);
    (new_rules, tx1)
}

/// `progressTransComb` (ProgressTranslation.hs:122-132).  Note: HS uses the SAME
/// `extendVars domPF pos` on both `tx1` and (fmap'd) `tx2`.
pub fn progress_trans_comb(
    dom_pf: &PosSet,
    inv_pf: &impl Fn(&[i64]) -> Option<Pos>,
    pos: &[i64],
    rules: Vec<RuleBody>,
    mut tx1: BTreeSet<LVar>,
    tx2: Option<BTreeSet<LVar>>,
) -> (Vec<RuleBody>, BTreeSet<LVar>, Option<BTreeSet<LVar>>) {
    let new_rules = rules
        .into_iter()
        .map(|b| add_progress_items(dom_pf, inv_pf, pos, b))
        .collect();
    extend_vars(dom_pf, pos, &mut tx1);
    let new_tx2 = tx2.map(|mut t| {
        extend_vars(dom_pf, pos, &mut t);
        t
    });
    (new_rules, tx1, new_tx2)
}

/// `resProgressInit` (ProgressTranslation.hs:150-153): `∃ #t. Init( ) @ #t`.
fn res_progress_init() -> p::Restriction {
    let tvar = p::VarSpec {
        name: "t".into(),
        idx: 0,
        sort: p::SortHint::Node,
        typ: None,
    };
    let init_at = p::Formula::Atom(p::Atom::Action(
        p::Fact {
            persistent: false,
            name: "Init".into(),
            args: vec![],
            annotations: vec![],
        },
        p::Term::Var(tvar.clone()),
    ));
    let formula = p::Formula::Exists(vec![tvar], Box::new(init_at));
    p::Restriction {
        name: "progressInit".to_string(),
        formula,
        attributes: vec![],
    }
}

/// `progressRestr anP restrictions` (ProgressTranslation.hs:156-178): append the
/// per-from-position `Progress_<pos>_to_<...>` restrictions, then `progressInit`.
pub fn progress_restr(
    an_proc: &AProc,
    mut restrictions: Vec<p::Restriction>,
) -> Result<Vec<p::Restriction>, String> {
    let dom_pf = pf_from(an_proc)?;
    // `lss_to <- mapM restriction (toList domPF)` — over the ascending domain.
    let mut lss_to: Vec<p::Restriction> = Vec::new();
    for pos in &dom_pf {
        lss_to.extend(restriction_for(an_proc, pos)?);
    }
    restrictions.extend(lss_to);
    restrictions.push(res_progress_init());
    Ok(restrictions)
}

/// `restriction pos` (ProgressTranslation.hs:163-177): for the given from-`pos`,
/// one restriction per element of `pf anP pos` (the CNF set-of-sets of "to"s).
fn restriction_for(an_proc: &AProc, pos: &[i64]) -> Result<Vec<p::Restriction>, String> {
    let toss = pf(an_proc, pos)?;
    let mut out = Vec::new();
    for tos in &toss {
        out.push(make_restriction(pos, tos));
    }
    Ok(out)
}

/// Build one `Progress_<pos>_to_<t1>_or_<t2>...` restriction.
///   `name = "Progress_" ++ prettyPosition pos ++ "_to_" ++ intercalate "_or_" (map prettyPosition (toList tos))`
///   `formula = ∀ prog_<pos>. ∀ #t. ProgressFrom_<pos>(prog_<pos>)@#t ⇒ bigOr [∃ #t.2. ProgressTo_<to>(prog_<pos>)@#t.2 | to ∈ tos]`
fn make_restriction(pos: &[i64], tos: &PosSet) -> p::Restriction {
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
    let pvar_spec = crate::convert::lvar_to_varspec(&pvar);
    let pvar_term = p::Term::Var(pvar_spec.clone());

    // `t1var = LVar "t" LSortNode 1`, `t2var = LVar "t" LSortNode 2`.
    let t1var = p::VarSpec {
        name: "t".into(),
        idx: 1,
        sort: p::SortHint::Node,
        typ: None,
    };
    let t2var = p::VarSpec {
        name: "t".into(),
        idx: 2,
        sort: p::SortHint::Node,
        typ: None,
    };

    // antecedent = ProgressFrom_<pos>( prog_<pos> ) @ #t.1
    let antecedent = p::Formula::Atom(p::Atom::Action(
        p::Fact {
            persistent: false,
            name: format!("ProgressFrom_{}", pretty_position(&pos_v)),
            args: vec![pvar_term.clone()],
            annotations: vec![],
        },
        p::Term::Var(t1var.clone()),
    ));

    // progressTo to = ∃ #t.2. ProgressTo_<to>( prog_<pos> ) @ #t.2
    let progress_to = |to: &[i64]| -> p::Formula {
        let act = p::Formula::Atom(p::Atom::Action(
            p::Fact {
                persistent: false,
                name: format!("ProgressTo_{}", pretty_position(&to.to_vec())),
                args: vec![pvar_term.clone()],
                annotations: vec![],
            },
            p::Term::Var(t2var.clone()),
        ));
        p::Formula::Exists(vec![t2var.clone()], Box::new(act))
    };

    // bigOr over `toList tos` (ascending), right-nested as in HS
    // `bigOr (to:tos) = to .||. bigOr tos`.
    let tos_list: Vec<&Pos> = tos.iter().collect();
    let conclusion = big_or(&tos_list, &progress_to);

    let body = p::Formula::Implies(Box::new(antecedent), Box::new(conclusion));
    // `hinted forAll pvar $ hinted forAll t1var $ ...`
    let formula = p::Formula::Forall(
        vec![pvar_spec],
        Box::new(p::Formula::Forall(vec![t1var], Box::new(body))),
    );
    p::Restriction {
        name,
        formula,
        attributes: vec![],
    }
}

/// `bigOr` (ProgressTranslation.hs:174-176): right-nested disjunction.  The
/// empty case never occurs (`tos` is always non-empty here).
fn big_or(tos: &[&Pos], progress_to: &impl Fn(&[i64]) -> p::Formula) -> p::Formula {
    match tos {
        [] => p::Formula::False,
        [to] => progress_to(to),
        [to, rest @ ..] => p::Formula::Or(
            Box::new(progress_to(to)),
            Box::new(big_or(rest, progress_to)),
        ),
    }
}

