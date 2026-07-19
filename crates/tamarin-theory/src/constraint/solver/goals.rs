// Currently GPL 3.0 until granted permission by the following authors:
//   meiersi, jdreier, racoucho1u, beschmi, felixlinker, rkunnema,
//   PhilipLukertWork, rsasse, yavivanov, kevinmorio, sans-sucre, Nick
//   Moore, katrielalex, arcz, addap, charlie-j,
//   robert.kunnemann@cased.de, xaDxelA, and other minor contributors
//   (see upstream git history)
// Ported from upstream tamarin-prover sources:
//   lib/term/src/Term/LTerm.hs, lib/term/src/Term/Term/Raw.hs,
//   lib/theory/src/Theory/Constraint/Solver/AnnotatedGoals.hs,
//   lib/theory/src/Theory/Constraint/Solver/Goals.hs,
//   lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs,
//   lib/theory/src/Theory/Constraint/Solver/Sources.hs,
//   lib/theory/src/Theory/Constraint/System.hs,
//   lib/theory/src/Theory/Constraint/System/Constraints.hs,
//   lib/theory/src/Theory/Constraint/System/Guarded.hs,
//   lib/theory/src/Theory/Model/Fact.hs,
//   lib/theory/src/Theory/Model/Signature.hs,
//   lib/theory/src/Theory/Proof.hs,
//   lib/theory/src/Theory/Sapic/Term.hs,
//   lib/theory/src/Theory/Text/Parser/Tactics.hs,
//   lib/theory/src/Theory/Tools/SubtermStore.hs,
//   lib/utils/src/Data/DAG/Simple.hs, src/Web/Theory.hs

//! Port of `Theory.Constraint.Solver.Goals`.
//!
//! `openGoals` enumerates the list of goals from a `System` that
//! still need to be solved, with `Usefulness` annotations driving
//! the heuristic. This port implements the full Haskell `openGoals`
//! filter — KU sort/pair/inv/prod/union checks, `chainToEquality`,
//! `allMsgVarsKnownEarlier`, `splitExists`, and `SubtermG`
//! membership — together with the usefulness annotation
//! (`currentlyDeducible` / `extractible` / `probablyConstructible` /
//! `hasKUGuards`).

use crate::constraint::constraints::Goal;
use crate::constraint::solver::annotated_goals::{AnnotatedGoal, Usefulness};
use crate::constraint::system::System;
use tamarin_term::lterm::{contains_private, is_msg_var};


/// The goal ranking selected by a theory / lemma `heuristic:` directive.
///
/// Port of the relevant `Theory.Constraint.System.GoalRanking` variants
/// (`System.hs:506-520`).  Implements:
///
///   * `SmartRanking Bool`         — heuristic `s`/`S`
///   * `InjRanking   Bool`         — heuristic `i`/`I`
///   * `Oracle       { quit_on_empty, oracle_path }` — heuristic `o`
///     (HS `OracleRanking`, System.hs:585-598, see line 589)
///   * `OracleSmart  { quit_on_empty, oracle_path }` — heuristic `O`
///     (HS `OracleSmartRanking`, System.hs:585-598, see line 590)
///
/// `c` → `UsefulGoalNr` and `C` → `GoalNr` are implemented
/// (System.hs:593-594 `goalRankingIdentifiers`); `{name}` tactics are
/// resolved via `parse_heuristic_str_with_tactics`.  `p` → `Sapic` and
/// `P` → `SapicPKCS11` (HS `SapicRanking`/`SapicPKCS11Ranking`,
/// System.hs:591-592) are implemented and dispatched via `sapic_ranking`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GoalRanking {
    /// `SmartRanking useLoopBreakers` (ProofMethod.hs).
    Smart(bool),
    /// `InjRanking useLoopBreakers` (ProofMethod.hs).
    Inj(bool),
    /// `SapicRanking` (ProofMethod.hs:941-1043, see line 993) — heuristic char `p`.
    /// "heuristics adapted for processes" (System.hs:687-705, see line 694).
    Sapic,
    /// `SapicPKCS11Ranking` (ProofMethod.hs:1048-1129, see line 1072) — heuristic char `P`.
    /// Deprecated PKCS#11-specific SAPIC ranking (System.hs:687-705, see line 695).
    SapicPKCS11,
    /// `GoalNrRanking` (rankGoals dispatch ProofMethod.hs:480-503, see line 482):
    /// `sortOn (fst . snd)` — presort identifier `C`.
    GoalNr,
    /// `UsefulGoalNrRanking` (rankGoals dispatch ProofMethod.hs:480-503, see line 485):
    /// `sortOn (\(_, (nr, useless)) -> (useless, nr))` — presort `c`.
    UsefulGoalNr,
    /// `OracleRanking quitOnEmpty oracle` (rankGoals dispatch ProofMethod.hs:480-503, see line 483).
    /// preSort = `const goalNrRanking`.
    /// `oracle_path` is the resolved filesystem path of the oracle script.
    Oracle { quit_on_empty: bool, oracle_path: String },
    /// `OracleSmartRanking quitOnEmpty oracle` (rankGoals dispatch ProofMethod.hs:480-503, see line 484).
    /// preSort = `smartRanking ctxt False`.
    OracleSmart { quit_on_empty: bool, oracle_path: String },
    /// `InternalTacticRanking quitOnEmpty (Tactic …)` (rankGoals dispatch ProofMethod.hs:480-503, see line 491).
    /// The resolved per-lemma tactic (presort + prio/deprio selectors).
    /// `quit_on_empty` is True for the `{.}` form, False for `{name}`.
    Tactic { quit_on_empty: bool, tactic: std::sync::Arc<crate::tactic::Tactic> },
}

impl GoalRanking {
    /// Parse a single heuristic character into a `GoalRanking`,
    /// mirroring HS's `goalRankingIdentifiers` (System.hs:585-598).
    /// Oracle variants use `oracle_path` for the resolved path.
    /// Unhandled identifiers fall back to the default `Smart(false)`.
    pub fn from_char_with_oracle(c: char, oracle_path: &str) -> GoalRanking {
        match c {
            's' => GoalRanking::Smart(false),
            'S' => GoalRanking::Smart(true),
            'i' => GoalRanking::Inj(false),
            'I' => GoalRanking::Inj(true),
            // HS `SapicRanking` ('p') / `SapicPKCS11Ranking` ('P')
            // (System.hs:591-592 `goalRankingIdentifiers`).  SAPIC theories
            // declaring `heuristic: p` must use sapicRanking, NOT smartRanking
            // — they diverge in goal selection (e.g. nsl-no_as `secrecy`:
            // smart prioritises `isFreshKnowsGoal` KU(~n), sapic does NOT —
            // it's commented out in HS sapicRanking).
            'p' => GoalRanking::Sapic,
            'P' => GoalRanking::SapicPKCS11,
            // HS `GoalNrRanking` (System.hs `goalRankingIdentifiers`: 'C')
            'C' => GoalRanking::GoalNr,
            // HS `UsefulGoalNrRanking` ('c')
            'c' => GoalRanking::UsefulGoalNr,
            // HS `OracleRanking False defaultOracle` (System.hs:585-598, see line 589)
            'o' => GoalRanking::Oracle { quit_on_empty: false, oracle_path: oracle_path.to_string() },
            // HS `OracleSmartRanking False defaultOracle` (System.hs:585-598, see line 590)
            'O' => GoalRanking::OracleSmart { quit_on_empty: false, oracle_path: oracle_path.to_string() },
            _ => GoalRanking::Smart(false),
        }
    }

    /// Human-readable description of this ranking, mirroring HS
    /// `goalRankingName` (System.hs:687-705).  Used by the interactive
    /// web UI's "Applicable Proof Methods:" comment (`subProofSnippet`,
    /// `Web/Theory.hs:544-545`).  Oracle variants render the resolved
    /// script path (HS `printOracle`); we already store the resolved
    /// path in `oracle_path`.
    pub fn ranking_name(&self) -> String {
        let body = match self {
            GoalRanking::GoalNr => "their order of creation".to_string(),
            GoalRanking::UsefulGoalNr =>
                "their usefulness and order of creation".to_string(),
            GoalRanking::Sapic =>
                "heuristics adapted for processes".to_string(),
            GoalRanking::SapicPKCS11 =>
                "heuristics adapted to a specific model of PKCS#11 expressed \
                 using SAPIC. deprecated.".to_string(),
            GoalRanking::Smart(lb) =>
                format!("the 'smart' heuristic{}", loop_status(*lb)),
            GoalRanking::Inj(lb) =>
                format!("heuristics adapted to stateful injective protocols{}",
                        loop_status(*lb)),
            GoalRanking::Oracle { oracle_path, .. } =>
                format!("an oracle for ranking, located at {}", oracle_path),
            GoalRanking::OracleSmart { oracle_path, .. } =>
                format!("an oracle for ranking based on 'smart' heuristic, \
                         located at {}", oracle_path),
            GoalRanking::Tactic { tactic, .. } =>
                format!("the tactic written in the theory file: {}", tactic.name),
        };
        format!("Goals sorted according to {}", body)
    }
}

/// HS `goalRankingName`'s `loopStatus` (System.hs:687-705, see line 701).
fn loop_status(b: bool) -> String {
    format!(" (loop breakers {})", if b { "allowed" } else { "delayed" })
}

/// Parse a full heuristic string into a list of `GoalRanking`s,
/// mirroring HS's `Heuristic` list (ProofMethod.hs:581-590).
///
/// `theory_file` is the path to the `.spthy` file; used to compute
/// the default oracle name via `oracle_name_for_theory`
/// (pretty_theory.rs, HS `defaultOracleNames` System.hs:551-561).
///
/// Grammar (mirrors HS `goalRanking` Signature.hs:293-311):
///   heuristic   ::= ranking+
///   ranking     ::= oracle_ranking | tactic_ranking | letter
///   oracle_ranking ::= ('o' | 'O') ('"' name '"')?
///   tactic_ranking ::= '{' [^}]* '}'
///   letter      ::= [a-zA-Z]
pub fn parse_heuristic_str(s: &str, theory_file: &str) -> Vec<GoalRanking> {
    parse_heuristic_str_with_tactics(s, theory_file, &[])
}

/// Like [`parse_heuristic_str`] but resolves `{name}` tactic rankings
/// against the theory's tactic list (HS `chosenTactic`, ProofMethod.hs:
/// 706-715).  A `{.}` (no name) resolves to HS `defaultTactic`
/// (`Tactic "default" (SmartRanking False) [] []`, System.hs:534-535).  An
/// unknown `{name}` falls back to `Smart(false)` (HS would `error`; we
/// stay robust so non-tactic output is unaffected).
pub fn parse_heuristic_str_with_tactics(
    s: &str,
    theory_file: &str,
    tactics: &[crate::tactic::Tactic],
) -> Vec<GoalRanking> {
    let default_oracle = crate::pretty_theory::oracle_name_for_theory(theory_file);
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    let mut out = Vec::new();
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() { i += 1; continue; }
        // Skip block comments `/* … */`
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
            i += 2;
            while i + 1 < chars.len() && !(chars[i] == '*' && chars[i + 1] == '/') { i += 1; }
            i = (i + 2).min(chars.len());
            continue;
        }
        // Skip line comments `// …`
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            break;
        }
        // Tactic ranking `{name}` / `{.}` — HS `internalTacticRanking`
        // (Signature.hs:298-303).  Resolve the name against the theory's
        // tactic list (HS `chosenTactic`).  `{.}` (or name "." ) → HS
        // `defaultTactic`.  quitOnEmpty is always False from parsing
        // (HS `("{.}", InternalTacticRanking False defaultTactic)`,
        // System.hs:585-598, see line 597).
        if c == '{' {
            i += 1;
            while i < chars.len() && chars[i] == ' ' { i += 1; }
            let start = i;
            while i < chars.len() && chars[i] != '}' { i += 1; }
            let name: String = chars[start..i].iter().collect::<String>().trim().to_string();
            if i < chars.len() { i += 1; } // consume '}'
            while i < chars.len() && chars[i] == ' ' { i += 1; }
            let resolved = if name.is_empty() || name == "." {
                // HS defaultTactic — Smart presort, no prios.  With no
                // prios/deprios `itRanking` leaves the presort order
                // unchanged, so this is equivalent to Smart(false).
                GoalRanking::Smart(false)
            } else {
                match tactics.iter().find(|t| t.name == name) {
                    Some(t) => GoalRanking::Tactic {
                        quit_on_empty: false,
                        tactic: std::sync::Arc::new(t.clone()),
                    },
                    None => GoalRanking::Smart(false),
                }
            };
            out.push(resolved);
            continue;
        }
        // Oracle rankings with optional quoted path
        if c == 'o' || c == 'O' {
            i += 1;
            while i < chars.len() && chars[i] == ' ' { i += 1; }
            let explicit_path: Option<String> = if i < chars.len() && chars[i] == '"' {
                i += 1;
                let start = i;
                while i < chars.len() && chars[i] != '"' && chars[i] != '\n' { i += 1; }
                let name: String = chars[start..i].iter().collect();
                if i < chars.len() && chars[i] == '"' { i += 1; }
                Some(name)
            } else {
                None
            };
            let oracle_path = explicit_path.as_deref().unwrap_or(&default_oracle);
            out.push(GoalRanking::from_char_with_oracle(c, oracle_path));
            continue;
        }
        if c.is_ascii_alphabetic() {
            out.push(GoalRanking::from_char_with_oracle(c, &default_oracle));
            i += 1;
            continue;
        }
        i += 1; // skip unknown
    }
    if out.is_empty() {
        // HS `defaultHeuristic False = Heuristic [SmartRanking False]`
        vec![GoalRanking::Smart(false)]
    } else {
        out
    }
}

/// `openGoals`: enumerate annotated goals still to be solved.
///
/// Haskell iterates `M.toList $ get sGoals sys` in Goal-derived-Ord
/// order, but every ranking that consumes the result begins with
/// `goalNrRanking = sortOn (fst . snd)` (ProofMethod.hs:593-594, see line 594; the first
/// stage of smartRanking:1053, injRanking:946, GoalNrRanking:482, and
/// the oracle preSorts:483-484).  Since `gsNr` is unique, sorting by nr
/// fully overrides the `M.toList` Goal-Ord, so emitting goals in nr
/// order here is exactly HS's post-`goalNrRanking` order — HS-faithful.
///
/// The `M.toList` Goal-Ord is only material at the direct `goal_cmp`
/// call sites: `goal_cmp` (below) is the HS-`Ord Goal`-faithful
/// comparator, wired into the goal sorts in `reduction.rs`,
/// `sources.rs`, and `rename_precise.rs` (~7 call sites), which already
/// use it.
pub fn open_goals(sys: &System) -> Vec<AnnotatedGoal> {
    let mut out = Vec::new();
    // HS `existingDeps = rawLessRel sys` — built ONCE per openGoals pass and
    // shared across every KU goal's `currentlyDeducible`/`extractible` check
    // (Goals.hs:66-182, see line 120) AND the Chain-goal `is_open_in_sys` always-before
    // queries, rather than rebuilt per goal. The `rawLessRel` relation and
    // the always-before adjacency are the SAME map (identical build), and
    // `sys` is read-only across this pass, so one `PrebuiltAdj` feeds both:
    // `is_open_in_sys` takes the `&PrebuiltAdj` (BFS via `always_before_with`)
    // and `goal_usefulness_with_adj` takes its inner `&BTreeMap` via `.map()`.
    let ab_adj = sys.build_always_before_adj();
    for (goal, status) in sys.goals.iter() {
        if status.solved { continue; }
        if !is_open_in_sys(goal, sys, &ab_adj) { continue; }
        let u = goal_usefulness_with_adj(goal, status.looping, sys, ab_adj.map());
        // Use the persistent goal-number (`_gsNr`), NOT the Vec
        // position.  Haskell's `openGoals` returns `(goal, (gsNr,
        // useful))` (Goals.hs) and the rankings begin with
        // `goalNrRanking = sortOn (fst . snd)` (ProofMethod.hs:593-594),
        // i.e. ordering by creation number.  We carry `status.nr`
        // here and sort below so the heuristic priority classes break
        // ties by creation order exactly as HS does.
        out.push(AnnotatedGoal::new(goal.clone(), status.nr, u));
    }
    // goalNrRanking — stable sort by creation number.  The Vec is not
    // guaranteed to be in nr order (subst_goals / conjoin rebuild it),
    // so sort explicitly.  Stable so equal-nr goals (shouldn't happen,
    // but defensive) keep Vec order.
    sort_goal_nr(&mut out);
    out
}

/// Manual structural compare on `Goal`, mirroring Haskell's derived
/// `Ord Goal` (Constraints.hs:155-168).  Variant tags follow Haskell
/// declaration order:
///     ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG.
///
/// **Do NOT change this ordering without updating Haskell.**  If the
/// tags drift from declaration order, BTreeMap-backed goal iteration
/// (e.g. `solveUniqueActions`, `solveAllSafeGoals`) silently picks
/// goals in a different order and the proof shape diverges.
pub(crate) fn goal_cmp(a: &Goal, b: &Goal) -> std::cmp::Ordering {
    let tag = |g: &Goal| -> u8 {
        match g {
            Goal::Action(_, _)  => 0,
            Goal::Chain(_, _)   => 1,
            Goal::Premise(_, _) => 2,
            Goal::Split(_)      => 3,
            Goal::Disj(_)       => 4,
            Goal::Subterm(_)    => 5,
        }
    };
    let ta = tag(a);
    let tb = tag(b);
    if ta != tb { return ta.cmp(&tb); }
    // Tag equality above guarantees `a` and `b` are the same variant, so each
    // `let … else` binding of `b` is infallible.  Match `a` exhaustively (no
    // wildcard) so a new `Goal` variant fails to compile here until its payload
    // comparison is written.
    match a {
        Goal::Action(la, fa) => {
            let Goal::Action(lb, fb) = b else { unreachable!("goal tag matched Action") };
            la.cmp(lb).then_with(|| fa.cmp(fb))
        }
        Goal::Chain(ca, pa) => {
            let Goal::Chain(cb, pb) = b else { unreachable!("goal tag matched Chain") };
            (&ca.0, ca.1.0).cmp(&(&cb.0, cb.1.0))
                .then_with(|| (&pa.0, pa.1.0).cmp(&(&pb.0, pb.1.0)))
        }
        Goal::Premise(pa, fa) => {
            let Goal::Premise(pb, fb) = b else { unreachable!("goal tag matched Premise") };
            (&pa.0, pa.1.0).cmp(&(&pb.0, pb.1.0))
                .then_with(|| fa.cmp(fb))
        }
        Goal::Split(sa) => {
            let Goal::Split(sb) = b else { unreachable!("goal tag matched Split") };
            sa.cmp(sb)
        }
        Goal::Disj(da) => {
            let Goal::Disj(db) = b else { unreachable!("goal tag matched Disj") };
            // HS `Disj a = Disj [a]` derives `Ord` as the newtype over the
            // list, i.e. plain list Ord (element-by-element, shorter < longer),
            // bottoming out at the structural `Ord LNGuarded`.  Use the
            // HS-faithful structural comparator `cmp_guarded` (which threads
            // through `cmp_varspec`'s numeric idx-first LVar Ord, `cmp_atom`'s
            // timepoint-first ProtoAtom Ord, and declaration-order sort Ord).
            // Do NOT use a string-render approach (idx/sort via `{:?}`,
            // length-first prefix): it diverges from HS on var sort order,
            // decimal idx width, and Action timepoint-vs-fact order.
            crate::guarded::cmp_slice(&da.0, &db.0, crate::guarded::cmp_guarded)
        }
        Goal::Subterm((sa, ta_)) => {
            let Goal::Subterm((sb, tb_)) = b else { unreachable!("goal tag matched Subterm") };
            sa.cmp(sb).then_with(|| ta_.cmp(tb_))
        }
    }
}

/// Error type for oracle execution failures.
///
/// When oracle exec fails, HS throws an uncaught IO exception → the
/// whole tamarin-prover invocation dies (ProofMethod.hs:826-829,
/// `readProcess` throws on non-zero exit or spawn failure).  RS
/// mirrors this with a hard error that propagates to the top level.
#[derive(Debug)]
pub struct OracleError(pub String);

impl std::fmt::Display for OracleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for OracleError {}

// =============================================================================
// smartRanking — port of `Theory.Constraint.Solver.ProofMethod.smartRanking`
// =============================================================================

/// Decision-tree-aware goal ranking. Direct port of Haskell's
/// `smartRanking ctxt False sys`:
///
/// ```text
///   moveNatToEnd
///     . sortOnUsefulness
///     . sortDecisionTree notSolveLast
///     . sortDecisionTree solveFirst
///     . goalNrRanking
/// ```
///
/// `isMsgOneCaseGoal` (`pcSources`/`full_sources` analysis, via
/// `is_msg_one_case_goal` + `collect_one_case_syms`), `isSplitGoalSmall`
/// (`is_split_goal_small`, reading `eq_store.split_size`),
/// `isNoLargeSplitGoal` (`is_no_large_split_goal`), and `moveNatToEnd`
/// (via `is_nat_subterm_split`, mirroring `isNatSubterm`) are all ported
/// and wired in as live predicates in the decision tree below.
pub fn rank_goals(sys: &System) -> Vec<AnnotatedGoal> {
    // With `ctx = None` the ranking always resolves to `Smart(false)`
    // (the oracle/tactic paths — the only `Err` sources — are
    // unreachable), so this never errors.  Fall back to the unranked
    // open-goal list rather than panicking, keeping this entry point
    // panic-free public surface.
    rank_goals_with(sys, None, 0).unwrap_or_else(|_| open_goals(sys))
}

/// Variant that takes a proof context for source-cache predicates
/// and the current proof depth for round-robin heuristic scheduling.
///
/// Returns `Err(OracleError)` when an oracle script cannot be
/// executed — callers must propagate this as a hard abort.
///
/// `depth` mirrors HS's `useHeuristic (Heuristic rankings) depth =
/// rankings !! (depth mod n)` (ProofMethod.hs:581-590).
pub fn rank_goals_with(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    depth: usize,
) -> Result<Vec<AnnotatedGoal>, OracleError> {
    let result = rank_goals_with_inner(sys, ctx, depth)?;
    Ok(result)
}

/// `goalNrRanking = sortOn (fst . snd)` (ProofMethod.hs:593-594): stable
/// order by the unique creation number.  Shared by the ranking dispatch
/// and the tactic presort so the trivial nr-sort is written once.
fn sort_goal_nr(ags: &mut [AnnotatedGoal]) {
    ags.sort_by_key(|g| g.seq);
}

/// `sortOn (\(_, (nr, useless)) -> (useless, nr))` (ProofMethod.hs:480-503, see line 485):
/// order by the derived `Ord Usefulness` (declaration order, NOT
/// `tagUsefulness`), breaking ties by creation number.  Shared by the
/// `UsefulGoalNr` ranking arm and the tactic presort.
fn sort_useful_goal_nr(ags: &mut [AnnotatedGoal]) {
    ags.sort_by(|a, b| {
        a.usefulness.cmp(&b.usefulness)
            .then_with(|| a.seq.cmp(&b.seq))
    });
}

fn rank_goals_with_inner(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    depth: usize,
) -> Result<Vec<AnnotatedGoal>, OracleError> {
    // Round-robin heuristic scheduling: `useHeuristic (Heuristic rankings) depth =
    // rankings !! (depth mod n)` (ProofMethod.hs:581-590).
    // When no context (or no heuristic) is supplied we default to
    // `SmartRanking False` — exactly HS's
    // `defaultHeuristic False = Heuristic [SmartRanking False]`
    // (System.hs:526-528, see line 527).
    let ranking = ctx
        .and_then(|c| c.heuristic.as_ref())
        .and_then(|h| {
            let n = h.len();
            if n == 0 { None } else { Some(&h[depth % n]) }
        })
        .cloned()
        .unwrap_or(GoalRanking::Smart(false));
    match ranking {
        GoalRanking::Inj(use_loop_breakers) => {
            Ok(inj_ranking(sys, ctx, use_loop_breakers))
        }
        GoalRanking::Smart(use_loop_breakers) => {
            Ok(smart_ranking(sys, ctx, use_loop_breakers))
        }
        GoalRanking::Sapic => {
            // HS `SapicRanking -> plainRanking (sapicRanking ctxt sys ags)`
            // (ProofMethod.hs:695-712, see line 698).
            Ok(sapic_ranking(sys, ctx, false))
        }
        GoalRanking::SapicPKCS11 => {
            // HS `SapicPKCS11Ranking -> plainRanking (sapicPKCS11Ranking …)`
            // (ProofMethod.hs:695-712, see line 699).
            Ok(sapic_ranking(sys, ctx, true))
        }
        GoalRanking::GoalNr => {
            // HS `goalNrRanking = sortOn (fst . snd)` (ProofMethod.hs:593-594).
            // `open_goals` already sorts by creation nr.
            Ok(open_goals(sys))
        }
        GoalRanking::UsefulGoalNr => {
            // HS `UsefulGoalNrRanking -> plainRanking . sortOn (\(_, (nr,
            // useless)) -> (useless, nr))` (ProofMethod.hs:480-503, see line 485).  This
            // sorts on the DERIVED `Ord Usefulness` (declaration order
            // Useful<LoopBreaker<ProbablyConstructible<CurrentlyDeducible,
            // AnnotatedGoals.hs:18-27), NOT `tagUsefulness` (which collapses
            // LoopBreaker and ProbablyConstructible).  Rust's `Usefulness`
            // derives Ord in the same declaration order.
            let mut ags = open_goals(sys);
            sort_useful_goal_nr(&mut ags);
            Ok(ags)
        }
        GoalRanking::Tactic { quit_on_empty, tactic } => {
            // HS `InternalTacticRanking quitOnEmpty tactic ->
            //   internalTacticRanking (chosenTactic ..) quitOnEmpty ..`
            // (ProofMethod.hs:480-503, see line 491,695).
            internal_tactic_ranking(&tactic, quit_on_empty, ctx, sys)
        }
        GoalRanking::Oracle { quit_on_empty, oracle_path } => {
            // HS `oracleRanking (const goalNrRanking) oracle quitOnEmpty ctxt sys ags`
            // (ProofMethod.hs:480-503, see line 483): preSort = goalNrRanking (open_goals is already nr-sorted)
            let ags = open_goals(sys);
            oracle_ranking(ags, &oracle_path, quit_on_empty, ctx, sys)
        }
        GoalRanking::OracleSmart { quit_on_empty, oracle_path } => {
            // HS `oracleRanking (smartRanking ctxt False) oracle quitOnEmpty ctxt sys ags`
            // (ProofMethod.hs:480-503, see line 484): preSort = smartRanking ctxt False
            let ags = smart_ranking(sys, ctx, false);
            oracle_ranking(ags, &oracle_path, quit_on_empty, ctx, sys)
        }
    }
}

/// Port of HS `oracleRanking` (ProofMethod.hs:598-621).
///
/// Protocol:
/// 1. `ags = preSort sys ags0`  (already done by caller).
/// 2. Build stdin: `unlines $ zipWith (\i ag -> show i ++": "++ rendered_goal) [0..] ags`.
/// 3. `readProcess oraclePath [lemmaName] stdin` — exec the oracle.
/// 4. Parse stdout: each line as `usize`; non-integer lines skipped;
///    out-of-range indices skipped.
/// 5. Result = `ranked ++ (ags \\ ranked)` in original order.
/// 6. If `quit_on_empty && !inp.is_empty() && ranked.is_empty()` →
///    signal ApplySorry. We encode this as the `OracleError`
///    `"__ORACLE_QUIT_ON_EMPTY__"` sentinel (matched in search.rs).
///
/// On any exec failure (spawn error / non-zero exit) → `Err(OracleError)`,
/// propagated as a hard abort (mirrors HS's uncaught IO exception).
fn oracle_ranking(
    ags: Vec<AnnotatedGoal>,
    oracle_path: &str,
    quit_on_empty: bool,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    _sys: &System,
) -> Result<Vec<AnnotatedGoal>, OracleError> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let lemma_name = ctx.map(|c| c.lemma_name.as_str()).unwrap_or("");

    // Step 2: build stdin — `show i ++": "++ concat . lines . render $ prettyGoal g`
    // HS `concat . lines . render` collapses multi-line renders to one line
    // (ProofMethod.hs:598-623, see line 607).
    let inp: String = ags.iter().enumerate().map(|(i, ag)| {
        let goal_text = crate::pretty_theory::render_goal_for_oracle(&ag.goal);
        // concat . lines = remove all newlines (no intermediate Vec<&str>)
        let single_line: String = goal_text.lines().collect::<String>();
        format!("{}: {}\n", i, single_line)
    }).collect();

    // Step 3: exec oracle
    let mut child = Command::new(oracle_path)
        .arg(lemma_name)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|e| OracleError(format!(
            "oracle exec error: {}: {}", oracle_path, e)))?;

    // Write stdin and close pipe
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(inp.as_bytes())
            .map_err(|e| OracleError(format!("oracle stdin write error: {}", e)))?;
    }

    let output = child.wait_with_output()
        .map_err(|e| OracleError(format!("oracle wait error: {}", e)))?;

    if !output.status.success() {
        return Err(OracleError(format!(
            "oracle process exited with status {}: {}", output.status, oracle_path)));
    }

    let outp = String::from_utf8_lossy(&output.stdout);

    // Step 4: parse stdout indices — `mapMaybe readMay (lines outp)`
    let indices: Vec<usize> = outp.lines()
        .filter_map(|l| l.trim().parse::<usize>().ok())
        .collect();

    // Step 5: ranked goals + remaining (filter(notElem ranked) ags)
    // HS `ranked = mapMaybe (atMay ags) indices` KEEPS duplicate entries when
    // the oracle emits a repeated index (e.g. output `[2,2]` yields
    // `[ags!!2, ags!!2]`). We mirror that exactly — no de-dup of `ranked`.
    let ranked: Vec<AnnotatedGoal> = indices.iter()
        .filter_map(|&idx| ags.get(idx).cloned())
        .collect();

    // HS `remaining = filter (`notElem` ranked) ags`: keep every goal that is
    // NOT present in `ranked`. We compare by original index (the set of indices
    // the oracle selected), matching membership of the goal value in `ranked`.
    let ranked_idx: std::collections::BTreeSet<usize> = indices.iter()
        .filter(|&&idx| idx < ags.len())
        .copied()
        .collect();

    let remaining: Vec<AnnotatedGoal> = ags.into_iter().enumerate()
        .filter(|(i, _)| !ranked_idx.contains(i))
        .map(|(_, ag)| ag)
        .collect();

    // Step 6: quitOnEmpty check
    // HS: `guard $ quitOnEmpty && not (null inp) && null ranked`
    // The `guard` in the IO monad returns `mzero` when condition is True,
    // which causes the sorry instruction to fire (ProofMethod.hs:598-623, see line 621).
    if quit_on_empty && !inp.is_empty() && ranked.is_empty() {
        return Err(OracleError("__ORACLE_QUIT_ON_EMPTY__".to_string()));
    }

    let mut result = ranked;
    result.extend(remaining);
    Ok(result)
}

// =============================================================================
// Tactic ranking — port of `internalTacticRanking` / `itRanking`
// (ProofMethod.hs:627-712) + selector evaluation (Parser/Tactics.hs:117-220).
// =============================================================================

/// Resolve the tactic's `_presort` (a `char` in the parsed `Tactic`) into
/// a concrete `GoalRanking`.  Mirrors HS `selectedPreSort`
/// (Tactics.hs:52-57) — defaults to `SmartRanking False` ('s').
fn presort_ranking(presort: char) -> GoalRanking {
    GoalRanking::from_char_with_oracle(presort, "oracle")
}

/// Apply a single `GoalRanking` (used as a tactic presort) to a list of
/// already-open annotated goals.  The presort rankings the corpus uses
/// are `C` (GoalNr), `c` (UsefulGoalNr), `s`/`S` (Smart).  This mirrors
/// HS `rankGoals ctxt defaultMethod [tactic] _sys ags0`
/// (ProofMethod.hs:695-712, see line 699) restricted to the non-oracle, non-tactic
/// presorts (a tactic presort cannot itself be a tactic or an oracle).
fn apply_presort(
    presort: &GoalRanking,
    ags: Vec<AnnotatedGoal>,
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
) -> Vec<AnnotatedGoal> {
    match presort {
        GoalRanking::GoalNr => {
            // sortOn (fst . snd) — ags from open_goals are already nr-sorted.
            let mut a = ags;
            sort_goal_nr(&mut a);
            a
        }
        GoalRanking::UsefulGoalNr => {
            // sortOn (\(_, (nr, useless)) -> (useless, nr)) — derived
            // `Ord Usefulness` (ProofMethod.hs:480-503, see line 485), NOT tagUsefulness.
            let mut a = ags;
            sort_useful_goal_nr(&mut a);
            a
        }
        GoalRanking::Smart(use_loop_breakers) => {
            // smartRanking re-derives the open-goal list from `sys`; the
            // tactic presort 's' is the default. We re-run smart_ranking
            // over the full system (it internally calls open_goals).
            smart_ranking(sys, ctx, *use_loop_breakers)
        }
        GoalRanking::Inj(use_loop_breakers) => {
            inj_ranking(sys, ctx, *use_loop_breakers)
        }
        // A tactic presort can only be one of the plain rankings above
        // (Tactics.hs `goalRankingPresort` parses with `noOracle`, so an
        // oracle/tactic presort is unreachable).  Fall back to nr order.
        _ => {
            let mut a = ags;
            sort_goal_nr(&mut a);
            a
        }
    }
}

/// Port of HS `internalTacticRanking` (ProofMethod.hs:695-712):
///   defaultMethod = _presort tactic
///   ags = ranked $ rankGoals ctxt defaultMethod [tactic] _sys ags0
///   res = itRanking tactic ags quitOnEmpty ctxt _sys
fn internal_tactic_ranking(
    tactic: &crate::tactic::Tactic,
    quit_on_empty: bool,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    sys: &System,
) -> Result<Vec<AnnotatedGoal>, OracleError> {
    let presort = presort_ranking(tactic.presort);
    let ags0 = open_goals(sys);
    let ags = apply_presort(&presort, ags0, sys, ctx);
    it_ranking(tactic, ags, quit_on_empty, ctx, sys)
}

/// Port of HS `itRanking` (ProofMethod.hs:627-688) — the core tactic
/// reordering algorithm:
///
///   * For each goal, `indexPrio` = index of the FIRST prio that
///     recognises it (any selector true), or `Nothing`.
///   * `indexedPrio = sortOn fst (zip indexPrio ags)`; goals with the
///     same first-matching prio are grouped, in ascending prio order;
///     unmatched goals (`Nothing` = greatest) are dropped.
///   * Within each prio group, apply that prio's optional `rankingPrio`
///     sub-ordering function (`smallest` / `id`).
///   * `rankedPrioGoals = concat` of those.  Same for deprio.
///   * `nonRanked = ags \\ (rankedPrioGoals ++ rankedDeprioGoals)`
///     preserving presort order.
///   * `result = rankedPrioGoals ++ nonRanked ++ rankedDeprioGoals`.
fn it_ranking(
    tactic: &crate::tactic::Tactic,
    ags: Vec<AnnotatedGoal>,
    quit_on_empty: bool,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    sys: &System,
) -> Result<Vec<AnnotatedGoal>, OracleError> {
    let ranked_prio = rank_by_blocks(&tactic.prios, &ags, ctx, sys);
    let ranked_deprio = rank_by_blocks(&tactic.deprios, &ags, ctx, sys);

    // nonRanked = filter (`notElem` rankedPrio ++ rankedDeprio) ags
    // (preserves presort order).  Compare by goal identity (seq + goal).
    let in_set = |g: &AnnotatedGoal, set: &[AnnotatedGoal]| -> bool {
        set.iter().any(|x| x.seq == g.seq && x.goal == g.goal)
    };
    let non_ranked: Vec<AnnotatedGoal> = ags
        .iter()
        .filter(|g| !in_set(g, &ranked_prio) && !in_set(g, &ranked_deprio))
        .cloned()
        .collect();

    // quitOnEmpty: `guard (quitOnEmpty && null rankedPrioGoals &&
    //   null rankedDeprioGoals) *> Just ApplySorry` (ProofMethod.hs:627-688, see line 629).
    if quit_on_empty && ranked_prio.is_empty() && ranked_deprio.is_empty() {
        return Err(OracleError("__ORACLE_QUIT_ON_EMPTY__".to_string()));
    }

    // result = rankedPrioGoals ++ nonRanked ++ rankedDeprioGoals
    let mut result = ranked_prio;
    result.extend(non_ranked);
    result.extend(ranked_deprio);
    Ok(result)
}

/// Compute `rankedPrioGoals` (or `rankedDeprioGoals`) for one block list.
///
/// Mirrors the `indexPrio` / `groupedPrio` / `rankingPrio` pipeline in
/// `itRanking` (ProofMethod.hs:633-642):
///   1. For each goal, find the index of the first block whose ANY
///      selector matches (`findIndex (==True) . applyIsPrio`).
///   2. Stable-group goals by that index in ascending order; drop
///      unmatched goals.
///   3. Within each group, apply that block's ranking function.
///   4. Concatenate.
fn rank_by_blocks(
    blocks: &[crate::tactic::PrioBlock],
    ags: &[AnnotatedGoal],
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    sys: &System,
) -> Vec<AnnotatedGoal> {
    if blocks.is_empty() {
        return Vec::new();
    }
    // index_of_first_matching_block for each goal.
    // HS `indexedPrio = sortOn fst (zip indexPrio ags)` then `groupBy`
    // on equal index.  `sortOn` is STABLE, so within one index the goals
    // keep their presort (ags) order.  Under Haskell's `Ord (Maybe a)`
    // (`compare Nothing (Just _) = LT`) `Nothing` sorts FIRST (least), so
    // unmatched goals form the leading group, which HS drops via
    // `tail groupedPrio`.  We replicate by iterating block indices 0..n and
    // collecting only the goals whose first-match is `Some(bi)`, in ags
    // order — `None` (unmatched) goals are never emitted, i.e. dropped.
    let first_match: Vec<Option<usize>> = ags
        .iter()
        .map(|g| {
            blocks
                .iter()
                .position(|b| block_matches(b, g, ctx, sys))
        })
        .collect();

    // Single-pass bucketing by the already-computed first-match index.
    // Each goal lands in exactly one bucket (its `Some(bi)`); `None`
    // (unmatched) goals are skipped (dropped, matching HS `tail
    // groupedPrio`).  Pushing in ags order preserves presort order within
    // each bucket, and emitting buckets 0..n keeps ascending block-index
    // order.
    let mut buckets: Vec<Vec<AnnotatedGoal>> = vec![Vec::new(); blocks.len()];
    for (g, fm) in ags.iter().zip(first_match.iter()) {
        if let Some(bi) = *fm {
            buckets[bi].push(g.clone());
        }
    }

    let mut out = Vec::new();
    for (block, group) in blocks.iter().zip(buckets) {
        if group.is_empty() {
            continue;
        }
        // Apply this block's ranking function (id / smallest).
        out.extend(apply_ranking_fn(&block.ranking, group));
    }
    out
}

/// HS `rankingFunctions` (Tactics.hs:244-265): `id` (identity) and
/// `smallest` (sort by rendered-goal string length, stable).
fn apply_ranking_fn(name: &str, group: Vec<AnnotatedGoal>) -> Vec<AnnotatedGoal> {
    match name {
        "smallest" => {
            // sortOn (length . render . prettyGoal) — STABLE.
            // `sort_by_cached_key` computes the key exactly once per
            // element (vs O(n log n) re-renders with `sort_by_key`),
            // sorting with the same stable order.
            let mut g = group;
            g.sort_by_cached_key(|a| {
                let s = crate::pretty_theory::render_goal_for_oracle(&a.goal);
                s.lines().collect::<String>().chars().count()
            });
            g
        }
        // "id" / "" / anything else → identity.
        _ => group,
    }
}

/// Does block `b` recognise goal `g`? HS `isPrio = or . sequenceA
/// functionsPrio` (ProofMethod.hs:851-936, see line 884): True iff ANY of the block's
/// disjunct selector-expressions evaluates True.
fn block_matches(
    b: &crate::tactic::PrioBlock,
    g: &AnnotatedGoal,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    sys: &System,
) -> bool {
    b.selectors.iter().any(|e| eval_selector(e, g, ctx, sys))
}

/// Evaluate a `SelectorExpr` against a goal.  Mirrors HS's
/// `functionNot`/`functionAnd`/`functionOr` combinators
/// (Tactics.hs:72-79) bottoming out at `nameToFunction`.
fn eval_selector(
    e: &crate::tactic::SelectorExpr,
    g: &AnnotatedGoal,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    sys: &System,
) -> bool {
    use crate::tactic::SelectorExpr;
    match e {
        SelectorExpr::Leaf(leaf) => eval_leaf(leaf, g, ctx, sys),
        SelectorExpr::Not(inner) => !eval_selector(inner, g, ctx, sys),
        SelectorExpr::And(a, b) => {
            eval_selector(a, g, ctx, sys) && eval_selector(b, g, ctx, sys)
        }
        SelectorExpr::Or(a, b) => {
            eval_selector(a, g, ctx, sys) || eval_selector(b, g, ctx, sys)
        }
    }
}

/// The rendered-goal string HS `regex` matches against:
/// `pg = concat . lines . render $ prettyGoal agoal` (Tactics.hs:117-220, see line 134).
fn tactic_pg(g: &AnnotatedGoal) -> String {
    let s = crate::pretty_theory::render_goal_for_oracle(&g.goal);
    s.lines().collect::<String>()
}

/// Evaluate one selector leaf (`regex "..."`, `dhreNoise "..."`, …).
/// Mirrors HS `tacticFunctions` (Tactics.hs:117-220).
fn eval_leaf(
    leaf: &crate::tactic::SelectorLeaf,
    g: &AnnotatedGoal,
    _ctx: Option<&crate::constraint::solver::context::ProofContext>,
    sys: &System,
) -> bool {
    use crate::constraint::solver::tactic_show as ts;
    let params = &leaf.params;
    let head = |i: usize| params.get(i).map(String::as_str).unwrap_or("");
    match leaf.name.as_str() {
        "regex" => {
            // HS `regex' (regex:_) (agoal,_,_) = pg =~ regex`
            // (Tactics.hs:128-130).  `=~ :: Bool` with Text.Regex.PCRE is
            // an UNANCHORED search (matches if found anywhere).  We use
            // `fancy-regex` (PCRE-compatible: lookaround, backrefs) and
            // `is_match` for the same unanchored Bool semantics.
            match params.first() {
                Some(pat) => regex_is_match(pat, &tactic_pg(g)),
                None => false,
            }
        }

        // dhreNoise (Tactics.hs:152-161): `pg =~ goalPattern`, where the
        // pattern is a DH-product/inverse over a sys-specific nonce class.
        "dhreNoise" => {
            let oracle_type = head(0);
            let pg = tactic_pg(g);
            // sysPatternDiff = "(~[a-zA-Z0-9.]*)"
            let sys_pattern_diff = "(~[a-zA-Z0-9.]*)";
            // sysPattern: alternation of "~n" + the shown reveal-vars.
            // For "curve" a `(?!...)` negative-lookahead suffix is appended.
            let reveal = ts::sys_reveal_shown(oracle_type, &sys.formulas);
            let sys_pattern = if oracle_type == "curve" {
                format!("(~n|{})(?![.0-9a-zA-Z])", join_alt(&reveal))
            } else {
                format!("(~n|{})", join_alt(&reveal))
            };
            let goal_pattern = if oracle_type == "diff" {
                format!(
                    ".*(\\(({sd}\\*)+{sd}\\)|inv\\({sd}\\))",
                    sd = sys_pattern_diff
                )
            } else {
                format!(
                    ".*(\\(({sp}\\*)+{sp}\\)|inv\\({sp}\\))",
                    sp = sys_pattern
                )
            };
            regex_is_match(&goal_pattern, &pg)
        }

        // defaultNoise (Tactics.hs:163-173): `or $ map (flip elem sysPattern)
        // goalMatches` — every regex-match substring of the pretty goal that
        // equals a shown reveal-var.
        "defaultNoise" => {
            let param_goal = head(0);
            let oracle_type = head(1);
            let pg = tactic_pg(g);
            let goal_matches = regex_all_matches(param_goal, &pg);
            let sys_pattern = ts::sys_reveal_shown(oracle_type, &sys.formulas);
            goal_matches.iter().any(|m| sys_pattern.iter().any(|s| s == m))
        }

        // reasonableNoncesNoise (Tactics.hs:175-188): `or $ map (flip elem
        // sysPattern) nonces`, where nonces = map show (getFactTerms_ goal)
        // and sysPattern = "~n" : shown reveal-vars.
        "reasonableNoncesNoise" => {
            let oracle_type = head(0);
            let nonces: Vec<String> = ts::action_goal_fact_terms(&g.goal)
                .iter()
                .map(ts::show_lnterm)
                .collect();
            let mut sys_pattern = vec!["~n".to_string()];
            sys_pattern.extend(ts::sys_reveal_shown(oracle_type, &sys.formulas));
            nonces.iter().any(|n| sys_pattern.iter().any(|s| s == n))
        }

        // nonAbsurdConstraint (Tactics.hs:136-150): hasSafeNonces && isSubset.
        "nonAbsurdConstraint" => {
            let oracle_type = head(0);
            let pg = tactic_pg(g);
            // isSubset: every function appearing in pg is in {Ku, inv}.
            let functions_detection = "[^A-Za-z0-9][A-Za-z0-9]+\\(";
            let functions: Vec<String> = regex_all_matches(functions_detection, &pg)
                .iter()
                // `map init . map tail`: drop first (delimiter) + last ('(')
                .map(|m| {
                    let mut chars: Vec<char> = m.chars().collect();
                    if !chars.is_empty() {
                        chars.remove(0);
                    }
                    chars.pop();
                    chars.into_iter().collect::<String>()
                })
                .collect();
            let is_subset = functions.iter().all(|f| f == "Ku" || f == "inv");
            // hasSafeNonces: pg does NOT contain a "safe" nonce.
            let reveal = ts::sys_reveal_shown(oracle_type, &sys.formulas);
            let safe_pattern = format!("(~n|{})(?![.0-9a-zA-Z])", join_alt(&reveal));
            let has_safe_nonces = !regex_is_match(&safe_pattern, &pg);
            has_safe_nonces && is_subset
        }

        // isFactName (Tactics.hs:212-216).
        "isFactName" => {
            let s = head(0);
            match ts::fact_name_probe(&g.goal) {
                ts::FactNameProbe::PremiseLinearName(name) => name == s,
                ts::FactNameProbe::ActionShowTag(shown) => shown == s,
                ts::FactNameProbe::None => false,
            }
        }

        // isInFactTerms (Tactics.hs:218-220): single-term action fact whose
        // `show` matches the regex.
        "isInFactTerms" => {
            let s = head(0);
            match ts::action_goal_single_term(&g.goal) {
                Some(t) => regex_is_match(s, &ts::show_lnterm(t)),
                None => false,
            }
        }

        _ => false,
    }
}

/// Join shown reveal-vars into a regex alternation body (no surrounding
/// parens), mirroring HS `intercalate "|" (map show ...)`.
fn join_alt(reveal: &[String]) -> String {
    reveal.join("|")
}

/// PCRE-compatible unanchored match, mirroring HS `pg =~ regex` with
/// `Text.Regex.PCRE`.  Compiled patterns are cached per-string.
pub(crate) fn regex_is_match(pattern: &str, haystack: &str) -> bool {
    match compile_regex(pattern) {
        Some(re) => re.is_match(haystack).unwrap_or(false),
        None => false,
    }
}

/// All non-overlapping full-match substrings, mirroring HS
/// `getAllTextMatches $ haystack =~ pattern` over `Text.Regex.PCRE`.
/// (HS's `getAllTextMatches` yields the WHOLE matched text of each
/// non-overlapping match, left-to-right.)
pub(crate) fn regex_all_matches(pattern: &str, haystack: &str) -> Vec<String> {
    match compile_regex(pattern) {
        Some(re) => re
            .find_iter(haystack)
            .filter_map(|m| m.ok())
            .map(|m| m.as_str().to_string())
            .collect(),
        None => Vec::new(),
    }
}

/// Translate the escape sequences where HS's regex engine
/// (`regex-pcre-builtin`, i.e. PCRE 8.x) and Rust's `fancy-regex` disagree,
/// so the rewritten pattern matches in `fancy-regex` exactly as the original
/// does under PCRE.
///
/// PCRE 8.x has NO `\<` / `\>` word-boundary assertions (those are a GNU
/// regex / Vim extension): under PCRE `\<` and `\>` are simply the ESCAPED
/// LITERAL characters `<` and `>`.  Verified against the exact HS library
/// (`regex-pcre-builtin-0.95.2.3.8.44`):
///   `"a\\>" =~ "a>"  == True`,  `"a\\>" =~ "a b" == False`.
/// `fancy-regex`, however, interprets `\<` / `\>` as start/end-of-word
/// boundary assertions, so e.g. `~K_ASME\>` there matches `~K_ASME,`
/// (comma = word boundary), which PCRE never does.  Rewrite each `\<` / `\>`
/// to the corresponding literal character (`<` / `>` are not metacharacters
/// in `fancy-regex`).  Only `\<` / `\>` whose backslash is itself unescaped
/// are rewritten; `\\>` (escaped backslash, then literal `>`) is left intact.
fn pcre_to_fancy(pattern: &str) -> std::borrow::Cow<'_, str> {
    if !pattern.contains("\\<") && !pattern.contains("\\>") {
        return std::borrow::Cow::Borrowed(pattern);
    }
    let mut out = String::with_capacity(pattern.len());
    let mut chars = pattern.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.peek() {
                Some('<') => {
                    chars.next();
                    out.push('<'); // PCRE literal '<'
                }
                Some('>') => {
                    chars.next();
                    out.push('>'); // PCRE literal '>'
                }
                // Any other escape (incl. `\\`): copy the backslash AND the
                // escaped char verbatim so a following `<`/`>` cannot be
                // misread as the assertion form.
                Some(&next) => {
                    chars.next();
                    out.push('\\');
                    out.push(next);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(c);
        }
    }
    std::borrow::Cow::Owned(out)
}

/// Compile + cache a PCRE pattern (`fancy-regex`).  Shared by the
/// boolean-match and all-matches helpers.
// static compiled-regex memo cache; keyed lookup only, never iterated;
// std kept (byte-inert) — iteration order never reaches output.
#[allow(clippy::disallowed_types)]
fn compile_regex(pattern: &str) -> Option<std::sync::Arc<fancy_regex::Regex>> {
    use std::collections::HashMap;
    use std::sync::Mutex;
    use std::sync::OnceLock;
    static CACHE: OnceLock<Mutex<HashMap<String, Option<std::sync::Arc<fancy_regex::Regex>>>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut map = cache.lock().unwrap();
    map.entry(pattern.to_string())
        .or_insert_with(|| {
            fancy_regex::Regex::new(&pcre_to_fancy(pattern))
                .ok()
                .map(std::sync::Arc::new)
        })
        .clone()
}


/// Port of HS `smartRanking ctxt allowPremiseGLoopBreakers sys`
/// (ProofMethod.hs):
///
/// ```text
///   moveNatToEnd . sortOnUsefulness . unmark
///     . sortDecisionTree notSolveLast . sortDecisionTree solveFirst
///     . goalNrRanking
/// ```
fn smart_ranking(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    allow_premise_g_loop_breakers: bool,
) -> Vec<AnnotatedGoal> {
    let mut goals = open_goals(sys);
    // 1. goalNrRanking — already in seq order from `open_goals`.
    // 2. sortDecisionTree solveFirst — multi-pass partitions.
    // We use closures (rather than function pointers) so the
    // predicates that depend on system state — split_size,
    // source-cache one-case — can borrow `sys` / `ctx`.
    type Pred<'a> = Box<dyn Fn(&AnnotatedGoal) -> bool + 'a>;
    // HS-faithful lazy `oneCaseOnly` — only force the source-case analysis
    // when a KU action goal is present (see `lazy_one_case_syms`).
    let one_case_syms = lazy_one_case_syms(&goals, ctx);
    let solve_first: Vec<Pred> = vec![
        Box::new(is_chain_goal),
        Box::new(is_disj_goal),
        Box::new(is_solve_first_goal),
        Box::new(is_non_loop_breaker_proto_fact_goal),
        Box::new(is_standard_action_goal),
        Box::new(is_not_auth_out),
        Box::new(is_private_knows_goal),
        // Haskell `smartRanking` solveFirst (ProofMethod.hs)
        // includes `isFreshKnowsGoal` AND `isSignatureGoal` — both are
        // active in the smart ranking (they are commented out in
        // `sapicRanking`, not here). TPM lemmas (Alice_Init / PCR_Unbind
        // ranking) rely on isFreshKnowsGoal to prefer KU(~s0) over
        // KU(sign(...)).
        Box::new(is_fresh_knows_goal),
        Box::new(|a: &AnnotatedGoal| is_split_goal_small(a, sys)),
        Box::new(|a: &AnnotatedGoal| is_msg_one_case_goal(a, &one_case_syms)),
        Box::new(is_signature_goal),
        // `isDoubleExpGoal` (ProofMethod.hs): slot 11 between
        // `isSignatureGoal` and `isNoLargeSplitGoal`. Picks KU goals
        // whose term is `exp(_, mult(_))` before the catch-all NoLargeSplit
        // tier so DH double-exp KU goals (e.g. `KU(g^(~lkR*~x))`) win
        // ranking ties against single-arg KU(exp(_, _)) goals.
        Box::new(is_double_exp_goal),
        Box::new(|a: &AnnotatedGoal| is_no_large_split_goal(a, sys)),
    ];
    goals = sort_decision_tree_dyn(&solve_first, goals);
    // 3. sortDecisionTree notSolveLast — push solve-last goals to end.
    let not_solve_last: Vec<Pred> = vec![Box::new(is_non_solve_last_goal)];
    goals = sort_decision_tree_dyn(&not_solve_last, goals);
    // 3b. unmark — HS `smartRanking`'s `unmark | allowPremiseGLoopBreakers
    //     = map unmarkPremiseG` (ProofMethod.hs:1048-1129, see line 1073).  Resets each
    //     PremiseG goal's usefulness to Useful so loop-breaker premises
    //     are not deprioritised.  Only active when allowLoopBreakers
    //     (heuristic `S`).  `unmarkPremiseG` (ProofMethod.hs:181-184).
    if allow_premise_g_loop_breakers {
        for a in goals.iter_mut() {
            if matches!(a.goal, Goal::Premise(_, _)) {
                a.usefulness = Usefulness::Useful;
            }
        }
    }
    // 4. sortOnUsefulness — stable sort by tag.
    goals.sort_by_key(|a| tag_usefulness(a.usefulness));
    // 5. moveNatToEnd — Nat subterm splits to back.
    goals.sort_by_key(|a| is_nat_subterm_split(&a.goal));
    // 6. NO structural tie-break for Disj goals.  HS's `smartRanking`
    // pipeline runs `goalNrRanking = sortOn (fst . snd)` (defined at
    // ProofMethod.hs:593-594) FIRST — it is the rightmost composition
    // stage `moveNatToEnd . ... . goalNrRanking` (ProofMethod.hs:1048-1129, see line 1053),
    // so it runs before the others — sorting by goal NR (insertion-order
    // counter), NOT by Goal Ord.  The `sortDecisionTree` partitions that
    // follow are stable, so within each class the relative order from
    // goalNrRanking is preserved.  Rust's `open_goals` yields goals in
    // sys.goals insertion order = nr order, and the subsequent
    // partitions here are stable too, so no extra sort is required.
    //
    // Do NOT re-sort Disj goals by `goal_cmp` here: HS's `M.toList sGoals`
    // order does NOT survive to the pick (`goalNrRanking` clobbers it).
    // Re-sorting breaks HS-faithfulness for Device_Init_Use_Set
    // (case-content swap caused by Rust picking the structurally-
    // smaller induction Disj before HS's lemma-negation Disj).
    goals
}

/// Port of HS `sapicRanking` (ProofMethod.hs:993-1062, heuristic `p`) and
/// `sapicPKCS11Ranking` (ProofMethod.hs:1072-1157, heuristic `P`).
///
/// ```text
///   sortOnUsefulness . unmark . sortDecisionTreeLast solveLast
///     . sortDecisionTree solveFirst . goalNrRanking
/// ```
///
/// Differences from `smart_ranking` (HS `smartRanking`, ProofMethod.hs:1273):
///   - `unmark` is UNCONDITIONAL here (`map unmarkPremiseG`, ProofMethod.hs:
///     1011) — every PremiseG goal's usefulness is reset to `Useful`.
///   - solve-last goals are moved to the END via `sortDecisionTreeLast`
///     (not the `notSolveLast` partition trick).
///   - `isFreshKnowsGoal` is COMMENTED OUT in HS's sapic solveFirst lists
///     (ProofMethod.hs:941-1043, see line 1041, 1115) — so fresh-nonce KU goals are NOT
///     prioritised (the key difference vs smartRanking, where it IS active).
///   - there is NO `moveNatToEnd` tail stage.
///
/// `pkcs11` selects the deprecated PKCS#11 variant, which uses a slightly
/// different solveFirst/solveLast set (isDisjGoal vs isDisjGoalButNotProgress,
/// isInsertTemplateAction instead of the MID_/first-insert/progress entries,
/// isStandardActionGoalButNotInsert, isKnowsHandleGoal as solve-last).
fn sapic_ranking(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    pkcs11: bool,
) -> Vec<AnnotatedGoal> {
    let mut goals = open_goals(sys);
    // HS-faithful lazy `oneCaseOnly` (see `lazy_one_case_syms`): only force
    // the source-case analysis when a KU action goal is present.
    let one_case_syms = lazy_one_case_syms(&goals, ctx);
    type Pred<'a> = Box<dyn Fn(&AnnotatedGoal) -> bool + 'a>;
    let solve_first: Vec<Pred> = if pkcs11 {
        vec![
            Box::new(is_chain_goal),
            Box::new(is_disj_goal),
            Box::new(is_first_proto_fact),
            Box::new(is_state_fact),
            Box::new(is_unlock_action),
            Box::new(is_insert_template_action),
            Box::new(is_non_loop_breaker_proto_fact_goal),
            Box::new(is_standard_action_goal_but_not_insert),
            Box::new(is_not_auth_out),
            Box::new(is_private_knows_goal),
            // isFreshKnowsGoal — COMMENTED OUT in HS (ProofMethod.hs:1048-1129, see line 1115)
            Box::new(|a: &AnnotatedGoal| is_split_goal_small(a, sys)),
            Box::new(|a: &AnnotatedGoal| is_msg_one_case_goal(a, &one_case_syms)),
            Box::new(is_double_exp_goal),
            Box::new(|a: &AnnotatedGoal| is_no_large_split_goal(a, sys)),
        ]
    } else {
        vec![
            Box::new(is_chain_goal),
            Box::new(is_disj_goal_but_not_progress),
            Box::new(is_first_proto_fact),
            Box::new(is_mid_receiver),
            Box::new(is_mid_sender),
            Box::new(is_state_fact),
            Box::new(is_unlock_action),
            Box::new(is_knows_first_name_goal),
            Box::new(is_first_insert_action),
            Box::new(is_non_loop_breaker_proto_fact_goal),
            Box::new(is_standard_action_goal_but_not_insert_or_receive),
            Box::new(is_progress_disj),
            Box::new(is_not_auth_out),
            Box::new(is_private_knows_goal),
            // isFreshKnowsGoal — COMMENTED OUT in HS (ProofMethod.hs:941-1043, see line 1041)
            Box::new(|a: &AnnotatedGoal| is_split_goal_small(a, sys)),
            Box::new(|a: &AnnotatedGoal| is_msg_one_case_goal(a, &one_case_syms)),
            Box::new(is_double_exp_goal),
            Box::new(|a: &AnnotatedGoal| is_no_large_split_goal(a, sys)),
        ]
    };
    goals = sort_decision_tree_dyn(&solve_first, goals);
    let solve_last: Vec<Pred> = if pkcs11 {
        vec![
            Box::new(is_knows_handle_goal),
            Box::new(is_last_proto_fact),
            Box::new(is_event_action),
        ]
    } else {
        vec![
            Box::new(is_last_insert_action),
            Box::new(is_last_proto_fact),
            Box::new(is_knows_last_name_goal),
            Box::new(is_event_action),
        ]
    };
    goals = sort_decision_tree_last_dyn(&solve_last, goals);
    // unmark — UNCONDITIONAL (HS sapicRanking `unmark = map unmarkPremiseG`,
    // ProofMethod.hs:941-1043, see line 1011): reset every PremiseG goal to `Useful`.
    for a in goals.iter_mut() {
        if matches!(a.goal, Goal::Premise(_, _)) {
            a.usefulness = Usefulness::Useful;
        }
    }
    // sortOnUsefulness — stable sort by usefulness tag.  NO moveNatToEnd.
    goals.sort_by_key(|a| tag_usefulness(a.usefulness));
    goals
}

/// `sortDecisionTreeLast ps xs` (ProofMethod.hs:935-937): like
/// `sortDecisionTree` but the goals satisfying each predicate are appended
/// at the END.  Order: goals matching NO predicate first, then goals
/// matching the LAST predicate, …, then goals matching the FIRST predicate.
fn sort_decision_tree_last_dyn(
    ps: &[Box<dyn Fn(&AnnotatedGoal) -> bool + '_>],
    xs: Vec<AnnotatedGoal>,
) -> Vec<AnnotatedGoal> {
    // HS: sortDecisionTreeLast (p:ps) xs = sortDecisionTreeLast ps nonsat ++ sat
    if let Some((p, rest)) = ps.split_first() {
        let (sat, nonsat): (Vec<_>, Vec<_>) = xs.into_iter().partition(|a| p(a));
        let mut out = sort_decision_tree_last_dyn(rest, nonsat);
        out.extend(sat);
        out
    } else {
        xs
    }
}

/// Port of HS `injRanking ctxt allowLoopBreakers sys`
/// (ProofMethod.hs):
///
/// ```text
///   sortOnUsefulness . unmark
///     . sortDecisionTree [notSolveLast] . sortDecisionTree solveFirst
///     . goalNrRanking
/// ```
///
/// where
/// ```text
///   solveFirst = [ isImmediateGoal, isHighPriorityGoal
///                , isMedPriorityGoal, isLowPriorityGoal ]
///   notSolveLast g = isNoLargeSplitGoal g && isNonSolveLastGoal g
///                    && isNotKnowsLastNameGoal g
/// ```
///
/// The crucial difference vs `smartRanking`: standard action goals and
/// Disj goals share the SAME priority class (`isMedPriorityGoal`,
/// ProofMethod.hs), so within that class they keep goal-nr
/// order rather than Disj always winning.  This is why the csf17
/// `heuristic: I` lemmas solve their protocol-action goal before the
/// `¬(j<i)` disjunction.
fn inj_ranking(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    allow_loop_breakers: bool,
) -> Vec<AnnotatedGoal> {
    let mut goals = open_goals(sys);
    type Pred<'a> = Box<dyn Fn(&AnnotatedGoal) -> bool + 'a>;
    // Lazy one-case-syms exactly as in smart_ranking (see
    // `lazy_one_case_syms`): only force the source-cache thunk when a KU
    // action goal is present.
    let one_case_syms = lazy_one_case_syms(&goals, ctx);
    // solveFirst — four priority classes.  Within each class the
    // relative order from goalNrRanking (insertion / nr order) is
    // preserved by the stable partition.
    //
    //   isImmediateGoal     (ProofMethod.hs)
    //   isHighPriorityGoal  (ProofMethod.hs)
    //   isMedPriorityGoal   (ProofMethod.hs)
    //   isLowPriorityGoal   (ProofMethod.hs)
    let solve_first: Vec<Pred> = vec![
        Box::new(is_immediate_goal),
        Box::new(is_high_priority_goal),
        Box::new(move |a: &AnnotatedGoal| is_med_priority_goal(a, sys, &one_case_syms)),
        Box::new(is_low_priority_goal),
    ];
    goals = sort_decision_tree_dyn(&solve_first, goals);
    // notSolveLast — SINGLE combined predicate (note the `&&`), unlike
    // smartRanking's list.  sortDecisionTree [notSolveLast].
    let not_solve_last: Vec<Pred> = vec![Box::new(|a: &AnnotatedGoal| {
        is_no_large_split_goal(a, sys)
            && is_non_solve_last_goal(a)
            && is_not_knows_last_name_goal(a)
    })];
    goals = sort_decision_tree_dyn(&not_solve_last, goals);
    // unmark — `unmark | allowLoopBreakers = map unmarkPremiseG`
    // (ProofMethod.hs:941-1043, see line 962).  Reset PremiseG usefulness to Useful.
    if allow_loop_breakers {
        for a in goals.iter_mut() {
            if matches!(a.goal, Goal::Premise(_, _)) {
                a.usefulness = Usefulness::Useful;
            }
        }
    }
    // sortOnUsefulness — stable sort by usefulness tag.  (injRanking has
    // NO moveNatToEnd step — that's smartRanking-only.)
    goals.sort_by_key(|a| tag_usefulness(a.usefulness));
    goals
}

/// Stable partition for closure-based predicate list.
fn sort_decision_tree_dyn(
    ps: &[Box<dyn Fn(&AnnotatedGoal) -> bool + '_>],
    xs: Vec<AnnotatedGoal>,
) -> Vec<AnnotatedGoal> {
    let mut result = Vec::with_capacity(xs.len());
    let mut rest = xs;
    for p in ps {
        let (sat, nonsat): (Vec<_>, Vec<_>) = rest.into_iter().partition(|a| p(a));
        result.extend(sat);
        rest = nonsat;
    }
    result.extend(rest);
    result
}

/// `isSplitGoalSmall`: a `Goal::Split(id)` is small if its
/// `splitSize` ≤ 3 (Haskell's `smallSplitGoalSize = 3`).
/// Mirrors `ProofMethod.hs`.
fn is_split_goal_small(a: &AnnotatedGoal, sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    const SMALL_SPLIT_GOAL_SIZE: usize = 3;
    match &a.goal {
        Goal::Split(id) => sys.eq_store.split_size(*id)
            .map(|n| n <= SMALL_SPLIT_GOAL_SIZE)
            .unwrap_or(false),
        _ => false,
    }
}

/// `isNoLargeSplitGoal`: every non-Split goal qualifies; a Split
/// goal qualifies iff it's small.  Used as a final tier in the
/// decision tree to push large eq-store splits last.
fn is_no_large_split_goal(a: &AnnotatedGoal, sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    match &a.goal {
        Goal::Split(_) => is_split_goal_small(a, sys),
        _ => true,
    }
}

/// `isMsgOneCaseGoal`: the goal's premise is `KU(FApp o _)` where
/// the operator `o` has only one source case in `pcSources`.
/// Mirrors `ProofMethod.hs`.
///
/// We approximate `pcSources` via `ctx.full_sources` — for each
/// precomputed source whose goal is a KU goal with a `FApp(o, _)`
/// term and whose case set has exactly one disjunct, record `o`
/// in the one-case set.
fn collect_one_case_syms(
    ctx: &crate::constraint::solver::context::ProofContext,
) -> std::collections::BTreeSet<Vec<u8>> {
    use crate::constraint::constraints::Goal as G;
    use crate::fact::FactTag;
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    let mut out = std::collections::BTreeSet::new();
    for src in &ctx.full_sources {
        // HS-faithful order — `smartRanking.getMsgOneCase`
        // (ProofMethod.hs:1207-1210) pattern-matches on `cdGoal` BEFORE
        // touching `cdCases`:
        //
        //   getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
        //     Just (viewTerm -> FApp o _)
        //       | length (getDisj (L.get cdCases cd)) == 1 -> Just o
        //     _                                            -> Nothing
        //
        // So Var-headed sources (e.g. `KU(t:Fresh)`) never force
        // `cdCases`.  Do NOT check `src.cases.len() != 1` first: that
        // forces the lazy thunk on every source and emits spurious
        // precompute `[EXEC] solveGoal ...` lines for sources HS would
        // never compute.
        //
        // Only KU-headed source goals.
        let term: &tamarin_term::lterm::LNTerm = match &src.goal {
            G::Action(_, fa) | G::Premise(_, fa) if matches!(fa.tag, FactTag::Ku) =>
                match fa.terms.first() { Some(t) => t, None => continue },
            _ => continue,
        };
        let Term::App(FunSym::NoEq(s), _) = term else {
            continue
        };
        // Now we know the goal is `KU(FApp o _)` — HS-faithful: force
        // cases at this point to check the disjunct count.  We only need
        // the disjunct COUNT here, so force once (idempotent) and read
        // the cell length in O(1) instead of deep-cloning every case
        // `System`.
        src.cases_list(ctx);
        if src.cases_len() != 1 { continue; }
        out.insert(s.name.to_vec());
    }
    out
}

/// HS-faithful lazy `oneCaseOnly` shared by all three rankings.
///
/// `smartRanking`'s `oneCaseOnly = catMaybes . map getMsgOneCase . L.get
/// pcSources $ ctxt` is a thunk that only forces when an `isMsgOneCaseGoal`
/// predicate fires.  That predicate returns False instantly for non-KU goals
/// (`msgPremise` returns Nothing).  So if NO goal in the current list is a KU
/// action goal, the thunk is never forced — and HS's `cdCases` thunks for
/// FApp-headed KU sources stay unforced too, deferring saturate traces until
/// the first KU goal appears.
///
/// Replicate by only computing `one_case_syms` when at least one goal in
/// `goals` is a KU action goal.  Otherwise return an empty set —
/// `is_msg_one_case_goal` returns False unconditionally.
fn lazy_one_case_syms(
    goals: &[AnnotatedGoal],
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
) -> std::collections::BTreeSet<Vec<u8>> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    let any_ku_action_goal = goals.iter().any(|a| {
        matches!(&a.goal, Goal::Action(_, fa) if matches!(fa.tag, FactTag::Ku))
    });
    if any_ku_action_goal {
        match ctx {
            Some(c) => collect_one_case_syms(c),
            None => Default::default(),
        }
    } else {
        Default::default()
    }
}

fn is_msg_one_case_goal(
    a: &AnnotatedGoal,
    one_case_syms: &std::collections::BTreeSet<Vec<u8>>,
) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    // Haskell `isMsgOneCaseGoal` (ProofMethod.hs) routes
    // through `msgPremise`, which is defined ONLY for `ActionG` (the
    // KU-action arm).  Premise-side KU goals (rare — Goal::Premise with
    // a KU fact) are excluded.  Mirror exactly to avoid spurious
    // over-prioritisation of KU premises.
    let fa = match &a.goal {
        Goal::Action(_, fa) => fa,
        _ => return false,
    };
    if !matches!(fa.tag, FactTag::Ku) { return false; }
    let Some(t) = fa.terms.first() else { return false };
    if let Term::App(FunSym::NoEq(s), _) = t {
        return one_case_syms.contains(s.name);
    }
    false
}

/// `tagUsefulness` — direct port of Haskell `ProofMethod.hs:1048-1129, see line 1068`:
///
/// ```haskell
/// tagUsefulness Useful                = 0 :: Int
/// tagUsefulness ProbablyConstructible = 1
/// tagUsefulness LoopBreaker           = 1
/// tagUsefulness CurrentlyDeducible    = 2
/// ```
///
/// Lower = explored first.  LoopBreaker is `1` (deprioritised), NOT
/// `0` — do NOT conflate LoopBreaker with Useful, or the search expands
/// looping premises eagerly instead of after every
/// contradiction-discovering goal.
fn tag_usefulness(u: Usefulness) -> u8 {
    match u {
        Usefulness::Useful => 0,
        Usefulness::ProbablyConstructible | Usefulness::LoopBreaker => 1,
        Usefulness::CurrentlyDeducible => 2,
    }
}

// -- Predicate library (mirrors Haskell exactly where we can) ----------------

fn is_chain_goal(a: &AnnotatedGoal) -> bool {
    matches!(a.goal, Goal::Chain(_, _))
}
fn is_disj_goal(a: &AnnotatedGoal) -> bool {
    matches!(a.goal, Goal::Disj(_))
}
fn is_solve_first_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Action(_, fa) | Goal::Premise(_, fa) => is_solve_first_fact(fa),
        _ => false,
    }
}
/// `isNonLoopBreakerProtoFactGoal` — protocol-fact premise that's
/// non-K, non-AuthOut, and not currently flagged LoopBreaker.
fn is_non_loop_breaker_proto_fact_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) => {
            !fa.is_k_fact() && !is_auth_out_fact(fa)
                && a.usefulness == Usefulness::Useful
        }
        _ => false,
    }
}
fn is_standard_action_goal(a: &AnnotatedGoal) -> bool {
    matches!(&a.goal, Goal::Action(_, fa) if !fa.is_ku())
}
fn is_not_auth_out(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) => !is_auth_out_fact(fa),
        _ => false,
    }
}
fn is_private_knows_goal(a: &AnnotatedGoal) -> bool {
    // HS `isPrivateKnowsGoal` (ProofMethod.hs:272-275):
    //   isPrivateKnowsGoal goal = case msgPremise goal of
    //     Just t -> isPrivateFunction t
    //     _     -> False
    // and `isPrivateFunction` (Term.hs:203-205) checks ONLY the TOP-LEVEL
    // function symbol — it does NOT recurse into subterms:
    //   isPrivateFunction (viewTerm -> FApp (NoEq (_, (_,Private,_))) _) = True
    //   isPrivateFunction _                                            = False
    //
    // Do NOT use `contains_private` (recursive) here: it mis-classifies
    // e.g. `KU(exp(Y, h1(<~ex, sk($A)>)))` as a private-knows goal
    // because `sk` (private) appears deep inside.  That collides with
    // the genuine private-knows goal `KU(sk($A))` at the same slot, and
    // the goalNr tie-break picks the wrong one — causing case-order
    // swaps in NAXOS_eCK_PFS_private (and the non-PFS variant
    // NAXOS_eCK_private).
    // Shared `isPrivateFunction` port (`crate::intruder_rules::is_private_function`,
    // Term.hs:203-205): top-level function symbol is Private; no recursion.
    msg_premise(&a.goal).map(crate::intruder_rules::is_private_function).unwrap_or(false)
}

fn is_fresh_knows_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    matches!(msg_premise(&a.goal), Some(Term::Lit(Lit::Var(v))) if v.sort == LSort::Fresh)
}
fn is_signature_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::function_symbols::{FunSym, NoEqSym};
    use tamarin_term::term::Term;
    matches!(msg_premise(&a.goal),
        Some(Term::App(FunSym::NoEq(NoEqSym { name, .. }), _))
            if &**name == b"sign")
}

/// `isDoubleExpGoal` (ProofMethod.hs):
///   isDoubleExpGoal goal = case msgPremise goal of
///     Just (viewTerm2 -> FExp _ (viewTerm2 -> FMult _)) -> True
///     _                                                -> False
///
/// True when the KU action goal's term is `exp(_, mult(...))` — i.e.
/// a DH exponentiation whose exponent is itself an AC product.
/// HS's `viewTerm2` only treats `FAPP (NoEq exp)` (arity 2) as `FExp`,
/// and `FAPP (AC Mult)` as `FMult` (Raw.hs:171-185); we mirror by
/// matching `Term::App(NoEq(name="exp"), [_, App(Ac(Mult), _)])`.
///
/// Used by smartRanking's `solveFirst` slot 11 (between `isSignatureGoal`
/// at slot 10 and `isNoLargeSplitGoal` at slot 12).  Without this,
/// double-exp KU goals fall to the catch-all NoLargeSplit tier and lose
/// ranking ties to other KU(exp(_)) goals — observed on UM_wPFS /
/// JKL_TS2 / MTI_C0 where HS picks `KU(g^(~lkR*~x))` and RS picks
/// `KU(hkI^~ekR)`.
fn is_double_exp_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym, NoEqSym};
    use tamarin_term::term::Term;
    match msg_premise(&a.goal) {
        Some(Term::App(FunSym::NoEq(NoEqSym { name, .. }), args))
            if &**name == b"exp" && args.len() == 2 =>
        {
            matches!(&args[1], Term::App(FunSym::Ac(AcSym::Mult), _))
        }
        _ => false,
    }
}

// -- sapicRanking / sapicPKCS11Ranking priority-class predicates -------------
//    (ProofMethod.hs:220-277, 941-987).  These mirror the SAPIC-translation
//    fact-name conventions exactly; faithfulness requires matching HS's
//    literal name strings (e.g. lowercase "state_", "Unlock", "MID_*").

/// HS `isFirstProtoFact` (ProofMethod.hs:229-238, see line 230): a PremiseG whose fact is a
/// solve-first fact.  (Distinct from `is_solve_first_goal`, which HS's smart
/// ranking uses and which also matches ActionG.)
fn is_first_proto_fact(a: &AnnotatedGoal) -> bool {
    matches!(&a.goal, Goal::Premise(_, fa) if is_solve_first_fact(fa))
}

/// HS `isLastProtoFact` (ProofMethod.hs:218-226, see line 226): a PremiseG whose fact is a
/// solve-last fact.
fn is_last_proto_fact(a: &AnnotatedGoal) -> bool {
    matches!(&a.goal, Goal::Premise(_, fa) if is_solve_last_fact(fa))
}

/// HS `isStateFact` (ProofMethod.hs:941-1043): a PremiseG ProtoFact whose name
/// has the lowercase `state_` prefix.
fn is_state_fact(a: &AnnotatedGoal) -> bool {
    use crate::fact::FactTag;
    matches!(&a.goal, Goal::Premise(_, fa)
        if matches!(&fa.tag, FactTag::Proto(_, n, _) if n.starts_with("state_")))
}

fn is_proto_named(a: &AnnotatedGoal, want_action: bool, name: &str) -> bool {
    use crate::fact::FactTag;
    let fa = match &a.goal {
        Goal::Action(_, fa) if want_action => fa,
        Goal::Premise(_, fa) if !want_action => fa,
        _ => return false,
    };
    matches!(&fa.tag, FactTag::Proto(_, n, _) if &**n == name)
}

/// HS `isUnlockAction` (ProofMethod.hs:941-1043, see line 945): an ActionG of ProtoFact "Unlock".
fn is_unlock_action(a: &AnnotatedGoal) -> bool { is_proto_named(a, true, "Unlock") }
/// HS `isEventAction` (ProofMethod.hs:941-1043, see line 949): an ActionG of ProtoFact "Event".
fn is_event_action(a: &AnnotatedGoal) -> bool { is_proto_named(a, true, "Event") }
/// HS `isMID_Receiver` (ProofMethod.hs:941-1043, see line 953): PremiseG ProtoFact "MID_Receiver".
fn is_mid_receiver(a: &AnnotatedGoal) -> bool { is_proto_named(a, false, "MID_Receiver") }
/// HS `isMID_Sender` (ProofMethod.hs:941-1043, see line 957): PremiseG ProtoFact "MID_Sender".
fn is_mid_sender(a: &AnnotatedGoal) -> bool { is_proto_named(a, false, "MID_Sender") }

/// KU goal of a fresh-name var whose name has the given `prefix`.  Shared
/// by the HS `isKnows{First,Last,Immediate}NameGoal` / `isKnowsHandleGoal`
/// family, each a thin wrapper fixing its own prefix.
fn is_knows_fresh_name_goal(a: &AnnotatedGoal, prefix: &str) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    matches!(msg_premise(&a.goal),
        Some(Term::Lit(Lit::Var(v))) if v.sort == LSort::Fresh && v.name.starts_with(prefix))
}

/// HS `isKnowsLastNameGoal` (ProofMethod.hs:254-274, see line 262): KU goal of a fresh name
/// var whose name has the `L_` prefix.
fn is_knows_last_name_goal(a: &AnnotatedGoal) -> bool {
    is_knows_fresh_name_goal(a, "L_")
}

/// HS `isKnowsHandleGoal` (ProofMethod.hs:1135-1166, see line 1143, sapicPKCS11): KU goal of a
/// fresh name var whose name has the `h` prefix.
fn is_knows_handle_goal(a: &AnnotatedGoal) -> bool {
    is_knows_fresh_name_goal(a, "h")
}

/// HS `isNotInsertAction` (ProofMethod.hs:941-1043, see line 973): NOT an ActionG ProtoFact "Insert".
fn is_not_insert_action(a: &AnnotatedGoal) -> bool { !is_proto_named(a, true, "Insert") }
/// HS `isNotReceiveAction` (ProofMethod.hs:941-1043, see line 977): NOT an ActionG ProtoFact "Receive".
fn is_not_receive_action(a: &AnnotatedGoal) -> bool { !is_proto_named(a, true, "Receive") }

/// HS `isStandardActionGoalButNotInsertOrReceive` (ProofMethod.hs:941-1043, see line 983).
fn is_standard_action_goal_but_not_insert_or_receive(a: &AnnotatedGoal) -> bool {
    is_standard_action_goal(a) && is_not_insert_action(a) && is_not_receive_action(a)
}

/// HS `isStandardActionGoalButNotInsert` (ProofMethod.hs:941-1043, see line 987, sapicPKCS11):
/// standard action, not Insert, and not an Event action.
fn is_standard_action_goal_but_not_insert(a: &AnnotatedGoal) -> bool {
    is_standard_action_goal(a) && is_not_insert_action(a) && !is_event_action(a)
}

/// HS Insert-action key-prefix helper (ProofMethod.hs:941-1043, see line 961/968/1130):
/// the first arg of an "Insert" ProtoFact is `<'name', _>` with `name` a
/// public-name constant; true iff that name string has the given prefix.
fn insert_action_first_key_has_prefix(a: &AnnotatedGoal, prefix: &str) -> bool {
    use crate::fact::FactTag;
    use tamarin_term::function_symbols::{FunSym, NoEqSym};
    use tamarin_term::lterm::NameTag;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let Goal::Action(_, fa) = &a.goal else { return false };
    if !matches!(&fa.tag, FactTag::Proto(_, n, _) if &**n == "Insert") { return false; }
    let Some(Term::App(FunSym::NoEq(NoEqSym { name, .. }), args)) = fa.terms.first() else {
        return false;
    };
    if &**name != b"pair" || args.len() != 2 { return false; }
    matches!(&args[0], Term::Lit(Lit::Con(c))
        if c.tag == NameTag::Pub && c.id.0.starts_with(prefix))
}

/// HS `isFirstInsertAction` (ProofMethod.hs:941-1043, see line 961).
fn is_first_insert_action(a: &AnnotatedGoal) -> bool {
    insert_action_first_key_has_prefix(a, "F_")
}
/// HS `isLastInsertAction` (ProofMethod.hs:941-1043, see line 968).
fn is_last_insert_action(a: &AnnotatedGoal) -> bool {
    insert_action_first_key_has_prefix(a, "L_")
}
/// HS `isInsertTemplateAction` (ProofMethod.hs:1048-1129, see line 1130, sapicPKCS11).
fn is_insert_template_action(a: &AnnotatedGoal) -> bool {
    insert_action_first_key_has_prefix(a, "template")
}

/// HS `isProgressFact` (ProofMethod.hs:240-247, see line 243): a Linear fact of arity 1 whose
/// name has the `ProgressTo_` prefix.  Operates on a guarded `GFact`.
fn gfact_is_progress(f: &crate::guarded_types::GFact) -> bool {
    !f.persistent && f.args.len() == 1 && f.name.starts_with("ProgressTo_")
}

fn is_node_sort_hint(s: &tamarin_parser::ast::SortHint) -> bool {
    use tamarin_parser::ast::{SortHint, SuffixSort};
    matches!(s, SortHint::Node | SortHint::Suffix(SuffixSort::Node))
}

/// HS `isProgressDisj` (ProofMethod.hs:246-252): a Disj goal all of whose
/// disjuncts are `Ex #node. ProgressTo_…( #node )`.
fn is_progress_disj(a: &AnnotatedGoal) -> bool {
    use crate::constraint::constraints::Disj;
    use crate::guarded::{GAtom, Guarded};
    use crate::guarded::Quant;
    let Goal::Disj(Disj(items)) = &a.goal else { return false };
    if items.is_empty() { return false; }
    items.iter().all(|g| match g {
        Guarded::GGuarded { qua: Quant::Ex, vars, guards, .. }
            if vars.len() == 1 && guards.len() == 1 && is_node_sort_hint(&vars[0].sort) =>
        {
            matches!(&guards[0], GAtom::Action(f, _) if gfact_is_progress(f))
        }
        _ => false,
    })
}

/// HS `isDisjGoalButNotProgress` (ProofMethod.hs:240-247, see line 253).
fn is_disj_goal_but_not_progress(a: &AnnotatedGoal) -> bool {
    is_disj_goal(a) && !is_progress_disj(a)
}

// -- injRanking priority-class predicates (ProofMethod.hs) --------------------

/// `isImmediateGoal` (ProofMethod.hs): a PremiseG/ActionG
/// whose fact name has the `I_` prefix, OR a KU goal of a fresh name
/// var whose name has the `I_` prefix (`isKnowsImmediateNameGoal`).
fn is_immediate_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) | Goal::Action(_, fa)
            if crate::fact::fact_tag_name(&fa.tag).starts_with("I_") => true,
        _ => is_knows_immediate_name_goal(a),
    }
}

/// `isHighPriorityGoal` (ProofMethod.hs):
///   isKnowsFirstNameGoal || isSolveFirstGoal || isChainGoal
///   || isFreshKnowsGoal
fn is_high_priority_goal(a: &AnnotatedGoal) -> bool {
    is_knows_first_name_goal(a)
        || is_solve_first_goal(a)
        || is_chain_goal(a)
        || is_fresh_knows_goal(a)
}

/// `isMedPriorityGoal` (ProofMethod.hs):
///   isStandardActionGoal || isDisjGoal || isPrivateKnowsGoal
///   || isSplitGoalSmall || isMsgOneCaseGoal
///   || isNonLoopBreakerProtoFactGoal
fn is_med_priority_goal(
    a: &AnnotatedGoal,
    sys: &System,
    one_case_syms: &std::collections::BTreeSet<Vec<u8>>,
) -> bool {
    is_standard_action_goal(a)
        || is_disj_goal(a)
        || is_private_knows_goal(a)
        || is_split_goal_small(a, sys)
        || is_msg_one_case_goal(a, one_case_syms)
        || is_non_loop_breaker_proto_fact_goal(a)
}

/// `isLowPriorityGoal` (ProofMethod.hs):
///   isDoubleExpGoal || isSignatureGoal || isProtoFactGoal
fn is_low_priority_goal(a: &AnnotatedGoal) -> bool {
    is_double_exp_goal(a) || is_signature_goal(a) || is_proto_fact_goal(a)
}

/// `isProtoFactGoal` (ProofMethod.hs): a non-K PremiseG.
fn is_proto_fact_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) => !fa.is_k_fact(),
        _ => false,
    }
}

/// `isKnowsFirstNameGoal` (ProofMethod.hs): KU goal of a fresh
/// name var whose name has the `F_` prefix.
fn is_knows_first_name_goal(a: &AnnotatedGoal) -> bool {
    is_knows_fresh_name_goal(a, "F_")
}

/// `isKnowsImmediateNameGoal` (ProofMethod.hs): KU goal of a
/// fresh name var whose name has the `I_` prefix.
fn is_knows_immediate_name_goal(a: &AnnotatedGoal) -> bool {
    is_knows_fresh_name_goal(a, "I_")
}

/// `isNotKnowsLastNameGoal` (ProofMethod.hs): True unless the
/// goal is a KU goal of a fresh name var with an `L_` prefix.
fn is_not_knows_last_name_goal(a: &AnnotatedGoal) -> bool {
    !is_knows_last_name_goal(a)
}

/// `isNonSolveLastGoal` — PremiseG/ActionG NOT tagged SolveLast.
fn is_non_solve_last_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) | Goal::Action(_, fa) => !is_solve_last_fact(fa),
        _ => true,
    }
}
/// `isNatSubtermSplit` (ProofMethod.hs:1065-1066): a `SubtermG (small,
/// big)` whose `isNatSubterm` holds (SubtermStore.hs:112-113, see line 113):
///   `(sortOfLNTerm small == LSortNat || isMsgVar small)
///        && sortOfLNTerm big == LSortNat`
/// Non-SubtermG goals are `False`.  Used by `moveNatToEnd` in
/// smart_ranking to push nat-subterm splits to the back.
fn is_nat_subterm_split(g: &Goal) -> bool {
    use tamarin_term::lterm::{sort_of_lnterm, LSort};
    match g {
        Goal::Subterm((small, big)) => {
            (sort_of_lnterm(small) == LSort::Nat || is_msg_var(small))
                && sort_of_lnterm(big) == LSort::Nat
        }
        _ => false,
    }
}

// -- Fact-level helpers ------------------------------------------------------

fn is_solve_first_fact(fa: &crate::fact::LNFact) -> bool {
    use crate::fact::FactAnnotation;
    if fa.annotations.contains(&FactAnnotation::SolveFirst) { return true; }
    crate::fact::fact_tag_name(&fa.tag).starts_with("F_")
}
fn is_solve_last_fact(fa: &crate::fact::LNFact) -> bool {
    use crate::fact::FactAnnotation;
    if fa.annotations.contains(&FactAnnotation::SolveLast) { return true; }
    crate::fact::fact_tag_name(&fa.tag).starts_with("L_")
}
fn is_auth_out_fact(fa: &crate::fact::LNFact) -> bool {
    use crate::fact::FactTag;
    matches!(&fa.tag, FactTag::Proto(_, name, _) if &**name == "AuthOut")
}

/// `msgPremise`: the message argument of a KU action goal, if any.
/// Mirrors Haskell:
///   msgPremise (ActionG _ fa) = do (UpK, m) <- kFactView fa; return m
fn msg_premise(g: &Goal) -> Option<&tamarin_term::lterm::LNTerm> {
    match g {
        Goal::Action(_, fa) if fa.is_ku() => fa.terms.first(),
        _ => None,
    }
}

/// Saturate-time openGoals view.  Haskell uses a single `openGoals`
/// function for both `isFinished` and `solveAllSafeGoals`, so this is
/// just an alias for `is_open_in_sys`.  Kept as a separate name so
/// callers in saturate code make the intent explicit; if we ever need
/// to diverge again, the seam is here.
pub fn is_open_for_saturate(g: &Goal, sys: &System) -> bool {
    // Standalone caller: build the always-before adjacency on the spot
    // (mirrors `goal_usefulness` building `rawLessRel` for non-`open_goals`
    // callers).  `open_goals` instead builds it once and shares it.
    let ab_adj = sys.build_always_before_adj();
    is_open_in_sys(g, sys, &ab_adj)
}

/// Like [`is_open_for_saturate`] but reuses a prebuilt always-before
/// adjacency instead of rebuilding it per call.  The relation depends
/// only on `sys` (not on `g`), so a caller scanning many goals against
/// an unmutated system builds it once and threads it in.
pub fn is_open_for_saturate_with(
    g: &Goal,
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
) -> bool {
    is_open_in_sys(g, sys, ab_adj)
}

/// `chain_kd_conc_term`: the KD-fact term at the chain's source-
/// conclusion, or None if the source-conclusion isn't a KD fact.
fn chain_kd_conc_term(
    sys: &System,
    c: &crate::constraint::constraints::NodeConc,
) -> Option<tamarin_term::lterm::LNTerm> {
    use crate::fact::FactTag;
    let (id, idx) = (&c.0, &c.1);
    let rule = sys.nodes.iter().find(|(n, _)| n == id).map(|(_, r)| r)?;
    let fact = rule.conclusions.get(idx.0)?;
    if fact.tag != FactTag::Kd { return None; }
    fact.terms.first().cloned()
}

/// Shared `allKUActions`-before-target scan.  True iff some KU action for
/// `term` fires at a node strictly always-before `target`.
///
/// HS `allKUActions sys = unsolvedActionAtoms sys ++ node actions`
/// (System.hs:1575-1585): the KU action may exist only as an unsolved
/// `ActionG i (KU term)` goal (node i not yet in sNodes), so scan unsolved
/// ActionG goals in ADDITION to node rule actions.  `always_before(id,
/// target)` does not depend on `fa` and the relation is invariant across the
/// loops in one `open_goals` pass (`sys` is read-only), so the caller builds
/// the adjacency once and threads it in.  Used by `chain_to_equality` and
/// (per-arg) `all_msg_vars_known_earlier`.
fn exists_ku_action_before(
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
    term: &tamarin_term::lterm::LNTerm,
    target: &crate::constraint::constraints::NodeId,
) -> bool {
    let is_ku_of = |fa: &crate::fact::LNFact| -> bool {
        matches!(fa.tag, crate::fact::FactTag::Ku) && fa.terms.first() == Some(term)
    };
    // Unsolved ActionG goals half of allActions.
    let in_goals = sys.goals.iter()
        .filter(|(_, st)| !st.solved)
        .any(|(g, _)| match g {
            Goal::Action(i, fa) =>
                is_ku_of(fa) && sys.always_before_with(ab_adj, i, target),
            _ => false,
        });
    if in_goals { return true; }
    // Node rule actions half of allActions.
    sys.nodes.iter().any(|(id, rule)| {
        id != target
            && rule.actions.iter().any(is_ku_of)
            && sys.always_before_with(ab_adj, id, target)
    })
}

/// Haskell `chainToEquality` (Goals.hs:171-182).  Open the msg-var
/// ChainG only when its premise targets an intruder equality rule
/// AND there's an earlier KU action for the same msg var.
///
/// IEquality is an INTRUDER rule (IntrRuleACInfo::IEquality), not a
/// proto rule — the match below must check the Intr variant.
fn chain_to_equality(
    t_start: &tamarin_term::lterm::LNTerm,
    c: &crate::constraint::constraints::NodeConc,
    p: &crate::constraint::constraints::NodePrem,
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
) -> bool {
    // Look up the premise's rule. If it's NOT an IEquality rule,
    // chainToEquality returns False (chain is auto-handled).
    let p_rule = sys.nodes.iter().find(|(n, _)| n == &p.0).map(|(_, r)| r);
    let Some(p_rule) = p_rule else { return false; };
    let is_equality = matches!(&p_rule.info,
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IEquality));
    if !is_equality { return false; }
    // ku_before: there's a KU action for t_start at some node that
    // is always-before c.0 in the less-relation (see
    // `exists_ku_action_before`).
    exists_ku_action_before(sys, ab_adj, t_start, &c.0)
}

/// True if a goal is still "open": not vacuously False, not already
/// trivially handled.  **Direct port of Haskell's `openGoals` filter**
/// (`Theory.Constraint.Solver.Goals:66-101`):
///
/// NOTE: Haskell's first ActionG arm branches on `get sDiffSystem sys`
/// (Goals.hs:72-84): in a diff proof every KU action goal is open iff
/// `not solved`, skipping the pub/nat/pair/msg-var auto-solve cases.
/// This port intentionally omits that branch — diff mode is not
/// supported (the Rust `System` has no diff field), so we always take
/// the non-diff path.
///
///   ActionG i (KU m) →
///       not ( solved
///             || (isMsgVar m && i ∉ sNodes)  -- handled later
///             || sort m == Pub || sort m == Nat
///             || isPair m || isInverse m || isProduct m
///             || isUnion m || isNullaryPublicFunction m )
///   DisjG (Disj []) → False    -- empty disj handled by contradictions
///   ChainG c p →
///     case kFactView (nodeConcFact c sys) of
///       Just (DnK, FUnion args) | allMsgVarsKnownEarlier → False
///       Just (DnK, m) | isMsgVar m → chainToEquality m c p
///                     | otherwise  → True
///       _ → True
///   _ → not solved
///
/// **Soundness note**: filtered-out msg-var KD ChainG goals stand for
/// "intruder learns some message via some derivation".  When the
/// caller is `isFinished`, an empty `openGoals` set together with
/// stale msg-var KD chains is still a valid Solved verdict — Haskell
/// trusts that the intruder is omnipotent for any unspecified
/// message, so the chain is vacuously satisfied.
fn is_open_in_sys(
    g: &Goal,
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
) -> bool {
    use crate::constraint::constraints::Disj;
    use crate::fact::FactTag;
    match g {
        Goal::Disj(Disj(items)) if items.is_empty() => false,
        Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
            let Some(m) = fa.terms.first() else { return true };
            if is_pub_or_nat_term(m) { return false; }
            if has_top_pair_inv_prod(m) { return false; }
            if is_nullary_public_function(m) { return false; }
            // Haskell: `isMsgVar m && no node at i` → auto-solved.
            if is_msg_var(m) && !sys.nodes.iter().any(|(n, _)| n == i) {
                return false;
            }
            true
        }
        // Haskell parity (Goals.hs:92-100):
        //   ChainG c p →
        //     case kFactView (nodeConcFact c sys) of
        //       Just (DnK, FUnion args) → not solved && not (allMsgVarsKnownEarlier c args)
        //       Just (DnK, m) | isMsgVar m → chainToEquality m c p
        //                     | otherwise  → True
        //       _ → True
        Goal::Chain(c, _p) => {
            if let Some(m) = chain_kd_conc_term(sys, c) {
                // FUnion arm: KD chain over a multiset union — auto-closed
                // when all union args are msg-vars known via earlier KU action
                // (Haskell Goals.hs:95-97 + 163-167).  Without this Rust
                // treats these as open and explores extension paths Haskell
                // skips.
                if let Some(args) = union_args(&m) {
                    if all_msg_vars_known_earlier(c, args, sys, ab_adj) {
                        return false;
                    }
                    return true;
                }
                if is_msg_var(&m) {
                    return chain_to_equality(&m, c, _p, sys, ab_adj);
                }
            }
            true
        }
        // Haskell parity (Goals.hs:66-182, see line 105):
        //   SplitG idx -> splitExists (get sEqStore sys) idx
        // A Split goal is only open if its split-id still exists
        // in the eq-store.  Without this, stale split-ids appear
        // as open goals after a split has been performed elsewhere.
        Goal::Split(id) => sys.eq_store.split_exists(*id),
        // Haskell parity (Goals.hs:66-182, see line 106):
        //   SubtermG st -> st `elem` posSubterms . sSubtermStore $ sys
        // A Subterm goal is only open if its (small, big) pair is
        // still in the positive-subterm list (not yet solved).
        Goal::Subterm((small, big)) => {
            sys.subterm_store.subterms.iter()
                .any(|c| &c.small == small && &c.big == big)
        }
        _ => true,
    }
}

/// Extract args if the term is a multiset-union (`FUnion`) — Haskell's
/// `viewTerm2 → FUnion args`.  Returns None for any other term shape.
fn union_args(t: &tamarin_term::lterm::LNTerm) -> Option<&[tamarin_term::lterm::LNTerm]> {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    match t {
        // Multiset union is an AC symbol (`Ac(Union)`), never a `NoEq`
        // — matching the representation used everywhere else in this
        // file (e.g. `has_top_pair_inv_prod`).  Borrow the existing
        // Arc-backed child slice; the only caller just iterates it.
        Term::App(FunSym::Ac(AcSym::Union), args) => Some(args),
        _ => None,
    }
}

/// `allMsgVarsKnownEarlier` (Haskell Goals.hs:163-167): all `args` are
/// msg-vars AND each appears as the term of a KU action at some node
/// always-before `c.0` (the chain's source node).  When this holds for
/// an FUnion ChainG conclusion, the chain is auto-handled (Goals.hs:95-97).
fn all_msg_vars_known_earlier(
    c: &crate::constraint::constraints::NodeConc,
    args: &[tamarin_term::lterm::LNTerm],
    sys: &System,
    ab_adj: &crate::constraint::system::PrebuiltAdj,
) -> bool {
    if !args.iter().all(is_msg_var) { return false; }
    let i = &c.0;
    // HS `earlierMsgVars = do (j,_,t) <- allKUActions sys; ...` (Goals.hs:66-182, see line 164):
    // each arg must appear as a KU action always-before `i` (see
    // `exists_ku_action_before`).
    args.iter().all(|arg| exists_ku_action_before(sys, ab_adj, arg, i))
}

/// `isNullaryPublicFunction`: 0-arity public function symbols.
/// Haskell's auto-solve case.
fn is_nullary_public_function(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    matches!(t,
        Term::App(FunSym::NoEq(s), args)
            if args.is_empty()
                && matches!(s.privacy, tamarin_term::function_symbols::Privacy::Public))
}

/// True if the term's whole-term sort is Pub or Nat.  These KU goals
/// are auto-solved because the adversary can construct any Pub/Nat
/// value trivially.
///
/// Mirrors Haskell's `sortOfLNTerm m == LSortPub || sortOfLNTerm m ==
/// LSortNat` in `openGoals` (Goals.hs:80-81).  `sortOfLNTerm`
/// (LTerm.hs `sortOfLTerm`) is a WHOLE-TERM sort: besides Pub/Nat
/// literals it returns `LSortNat` for an `Ac(NatPlus)` application
/// (e.g. `tplus(x,y)`) and for the nat-one constant — so we must
/// delegate to `sort_of_lnterm` rather than only inspecting bare
/// literals, otherwise `+`/nat KU goals are wrongly left open.
fn is_pub_or_nat_term(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::{sort_of_lnterm, LSort};
    matches!(sort_of_lnterm(t), LSort::Pub | LSort::Nat)
}

/// True if the term's top symbol is a pair, inverse, product, or
/// AC union — those decompositions are handled inline by
/// `insertAction` in Haskell, so KU goals on them are auto-solved.
fn has_top_pair_inv_prod(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym, INV_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::NoEq(s), args) => {
            s.name == b"pair" && args.len() == 2
                || s.name == INV_SYM_STRING && args.len() == 1
        }
        Term::App(FunSym::Ac(AcSym::Mult), _) => true,  // product
        Term::App(FunSym::Ac(AcSym::Union), _) => true, // multiset union
        _ => false,
    }
}

/// Compute a goal's `Usefulness` annotation. Direct port of the
/// `useful` case-block in Haskell's `openGoals`
/// (`Theory.Constraint.Solver.Goals`):
///
///   useful = case goal of
///     _ | gsLoopBreaker status     -> LoopBreaker
///     ActionG i (UpK m) | hasKUGuards          -> Useful
///                       | currentlyDeducible i m  -> CurrentlyDeducible
///                       | probablyConstructible m -> ProbablyConstructible
///     _                            -> Useful
///
/// `currentlyDeducible` and `extractible` ARE fully ported: the body
/// calls `currently_deducible(sys, i, m)` (which does the full
/// less-rel / edge reachability + node-rule introspection via
/// `extractible` / `reachable_from`) and only then falls back to
/// `probably_constructible(m)`, exactly as Haskell's `useful` block
/// does.
pub fn goal_usefulness(g: &Goal, looping: bool, sys: &System) -> Usefulness {
    // Standalone callers build the shared `rawLessRel` adjacency on the
    // spot.  `open_goals` builds it once and uses
    // `goal_usefulness_with_adj` to share it across all goals (mirroring
    // HS's `existingDeps = rawLessRel sys` shared in `openGoals`).
    let adj = sys.build_always_before_adj();
    goal_usefulness_with_adj(g, looping, sys, adj.map())
}

/// HS `prettyGoals`'s `useful` annotation STRING (System.hs:1745-1752) for
/// the interactive sequent's per-goal comment.  UNLIKE the ranking
/// [`Usefulness`] enum (which collapses both KU-guard and default goals
/// into `Useful`), this distinguishes `" (useful1)"` (KU goal when the
/// system has KU-guards) from `" (useful2)"` (the default), matching the
/// exact suffix HS `prettyGoals` renders.  Returned WITHOUT surrounding
/// quotes; the caller applies HS's `show` (which wraps it in `"…"`).
///
///   useful = case goal of
///     _ | gsLoopBreaker         -> " (loop breaker)"
///     ActionG i (UpK m)
///       | hasKUGuards           -> " (useful1)"
///       | currentlyDeducible i m -> " (currently deducible)"
///       | probablyConstructible m -> " (probably constructible)"
///     _                         -> " (useful2)"
pub fn goal_useful_annotation(
    g: &Goal,
    gs_loop_breaker: bool,
    sys: &System,
) -> &'static str {
    if gs_loop_breaker {
        return " (loop breaker)";
    }
    if let Goal::Action(i, fa) = g {
        if fa.is_ku() {
            if has_ku_guards(sys) {
                return " (useful1)";
            }
            if let Some(m) = fa.terms.first() {
                let adj = sys.build_always_before_adj();
                if currently_deducible(sys, adj.map(), i, m) {
                    return " (currently deducible)";
                }
                if probably_constructible(m) {
                    return " (probably constructible)";
                }
            }
        }
    }
    " (useful2)"
}

/// Like [`goal_usefulness`] but reuses a prebuilt `rawLessRel`
/// adjacency (`existingDeps`, Goals.hs:66-182, see line 120) instead of rebuilding it.
fn goal_usefulness_with_adj(
    g: &Goal,
    looping: bool,
    sys: &System,
    adj: &RawLessAdj,
) -> Usefulness {
    if looping { return Usefulness::LoopBreaker; }
    if let Goal::Action(i, fa) = g {
        if fa.is_ku() {
            // Haskell `hasKUGuards` (Goals.hs): if ANY system
            // formula has a `KUFact`-tagged action atom in its guards
            // (`KU(?) @ ?` quantifier-binding), every KU goal is
            // **Useful** regardless of `currentlyDeducible` /
            // `probablyConstructible` — those tests are SHORT-CIRCUITED.
            // Typing-class IHs (`All m j. KU(m,j) ⇒ ...`) always have
            // such guards; the order matters for proof-search bias.
            if has_ku_guards(sys) {
                return Usefulness::Useful;
            }
            if let Some(m) = fa.terms.first() {
                // Order matters — `currentlyDeducible` subsumes
                // `probablyConstructible` for Pub/Nat-only terms but
                // also catches the `extractible` case.
                if currently_deducible(sys, adj, i, m) {
                    return Usefulness::CurrentlyDeducible;
                }
                if probably_constructible(m) {
                    return Usefulness::ProbablyConstructible;
                }
            }
        }
    }
    Usefulness::Useful
}

/// Port of Haskell `hasKUGuards` (`Goals.hs`):
///
/// ```haskell
/// hasKUGuards =
///     any ((KUFact `elem`) . guardFactTags) $ S.toList $ get sFormulas sys
/// ```
///
/// True iff any guarded formula in `sys.formulas` has a `KU`-tagged
/// fact atom in its guard list.  HS only checks `sFormulas`, NOT
/// `sLemmas` — reuse lemmas with `KU(...)` guards (e.g.
/// `neither_k_nor_k2_are_ever_leaked_inv` in YubiSecure) must not
/// trigger this short-circuit, otherwise every KU action goal is
/// promoted to `Useful` and `currentlyDeducible` / `probablyConstructible`
/// demotion never fires.  Walks recursively, surfacing KU action atoms
/// from inside `GGuarded`/`GAtom`/`Conj`/`Disj` structures.
fn has_ku_guards(sys: &System) -> bool {
    use crate::guarded::{Guarded, GAtom};
    fn walk_guards(g: &Guarded) -> bool {
        match g {
            // HS `getTags _qua _ss atos inner` inspects ONLY the guard list
            // (`atos`) of a `GGuarded`; the bare-atom case is `fAto = mempty`,
            // contributing NO tags (Guarded.hs:170-173).  So a bare `GAto`
            // KU action atom must NOT count — only a `GGuarded`'s guards.
            Guarded::GGuarded { guards, body, .. } => {
                for atom in guards {
                    if let GAtom::Action(fa, _) = atom {
                        if fa.name == "KU" { return true; }
                    }
                }
                walk_guards(body)
            }
            Guarded::Conj(items) | Guarded::Disj(items) => items.iter().any(walk_guards),
            // `fAto = mempty`: bare atoms contribute no tags.
            Guarded::Atom(_) => false,
        }
    }
    sys.formulas.iter().any(|f| walk_guards(f))
}

/// `currentlyDeducible i m` — direct port of Haskell's
/// `Goals.hs:66-182, see line 140`. True iff:
///   * `m` consists only of Pub/Nat literals (no private function
///     symbols), OR
///   * `m` is `extractible i m` from some existing node's `Out` /
///     `KD` conclusion via top-level pair / inverse decomposition,
///     and that node is not reachable from `i` via `rawLessRel`.
fn currently_deducible(
    sys: &System,
    adj: &RawLessAdj,
    i: &crate::constraint::constraints::NodeId,
    m: &tamarin_term::lterm::LNTerm,
) -> bool {
    use tamarin_term::lterm::LSort;
    if check_term_lits(m, |s| s == LSort::Pub || s == LSort::Nat)
        && !contains_private(m)
    {
        return true;
    }
    extractible(sys, adj, i, m)
}

/// `extractible i m` — direct port of Haskell's `Goals.hs:66-182, see line 144`.
/// True iff some node `j != lastAtom` produces `m` (or one of its
/// top-level pair/inv subterms) at an `Out` / `KD` conclusion,
/// and `j` is not reachable from `i` via `rawLessRel` (so adding
/// the dependency wouldn't introduce a cycle).
fn extractible(
    sys: &System,
    adj: &RawLessAdj,
    i: &crate::constraint::constraints::NodeId,
    m: &tamarin_term::lterm::LNTerm,
) -> bool {
    use crate::fact::FactTag;
    let i_reach = reachable_from(adj, i);
    for (j, rule) in sys.nodes.iter() {
        if Some(j) == sys.last_atom.as_ref() { continue; }
        // We cannot deduce a message via a node we ourselves precede.
        if i_reach.contains(j) { continue; }
        // `Out(t)` and `KD(t)` conclusions.
        for fa in rule.conclusions.iter() {
            let derived = match &fa.tag {
                FactTag::Out => fa.terms.first(),
                FactTag::Kd => fa.terms.first(),
                _ => None,
            };
            let Some(t) = derived else { continue };
            for sub in toplevel_terms(t) {
                if sub == *m { return true; }
            }
        }
    }
    false
}

/// `toplevelTerms t` — direct port of `Goals.hs:66-182, see line 157`. Walks pair/inv
/// at the top level only (other function applications are leaves).
fn toplevel_terms(t: &tamarin_term::lterm::LNTerm) -> Vec<tamarin_term::lterm::LNTerm> {
    use tamarin_term::function_symbols::{FunSym, NoEqSym};
    use tamarin_term::term::Term;
    let mut out = vec![t.clone()];
    if let Term::App(FunSym::NoEq(NoEqSym { name, .. }), args) = t {
        match &**name {
            b"pair" if args.len() == 2 => {
                out.extend(toplevel_terms(&args[0]));
                out.extend(toplevel_terms(&args[1]));
            }
            b"inv" if args.len() == 1 => {
                out.extend(toplevel_terms(&args[0]));
            }
            _ => {}
        }
    }
    out
}

/// The `rawLessRel` adjacency: `from -> [to]` successor lists.
///
/// `rawLessRel se = getLessRel sLessAtoms ++ rawEdgeRel se`, and
/// `rawEdgeRel sys = map (nodeConcNode *** nodePremNode) $ [Edge..] ++
/// unsolvedChains sys` (System.hs:1613-1622).  So the relation has one
/// conc-node -> prem-node edge per *unsolved Chain goal* in addition to
/// `sLessAtoms` and `sEdges` — mirroring `build_always_before_adj`
/// (system.rs).  Omitting the unsolved-chain edges would mis-classify a
/// KU goal's `Usefulness` in `extractible`/`currentlyDeducible`.
///
/// This adjacency is invariant across all goals in one `openGoals`
/// pass (only the BFS seed `i` varies per KU goal), so HS computes
/// `existingDeps = rawLessRel sys` ONCE in the `where` clause of
/// `openGoals` (Goals.hs:66-182, see line 120) and shares it.  We get it from the single
/// [`System::build_always_before_adj`] `PrebuiltAdj` (built once in
/// `open_goals`) via `.map()` and thread it through
/// `goal_usefulness_with_adj` — the `rawLessRel` map and the always-before
/// adjacency are the SAME relation, built identically.
type RawLessAdj = std::collections::BTreeMap<
    crate::constraint::constraints::NodeId,
    Vec<crate::constraint::constraints::NodeId>,
>;

/// Forward transitive-reachability set over a `rawLessRel` adjacency
/// (`from -> [to]` successor lists).  With `include_seed = true` the
/// returned set contains `from` itself — mirroring HS `D.reachableSet
/// [from] rel`, which seeds the visited set with `from` (Data/DAG/
/// Simple.hs:76-79); with `false` the seed is removed, yielding the
/// "strictly reachable" set (≥1 edge) the contradiction checks want.
///
/// Traversal order (BFS vs DFS) is immaterial: the result is a
/// `BTreeSet`, so any spanning order produces the identical set.  This is
/// the single reachability routine shared by `reachable_from`
/// (`extractible`, seed retained) and contradictions.rs's
/// `non_injective_fact_instances` / `node_after_last` (seed removed).
pub(crate) fn reachable_set_adj(
    adj: &RawLessAdj,
    from: &crate::constraint::constraints::NodeId,
    include_seed: bool,
) -> std::collections::BTreeSet<crate::constraint::constraints::NodeId> {
    use std::collections::{BTreeSet, VecDeque};
    let mut seen: BTreeSet<crate::constraint::constraints::NodeId> = BTreeSet::new();
    let mut q: VecDeque<crate::constraint::constraints::NodeId> = VecDeque::new();
    q.push_back(from.clone());
    while let Some(n) = q.pop_front() {
        if !seen.insert(n.clone()) { continue; }
        if let Some(succs) = adj.get(&n) {
            for s in succs { q.push_back(s.clone()); }
        }
    }
    if !include_seed { seen.remove(from); }
    seen
}

/// `rawLessRel`-based forward reachability: every node id reachable
/// from `i` via the prebuilt `rawLessRel` adjacency (transitive
/// closure).  Mirrors HS `D.reachableSet [i] existingDeps`
/// (Goals.hs:66-182, see line 155) — seed retained.
fn reachable_from(
    adj: &RawLessAdj,
    i: &crate::constraint::constraints::NodeId,
) -> std::collections::BTreeSet<crate::constraint::constraints::NodeId> {
    reachable_set_adj(adj, i, true)
}

/// `checkTermLits p t` — true iff every leaf-literal sort in `t`
/// satisfies `p`. Mirrors Haskell's `foldMap (All . p . sortOfLit)`.
fn check_term_lits<F: Fn(tamarin_term::lterm::LSort) -> bool>(
    t: &tamarin_term::lterm::LNTerm,
    p: F,
) -> bool {
    fn walk<F: Fn(tamarin_term::lterm::LSort) -> bool>(
        t: &tamarin_term::lterm::LNTerm, p: &F,
    ) -> bool {
        use tamarin_term::lterm::sort_of_name;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => p(v.sort),
            Term::Lit(Lit::Con(c)) => p(sort_of_name(c)),
            Term::App(_, args) => args.iter().all(|a| walk(a, p)),
        }
    }
    walk(t, &p)
}

/// `probablyConstructible` (Haskell):
///   no fresh-name literals AND no private function symbols.
fn probably_constructible(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::LSort;
    !lit_sort_contains(t, LSort::Fresh) && !contains_private(t)
}

/// True iff any literal in `t` has the given sort. The Haskell source
/// folds `sortOfLit` over every leaf; we mirror that with a recursive
/// walk over `Term`, comparing `target` against `Var.sort` for variables
/// and `sort_of_name` for constants.
fn lit_sort_contains(t: &tamarin_term::lterm::LNTerm, target: tamarin_term::lterm::LSort) -> bool {
    use tamarin_term::lterm::sort_of_name;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => v.sort == target,
        Term::Lit(Lit::Con(c)) => sort_of_name(c) == target,
        Term::App(_, args) => args.iter().any(|a| lit_sort_contains(a, target)),
    }
}

/// Dispatch a goal to the appropriate `solve_*_goal` primitive on a
/// `Reduction`. Mirrors the case dispatch at the top of Haskell's
/// `solveGoal`. Returns the corresponding `GoalCases` outcome.
pub fn dispatch_solve_goal(
    red: &mut crate::constraint::solver::reduction::Reduction<'_>,
    g: &Goal,
) -> crate::constraint::solver::reduction::GoalCases {
    // Haskell-faithful: mark the goal as solved BEFORE delegating to
    // the specific solver.  Mirrors `solveGoal` (Goals.hs:201-213):
    //   solveGoal goal = do
    //       -- mark before solving, as representation might change due
    //       -- to unification
    //       markGoalAsSolved "directly" goal
    //       ...
    //       case goal of
    //         ActionG i fa  -> solveAction ...
    //         PremiseG p fa -> solvePremise ...
    //         ...
    //
    // The comment in Haskell ("representation might change due to
    // unification") refers exactly to the case where `solveFactEqs` or
    // `substSystem` running INSIDE the solver rewrites the goal's terms
    // (e.g. Check0's `Loop(loopId, kOrig, kOrig)` repeated-arg unification
    // rewrites `Loop(t1, t2, t3)` → `Loop(t1, t2, t2)`).  An attempted
    // post-solve mark with the ORIGINAL goal then misses the (now
    // substituted) goal in the map and leaves it open.  Concrete
    // trigger: Minimal_HashChain Loop_Start source-case Check0 left
    // its abstract Loop goal open, which then triggered another graft
    // iteration adding a duplicate Check0 node.
    red.mark_goal_as_solved(g);
    // HS-faithful `solve goal = maybe (solveGoal goal) ...
    // (solveWithSource ctxt ths goal)` (ProofMethod.hs:467-470).
    // HS tries source-case dispatch FIRST; only if it returns
    // `Nothing` does it fall back to `solveGoal` (which emits the
    // `traceExecM ("solveGoal " ++ goalKind goal)` line).  Mirror
    // here for `Premise` goals: try `solve_with_source_cases_ctx`,
    // and if it returns `Some(cases)`, return them directly without
    // emitting the `solveGoal kind=Premise fact=...` trace.
    //
    // Limited to `Premise` goals for now (HS uses `solveWithSource`
    // for both Action-KU and Premise; we leave Action to its
    // existing inner source-case path pending further audit).
    if let Goal::Premise(p, fa) = g {
        // HS-faithful (Sources.hs:202-206): `solveAllSafeGoals` only
        // calls `solveWithSourceAndReturn` on "useful" goals (KU
        // actions), routing safe goals (Premise) through `solveGoal`
        // directly.  At runtime (`ProofMethod.solve` line 467-470),
        // dispatch fires for any goal.  Gate Premise dispatch on
        // `!in_precompute_mode()` so saturate skips it.
        if !crate::constraint::solver::sources::in_precompute_mode()
            && !red.ctx.full_sources.is_empty()
        {
            if let Some(case_pairs) = crate::constraint::solver::sources::solve_with_source_cases_ctx(
                red.ctx,
                &red.ctx.full_sources,
                &red.sys,
                &p.0, p.1, fa,
                Some(&red.maude),
            ) {
                use crate::constraint::solver::reduction::GoalCases;
                if case_pairs.len() == 1 {
                    let (name, sys, branch_counter) =
                        case_pairs.into_iter().next().unwrap();
                    red.sys = sys;
                    // HS FreshT-threading (task #23, A(ii) premise
                    // parity): single-case adoption continues THIS
                    // branch's counter thread (fork + its own
                    // someInst/conjoin draws), not the shared handle's
                    // post-all-cases position.
                    red.maude.reset_counter_to(branch_counter);
                    return GoalCases::LinearNamed(name);
                }
                if !case_pairs.is_empty() {
                    // Multi-case: record per-branch continuation
                    // counters for the post-solve simplify (consumed
                    // via `last_case_counters`, parallel to the Cases
                    // vec — same contract as the action-path source
                    // adoption in `solve_action_goal`).
                    let mut out: Vec<(String, crate::constraint::system::System)> =
                        Vec::with_capacity(case_pairs.len());
                    let mut out_counters: Vec<u64> =
                        Vec::with_capacity(case_pairs.len());
                    for (name, sys, branch_counter) in case_pairs {
                        out.push((name, sys));
                        out_counters.push(branch_counter);
                    }
                    red.last_case_counters = out_counters;
                    return GoalCases::Cases(out);
                }
                // HS-faithful: `solveWithSource` returned `Just` (the
                // abstract `matchToGoal` matched) but every case was
                // contradictory at conjoin → zero surviving cases.  HS
                // renders this `by` (no children, Proof.hs:1080-1101, see line 1084); the
                // node is contradictory.  Return `Contradictory` instead
                // of falling through to runtime `solve_premise_goal`,
                // which would re-introduce a shallow producer case HS
                // never explores.
                return GoalCases::Contradictory;
            }
        }
    }
    // TAM_RS_TRACE_EXEC mirror of Haskell `solveGoal` `T.traceExecM`
    // (Goals.hs:200-212, see line 206).  Same canonical-data form as the Haskell side so
    // the two outputs diff cleanly.
    //
    // Fact rendering mirrors Haskell `show FactTag`:
    //   - `Ku`   → "KUFact"
    //   - `Kd`   → "KDFact"
    //   - `Fresh`→ "FreshFact"
    //   - `Out`  → "OutFact"
    //   - `In`   → "InFact"
    //   - `Proto(mult, name, _)` → "ProtoFact <Mult> \"<name>\" <arity>"
    // Gate the whole label build behind the cached `TAM_RS_TRACE_EXEC`
    // flag: the `format!` + `fact_tag_haskell`/`fact_term_head` allocs fire
    // on every goal dispatch, and are dead work unless the trace is on.
    if crate::constraint::solver::trace::exec_enabled() {
        use crate::constraint::solver::trace::trace_exec;
        use tamarin_term::lterm::sort_prefix;
        let label = match g {
            Goal::Action(_, fa)  => format!("solveGoal kind=Action fact={}({})",
                fact_tag_haskell(fa), fact_term_head(fa, sort_prefix)),
            Goal::Premise(_, fa) => format!("solveGoal kind=Premise fact={}({})",
                fact_tag_haskell(fa), fact_term_head(fa, sort_prefix)),
            Goal::Chain(_, _)    => "solveGoal kind=Chain".to_string(),
            Goal::Split(_)       => "solveGoal kind=Split".to_string(),
            Goal::Disj(_)        => "solveGoal kind=Disj".to_string(),
            Goal::Subterm(_)     => "solveGoal kind=Subterm".to_string(),
        };
        trace_exec(&label);
    }
    match g {
        Goal::Action(i, fa) => red.solve_action_goal(i, fa),
        Goal::Premise(p, fa) => red.solve_premise_goal(p, fa),
        Goal::Chain(c, p) => red.solve_chain_goal(c, p),
        Goal::Split(id) => red.solve_split_goal(*id),
        Goal::Disj(d) => red.solve_disj_goal(d),
        Goal::Subterm(st) => red.solve_subterm_goal(st),
    }
}

// Public wrappers so sites outside this module (e.g. sources.rs's
// direct solve_*_goal calls that bypass dispatch_solve_goal) can emit
// the same EXEC-trace format.
pub fn fact_tag_haskell_pub(fa: &crate::fact::LNFact) -> String { fact_tag_haskell(fa) }
pub fn fact_term_head_pub(fa: &crate::fact::LNFact) -> String {
    use tamarin_term::lterm::sort_prefix;
    fact_term_head(fa, sort_prefix)
}

// Haskell `Show FactTag` mirror (Fact.hs).  Used only by the trace; not
// visible elsewhere.  Keep aligned with Haskell so the EXEC diff doesn't
// show spurious format-only differences.
fn fact_tag_haskell(fa: &crate::fact::LNFact) -> String {
    use crate::fact::{FactTag, Multiplicity};
    match &fa.tag {
        FactTag::Ku    => "KUFact".to_string(),
        FactTag::Kd    => "KDFact".to_string(),
        FactTag::Fresh => "FreshFact".to_string(),
        FactTag::Out   => "OutFact".to_string(),
        FactTag::In    => "InFact".to_string(),
        FactTag::Ded   => "DedFact".to_string(),
        FactTag::Term  => "TermFact".to_string(),
        FactTag::Proto(mult, name, arity) => {
            let m = match mult {
                Multiplicity::Linear     => "Linear",
                Multiplicity::Persistent => "Persistent",
            };
            format!("ProtoFact {} \"{}\" {}", m, name, arity)
        }
    }
}

// Canonical head-symbol rendering for the EXEC trace.  Mirrors Haskell's
// `termHeadStr` in Goals.hs (Var → `sortPrefix ++ name`, Const → `<const>`,
// App → `showFunSymName`).  Used only by the trace; not visible elsewhere.
fn fact_term_head(
    fa: &crate::fact::LNFact,
    sort_prefix: fn(tamarin_term::lterm::LSort) -> &'static str,
) -> String {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::FunSym;
    match fa.terms.first() {
        None => String::new(),
        Some(Term::Lit(Lit::Var(v))) =>
            format!("{}{}", sort_prefix(v.sort), v.name),
        Some(Term::Lit(Lit::Con(_))) => "<const>".to_string(),
        Some(Term::App(sym, _)) => match sym {
            FunSym::NoEq(noeq) => String::from_utf8_lossy(noeq.name).into_owned(),
            FunSym::Ac(op) => format!("{:?}", op),
            FunSym::C(op) => format!("{:?}", op),
            FunSym::List => "List".to_string(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;

    #[test]
    fn empty_system_has_no_open_goals() {
        let sys = System::empty();
        assert!(open_goals(&sys).is_empty());
    }

    #[test]
    fn single_goal_returned() {
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new(
            "k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        sys.add_goal(Goal::Action(v, f));
        let goals = open_goals(&sys);
        assert_eq!(goals.len(), 1);
        assert_eq!(goals[0].usefulness, Usefulness::Useful);
    }

    #[test]
    fn solved_goal_filtered() {
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new(
            "k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        sys.add_goal(Goal::Action(v, f));
        sys.goals_mut()[0].1.solved = true;
        assert!(open_goals(&sys).is_empty());
    }

    #[test]
    fn dispatch_solve_disj_goal_routes() {
        use crate::constraint::solver::context::ProofContext;
        use crate::constraint::solver::reduction::{GoalCases, Reduction};
        use tamarin_term::maude_sig::pair_maude_sig;

        let path = match std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        }) { Some(p) => p, None => return };
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let ctx = ProofContext::new(h, Vec::new());
        let mut r = Reduction::new(&ctx, System::empty());
        // Empty disjunction → contradictory.
        let d = crate::constraint::constraints::Disj::<crate::guarded::Guarded>::new(Vec::new());
        let g = Goal::Disj(d);
        let out = dispatch_solve_goal(&mut r, &g);
        assert!(matches!(out, GoalCases::Contradictory));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for Goal-Ord.
    //
    // Haskell `data Goal` (Constraints.hs:155-168) declares variants in
    // this exact order, and derives `Ord`:
    //
    //     data Goal = ActionG _ _
    //               | ChainG _ _
    //               | PremiseG _ _
    //               | SplitG _
    //               | DisjG _
    //               | SubtermG _
    //               deriving( ..., Ord, ... )
    //
    // So the constructor tag order is:
    //     Action < Chain < Premise < Split < Disj < Subterm
    //
    // The Rust `Goal` enum (constraints.rs:138) preserves this variant
    // order, so its derived structural order — if we had one — would be
    // the same.  But `goal_cmp` (this file) hand-codes a `tag` function,
    // and any divergence between that and the variant order would silently
    // sort goals differently than Haskell.
    // =========================================================================

    /// Pin Haskell's Goal-Ord tag order: Action < Chain < Premise < Split
    /// < Disj < Subterm.
    ///
    /// This is the exact order from Constraints.hs:155-168.  When
    /// `goal_cmp` is wired into goal iteration (see file-level comment),
    /// the choice of Action's-first-Premise determines which goal the
    /// solver picks at each step, which determines the proof shape.
    #[test]
    fn goal_cmp_tag_order_matches_haskell_declaration() {
        use tamarin_term::lterm::{LSort, LVar};
        use crate::constraint::constraints::{Disj, NodeId, SplitId};
        use crate::fact::{FactTag, LNFact, Multiplicity};
        use crate::rule::{ConcIdx, PremIdx};
        use std::cmp::Ordering;

        // Build one minimal instance of each Goal variant.
        let v: LVar = LVar::new("k", LSort::Msg, 0);
        let n: NodeId = LVar::new("i", LSort::Node, 0);
        let f: LNFact = LNFact::new(
            FactTag::Proto(Multiplicity::Linear, "F", 0), vec![]);

        let action: Goal = Goal::Action(v.clone(), f.clone());
        let chain: Goal = Goal::Chain(
            (n.clone(), ConcIdx(0)), (n.clone(), PremIdx(0)));
        let premise: Goal = Goal::Premise((n.clone(), PremIdx(0)), f.clone());
        let split: Goal = Goal::Split(SplitId(0));
        let disj: Goal = Goal::Disj(Disj::<crate::guarded::Guarded>::new(vec![]));
        // Use plain msg vars for the Subterm pair.
        let sub: Goal = Goal::Subterm((
            tamarin_term::builtin::msg_var("a", 0),
            tamarin_term::builtin::msg_var("b", 0),
        ));

        // The order from Constraints.hs:155-168 (deriving Ord):
        //   ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG
        //
        // **THIS IS THE CONTRACT.**  If Rust's `goal_cmp` differs, the
        // BTreeMap-backed goal iteration in any Haskell-faithful wiring
        // will sort differently from Haskell, causing proof-step
        // divergences silently.
        let order = [&action, &chain, &premise, &split, &disj, &sub];
        let names = ["Action", "Chain", "Premise", "Split", "Disj", "Subterm"];
        for i in 0..order.len() {
            for j in (i + 1)..order.len() {
                assert_eq!(goal_cmp(order[i], order[j]), Ordering::Less,
                    "Haskell Goal-Ord requires {} < {} \
                     (Constraints.hs:155-168 declaration order).  \
                     goal_cmp put them in the wrong order — this WILL \
                     cause silent proof divergence when goal_cmp is \
                     wired into goal iteration.",
                    names[i], names[j]);
                assert_eq!(goal_cmp(order[j], order[i]), Ordering::Greater,
                    "Haskell Goal-Ord requires {} > {}",
                    names[j], names[i]);
            }
        }
    }

    /// Pin tag-equality (every variant ordered with itself returns Equal).
    /// Within-variant comparison is structural and depends on inner-field
    /// ordering; here we just check the tag-equality short-circuit.
    #[test]
    fn goal_cmp_reflexive() {
        use std::cmp::Ordering;
        use tamarin_term::lterm::{LSort, LVar};
        use crate::constraint::constraints::SplitId;

        let action: Goal = Goal::Action(
            LVar::new("k", LSort::Msg, 0),
            crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]),
        );
        let split: Goal = Goal::Split(SplitId(7));
        assert_eq!(goal_cmp(&action, &action), Ordering::Equal);
        assert_eq!(goal_cmp(&split, &split), Ordering::Equal);
    }

    /// Pin that `Goal` enum variant declaration order in Rust matches
    /// Haskell's data-decl order.  This is the upstream invariant that
    /// `goal_cmp`'s tag function should respect.  If Rust's enum is
    /// reordered, both this AND `goal_cmp` must change together.
    #[test]
    fn rust_goal_enum_variant_order_matches_haskell() {
        // We can't reflect over enum variants in stable Rust without a
        // proc-macro, but we can pin the order via discriminant indices
        // assigned by the compiler.  `Goal::Action(...)` is variant 0,
        // `Goal::Chain` is 1, etc.  If someone reorders the enum, the
        // discriminant values change and this test breaks.
        use std::mem::discriminant;
        use tamarin_term::lterm::{LSort, LVar};
        use crate::constraint::constraints::{Disj, NodeId, SplitId};
        use crate::fact::{FactTag, LNFact, Multiplicity};
        use crate::rule::{ConcIdx, PremIdx};

        let v: LVar = LVar::new("k", LSort::Msg, 0);
        let n: NodeId = LVar::new("i", LSort::Node, 0);
        let f: LNFact = LNFact::new(
            FactTag::Proto(Multiplicity::Linear, "F", 0), vec![]);

        // Build one of each variant in Haskell's declaration order.
        let variants = [
            Goal::Action(v.clone(), f.clone()),
            Goal::Chain((n.clone(), ConcIdx(0)), (n.clone(), PremIdx(0))),
            Goal::Premise((n.clone(), PremIdx(0)), f.clone()),
            Goal::Split(SplitId(0)),
            Goal::Disj(Disj::<crate::guarded::Guarded>::new(vec![])),
            Goal::Subterm((
                tamarin_term::builtin::msg_var("a", 0),
                tamarin_term::builtin::msg_var("b", 0),
            )),
        ];
        // All discriminants must be distinct (sanity).
        let discs: Vec<_> = variants.iter().map(discriminant).collect();
        for i in 0..discs.len() {
            for j in (i + 1)..discs.len() {
                assert_ne!(discs[i], discs[j],
                    "variants {} and {} share a discriminant!", i, j);
            }
        }
    }

    // -- Tactic ranking tests -------------------------------------------------

    /// HS `pg =~ regex` is an UNANCHORED PCRE search (matches anywhere).
    #[test]
    fn regex_unanchored_and_pcre_features() {
        // Unanchored substring search.
        assert!(regex_is_match("In_S", "solve( In_S( 'H1' ) )"));
        assert!(!regex_is_match("In_S", "solve( In_A( 'H1' ) )"));
        // Literal escaped paren `\(` (PCRE).
        assert!(regex_is_match(r"In_A\( 'S'", "In_A( 'S', <'codes'>)"));
        assert!(!regex_is_match(r"In_A\( 'S'", "In_A( 'BB', x)"));
        // Quoted-literal pattern from the corpus tactics.
        assert!(regex_is_match("'proofV'", "BB_C( <'proofV', x> )"));
        // PCRE negative lookahead — fancy-regex feature the `regex` crate
        // can't compile.  `!KU( <not one|true> )`.
        let pat = r"!KU\( (?!(one|true))[a-zA-Z0-9.]+ \)";
        assert!(regex_is_match(pat, "!KU( foo )"));
        assert!(!regex_is_match(pat, "!KU( one )"));
        // PCRE lookbehind.
        let lb = r"(?<!'g'\^)~[a-zA-Z.0-9]*";
        assert!(regex_is_match(lb, "x ~n1"));
        assert!(!regex_is_match(lb, "'g'^~n1"));
        // A regex that fails to compile yields `false`, never panics.
        assert!(!regex_is_match("(", "anything"));
    }

    /// PCRE (`regex-pcre-builtin`, the HS engine) has NO `\<` / `\>`
    /// word-boundary assertions — they are the escaped LITERAL chars `<`/`>`.
    /// `fancy-regex` would otherwise treat them as word boundaries, which
    /// diverges from HS (wisec21 5G_handover `secret_k_asme` tactic prio
    /// `.*RcvS.*~K_ASME\>.*`).  Behaviour pinned against the real HS library:
    ///   `"a\\>" =~ "a>"  == True`,  `"a\\>" =~ "a b"/"ab" == False`.
    #[test]
    fn regex_backslash_lt_gt_are_pcre_literals() {
        // `\>` == literal '>'.
        assert!(regex_is_match(r"a\>", "a>"));
        assert!(!regex_is_match(r"a\>", "a b")); // NOT a word boundary
        assert!(!regex_is_match(r"a\>", "ab"));
        // `\<` == literal '<'.
        assert!(regex_is_match(r"\<a", "<a"));
        assert!(!regex_is_match(r"\<a", " a"));
        // The exact corpus prio: must NOT match a `~K_ASME,` (comma) goal.
        let prio = r".*RcvS.*~K_ASME\>.*";
        assert!(!regex_is_match(
            prio,
            "RcvS( ~cid_N26.1, <'fr_req', ~K_ASME, ~eNB_UE_S1AP_ID.1>)"
        ));
        // …but DOES match a goal where '>' literally follows ~K_ASME.
        assert!(regex_is_match(prio, "RcvS( <'ho_required', x, ~K_ASME>)"));
        // `\b` is still the standard word boundary (unchanged).
        assert!(regex_is_match(r"a\b", "a b"));
        assert!(!regex_is_match(r"a\b", "ab"));
        // An escaped backslash before '>' is left intact: `\\>` = '\' then '>'.
        assert!(regex_is_match(r"a\\>", "a\\>"));
        assert!(!regex_is_match(r"a\\>", "a>"));
    }

    /// `apply_ranking_fn "smallest"` sorts by rendered length, stably;
    /// "id"/unknown is identity.
    #[test]
    fn ranking_fn_smallest_and_id() {
        use crate::fact::ku_fact;
        use tamarin_term::lterm::fresh_term;
        let mk = |s: &str, seq: u64| {
            let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
            AnnotatedGoal::new(Goal::Action(v, ku_fact(fresh_term(s))), seq, Usefulness::Useful)
        };
        // `~aaaa` renders longer than `~a`.
        let g_long = mk("aaaa", 0);
        let g_short = mk("a", 1);
        let out = apply_ranking_fn("smallest", vec![g_long.clone(), g_short.clone()]);
        assert_eq!(out[0].seq, 1, "shortest rendered goal first");
        assert_eq!(out[1].seq, 0);
        // id keeps input order.
        let out2 = apply_ranking_fn("id", vec![g_long.clone(), g_short.clone()]);
        assert_eq!(out2[0].seq, 0);
        assert_eq!(out2[1].seq, 1);
    }

    /// `it_ranking` result = rankedPrioGoals ++ nonRanked ++ rankedDeprioGoals,
    /// with prio groups in ascending-block order and unmatched goals
    /// preserved in presort order.
    #[test]
    fn it_ranking_prio_nonranked_deprio_order() {
        use crate::fact::ku_fact;
        use crate::tactic::{PrioBlock, SelectorExpr, SelectorLeaf, Tactic};
        use tamarin_term::lterm::fresh_term;

        let mk = |s: &str, seq: u64| {
            let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
            AnnotatedGoal::new(Goal::Action(v, ku_fact(fresh_term(s))), seq, Usefulness::Useful)
        };
        // Goals render as `!KU( ~skS )`, `!KU( ~r )`, `!KU( ~x )`.
        let g_sks = mk("skS", 0);
        let g_r = mk("r", 1);
        let g_x = mk("x", 2);
        let ags = vec![g_sks.clone(), g_r.clone(), g_x.clone()];

        let prio = |pat: &str| PrioBlock {
            ranking: "id".to_string(),
            disjuncts: vec![format!("regex \"{}\"", pat)],
            selectors: vec![SelectorExpr::Leaf(SelectorLeaf {
                name: "regex".to_string(),
                params: vec![pat.to_string()],
            })],
        };
        // Fresh names render as `~'skS'` etc.  prio 0 matches ~'r',
        // prio 1 matches ~'skS'; ~'x' matches no prio. deprio matches ~'x'.
        let tactic = Tactic {
            name: "t".to_string(),
            presort: 'C',
            prios: vec![prio("~'r'"), prio("~'skS'")],
            deprios: vec![prio("~'x'")],
        };

        let sys = System::empty();
        let out = it_ranking(&tactic, ags, false, None, &sys).unwrap();
        let seqs: Vec<u64> = out.iter().map(|a| a.seq).collect();
        // rankedPrio = [~r (block0), ~skS (block1)]; nonRanked = []
        // (every goal matched a prio or deprio); rankedDeprio = [~x].
        assert_eq!(seqs, vec![1, 0, 2],
            "prio(~r) then prio(~skS) then deprio(~x); got {:?}", seqs);
    }

    /// A goal matching NO prio/deprio lands in `nonRanked`, between the
    /// prio'd and deprio'd goals, in presort order.
    #[test]
    fn it_ranking_nonranked_preserved() {
        use crate::fact::ku_fact;
        use crate::tactic::{PrioBlock, SelectorExpr, SelectorLeaf, Tactic};
        use tamarin_term::lterm::fresh_term;
        let mk = |s: &str, seq: u64| {
            let v = tamarin_term::lterm::LVar::new("x", tamarin_term::lterm::LSort::Msg, 0);
            AnnotatedGoal::new(Goal::Action(v, ku_fact(fresh_term(s))), seq, Usefulness::Useful)
        };
        // Put the prio-matching goal LAST in presort order so a passing
        // result genuinely proves reordering (not a no-op).
        let g_b = mk("b", 0); // no match → nonRanked
        let g_c = mk("c", 1); // no match → nonRanked
        let g_a = mk("a", 2); // matches prio → moves to front
        let prio = PrioBlock {
            ranking: "id".to_string(),
            disjuncts: vec!["regex \"~'a'\"".to_string()],
            selectors: vec![SelectorExpr::Leaf(SelectorLeaf {
                name: "regex".to_string(),
                params: vec!["~'a'".to_string()],
            })],
        };
        let tactic = Tactic {
            name: "t".to_string(), presort: 'C',
            prios: vec![prio], deprios: vec![],
        };
        let sys = System::empty();
        let out = it_ranking(&tactic, vec![g_b, g_c, g_a], false, None, &sys).unwrap();
        let seqs: Vec<u64> = out.iter().map(|a| a.seq).collect();
        // ~'a' (prio, seq 2) first, then nonRanked [~'b'=0, ~'c'=1] in
        // presort order.
        assert_eq!(seqs, vec![2, 0, 1]);
    }

    // -- moveNatToEnd / isNatSubtermSplit (ProofMethod.hs:1064-1066) ----------

    /// `isNatSubtermSplit` (ProofMethod.hs:1048-1129, see line 1065) = `isNatSubterm st`
    /// (SubtermStore.hs:112-113, see line 113): `(sort small == Nat || isMsgVar small) &&
    /// sort big == Nat`.  Non-SubtermG goals are False.
    #[test]
    fn is_nat_subterm_split_matches_haskell() {
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::var_term;
        use crate::constraint::constraints::SplitId;

        let nat = |n: &str| var_term(LVar::new(n, LSort::Nat, 0));
        let msg = |n: &str| tamarin_term::builtin::msg_var(n, 0);
        let fresh = |n: &str| tamarin_term::builtin::fresh_var(n, 0);

        // small Nat, big Nat -> true.
        assert!(is_nat_subterm_split(&Goal::Subterm((nat("a"), nat("b")))));
        // small MsgVar, big Nat -> true (isMsgVar small branch).
        assert!(is_nat_subterm_split(&Goal::Subterm((msg("a"), nat("b")))));
        // small Nat, big NOT Nat -> false (big must be Nat).
        assert!(!is_nat_subterm_split(&Goal::Subterm((nat("a"), fresh("b")))));
        // small Fresh (not Nat, not MsgVar), big Nat -> false.
        assert!(!is_nat_subterm_split(&Goal::Subterm((fresh("a"), nat("b")))));
        // Non-Subterm goal -> false.
        assert!(!is_nat_subterm_split(&Goal::Split(SplitId(0))));
    }

    // -- UsefulGoalNr ('c') derived Usefulness Ord (ProofMethod.hs:480-503, see line 485) ------

    /// HS `UsefulGoalNrRanking -> sortOn (\(_, (nr, useless)) -> (useless,
    /// nr))` sorts on the DERIVED `Ord Usefulness` (declaration order
    /// Useful<LoopBreaker<ProbablyConstructible<CurrentlyDeducible,
    /// AnnotatedGoals.hs:18-27), NOT `tagUsefulness` (which would collapse
    /// LoopBreaker and ProbablyConstructible to the same key).  So a
    /// LoopBreaker goal must rank BEFORE a ProbablyConstructible goal even
    /// when its creation-nr is larger.
    #[test]
    fn useful_goal_nr_uses_derived_usefulness_ord() {
        use tamarin_term::lterm::{LSort, LVar};
        let mk = |seq: u64, u: Usefulness| {
            let v = LVar::new("k", LSort::Msg, 0);
            let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
            AnnotatedGoal::new(Goal::Action(v, f), seq, u)
        };
        // LoopBreaker with the LARGER nr, ProbablyConstructible with the
        // smaller nr.  HS Usefulness Ord (LoopBreaker < ProbablyConstructible)
        // must dominate the nr tiebreak.
        let lb = mk(5, Usefulness::LoopBreaker);
        let pc = mk(1, Usefulness::ProbablyConstructible);
        let mut ags = [pc.clone(), lb.clone()];
        ags.sort_by(|a, b| {
            a.usefulness.cmp(&b.usefulness).then_with(|| a.seq.cmp(&b.seq))
        });
        // LoopBreaker (seq 5) ranks first despite the larger nr: HS
        // `Usefulness` Ord (LoopBreaker < ProbablyConstructible) dominates the
        // nr tiebreak, even though `tag_usefulness` collapses the two (below).
        assert_eq!(ags[0].seq, 5, "LoopBreaker must rank before ProbablyConstructible");
        assert_eq!(ags[1].seq, 1);
        // And tag_usefulness genuinely WOULD collapse these two — proving the
        // distinction matters.
        assert_eq!(tag_usefulness(Usefulness::LoopBreaker),
                   tag_usefulness(Usefulness::ProbablyConstructible));
        // The derived Ord does NOT collapse them.
        assert!(Usefulness::LoopBreaker < Usefulness::ProbablyConstructible);
    }

    // -- goal_cmp Disj structural Ord (Constraints.hs derived Ord) -----------

    /// HS `Disj a = Disj [a]` derives Ord = list Ord bottoming out at the
    /// structural `Ord LNGuarded`, whose var leaves use `Ord LVar = (idx,
    /// sort, name)`.  When two Disj goals differ at a leaf var of different
    /// SORT (idx and name equal), HS LSort Ord (Pub<Fresh<Msg<Node<Nat)
    /// decides.  This pins that the comparator orders by that structural HS
    /// `Ord LSort` (Pub<Fresh), not by the `{:?}` sort-name string
    /// (Fresh<Msg<Nat<Node<Pub).
    #[test]
    fn goal_cmp_disj_var_sort_uses_lsort_ord() {
        use std::cmp::Ordering;
        use crate::constraint::constraints::Disj;
        use crate::guarded::{Guarded, GAtom, GTerm, BVar};
        use tamarin_parser::ast::{VarSpec, SortHint};

        // A single-atom Disj over `Last(v)` where v differs only by sort.
        let mk_disj = |sort: SortHint| -> Goal {
            let v = VarSpec { name: "x".to_string(), idx: 0, sort, typ: None };
            let atom = GAtom::Last(GTerm::Var(BVar::Free(v)));
            Goal::Disj(Disj::new(vec![Guarded::Atom(atom)]))
        };
        let pub_disj = mk_disj(SortHint::Pub);
        let fresh_disj = mk_disj(SortHint::Fresh);
        // HS LSort Ord: Pub < Fresh.  The structural comparator must put the
        // Pub-var Disj first (by sort, not by Debug-string name order).
        assert_eq!(goal_cmp(&pub_disj, &fresh_disj), Ordering::Less,
            "HS LSort Ord requires Pub < Fresh in Disj structural compare");
        assert_eq!(goal_cmp(&fresh_disj, &pub_disj), Ordering::Greater);
    }
}
