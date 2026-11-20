import Tamarin.CheckedVariants
import Tamarin.NarrowingStages

/-! Executable folding on a supplied rule table. Semantic hypotheses establish
that the search terminates and is complete. Neither is an argument to the evaluator. -/
namespace Tamarin.GeneralVariants
open Rewriting MaudeOperations ReferenceVariantFrontier
variable {s : Signature} [DecidableEq s.FreeSym] [DecidableEq s.CSym]
  [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def normalized {n : Nat} (rs : Problem s) (fuel : Nat) (p : Point s n) : Option (Point s n) :=
  let out := fun i => CheckedReduction.choose rs fuel (p.value i)
  if (List.finRange n).all (fun i => (out i).isSome) then
    some ⟨p.assignment,fun i => (out i).getD (p.value i)⟩
  else none

private def children {n : Nat} (rs : Problem s) (q : Fin n → Term s)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s)) (fuel : Nat) (p : Point s n) :=
  ((expand p (branches p)).filter (FoldingNarrowing.admissible rs q)).mapM (normalized rs fuel)

private def generate (rs : Problem s) (q : List (Term s)) (fuel : Nat) : Option (List (Variant s)) := do
  if hb : CheckedReduction.rangeBound rs then
    if hv : rs.all (fun r => CheckedVariants.nonvar r.lhs) then
      let bound := (CheckedReduction.rangeBound_iff rs).mp hb
      let vars := CheckedVariants.varsNormal rs hv
      let query := fun i : Fin q.length => q[i.val]
      let narrow := TableNarrowing.narrower bound vars query
      let first ← normalized rs fuel (seed query)
      let found ← VariantLayers.attempt (children rs query narrow.branches fuel)
        (VariantSaturation.subsumes query) fuel (VariantLayers.start first)
      let keys := keysOf query
      return VariantFreshening.freshen keys [] (found.map (Point.answer · keys))
    else none
  else none

private theorem choose_exact {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (k : Nat) (t u : Term s)
    (ok : CheckedReduction.choose rs k t = some u) : u = (ReferenceReduction.reducer rs bound can).reduce t := by
  induction k generalizing t with
  | zero => contradiction
  | succ k ih =>
    rw [show (ReferenceReduction.reducer rs bound can).reduce t = _ from
      reducerOfSteps_eq can (ReferenceReduction.finder rs bound) t]
    cases e : ReferenceReduction.successors rs t with
    | nil =>
      have stopped : (ReferenceReduction.finder rs bound).next t = none := by simp [ReferenceReduction.finder,e]
      rw [stopped]
      change (match ReferenceReduction.successors rs t with | [] => some t | x :: _ => CheckedReduction.choose rs k x) = some u at ok
      simpa [e] using ok.symm
    | cons x xs =>
      have step : (ReferenceReduction.finder rs bound).next t = some x := by simp [ReferenceReduction.finder,e]
      rw [step]
      apply ih
      change (match ReferenceReduction.successors rs t with | [] => some t | x :: _ => CheckedReduction.choose rs k x) = some u at ok
      simpa [e] using ok

private theorem choose_eventually {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (t : Term s) :
    ∃ k, ∀ n ≥ k, CheckedReduction.choose rs n t = some ((ReferenceReduction.reducer rs bound can).reduce t) := by
  let h := ReductionHeight.height bound can.terminating
  refine ⟨h t + 1,fun n enough => ?_⟩
  obtain ⟨u,ok⟩ := CheckedReduction.chosen_within bound h (ReductionHeight.step bound can.terminating) n t enough
  exact (choose_exact bound can n t u ok) ▸ ok

private def reduced {n : Nat} {rs : Problem s} (r : VerifiedReducer (ruleRoot rs)) (p : Point s n) : Point s n :=
  ⟨p.assignment,fun i => r.reduce (p.value i)⟩

private theorem normalized_exact {n : Nat} {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (fuel : Nat) (p v : Point s n)
    (ok : normalized rs fuel p = some v) : v = reduced (ReferenceReduction.reducer rs bound can) p := by
  unfold normalized at ok
  dsimp only at ok
  split at ok <;> try contradiction
  next valid =>
    cases ok
    congr 1
    funext i
    obtain ⟨u,eq⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp valid i (List.mem_finRange i))
    simpa only [eq,Option.getD_some] using choose_exact bound can fuel (p.value i) u eq

private theorem normalized_eventually {n : Nat} {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (p : Point s n) :
    ∃ k, ∀ f ≥ k, normalized rs f p = some (reduced (ReferenceReduction.reducer rs bound can) p) := by
  obtain ⟨k,all⟩ := CheckedReduction.common_budget (List.finRange n) _ (fun i _ => choose_eventually bound can (p.value i))
  refine ⟨k,fun f hf => ?_⟩
  have all' := fun i => all f hf i (List.mem_finRange i)
  simp [normalized,all',reduced]

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem nonvariable {rs : Problem s} (can : CanonicalPresentation (ruleRoot rs)) :
    rs.all (fun r => CheckedVariants.nonvar r.lhs) := by
  apply List.all_eq_true.mpr
  intro r hr
  cases src : r.lhs <;> try rfl
  next v =>
    exfalso
    apply TableNarrowing.variablesNormal can v (Substitution.identity.apply r.rhs)
    exact ⟨_,_,.refl _,.root ⟨r,hr,.identity,by simp [src,Substitution.identity,Substitution.apply],rfl⟩,.refl _⟩

private theorem generated_correct {rs : Problem s} {q fuel rows} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (hit : generate rs q fuel = some rows) :
    VariantReply (ruleRoot rs) q [] rows := by
  let query := fun i : Fin q.length => q[i.val]
  let vars := TableNarrowing.variablesNormal can
  let narrow := TableNarrowing.narrower bound vars query
  let r := ReferenceReduction.reducer rs bound can
  let g := FoldingNarrowing.expansion bound can vars r narrow
  let test := children rs query narrow.branches fuel
  let cover := VariantSaturation.subsumes query
  simp only [generate,(CheckedReduction.rangeBound_iff _).mpr bound,nonvariable can,dite_eq_left] at hit
  change (normalized rs fuel (seed query)).bind _ = some rows at hit
  obtain ⟨first,initial,hit⟩ := Option.bind_eq_some_iff.mp hit
  have e : first = g.seed := normalized_exact bound can _ _ _ initial
  subst first
  change (VariantLayers.attempt test cover fuel (VariantLayers.start g.seed)).bind _ = some rows at hit
  obtain ⟨states,h,final⟩ := Option.bind_eq_some_iff.mp hit
  cases final
  have closed := VariantLayers.attempt_closed (seed := g.seed) (next := g.next) (covers := cover)
    (fun p => (VariantSaturation.subsumes_iff ..).mpr (VariantJoin.Row.Subsumes.refl _))
    (fun p cs ok => VariantLayers.mapM_sound (normalized_exact bound can fuel) _ cs ok) fuel 0 h
  simpa [query] using VariantSaturation.reply_of_closed g can vars r states closed []

private theorem generates (rs : Problem s) (q : List (Term s)) (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (finite : FiniteVariantProperty (ruleRoot rs)) :
    ∃ rows k, ∀ n ≥ k, generate rs q n = some rows := by
  let query := fun i : Fin q.length => q[i.val]
  let vars := TableNarrowing.variablesNormal can
  let narrow := TableNarrowing.narrower bound vars query
  let g := FoldingNarrowing.expansion bound can vars (ReferenceReduction.reducer rs bound can) narrow
  let test := children rs query narrow.branches
  have per (p) : ∃ k, ∀ n ≥ k, test n p = some (g.next p) := by
    let raw := (expand p (narrow.branches p)).filter (FoldingNarrowing.admissible rs query)
    obtain ⟨k,h⟩ := CheckedReduction.common_budget raw _ (fun x _ => normalized_eventually bound can x)
    exact ⟨k,fun n hn => VariantLayers.mapM_exact raw (h n hn)⟩
  obtain ⟨states,k,h⟩ := VariantLayers.attempt_eventually per (VariantSaturation.basis g can (by simpa [query] using finite q))
  obtain ⟨m,first⟩ := normalized_eventually bound can (seed query)
  refine ⟨VariantFreshening.freshen (keysOf query) [] (states.map (Point.answer · (keysOf query))),max k m,fun n hn => ?_⟩
  simp only [generate,(CheckedReduction.rangeBound_iff _).mpr bound,nonvariable can,dite_eq_left]
  have initial : normalized rs n (seed query) = some g.seed := first n (Nat.le_trans (Nat.le_max_right ..) hn)
  change (normalized rs n (seed query)).bind _ = _
  rw [initial]
  change (VariantLayers.attempt (test n) _ n (VariantLayers.start g.seed)).bind _ = _
  rw [h n (Nat.le_trans (Nat.le_max_left ..) hn)]
  rfl

private def agrees (rs : Problem s) (fuel : Nat) (σ : Substitution s) : List (Term s) → List (Term s) → Bool
  | [],[] => true
  | t :: ts, v :: vs =>
    let a := σ.apply t
    (CheckedReduction.choose rs fuel a).any (ReferenceMatching.equal v) &&
      CheckedReduction.sorts a v && agrees rs fuel σ ts vs
  | _,_ => false

private def sound (rs : Problem s) (fuel : Nat) (q : List (Term s)) (row : Variant s) :=
  row.subst.support.all (fun v => normal rs (row.subst.image v)) && agrees rs fuel row.subst q row.values

private theorem replay_sound {rs : Problem s} (bound : ReferenceReduction.Bound rs) (fuel : Nat) (σ : Substitution s)
    (q vs : List (Term s)) (ok : agrees rs fuel σ q vs) :
    Aligned (fun t v => NormalForm (ruleRoot rs) (σ.apply t) v) q vs := by
  induction q generalizing vs with
  | nil => cases vs <;> simp_all [agrees,Aligned]
  | cons t ts ih =>
    cases vs with
    | nil => contradiction
    | cons v vs =>
      obtain ⟨⟨hit,sorts⟩,tail⟩ := (by simpa only [agrees,Bool.and_eq_true] using ok :
        (_ ∧ _) ∧ agrees rs fuel σ ts vs)
      obtain ⟨u,done,same⟩ := (Option.any_eq_true _ _).mp hit
      have eq := (ReferenceMatching.equal_iff ..).mp same
      obtain ⟨path,nf⟩ := CheckedReduction.chosen bound fuel _ _ done
      exact ⟨⟨path.trans (.basis eq.symm),(normal_equiv _ eq).mpr nf,(CheckedReduction.sorts_iff ..).mp sorts⟩,ih _ tail⟩

private theorem replay_eventually {rs : Problem s} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (σ : Substitution s) (q vs : List (Term s))
    (forms : Aligned (fun t v => NormalForm (ruleRoot rs) (σ.apply t) v) q vs) :
    ∃ k, ∀ n ≥ k, agrees rs n σ q vs := by
  induction q generalizing vs with
  | nil => cases vs <;> first | exact ⟨0,fun _ _ => rfl⟩ | contradiction
  | cons t ts ih =>
    cases vs with
    | nil => contradiction
    | cons v vs =>
      obtain ⟨k,head⟩ := choose_eventually bound can (σ.apply t)
      obtain ⟨m,tail⟩ := ih vs forms.2
      have eq := ((ReferenceReduction.reducer rs bound can).correct (σ.apply t)).unique v forms.1
      exact ⟨max k m,fun n hn => by simp [agrees,head n (Nat.le_trans (Nat.le_max_left ..) hn),
        ReferenceMatching.equal_iff,eq,(CheckedReduction.sorts_iff ..).mpr forms.1.2.2,tail n (Nat.le_trans (Nat.le_max_right ..) hn)]⟩

/-- Independently replay every row against the equations. Even a terminating
run on a noncanonical table can only report genuine variants. -/
def run (rs : Problem s) (q : List (Term s)) (fuel : Nat) : Option (List (Variant s)) :=
  (generate rs q fuel).bind fun rows => if rows.all (sound rs fuel q) then some rows else none

theorem sound_on_success {rs : Problem s} {q fuel rows} (hit : run rs q fuel = some rows) :
    ∀ a ∈ rows, a.Sound (ruleRoot rs) q := by
  cases hb : CheckedReduction.rangeBound rs with
  | false => simp [run,generate,hb] at hit
  | true =>
    cases hv : rs.all (fun r => CheckedVariants.nonvar r.lhs) with
    | false => simp [run,generate,hb,hv] at hit
    | true =>
      have bound := (CheckedReduction.rangeBound_iff rs).mp hb
      cases found : generate rs q fuel with
      | none => simp [run,found] at hit
      | some ps =>
        simp only [run,found,Option.bind_some] at hit
        split at hit <;> try contradiction
        next check =>
          cases hit
          intro a ha
          obtain ⟨images,vals⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp check a ha)
          refine ⟨fun v => ?_,replay_sound bound fuel _ _ _ vals⟩
          by_cases live : v ∈ a.subst.support
          · exact (normal_iff bound _).mp (List.all_eq_true.mp images v live)
          · rw [a.subst.outside v live]
            exact CheckedVariants.varsNormal rs hv v

theorem correct {rs : Problem s} {q fuel rows} (bound : ReferenceReduction.Bound rs)
    (can : CanonicalPresentation (ruleRoot rs)) (hit : run rs q fuel = some rows) :
    VariantReply (ruleRoot rs) q [] rows := by
  obtain ⟨ps,done,h⟩ := Option.bind_eq_some_iff.mp hit
  split at h <;> try contradiction
  cases h
  exact generated_correct bound can done

theorem completes (rs : Problem s) (q : List (Term s))
    (bound : ReferenceReduction.Bound rs) (can : CanonicalPresentation (ruleRoot rs))
    (finite : FiniteVariantProperty (ruleRoot rs)) :
    ∃ rows k, (∀ n ≥ k, run rs q n = some rows) ∧ VariantReply (ruleRoot rs) q [] rows := by
  obtain ⟨rows,k,found⟩ := generates rs q bound can finite
  have reply := generated_correct bound can (found k (Nat.le_refl _))
  obtain ⟨m,check⟩ := CheckedReduction.common_budget rows (fun a n => sound rs n q a = true) (by
    intro a ha
    have ok := reply.complete.1 a ha
    obtain ⟨l,h⟩ := replay_eventually bound can _ _ _ ok.2
    exact ⟨l,fun n hn => Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr (fun v _ => (normal_iff bound _).mpr (ok.1 v)),h n hn⟩⟩)
  refine ⟨rows,max k m,fun n hn => ?_,reply⟩
  have all := List.all_eq_true.mpr (check n (Nat.le_trans (Nat.le_max_right ..) hn))
  simp only [run,found n (Nat.le_trans (Nat.le_max_left ..) hn),Option.bind_some,all,ite_true]

/-- Follow ordinary reductions on the entire tuple, retaining each intermediate
point. The public checker can then test alternative symbolic rewrites there.
The credit is shared by all coordinates in this trace. -/
private def trace {n : Nat} (rs : Problem s) (work : Nat) (p : Point s n) :
    Nat → List (Point s n)
  | 0 => [p]
  | k+1 => Id.run do
    if !FrontierWork.admits rs (List.ofFn p.value) work then return [p]
    for i in List.finRange n do
      if let some u := (ReferenceReduction.successors rs (p.value i)).head? then
        return p :: trace rs work ⟨p.assignment,fun j => if j = i then u else p.value j⟩ k
    return [p]

/-- Explore normalized observations. Retain their ordinary paths for independent
closure and replay on the *original* query, including alternative reductions.
Failure to fit or certify the proposed frontier defers the whole result. -/
private def propose {n : Nat} (rs : Problem s) (query : Fin n → Term s)
    (branches : Point s n → Fin n → List (RootNarrowing.Branch s))
    (work : Nat) (seen frontier : List (Point s n)) (credits : Nat) :
    Nat → List (Point s n)
  | 0 => seen
  | k+1 => Id.run do
    let keys := keysOf query
    let mut live := []
    let mut states := seen
    let mut remaining := credits
    for p in frontier do
      if !FrontierWork.admits rs (keys.map p.assignment.image ++ List.ofFn p.value) work then return seen
      let children := expand p (branches p)
      if children.length > remaining then return seen
      remaining := remaining - children.length
      for child in children do
        if !FoldingNarrowing.admissible rs query child then continue
        if states.any (fun a => VariantSaturation.subsumes query a child) then continue
        let path := trace rs work child (min work remaining)
        if path.length > remaining then return seen
        remaining := remaining - path.length
        if let some last := path.getLast? then
          if !states.any (fun a => VariantSaturation.subsumes query a last) then
            live := last :: live
        states := path ++ states
    if live.isEmpty then return states
    return propose rs query branches work states live remaining k

def checked (rs : Problem s) (q : List (Term s)) (depth : Nat) :
    Option {rows // CheckedVariants.Reply (ruleRoot rs) q rows} := do
  if depth == 0 then none else
  if hb : CheckedReduction.rangeBound rs then
    if hv : rs.all (fun r => CheckedVariants.nonvar r.lhs) then
      let bound := (CheckedReduction.rangeBound_iff rs).mp hb
      let vars := CheckedVariants.varsNormal rs hv
      let query := fun i : Fin q.length => q[i.val]
      let narrow := TableNarrowing.narrower bound vars query
      let first := seed query
      let credits := 256 * (depth+1)
      let work := depth + rs.length + q.length
      let path := trace rs work first work
      let last ← path.getLast?
      let states := propose rs query narrow.branches work path [last] (credits - path.length) depth
      let result ← CheckedVariants.certify bound vars query (max work states.length)
        (first :: states) List.mem_cons_self
      return ⟨result.val,by simpa [query] using result.property⟩
    else none
  else none

end Tamarin.GeneralVariants
