import Tamarin.CheckedVariantOverlap
import Tamarin.CheckedReduction
import Tamarin.TableDecrease

/-! A finite closed frontier certifies an individual variants reply directly on
the actual rule table. Each terminal row is replayed against all ordinary
reduction paths from its own input images. No global confluence or finite
variant property is needed when these local checks succeed. -/
namespace Tamarin.CheckedVariants
open Rewriting MaudeOperations VariantJoin ReferenceVariantFrontier TupleNarrowingFrontier
variable {s : Signature} {n : Nat} {rs : List (Equation s)}
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def tracked (keys : List Variable) (p : Point s n) : Bool :=
  let vars := keys.flatMap fun v => (p.assignment.image v).variables
  (List.ofFn p.value).all fun t => t.variables.all vars.contains

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
private theorem tracks {keys : List Variable} {p : Point s n} (h : tracked keys p) :
    TableNarrowing.Tracked keys p := by
  intro i w occ
  have live := List.all_eq_true.mp (List.all_eq_true.mp h (p.value i) (List.mem_ofFn.mpr ⟨i,rfl⟩)) w
    ((Term.mem_variables ..).mpr occ)
  obtain ⟨v,hv,hw⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp live)
  exact ⟨⟨v,hv⟩,(Term.mem_variables ..).mp hw⟩

private def reduce (rs : List (Equation s)) (fuel : Nat) (t : Term s) : Option (Term s) :=
  let depth := (TableDecrease.budget rs t).getD fuel
  if CheckedReduction.affordable rs depth 100000 t then CheckedReduction.run rs depth t else none

private theorem reduce_correct (bound : ReferenceReduction.Bound rs) (fuel : Nat) {t u}
    (ok : reduce rs fuel t = some u) : ReductionReply (ruleRoot rs) t u := by
  simp only [reduce] at ok
  split at ok
  · exact CheckedReduction.correct bound ok
  · contradiction

private def replay (rs : List (Equation s)) (fuel : Nat) (t v : Term s) : Bool :=
  match reduce rs fuel t with
  | some u => ReferenceMatching.equal u v
  | none => false

private theorem replay_correct (bound : ReferenceReduction.Bound rs) (fuel : Nat) (t v : Term s)
    (yes : replay rs fuel t v) : ReductionReply (ruleRoot rs) t v := by
  unfold replay at yes
  split at yes
  next u ran =>
    have reply := reduce_correct bound fuel ran
    have eq := (ReferenceMatching.equal_iff ..).mp yes
    refine ⟨⟨reply.normalForm.1.trans (.basis eq),(normal_equiv _ eq).mp reply.normalForm.2.1,
      fun k kt => Term.checkSort_sound _ _
        ((SortClash.check_equiv eq k) ▸ Term.checkSort_complete (reply.normalForm.2.2 k kt))⟩,
      fun w hw => (reply.unique w hw).trans eq⟩
  next => contradiction

private def replays (rs : List (Equation s)) (fuel : Nat) (query : Fin n → Term s) (p : Point s n) :=
  (List.finRange n).all fun i => replay rs fuel (p.assignment.apply (query i)) (p.value i)

private theorem row_correct (bound : ReferenceReduction.Bound rs)
    (vars : Normalized (ruleRoot rs) Substitution.identity) (fuel : Nat) (query : Fin n → Term s)
    (p : Point s n) (term : terminal rs (keysOf query) p) (ok : replays rs fuel query p) :
    let a := p.answer (keysOf query)
    a.Sound (ruleRoot rs) (List.ofFn query) ∧ a.Safe (List.ofFn query) [] ∧
      a.Reconstructible (ruleRoot rs) (List.ofFn query) := by
  let keys := keysOf query
  let a := p.answer keys
  have same (i : Fin n) : a.subst.apply (query i) = p.assignment.apply (query i) := by
    apply Term.subst_eq_of_agree
    intro v hv
    exact (p.row keys).project_key (fun j => p.assignment.sorted j.val)
      ⟨v,(observed query v).mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩⟩
  have per (i : Fin n) : ReductionReply (ruleRoot rs) (a.subst.apply (query i)) (p.value i) := by
    rw [same]
    exact replay_correct bound fuel _ _ (List.all_eq_true.mp ok i (List.mem_finRange _))
  have sound : a.Sound (ruleRoot rs) (List.ofFn query) :=
    ⟨(p.row keys).project_normal (fun j => p.assignment.sorted j.val) vars ((terminal_iff bound keys p).mp term),
     alignedFn query p.value (fun i => (per i).normalForm)⟩
  refine ⟨sound,⟨fun v hv => a.subst.outside v (fun h => hv ((observed query v).mp h)),
    by simp,by simp⟩,Variant.reconstructible_of_unique sound ?_⟩
  rintro t ht u v hu hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
  exact ((per i).unique u hu).trans ((per i).unique v hv).symm

private def next (bound : ReferenceReduction.Bound rs) (vars : Normalized (ruleRoot rs) Substitution.identity)
    (keys : List Variable) (p : Point s n) : List (Point s n) :=
  let u := MixedUnification.verified (s := s)
  expand p (TableNarrowing.atPoint u bound (TableNarrowing.groups u bound vars) keys p).branches

private theorem successors (bound : ReferenceReduction.Bound rs)
    (vars : Normalized (ruleRoot rs) Substitution.identity) (keys : List Variable) (p : Point s n)
    (hp : tracked keys p) : Successors rs (p.row keys) ((next bound vars keys p).map (Point.row · keys)) := by
  let u := MixedUnification.verified (s := s)
  exact expand_covers keys p _ ((TableNarrowing.atPoint u bound (TableNarrowing.groups u bound vars)
    keys p).covers (tracks hp))

def certify (bound : ReferenceReduction.Bound rs) (vars : Normalized (ruleRoot rs) Substitution.identity)
    (query : Fin n → Term s) (fuel : Nat) (states : List (Point s n)) (seeded : seed query ∈ states) :
    Option {answers // Reply (ruleRoot rs) (List.ofFn query) answers} := by
  let keys := keysOf query
  let kept := states.filter (terminal rs keys)
  let rows := kept.map (Point.answer · keys)
  if !states.all (fun p => FrontierWork.admits rs ((keys.map p.assignment.image) ++ List.ofFn p.value) (fuel+1)) then
    exact none
  else if tracks : states.all (tracked keys) then
    if closed : accounted rs keys states (next bound vars keys) then
      if nonempty : !rows.isEmpty then
        if replayed : kept.all (replays rs fuel query) then
          have row (p) (hp : p ∈ kept) := row_correct bound vars fuel query p
            (List.mem_filter.mp hp).2 (List.all_eq_true.mp replayed p hp)
          if agree : compatible rs fuel keys kept then
            have family : CompleteVariants (ruleRoot rs) (List.ofFn query) rows :=
              ⟨fun a ha => by obtain ⟨p,h,rfl⟩ := List.mem_map.mp ha; exact (row p h).1,
               covered bound vars query states seeded _ (fun p hp => successors bound vars keys p
                 (List.all_eq_true.mp tracks p hp)) closed⟩
            exact some ⟨rows,⟨⟨family,by simpa using nonempty,
              fun a ha => by obtain ⟨p,h,rfl⟩ := List.mem_map.mp ha; exact (row p h).2.1,
              fun a ha => by obtain ⟨p,h,rfl⟩ := List.mem_map.mp ha; exact (row p h).2.2⟩,
              unique_of_checked bound vars query fuel kept family agree⟩⟩
          else exact none
        else exact none
      else exact none
    else exact none
  else exact none

/-- Charge every expanded tuple coordinate against every rule, including
a second expansion when validating closure. This bounds the number and size
of positional requests independently of how many breadth-first layers fit. -/
private def charge (tableSize : Nat) (states : List (Point s n)) (keys : List Variable) : Nat :=
  (states.map fun p =>
    let images := (keys.map fun v => FiniteOccurs.nodes (p.assignment.image v)).sum
    let values := ((List.ofFn p.value).map FiniteOccurs.nodes).sum
    (1 + tableSize) * (1 + values + images)).sum

private def search (bound : ReferenceReduction.Bound rs) (vars : Normalized (ruleRoot rs) Substitution.identity)
    (query : Fin n → Term s) (fuel tableSize credits : Nat) (states frontier : List (Point s n))
    (seeded : seed query ∈ states) :
    Nat → Option {answers // Reply (ruleRoot rs) (List.ofFn query) answers}
  | 0 =>
    if charge tableSize states (keysOf query) ≤ credits then certify bound vars query fuel states seeded
    else none
  | depth+1 =>
    let keys := keysOf query
    let cost := charge tableSize frontier keys
    if cost > credits || !frontier.all (fun p =>
      FrontierWork.admits rs ((keys.map p.assignment.image) ++ List.ofFn p.value) (fuel+1)) then none else
    let children := frontier.flatMap (next bound vars keys)
    let remaining := credits - cost
    if children.length > remaining then none else
    let subsumes := fun (a b : Point s n) =>
      ReferenceVariantFolding.subsumes keys.attach (List.finRange n) (a.row keys) (b.row keys)
    -- Fold the new layer before expanding it. Closure is certified against
    -- every unpruned successor, including redundant sort refinements.
    let fresh := children.foldl (init := []) fun kept child =>
      if states.any (subsumes · child) || kept.any (subsumes · child) then kept
      else child :: kept.filter (fun p => !subsumes child p)
    let remaining := remaining - children.length
    if fresh.isEmpty then
      if charge tableSize states keys ≤ remaining then certify bound vars query fuel states seeded
      else none
    else search bound vars query fuel tableSize remaining (fresh ++ states) fresh (List.mem_append_right _ seeded) depth

def nonvar (t : Term s) := match t with
  | .var _ => false
  | _ => true

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom] in
theorem varsNormal (rs : List (Equation s)) (h : rs.all (fun r => nonvar r.lhs)) :
    Normalized (ruleRoot rs) Substitution.identity := by
  intro v rhs ⟨l,r,pre,fire,_⟩
  change EquivB (.var v) l at pre
  cases l <;> cases pre.head_eq
  cases fire with
  | root hroot =>
    obtain ⟨e,he,σ,same,_⟩ := hroot
    have good := List.all_eq_true.mp h e he
    cases hl : e.lhs <;> simp [nonvar,hl,Substitution.apply,Term.subst] at good same

/-- Return a certified family or decline the whole query. The bounds control
the search for a certificate and the local reduction check, respectively. -/
def solve (rules : List (Equation s)) (query : List (Term s)) (depth fuel : Nat) :
    Option {answers // Reply (ruleRoot rules) query answers} :=
  if hb : CheckedReduction.rangeBound rules then
    if hv : rules.all (fun r => nonvar r.lhs) then
      -- A successful reconstruction needs an unambiguous replay. Check
      -- the input tuple before invoking potentially branching narrowing.
      if !query.all (fun t => (reduce rules fuel t).isSome) then none else
      let tableSize := (rules.map fun r => FiniteOccurs.nodes r.lhs + FiniteOccurs.nodes r.rhs).sum
      let out := search ((CheckedReduction.rangeBound_iff rules).mp hb) (varsNormal rules hv)
        (fun i : Fin query.length => query[i]) fuel tableSize (256 * (fuel + 1)) [seed (fun i : Fin query.length => query[i])]
        [seed (fun i : Fin query.length => query[i])] List.mem_cons_self depth
      out.map fun a => ⟨a.val,by simpa using a.property⟩
    else none
  else none

end Tamarin.CheckedVariants
