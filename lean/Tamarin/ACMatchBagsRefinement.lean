import Tamarin.ACMatchBags
import Tamarin.ACMatchProfiles
import Tamarin.LinearACMatch

namespace Tamarin.Matching.ACBags
open OpenMatch.Profiles
variable {sig : Signature} {κ α : Type}

theorem of_matches [DecidableEq sig.ACSym] (f : sig.ACSym) (problem : Problem sig)
    (layout : Equation sig → List κ × List α) (name : κ → Variable) (term : α → Term sig)
    (fixed : Equation sig → List (Term sig)) (ground : ∀ e ∈ problem, ∀ t ∈ fixed e, t.Ground)
    (left : ∀ e ∈ problem, (fixed e ++ ((layout e).1.map name).map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    (right : ∀ e ∈ problem, (fixed e ++ (layout e).2.map term).Perm (ACRepresentation.flatten f e.rhs))
    (reflects : ∀ e ∈ problem, ∀ a ∈ (layout e).2, ∀ d ∈ problem, ∀ b ∈ (layout d).2,
      EquivB (term a) (term b) → a = b)
    (σ : Substitution sig) (matched : Matches problem σ) : Feasible (problem.map layout) := by
  classical
  let cls (a : α) := Cancellation.classOf (term a)
  let source := fun k => Cancellation.flatten f (σ.image (name k))
  let Live (a : α) := ∃ e ∈ problem, a ∈ (layout e).2
  let identify (c : Cancellation.Class sig) : List α :=
    if h : ∃ a, Live a ∧ cls a = c then [h.choose] else []
  have back (a : α) (ha : Live a) : identify (cls a) = [a] := by
    have exists_key : ∃ b, Live b ∧ cls b = cls a := ⟨a,ha,rfl⟩
    obtain ⟨e,he,hm⟩ := exists_key.choose_spec.1
    obtain ⟨d,hd,hn⟩ := ha
    have eq := reflects e he exists_key.choose hm d hd a hn (Quotient.exact exists_key.choose_spec.2)
    simp [identify,exists_key,eq]
  have source_eq (e : Equation sig) (he : e ∈ problem) :
      ((layout e).1.flatMap source).Perm ((layout e).2.map cls) := by
    have run := (LinearAC.remainder f e.lhs e.rhs (fixed e) _ _ (left e he) (right e he) (ground e he) σ).mp (matched e he)
    have perm := coordinate f ((layout e).1.map name) ((layout e).2.map term) (by
      rintro _ ht
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      exact OpenMatch.factor_of_mem_flatten f e.rhs _ ((right e he).subset (List.mem_append_right _ (List.mem_map.mpr ⟨a,ha,rfl⟩)))) σ run
    simpa [cls,source,List.map_map,List.flatMap_map,Function.comp_def] using perm
  let im (k : κ) := (source k).flatMap identify
  have transported (e : Equation sig) (he : e ∈ problem) : ((layout e).1.flatMap im).Perm (layout e).2 := by
    have perm := (source_eq e he).flatMap_right identify
    have ret (ids : List α) (present : ∀ a ∈ ids, Live a) : (ids.map cls).flatMap identify = ids := by
      induction ids with
      | nil => rfl
      | cons a tail ih =>
        simp [back a (present a List.mem_cons_self),ih (fun b hb => present b (List.mem_cons_of_mem _ hb))]
    rw [ret _ (fun a ha => ⟨e,he,ha⟩)] at perm
    simpa [List.flatMap_assoc,im] using perm
  refine ⟨im,?_,?_⟩
  · intro row hr k hk
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    obtain ⟨c,hc⟩ : ∃ c, c ∈ source k := by
      cases h : source k with
      | cons c cs => exact ⟨c,List.mem_cons_self⟩
      | nil =>
        have impossible := Cancellation.fold_flatten f (σ.image (name k))
        rw [show Cancellation.flatten f (σ.image (name k)) = [] from h] at impossible
        cases impossible
    have mem := (source_eq e he).subset (List.mem_flatMap.mpr ⟨k,hk,hc⟩)
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    have belongs : a ∈ im k := List.mem_flatMap.mpr ⟨cls a,hc,by simp [back a ⟨e,he,ha⟩]⟩
    intro empty
    simp [empty] at belongs
  · intro row hr
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact transported e he

/-- Realize a numeric solution by simultaneous substitution. Every occurrence
of a key uses the same decoded product, even in different equations. No
restriction on repetitions in either side or sharing among right-hand terms. -/
theorem to_matches [DecidableEq sig.ACSym] (f : sig.ACSym) (problem : Problem sig)
    (layout : Equation sig → List κ × List α) (name : κ → Variable) (term : α → Term sig)
    (fixed : Equation sig → List (Term sig)) (ground : ∀ e ∈ problem, ∀ t ∈ fixed e, t.Ground)
    (left : ∀ e ∈ problem, (fixed e ++ ((layout e).1.map name).map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    (right : ∀ e ∈ problem, (fixed e ++ (layout e).2.map term).Perm (ACRepresentation.flatten f e.rhs))
    (sorts : ∀ e ∈ problem, ∀ k ∈ (layout e).1, Subsort (sig.acSort f) (name k).sort)
    (subjects : ∀ e ∈ problem, HasSort e.rhs (sig.acSort f))
    (keys : ∀ e ∈ problem, ∀ k ∈ (layout e).1, ∀ d ∈ problem, ∀ j ∈ (layout d).1,
      name k = name j → k = j)
    (feasible : Feasible (problem.map layout)) : ∃ σ, Matches problem σ := by
  classical
  obtain ⟨im,pos,rows⟩ := feasible
  let used := problem.flatMap fun e => (layout e).1
  let row e (he : e ∈ problem) := rows _ (List.mem_map_of_mem (f := layout) he)
  let value k : Term sig := match im k with
    | [] => .var (name k)
    | a :: tail => ACRepresentation.fold f (term a) (tail.map term)
  have image k (hk : k ∈ used) :
      HasSort (value k) (name k).sort ∧
      Cancellation.flatten f (value k) = (im k).flatMap (fun a => Cancellation.flatten f (term a)) := by
    obtain ⟨e,he,mem⟩ := List.mem_flatMap.mp hk
    have sorted a (ha : a ∈ im k) : HasSort (term a) (sig.acSort f) :=
      ACRepresentation.flatten_hasSort f e.rhs (subjects e he) _
        ((right e he).subset (List.mem_append_right _ (List.mem_map_of_mem ((row e he).subset (List.mem_flatMap.mpr ⟨k,mem,ha⟩)))))
    cases eq : im k with
    | nil => exact False.elim (pos _ (List.mem_map_of_mem (f := layout) he) k mem eq)
    | cons a tail =>
      refine ⟨?_,?_⟩
      · simp only [value,eq]
        apply HasSort.widen _ (sorts e he k mem)
        apply ACRepresentation.fold_hasSort
        · exact sorted a (by simp [eq])
        · intro u hu
          obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hu
          exact sorted b (by simp [eq,hb])
      · simpa [value,eq,List.flatMap_map] using OpenMatch.subject_flat f (term a) (tail.map term)
  let domain := used.map name
  let rep (v) (h : v ∈ domain) := (List.mem_map.mp h).choose
  have entry v (h : v ∈ domain) : rep v h ∈ used ∧ name (rep v h) = v :=
    (List.mem_map.mp h).choose_spec
  let σ : Substitution sig := {
    image := fun v => if h : v ∈ domain then value (rep v h) else .var v
    support := domain
    outside := fun _ h => dite_eq_right h
    sorted := fun v => by
      split
      · next h =>
        have ht := (image _ (entry v h).1).1
        rwa [show (name (rep v h)).sort = v.sort from congrArg Variable.sort (entry v h).2] at ht
      · exact .var _ }
  have lookup k (hk : k ∈ used) : σ.image (name k) = value k := by
    have h : name k ∈ domain := List.mem_map_of_mem hk
    obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp (entry _ h).1
    obtain ⟨d,hd,hn⟩ := List.mem_flatMap.mp hk
    have eq := keys e he _ hm d hd k hn (entry _ h).2
    simp [σ,h,eq]
  refine ⟨σ,?_⟩
  intro e he
  apply (LinearAC.remainder f e.lhs e.rhs (fixed e) _ _ (left e he) (right e he) (ground e he) σ).2
  apply (OpenMatch.holds_iff ..).2
  let pieces := fun a => Cancellation.flatten f (term a)
  have expand : ((layout e).1.flatMap fun k => Cancellation.flatten f (σ.image (name k))) =
      ((layout e).1.flatMap im).flatMap pieces := by
    rw [List.flatMap_assoc]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro k hk
    have mem : k ∈ used := List.mem_flatMap.mpr ⟨e,he,hk⟩
    rw [lookup k mem]
    exact (image _ mem).2
  have perm := (row e he).flatMap_right pieces
  rw [← expand] at perm
  simpa [List.flatMap_map,Substitution.apply,Term.subst,pieces] using perm

/-- The reader only needs to identify the variables and structural classes
actually used by the query. Subject classes may contain caller variables. -/
structure Layout [DecidableEq sig.ACSym] (f : sig.ACSym) (problem : Problem sig)
    (row : Equation sig → List κ × List α) (name : κ → Variable) (term : α → Term sig)
    (fixed : Equation sig → List (Term sig)) : Prop where
  ground : ∀ e ∈ problem, ∀ t ∈ fixed e, t.Ground
  left : ∀ e ∈ problem, (fixed e ++ ((row e).1.map name).map Term.var).Perm (ACRepresentation.flatten f e.lhs)
  right : ∀ e ∈ problem, (fixed e ++ (row e).2.map term).Perm (ACRepresentation.flatten f e.rhs)
  keys : ∀ e ∈ problem, ∀ k ∈ (row e).1, ∀ d ∈ problem, ∀ j ∈ (row d).1, name k = name j → k = j
  factors : ∀ e ∈ problem, ∀ a ∈ (row e).2, ∀ d ∈ problem, ∀ b ∈ (row d).2,
    EquivB (term a) (term b) → a = b
  sorts : ∀ e ∈ problem, ∀ k ∈ (row e).1, Subsort (sig.acSort f) (name k).sort
  subjects : ∀ e ∈ problem, HasSort e.rhs (sig.acSort f)

/-- Sound and complete term-level interpretation of repeated and shared
ordinary AC captures across all rows, independent of search or packing order. -/
theorem Layout.exact [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → List κ × List α} {name term fixed} (layout : Layout f problem row name term fixed) :
    Feasible (problem.map row) ↔ ∃ σ, Matches problem σ :=
  ⟨to_matches f problem row name term fixed layout.ground layout.left layout.right layout.sorts layout.subjects layout.keys,
   fun ⟨σ,h⟩ => of_matches f problem row name term fixed layout.ground layout.left layout.right layout.factors σ h⟩

end Tamarin.Matching.ACBags
