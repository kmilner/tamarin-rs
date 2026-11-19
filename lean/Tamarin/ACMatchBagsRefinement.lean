import Tamarin.ACMatchBags
import Tamarin.ACMatchProfiles
import Tamarin.LinearACMatch

namespace Tamarin.Matching.ACBags
open OpenMatch.Profiles
variable {sig : Signature} {κ α : Type}

/-- The decoded substitution contains exactly these rigid factors in each
captured image, up to permutations and B-equivalence inside a factor. -/
def Represents (f : sig.ACSym) (rows : List (List κ × List α)) (name : κ → Variable)
    (term : α → Term sig) (σ : Substitution sig) (im : κ → List α) : Prop :=
  ∀ r ∈ rows, ∀ k ∈ r.1, (Cancellation.flatten f (σ.image (name k))).Perm
    ((im k).map (fun a => Cancellation.classOf (term a)))

theorem of_matches [DecidableEq sig.ACSym] (f : sig.ACSym) (problem : Problem sig)
    (layout : Equation sig → List κ × List α) (name : κ → Variable) (term : α → Term sig)
    (fixed : Equation sig → List (Term sig)) (ground : ∀ e ∈ problem, ∀ t ∈ fixed e, t.Ground)
    (left : ∀ e ∈ problem, (fixed e ++ ((layout e).1.map name).map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    (right : ∀ e ∈ problem, (fixed e ++ (layout e).2.map term).Perm (ACRepresentation.flatten f e.rhs))
    (reflects : ∀ e ∈ problem, ∀ a ∈ (layout e).2, ∀ d ∈ problem, ∀ b ∈ (layout d).2,
      EquivB (term a) (term b) → a = b)
    (σ : Substitution sig) (matched : Matches problem σ) :
    ∃ im, Solution (problem.map layout) im ∧ Represents f (problem.map layout) name term σ im := by
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
  refine ⟨im,⟨?_,?_⟩,?_⟩
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

  · intro row hr k hk
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    have origin c (hc : c ∈ source k) : ∃ a, Live a ∧ cls a = c := by
      obtain ⟨a,ha,eq⟩ := List.mem_map.mp ((source_eq e he).subset (List.mem_flatMap.mpr ⟨k,hk,hc⟩))
      exact ⟨a,⟨e,he,ha⟩,eq⟩
    have inverse (xs : List (Cancellation.Class sig)) (live : ∀ c ∈ xs, ∃ a, Live a ∧ cls a = c) :
        ((xs.flatMap identify).map cls) = xs := by
      induction xs with
      | nil => rfl
      | cons c cs ih =>
        obtain ⟨a,ha,rfl⟩ := live c List.mem_cons_self
        simp [back a ha,ih (fun u hu => live u (List.mem_cons_of_mem _ hu))]
    exact List.Perm.of_eq (inverse _ origin).symm

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
    (im : κ → List α) (solution : Solution (problem.map layout) im) :
    ∃ σ, Matches problem σ ∧ Scoped problem (fun _ => True) σ ∧
      Represents f (problem.map layout) name term σ im := by
  classical
  obtain ⟨pos,rows⟩ := solution
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
  refine ⟨σ,?_,?_,?_⟩
  · intro e he
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
  · intro v outside
    have absent : v ∉ domain := by
      intro h
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
      obtain ⟨e,he,mem⟩ := List.mem_flatMap.mp hk
      apply outside
      refine ⟨⟨e,he,(OpenMatch.occurs_flatten f _ e.lhs).1 ?_⟩,trivial⟩
      exact ⟨_,(left e he).subset (List.mem_append_right _ (List.mem_map_of_mem
        (f := Term.var) (List.mem_map_of_mem (f := name) mem))),rfl⟩
    simp [σ,absent]
  · intro r hr k hk
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    have mem : k ∈ used := List.mem_flatMap.mpr ⟨e,he,hk⟩
    rw [lookup k mem,(image _ mem).2]
    have atomic a (ha : a ∈ im k) := OpenMatch.factor_of_mem_flatten f e.rhs _
      ((right e he).subset (List.mem_append_right _ (List.mem_map_of_mem ((row e he).subset
        (List.mem_flatMap.mpr ⟨k,hk,ha⟩)))))
    apply List.Perm.of_eq
    rw [List.map_eq_flatMap]
    apply congrArg List.flatten
    exact List.map_congr_left atomic

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
  ⟨fun ⟨im,sol⟩ => (to_matches f problem row name term fixed layout.ground layout.left layout.right
      layout.sorts layout.subjects layout.keys im sol).imp (fun _ h => h.1),
   fun ⟨σ,h⟩ => (of_matches f problem row name term fixed layout.ground layout.left layout.right
      layout.factors σ h).imp (fun _ result => result.1)⟩

/-- Reconstructing each variable image by folding its returned factor IDs is
sufficient, including a caller that canonically reorders those terms. -/
theorem Layout.represents_fold [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → List κ × List α} {name term fixed} (layout : Layout f problem row name term fixed)
    {out : Substitution sig} {im : κ → List α} (sol : Solution (problem.map row) im)
    (read : ∀ e ∈ problem, ∀ k ∈ (row e).1, ∀ a tail, im k = a :: tail →
      EquivB (out.image (name k)) (ACRepresentation.fold f (term a) (tail.map term))) :
    Represents f (problem.map row) name term out im := by
  rintro r hr k hk
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  have mem := List.mem_map_of_mem (f := row) he
  have atomic t (ht : t ∈ im k) := OpenMatch.factor_of_mem_flatten f e.rhs (term t)
    ((layout.right e he).subset (List.mem_append_right _ (List.mem_map_of_mem
      ((sol.2 _ mem).subset (List.mem_flatMap.mpr ⟨k,hk,ht⟩)))))
  cases h : im k with
  | nil => exact False.elim (sol.1 _ mem k hk h)
  | cons a tail =>
    have pieces := Cancellation.flatten_equiv f (read e he k hk a tail h)
    rw [OpenMatch.subject_flat] at pieces
    apply pieces.trans
    apply List.Perm.of_eq
    change (((a :: tail).map term).flatMap (Cancellation.flatten f)) = _
    rw [List.flatMap_map,List.map_eq_flatMap]
    apply congrArg List.flatten
    exact List.map_congr_left (fun t ht => atomic t (h ▸ ht))

private theorem Layout.agrees [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → List κ × List α} {name term fixed} (layout : Layout f problem row name term fixed)
    {σ τ : Substitution sig} {im arm : κ → List α}
    (src : Represents f (problem.map row) name term σ im) (dst : Represents f (problem.map row) name term τ arm)
    (same : ∀ r ∈ problem.map row, ∀ k ∈ r.1, (im k).Perm (arm k)) :
    Substitution.AgreesOn (Observed problem) σ τ := by
  rintro v ⟨e,he,hv⟩
  obtain ⟨t,ht,occ⟩ := (OpenMatch.occurs_flatten f v e.lhs).2 hv
  rcases List.mem_append.mp ((layout.left e he).symm.subset ht) with h | h
  · exact False.elim (layout.ground e he t h v occ)
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hw
    change v = name k at occ
    subst v
    have mem := List.mem_map_of_mem (f := row) he
    exact Cancellation.equiv_of_flatten_perm f ((src _ mem k hk).trans
      (((same _ mem k hk).map _).trans (dst _ mem k hk).symm))

/-- Reading the bags from each returned arm gives every simultaneous matcher
modulo B, with identity on variables outside the caller's patterns. -/
theorem Layout.complete [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → List κ × List α} {name term fixed} (layout : Layout f problem row name term fixed)
    {ι : Type} (arms : List ι) (source : ι → κ → List α) (out : ι → Substitution sig)
    (numeric : Complete (problem.map row) (arms.map source))
    (reads : ∀ a ∈ arms, Scoped problem (fun _ => True) (out a) ∧
      Represents f (problem.map row) name term (out a) (source a)) :
    Matching.Complete problem (fun _ => True) (arms.map out) where
  sound σ hs := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    obtain ⟨τ,good,_,rep⟩ := to_matches f problem row name term fixed layout.ground layout.left
      layout.right layout.sorts layout.subjects layout.keys (source a)
      (numeric.sound _ (List.mem_map_of_mem ha))
    exact ⟨matches_of_agrees good (layout.agrees (reads a ha).2 rep (fun _ _ _ _ => .refl _)),(reads a ha).1⟩
  covers ρ fits _ := by
    obtain ⟨im,good,rep⟩ := of_matches f problem row name term fixed layout.ground layout.left
      layout.right layout.factors ρ fits
    obtain ⟨arm,hm,same⟩ := numeric.covers im good
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact ⟨out a,List.mem_map_of_mem ha,layout.agrees rep (reads a ha).2 same⟩

/-- Every valid numeric family can be decoded into sorted substitutions.
No assumption about the existence of a successful caller-side decoder is needed. -/
theorem Layout.realizable [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → List κ × List α} {name term fixed} (layout : Layout f problem row name term fixed)
    {ι : Type} (arms : List ι) (source : ι → κ → List α)
    (numeric : Complete (problem.map row) (arms.map source)) :
    ∃ out : ι → Substitution sig, Matching.Complete problem (fun _ => True) (arms.map out) ∧
      ∀ a ∈ arms, Represents f (problem.map row) name term (out a) (source a) := by
  classical
  have build a (ha : a ∈ arms) := to_matches f problem row name term fixed layout.ground layout.left
    layout.right layout.sorts layout.subjects layout.keys (source a) (numeric.sound _ (List.mem_map_of_mem ha))
  let out (a : ι) := if ha : a ∈ arms then (build a ha).choose else Substitution.identity
  have reads a (ha : a ∈ arms) : Scoped problem (fun _ => True) (out a) ∧
      Represents f (problem.map row) name term (out a) (source a) := by
    simpa only [out,dite_eq_left ha] using (build a ha).choose_spec.2
  exact ⟨out,layout.complete _ _ _ numeric reads,fun a h => (reads a h).2⟩

end Tamarin.Matching.ACBags
