import Tamarin.ACMatchAnswerPacket

namespace Tamarin.Matching.ACBags
variable {sig : Signature} {κ α : Type} [DecidableEq sig.ACSym]
    {f : sig.ACSym} {problem : Problem sig} {row : Equation sig → List κ × List α}
    {name : κ → Variable} {term : α → Term sig} {fixed : Equation sig → List (Term sig)}

/-- Principal sorts are checked independently for each concrete image.
A nonempty singleton keeps the sort of its frozen term, while larger bags
have the operator's result sort. -/
def Fits (f : sig.ACSym) (rows : List (List κ × List α)) (name : κ → Variable)
    (term : α → Term sig) (im : κ → List α) : Prop :=
  ∀ r ∈ rows, ∀ k ∈ r.1, ∀ a tail, im k = a :: tail →
    Subsort (ACRepresentation.fold f (term a) (tail.map term)).rootSort (name k).sort

omit [DecidableEq sig.ACSym] in
private theorem principal {t : Term sig} {s : SortId} (h : HasSort t s) : HasSort t t.rootSort := by
  induction h with
  | widen _ _ ih => exact ih
  | var v => exact .var v
  | atom a => exact .atom a
  | free f args h _ => exact .free f args h
  | comm f x y hx hy _ _ => exact .comm f x y hx hy
  | ac f x y hx hy _ _ => exact .ac f x y hx hy

private theorem folded (p : Presentation f problem row name term fixed)
    {im : κ → List α} (good : Solution (problem.map row) im)
    {e} (he : e ∈ problem) {k} (hk : k ∈ (row e).1) {a tail} (h : im k = a :: tail) :
    Cancellation.flatten f (ACRepresentation.fold f (term a) (tail.map term)) =
      ((im k).map fun b => Cancellation.classOf (term b)) := by
  have atomic b (hb : b ∈ im k) := OpenMatch.factor_of_mem_flatten f e.rhs (term b)
    ((p.right e he).subset (List.mem_append_right _ (List.mem_map_of_mem
      ((good.2 _ (List.mem_map_of_mem (f := row) he)).subset (List.mem_flatMap.mpr ⟨k,hk,hb⟩)))))
  rw [OpenMatch.subject_flat, h]
  change ((a :: tail).map term).flatMap (Cancellation.flatten f) = _
  rw [List.flatMap_map,List.map_eq_flatMap]
  exact congrArg List.flatten (List.map_congr_left fun b hb => atomic b (h ▸ hb))

theorem Presentation.fold_sorted (p : Presentation f problem row name term fixed)
    {im : κ → List α} (good : Solution (problem.map row) im)
    {e} (he : e ∈ problem) {k} (hk : k ∈ (row e).1) {a tail} (h : im k = a :: tail) :
    HasSort (ACRepresentation.fold f (term a) (tail.map term)) (sig.acSort f) := by
  have mem := List.mem_map_of_mem (f := row) he
  have sorted b (hb : b ∈ im k) := ACRepresentation.flatten_hasSort f e.rhs (p.subjects e he) (term b)
    ((p.right e he).subset (List.mem_append_right _ (List.mem_map_of_mem
      ((good.2 _ mem).subset (List.mem_flatMap.mpr ⟨k,hk,hb⟩)))))
  apply ACRepresentation.fold_hasSort
  · exact sorted a (by simp [h])
  · intro u hu
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hu
    exact sorted b (by simp [h,hb])

private theorem realizes (p : Presentation f problem row name term fixed)
    {im : κ → List α} (good : Solution (problem.map row) im)
    (fits : Fits f (problem.map row) name term im) :
    ∃ σ, Matches problem σ ∧ Scoped problem (fun _ => True) σ ∧
      Represents f (problem.map row) name term σ im := by
  apply to_matches_of_typed f problem row name term fixed p.ground p.left p.right p.keys im good
  intro e he k hk a tail h
  have mem := List.mem_map_of_mem (f := row) he
  exact (principal (p.fold_sorted good he hk h)).widen (fits _ mem k hk a tail h)

private theorem fits_of_agrees (p : Presentation f problem row name term fixed)
    {σ : Substitution sig} {im arm : κ → List α} (ok : Solution (problem.map row) arm)
    (rep : Represents f (problem.map row) name term σ im)
    (same : ∀ r ∈ problem.map row, ∀ k ∈ r.1, (im k).Perm (arm k)) :
    Fits f (problem.map row) name term arm := by
  intro r hr k hk b tail h
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
  have flat := (rep _ (List.mem_map_of_mem he) k hk).trans
    ((same _ (List.mem_map_of_mem he) k hk).map (fun u => Cancellation.classOf (term u)))
  rw [← folded p ok he hk h] at flat
  exact Term.rootSort_equiv (Cancellation.equiv_of_flatten_perm f flat) ▸ Term.rootSort_le (σ.sorted _)

theorem Presentation.sorted_exact (p : Presentation f problem row name term fixed) :
    (∃ im, Solution (problem.map row) im ∧ Fits f (problem.map row) name term im) ↔
      ∃ σ, Matches problem σ := by
  constructor
  · rintro ⟨im,good,typed⟩
    exact (realizes p good typed).imp (fun _ h => h.1)
  · rintro ⟨σ,ok⟩
    obtain ⟨im,good,rep⟩ := of_matches f problem row name term fixed p.ground p.left p.right p.factors σ ok
    exact ⟨im,good,fits_of_agrees p good rep (fun _ _ _ _ => .refl _)⟩

/-- Filtering the complete numerical family on the principal sort of every
returned image gives the exact simultaneous sorted matcher family. In
particular an empty filtered family is a definitive negative answer. -/
theorem Presentation.sorted_complete (p : Presentation f problem row name term fixed)
    {ι : Type} (raw accepted : List ι) (source : ι → κ → List α) (out : ι → Substitution sig)
    (numeric : Complete (problem.map row) (raw.map source))
    (retain : ∀ a, a ∈ accepted ↔ a ∈ raw ∧ Fits f (problem.map row) name term (source a))
    (reads : ∀ a ∈ accepted, Scoped problem (fun _ => True) (out a) ∧
      Represents f (problem.map row) name term (out a) (source a)) :
    Matching.Complete problem (fun _ => True) (accepted.map out) where
  sound σ hs := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    obtain ⟨mem,typed⟩ := (retain a).1 ha
    obtain ⟨τ,ok,_,rep⟩ := realizes p (numeric.sound _ (List.mem_map_of_mem mem)) typed
    exact ⟨matches_of_agrees ok (p.agrees (reads a ha).2 rep (fun _ _ _ _ => .refl _)),(reads a ha).1⟩
  covers ρ hm _ := by
    obtain ⟨im,good,rep⟩ := of_matches f problem row name term fixed p.ground p.left p.right p.factors ρ hm
    obtain ⟨arm,mem,same⟩ := numeric.covers im good
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    have ok := numeric.sound _ (List.mem_map_of_mem ha)
    have keep := (retain a).2 ⟨ha,fits_of_agrees p ok rep same⟩
    exact ⟨out a,List.mem_map_of_mem keep,p.agrees rep (reads a keep).2 same⟩

end Tamarin.Matching.ACBags

namespace Tamarin.Matching.ACMatchPacket

theorem FamilyCorrect.sorted_term {floor run} (ok : FamilyCorrect floor run)
    {sig : Signature} [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → Row} {name term fixed} (p : ACBags.Presentation f problem row name term fixed)
    {packet rows arms} (read : decode packet.toList = some rows) (order : rows.Perm (problem.map row))
    (done : run packet = some arms) (accepted : List (List (List UInt64))) (out : List (List UInt64) → Substitution sig)
    (retain : ∀ a, a ∈ accepted ↔ a ∈ unpack arms ∧ ACBags.Fits f (problem.map row) name term (readArm rows a))
    (scope : ∀ a ∈ accepted, Scoped problem (fun _ => True) (out a))
    (images : ∀ arm ∈ accepted, ∀ e ∈ problem, ∀ k ∈ (row e).1, ∀ a tail,
      readArm rows arm k = a :: tail →
      EquivB ((out arm).image (name k)) (ACRepresentation.fold f (term a) (tail.map term))) :
    Matching.Complete problem (fun _ => True) (accepted.map out) := by
  have complete := ACBags.complete_perm order (ok.exact _ _ _ read done).1
  exact p.sorted_complete _ _ _ _ complete retain (fun a ha => ⟨scope a ha,
    p.represents_fold (complete.sound _ (List.mem_map_of_mem ((retain a).1 ha).1)) (images a ha)⟩)

end Tamarin.Matching.ACMatchPacket
