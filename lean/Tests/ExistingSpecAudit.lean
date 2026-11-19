import Tamarin

namespace Tamarin.ExistingSpecAudit
open Pairing (signature PTerm PSubst)
open Rewriting

private abbrev msg (id : Nat) : Variable := ⟨id, .msg⟩
private abbrev x := msg 0
private abbrev y := msg 1
private abbrev u := msg 2
private abbrev v := msg 3
private abbrev w := msg 4
private def offset (n : Variable) : PTerm := .comm 7 (.var n) (.atom (8, .pub))
private def query : Problem signature :=
  [⟨.ac 0 (.var x) (offset u), .ac 0 (.var y) (offset v)⟩]

-- All four variables can consistently name the same still-open message.
private def collapse : PSubst where
  image n := if n ∈ [x,y,u,v] then .var w else .var n
  support := [x,y,u,v]
  outside := by intro n hn; simp [hn]
  sorted := by
    intro n
    split
    · next h =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> exact .var w
    · exact .var n

-- Syntactically different, same-head offsets may coalesce under a later
-- substitution. Neither the swapped nor the positive shared-residual branch
-- can cover this solution. This is why CompoundOffset.Query.distinct
-- quantifies over substitutions.
example : offset u ≠ offset v ∧ query.Solves collapse ∧
    ¬ (EquivB (collapse.image x) (collapse.apply (offset v)) ∨
       ∃ r, EquivB (collapse.image x) (.ac 0 r (collapse.apply (offset v)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have bad := Term.comm.inj e
    have : u = v := Term.var.inj bad.2.1
    contradiction
  · intro e he
    obtain rfl := List.mem_singleton.mp he
    exact .refl _
  · rintro (h | ⟨r,h⟩) <;> cases h.head_eq

-- The input exposes the same AC match through two different syntactic
-- subsequences. The fixed flat-matching packet requires *both* encodings.
-- A solver returning just one could still satisfy directional matching.
example (backend : FlatMatchBackend) (correct : backend.Correct) :
    [[1,2],[1]] ∈ backend.run 2 [0,1] [] [1,2,1] ∧
    [[2,1],[1]] ∈ backend.run 2 [0,1] [] [1,2,1] := by
  constructor <;> apply (correct ..).mpr <;> decide

example {sig : Signature} (f : sig.ACSym) (a b : sig.Atom) :
    EquivB (FlatAC.term f [a,b]) (FlatAC.term f [b,a]) := .ac_swap _ _ _


-- The generic rule relation accepts rules with extra RHS variables. A
-- variant's mathematical output can then introduce a variable independently
-- of every input and substitution range. Exercise the value-side scope
-- obligation before generalizing the current range-restricted rule schemas.
private def start : PTerm := .free (.other 90 0) Fin.elim0
private def extraRules : List (Equation signature) := [⟨start, .var w⟩]
private def valueOnly : Variant signature := ⟨Substitution.identity, [.var w]⟩

private theorem varsNormal : Normalized (ruleRoot extraRules) Substitution.identity := by
  apply (ConstructorVariants.constructor_normal extraRules ?_).1
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  trivial

private theorem noObserved (n : Variable) : ¬ Observed [start] n := by
  rintro ⟨_,hm,ht⟩
  obtain rfl := List.mem_singleton.mp hm
  obtain ⟨i,_⟩ := ht
  exact Fin.elim0 i

private theorem startSorted : HasSort start .msg := .free _ _ fun i => Fin.elim0 i

example : CompleteVariants (ruleRoot extraRules) [start] [valueOnly] ∧
    valueOnly.Safe [start] [] ∧
    (∀ n, ¬ Observed [start] n → valueOnly.subst.image n = .var n) ∧
    (∀ n, Observed [start] n → ∀ a, (valueOnly.subst.image n).Occurs a → Observed [start] a ∨ a ∉ [w]) ∧
    ¬ valueOnly.Safe [start] [w] := by
  have domain : ∀ n, ¬ Observed [start] n → valueOnly.subst.image n = .var n := fun _ _ => rfl
  have ranges (avoid : List Variable) : ∀ n, Observed [start] n → ∀ a,
      (valueOnly.subst.image n).Occurs a → Observed [start] a ∨ a ∉ avoid :=
    fun n hn => False.elim (noObserved n hn)
  refine ⟨⟨?_, ?_⟩, ⟨domain, ranges [], fun _ _ _ _ => Or.inr List.not_mem_nil⟩,
    domain, ranges [w], fun unsafeValue => ?_⟩
  · intro a ha
    obtain rfl := List.mem_singleton.mp ha
    refine ⟨varsNormal, ⟨⟨?_, varsNormal w, ?_⟩, trivial⟩⟩
    · rw [show valueOnly.subst.apply start = start from Substitution.apply_identity start]
      exact .step ⟨_, _, .refl _, .root ⟨_, List.mem_singleton_self _, Substitution.identity,
        (Substitution.apply_identity _).symm, rfl⟩, .refl _⟩
    · intro s hs
      exact .widen (.var w) (Term.rootSort_le hs)
  · intro ρ _ values hv
    cases values with
    | nil => contradiction
    | cons t ts =>
      cases ts with
      | cons => exact False.elim hv.2
      | nil =>
        have hn : Normal (ruleRoot extraRules) t := hv.1.2.1
        have hsort : HasSort t w.sort := hv.1.2.2 _ (startSorted.subst ρ.image ρ.sorted)
        let δ := Substitution.binding w t hsort
        have hnorm : Normalized (ruleRoot extraRules) δ := by
          intro n
          by_cases he : n = w
          · subst n
            simpa [δ] using hn
          · rw [show δ.image n = .var n from Substitution.binding_image_other _ _ _ _ he]
            exact varsNormal n
        refine ⟨valueOnly, List.mem_singleton_self _, δ, hnorm, fun n hn => False.elim (noObserved n hn), ?_⟩
        change EquivB t (δ.image w) ∧ True
        simp only [δ, Substitution.binding_image_self]
        exact ⟨.refl _, trivial⟩
  · have captured := unsafeValue.values (.var w) (List.mem_singleton_self _) w rfl
    exact captured.elim (noObserved w) (fun h => h (List.mem_singleton_self _))

/-- Reorder only atom words of a success packet. Status codes retain their
positions, including for unsupported inputs and complete failures. -/
private def reversePayload (packet : Array UInt64) : Array UInt64 :=
  match packet.toList with
  | 2 :: rest => (2 :: rest.reverse).toArray
  | _ => packet

@[simp] private theorem reverse_two (rest : List UInt64) :
    reversePayload (2 :: rest).toArray = (2 :: rest.reverse).toArray := by
  simp [reversePayload]

private theorem reverse_twice (packet : Array UInt64) : reversePayload (reversePayload packet) = packet := by
  cases packet with
  | mk words =>
    cases words with
    | nil => rfl
    | cons k rest =>
      by_cases hk : k = 2
      · subst k; simp [reversePayload]
      · simp [reversePayload, hk]

private def reverseBackend (b : FlatACBackend) : FlatACBackend where
  equal := b.equal
  residual := fun s t => reversePayload (b.residual s t)

-- Acceptance checks against the entire fixed contract, including complete
-- failures, sort checks, arbitrary atom decoders and nonground solutions.
private theorem reverse_correct (b : FlatACBackend) (hc : b.Correct) : (reverseBackend b).Correct where
  equal_status := hc.equal_status
  equal_correct := hc.equal_correct
  equal_completes := hc.equal_completes
  equal_words := hc.equal_words
  empty_inputs := by
    intro s t h
    obtain ⟨eq, hr⟩ := hc.empty_inputs s t h
    exact ⟨eq, show reversePayload (b.residual s t) = #[0] by rw [hr]; rfl⟩
  residual_admits := by
    intro s t excess hs hx hp
    obtain ⟨r, h⟩ := hc.residual_admits s t excess hs hx hp
    exact ⟨r.reverse, (congrArg reversePayload h).trans (reverse_two r)⟩
  residual_packet := by
    intro s t
    rcases hc.residual_packet s t with h | h | ⟨r, hr, h⟩
    · exact Or.inl (congrArg reversePayload h)
    · exact Or.inr (Or.inl (congrArg reversePayload h))
    · exact Or.inr (Or.inr ⟨r.reverse, by simpa using hr, (congrArg reversePayload h).trans (reverse_two r)⟩)
  residual_difference := by
    intro s t r h
    have original := congrArg reversePayload h
    change reversePayload (reversePayload _) = _ at original
    rw [reverse_twice, reverse_two] at original
    exact (hc.residual_difference s t r.reverse original).trans ((List.reverse_perm r).append_right _)
  residual_success := by
    intro sig decode v f s t r h typed
    have original := congrArg reversePayload h
    change reversePayload (reversePayload _) = _ at original
    rw [reverse_twice, reverse_two] at original
    have hp := (hc.residual_difference s t _ original).trans ((List.reverse_perm r).append_right _)
    apply FlatAC.variable_complete_difference
    · simpa using show s.toList ≠ [] by
        intro he
        rw [(hc.empty_inputs _ _ (Or.inl (by simpa using he))).2] at original
        exact (by simpa using congrArg Array.toList original : False)
    · simpa using show t.toList ≠ [] by
        intro he
        rw [(hc.empty_inputs _ _ (Or.inr (by simpa using he))).2] at original
        exact (by simpa using congrArg Array.toList original : False)
    · simpa using hc.residual_nonempty s t r.reverse original
    · simpa only [List.map_append] using hp.map decode
  residual_failure := by
    intro sig inst d enc v f s t live h
    have original := congrArg reversePayload h
    change reversePayload (reversePayload _) = _ at original
    exact hc.residual_failure d enc v f s t live ((reverse_twice _).symm.trans original)
  residual_completes := by
    intro s t hs ht
    rcases hc.residual_completes s t hs ht with h | ⟨r,hr,h⟩
    · exact Or.inl (congrArg reversePayload h)
    · exact Or.inr ⟨r.reverse, by simpa using hr, (congrArg reversePayload h).trans (reverse_two r)⟩

example : (reverseBackend RuntimeCandidate.backend).Correct := reverse_correct _ CandidateProofs.correct

-- Check the change on a witness where reversal is observable, independently
-- of which valid order the production candidate currently chooses.
example (b : FlatACBackend) (hc : b.Correct) :
    (reverseBackend b).residual #[2] #[4,3,2] ≠ b.residual #[2] #[4,3,2] := by
  have input : (#[4,3,2] : Array UInt64).toList.Perm ([3,4] ++ [2]) := by decide
  obtain ⟨r, hr⟩ := hc.residual_admits #[2] #[4,3,2] [3,4] (by decide) (by decide) input
  have hp : r.Perm [3,4] := (List.perm_append_right_iff _).mp
    ((hc.residual_difference _ _ _ hr).symm.trans input)
  obtain ⟨a,b',he⟩ : ∃ a b', r = [a,b'] :=
    ⟨_, _, List.eq_getElem_of_length_eq_two r hp.length_eq⟩
  subst r
  intro unchanged
  change reversePayload _ = _ at unchanged
  rw [hr, reverse_two] at unchanged
  have eq := congrArg Array.toList unchanged
  have h3 := hp.symm.subset (a := 3) (by decide)
  have h4 := hp.symm.subset (a := 4) (by decide)
  simp at eq h3 h4
  grind

end Tamarin.ExistingSpecAudit
