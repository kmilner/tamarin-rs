import Tamarin.SortedMatchSorts

/-! Decode completed sorted matcher packets to the caller's concrete variables
and atoms. Only identities and sorts of live words matter. -/
namespace Tamarin.SortedMatchRefinement
open FlatMatching WholeProblem
variable {sig : Signature}

def FlatCorrect (flat : SortedMatch.Flat) : Prop :=
  ∀ n occ tail rhs rows,
    rows ∈ (flat n occ tail rhs).toList.map (fun a => a.toList.map Array.toList) ↔
    rows.length = n.toNat ∧ (∀ r ∈ rows, r ≠ [] ∧ List.Sublist r rhs.toList) ∧
      (FlatMatchSearch.expand rows (occ.toList.map UInt64.toNat) ++ tail.toList).Perm rhs.toList

private abbrev words := fun (a : Array (Array UInt64)) => a.toList.map Array.toList

def decodeArm (decode : UInt64 → sig.Atom) (a : Array (Array UInt64)) :=
  a.toList.map fun r => r.toList.map decode

private theorem map_decode (decode : UInt64 → sig.Atom) (a : Array (Array UInt64)) :
    (words a).map (List.map decode) = decodeArm decode a := by
  simp [words, decodeArm, List.map_map, Function.comp_def]

/-- The wire-level row membership contract lifts through a sort-preserving
filter for every arm of the unfiltered numeric matcher. -/
private theorem transfer [DecidableEq sig.Atom] {run flat}
    (check : SortedMatch.Correct run flat) (base : FlatCorrect flat)
    (decode : UInt64 → sig.Atom) (encode : sig.Atom → Option UInt64)
    (f : sig.ACSym) (vs ats : Array UInt64) (vars : Fin vs.size → Variable)
    (occ : List (Fin vs.size)) (tail rhs : Array UInt64)
    (live : ∀ id ∈ tail.toList ++ rhs.toList, encode (decode id) = some id)
    (fit : ∀ a, ((words a).length = vs.size ∧ ∀ r ∈ words a, r ≠ [] ∧ List.Sublist r rhs.toList) →
      (SortedMatch.Fits (sortWord (sig.acSort f)) vs ats a ↔
         SortedFlatMatching.Typed f vars (decodeArm decode a)))
    (out : SortedMatch.Answers)
    (returned : run (sortWord (sig.acSort f)) vs ats
      (occ.map (fun i => i.val.toUInt64)).toArray tail rhs = some out) :
    ∀ rows, rows ∈ out.toList.map (decodeArm decode) ↔
      rows ∈ FlatMatchSearch.solve vs.size (occ.map Fin.val) (tail.toList.map decode) (rhs.toList.map decode) ∧
      SortedFlatMatching.Typed f vars rows := by
  let inputs := (occ.map fun i => i.val.toUInt64).toArray
  have admitted := (check.completes ..).mp (Option.isSome_of_eq_some returned)
  have bound : vs.size < UInt64.size := admitted.2.1
  have targets : inputs.toList.map UInt64.toNat = occ.map Fin.val := by
    simp only [inputs,List.map_map]
    apply List.map_congr_left
    intro i _
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt bound)
  have rawRows (xs : List (List UInt64)) :
      xs ∈ (flat vs.size.toUInt64 inputs tail rhs).toList.map words ↔
      xs ∈ FlatMatchSearch.solve vs.size (occ.map Fin.val) tail.toList rhs.toList := by
    rw [FlatMatchSearch.mem_solve]
    simpa only [UInt64.toNat_ofNat_of_lt' bound, targets] using
      base vs.size.toUInt64 inputs tail rhs xs
  intro rows
  constructor
  · intro present
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp present
    obtain ⟨raw, fits⟩ := (check.rows _ _ _ _ _ _ _ returned a).mp (Array.mem_def.mpr ha)
    have mem := (rawRows (words a)).mp (List.mem_map_of_mem (Array.mem_def.mp raw))
    have h := (FlatMatchSearch.mem_solve ..).mp mem
    exact ⟨(FlatMatchSearch.mem_solve_map decode encode _ _ _ _ live _).mpr
      ⟨words a,mem,(map_decode decode a).symm⟩, (fit a ⟨h.1,h.2.1⟩).mp fits⟩
  · rintro ⟨found,typed⟩
    obtain ⟨xs,mem,rfl⟩ := (FlatMatchSearch.mem_solve_map decode encode _ _ _ _ live rows).mp found
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ((rawRows xs).mpr mem)
    rw [map_decode] at typed ⊢
    have h := (FlatMatchSearch.mem_solve ..).mp mem
    have ok := (check.rows _ _ _ _ _ _ _ returned a).mpr ⟨Array.mem_def.mpr ha, (fit a ⟨h.1,h.2.1⟩).mpr typed⟩
    exact List.mem_map_of_mem (Array.mem_def.mp ok)

/-- The actual returned rows, decoded in the request's variable order, give
all matches on that query. Exactness includes both clashes and nonground
candidate substitutions. No completeness assumption about the cutoff is needed. -/
def Correct (run : SortedMatch.Kernel) : Prop :=
  ∀ {s : Signature} [DecidableEq s.Atom] (decode : UInt64 → s.Atom) (encode : s.Atom → Option UInt64)
    (f : s.ACSym) (vs ats : Array UInt64) (vars : Fin vs.size → Variable)
    (occ : List (Fin vs.size)) (tail rhs : Array UInt64),
    (∀ id ∈ tail.toList ++ rhs.toList, encode (decode id) = some id) →
    (∀ i : Fin vs.size, vs[i] = sortWord (vars i).sort) →
    (∀ id ∈ rhs.toList, ats[id.toNat]? = some (sortWord (s.atomSort (decode id)))) →
    Function.Injective vars → (∀ i, i ∈ occ) →
    queryLeaves vars occ (tail.toList.map decode) ≠ [] → rhs.toList ≠ [] →
    ∀ out, run (sortWord (s.acSort f)) vs ats (occ.map (fun i => i.val.toUInt64)).toArray tail rhs = some out →
    let rows := out.toList.map (decodeArm decode)
    let atoms := rhs.toList.map decode
    ∃ hs : ∀ a ∈ atoms, Subsort (s.atomSort a) (s.acSort f),
    ∃ valid : ∀ r ∈ rows, admissibleRows (n := vs.size) atoms r ∧ SortedFlatMatching.Typed f vars r,
      Matching.Complete [⟨pattern f (queryLeaves vars occ (tail.toList.map decode)), FlatAC.term f atoms⟩]
        (fun _ => True) (SortedFlatMatching.answers f vars atoms hs rows valid)

theorem correct {run flat} (check : SortedMatch.Correct run flat) (base : FlatCorrect flat) :
    Correct run := by
  intro s _ decode encode f vs ats vars occ tail rhs live varWords atomWords inj used hq hr out returned
  have admitted := (check.completes ..).mp (Option.isSome_of_eq_some returned)
  have hs (a) (ha : a ∈ rhs.toList.map decode) : Subsort (s.atomSort a) (s.acSort f) := by
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    exact (SortedMatchSorts.subsort_iff ..).mp
      ((admitted.2.2.2.1 _ (Array.mem_of_getElem? (atomWords k hk))).2)
  refine ⟨hs, SortedFlatMatching.complete_of_rows f vars occ _ _ hs inj used hq (by simpa using hr) _ ?_⟩
  exact transfer check base decode encode f vs ats vars occ tail rhs live
    (fun arm => SortedMatchSorts.fits_iff vs vars f ats decode rhs arm varWords atomWords) out returned

end Tamarin.SortedMatchRefinement
