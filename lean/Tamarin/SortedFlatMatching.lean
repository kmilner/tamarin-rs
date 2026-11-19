import Tamarin.FlatMatchContract
import Tamarin.FreshSubstitution
import Tamarin.SortCheck

/-! Interpret partitions of a literal AC subject when each pattern variable
has its own declared sort. Singleton images retain the atom's principal sort.
Products take the operator's result sort. -/
namespace Tamarin.SortedFlatMatching
open FlatMatching
variable {sig : Signature} {n : Nat}

/-- Check the principal sort of the decoded image on each coordinate. -/
def Typed (f : sig.ACSym) (vars : Fin n → Variable) (rows : List (List sig.Atom)) : Prop :=
  ∃ hl : rows.length = n, ∀ i, Subsort (FlatAC.term f (rowVector rows hl i)).rootSort (vars i).sort

private theorem typed_term (f : sig.ACSym) (xs : List sig.Atom) (hn : xs ≠ [])
    (hs : ∀ a ∈ xs, Subsort (sig.atomSort a) (sig.acSort f)) {s : SortId}
    (fits : Subsort (FlatAC.term f xs).rootSort s) : HasSort (FlatAC.term f xs) s := by
  cases xs with
  | nil => contradiction
  | cons a xs =>
    cases xs with
    | nil => exact .widen (.atom a) fits
    | cons b xs => exact .widen (FlatAC.term_hasSort f _ hn hs) fits

private def bindings (f : sig.ACSym) (vars : Fin n → Variable)
    (rows : List (List sig.Atom)) (hl : rows.length = n) : List (Variable × Term sig) :=
  List.ofFn fun i => (vars i, FlatAC.term f (rowVector rows hl i))

/-- The table is read in the same variable order as the request. Other
variables keep their identity image. -/
def answer (f : sig.ACSym) (vars : Fin n → Variable) (rhs : List sig.Atom)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (rows : List (List sig.Atom)) (ha : admissibleRows (n := n) rhs rows) (h : Typed f vars rows) :
    Substitution sig :=
  Substitution.fromBindings (bindings f vars rows ha.1) (by
    intro v t hm
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp hm
    cases eq
    have inRows : rowVector rows ha.1 i ∈ rows := List.getElem_mem (by omega)
    have constraints := ha.2 _ inRows
    exact typed_term f _ constraints.1 (fun a hm => hs a (constraints.2.subset hm)) (h.choose_spec i))

private theorem answer_image (f : sig.ACSym) (vars : Fin n → Variable) (rhs : List sig.Atom)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (rows : List (List sig.Atom)) (ha : admissibleRows (n := n) rhs rows) (h : Typed f vars rows)
    (inj : Function.Injective vars) (i : Fin n) :
    (answer f vars rhs hs rows ha h).image (vars i) = FlatAC.term f (rowVector rows ha.1 i) := by
  apply Substitution.lookupBinding_eq_of_mem
  · intro v t u ht hu
    obtain ⟨j,ej⟩ := List.mem_ofFn.mp ht
    obtain ⟨k,ek⟩ := List.mem_ofFn.mp hu
    have jk : j = k := inj ((congrArg Prod.fst ej).trans (congrArg Prod.fst ek).symm)
    exact (congrArg Prod.snd ej).symm.trans (jk ▸ (congrArg Prod.snd ek))
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩

def answers (f : sig.ACSym) (vars : Fin n → Variable) (rhs : List sig.Atom)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (out : List (List (List sig.Atom)))
    (valid : ∀ rows ∈ out, admissibleRows (n := n) rhs rows ∧ Typed f vars rows) :
    List (Substitution sig) :=
  out.attach.map fun r => answer f vars rhs hs r.val (valid _ r.property).1 (valid _ r.property).2

/-- A sorted solution can always be represented by one of the unfiltered
finite partitions. Equivalence preserves its principal sort, so filtering
cannot lose that solution, even when variables repeat or have different sorts. -/
theorem complete_of_rows [DecidableEq sig.Atom] (f : sig.ACSym) (vars : Fin n → Variable)
    (occ : List (Fin n)) (tail rhs : List sig.Atom)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (inj : Function.Injective vars) (used : ∀ i, i ∈ occ)
    (hq : queryLeaves vars occ tail ≠ []) (hr : rhs ≠ [])
    (out : List (List (List sig.Atom)))
    (rows_iff : ∀ rows, rows ∈ out ↔ rows ∈ FlatMatchSearch.solve n (occ.map Fin.val) tail rhs ∧
      Typed f vars rows) :
    ∃ valid : ∀ rows ∈ out, admissibleRows (n := n) rhs rows ∧ Typed f vars rows,
      Matching.Complete [⟨pattern f (queryLeaves vars occ tail), FlatAC.term f rhs⟩]
        (fun _ => True) (answers f vars rhs hs out valid) := by
  have valid (rows) (hm : rows ∈ out) : admissibleRows (n := n) rhs rows ∧ Typed f vars rows := by
    obtain ⟨mem, fits⟩ := (rows_iff rows).mp hm
    have q := (FlatMatchSearch.mem_solve ..).mp mem
    exact ⟨⟨q.1,q.2.1⟩, fits⟩
  refine ⟨valid, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨⟨rows, hm⟩, _, rfl⟩ := List.mem_map.mp hσ
    have ha := (valid rows hm).1
    have ht := (valid rows hm).2
    have hi := answer_image f vars rhs hs rows ha ht inj
    have hp := ((FlatMatchSearch.mem_solve ..).mp ((rows_iff rows).mp hm).1).2.2
    rw [expand_vector rows ha.1 occ tail] at hp
    have hn : expanded (rowVector rows ha.1) occ tail ≠ [] := by
      intro he; exact hr (List.Perm.nil_eq (he ▸ hp)).symm
    constructor
    · intro e he
      obtain rfl := List.mem_singleton.mp he
      exact (pattern_expand f vars occ tail _ _
        (fun i => (ha.2 _ (List.getElem_mem (by omega))).1)
        (fun i => by rw [hi]; exact .refl _) hq hn).trans (FlatAC.perm_equiv f hp)
    · intro v hidden
      apply (answer f vars rhs hs rows ha ht).outside v
      intro hm
      obtain ⟨_, entry, rfl⟩ := List.mem_map.mp hm
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp entry
      apply hidden
      refine ⟨⟨_, List.mem_singleton_self _, ?_⟩, trivial⟩
      exact (occurs_pattern f vars occ tail hq _).mpr ⟨i,used i,rfl⟩
  · intro ρ hm _
    have he := hm _ (List.mem_singleton_self _)
    obtain ⟨rows, hrows, hl, hi⟩ := search_covers f vars occ tail rhs hq hr used ρ he
    have validSort : Typed f vars rows := ⟨hl, fun i => by
      rw [← Term.rootSort_equiv (hi i)]
      exact Term.rootSort_le (ρ.sorted _)⟩
    have mem := (rows_iff rows).mpr ⟨hrows,validSort⟩
    refine ⟨answer f vars rhs hs rows (valid rows mem).1 (valid rows mem).2,
      List.mem_map.mpr ⟨⟨rows,mem⟩, List.mem_attach _ _, rfl⟩, ?_⟩
    intro v ⟨e, he, hv⟩
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨i,_,rfl⟩ := (occurs_pattern f vars occ tail hq v).mp hv
    rw [answer_image f vars rhs hs rows _ _ inj]
    exact hi i

end Tamarin.SortedFlatMatching
