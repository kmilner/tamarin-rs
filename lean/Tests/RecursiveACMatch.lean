import TamarinCI

namespace Tamarin.RecursiveACMatchTests
open RecursiveACMatch
private abbrev sig : Signature where
  FreeSym := Unit
  CSym := Unit
  ACSym := Bool
  Atom := Bool
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .pub

private abbrev select := Executable.openMatchSelect
private abbrev flat := Executable.flatACMatch
private abbrev orient := Executable.commOrientations
private def enc : NestedTreeMatch.Encoding sig where
  key _ _ := 0
  priority _ := 0
  valid _ := ⟨by simp,by simp⟩

private def a : Term sig := .atom false
private def x : Variable := ⟨10,.msg⟩
private def xx : Term sig := .ac true (.var x) (.var x)
private def aa : Term sig := .ac true a a
private def h (t : Term sig) : Term sig := .free () (fun _ => t)

private def zero : Fin (1 : UInt64).toNat := ⟨0, by decide⟩
private def vars (_ : Fin 1) := x
private abbrev noneRead : Term sig → Term sig → Observation sig := fun _ _ _ => False
private def inner : Layout true xx aa where
  rigid := []
  m := 1
  vars := vars
  occ := [zero,zero]
  subject _ := a
  k := 0
  n := 2
  pack is := {
    rhs := (is.map (fun _ => (0 : UInt64))).toArray
    decode := fun _ => a
    represents := by simp [List.map_map,Function.comp_def]
    faithful := by
      intro i hi j hj _
      simp only [List.mem_map] at hi hj
      obtain ⟨_,_,rfl⟩ := hi
      obtain ⟨_,_,rfl⟩ := hj
      rfl }
  count := rfl
  used := by decide
  patternLayout := .refl _
  subjectLayout := .refl _
  rigidHead := by simp
  subjectHead := by intro _ _; trivial
  le := Eq
  antisymmetric _ _ hab _ := hab
  canonical _ _ := .atom _

private def rows (k : UInt64) := (select k 2).getD #[]
private abbrev innerRead := inner.read flat (rows 0) noneRead
private abbrev S := Search select flat orient Executable.cancelCommon enc
private theorem innerSearch : S xx aa innerRead :=
  .ac inner (rows 0) (by apply Option.eq_some_of_isSome; decide +kernel)
    noneRead (by simp [inner])

-- Twice the same variable consumes two copies of the *same nonempty image*.
private theorem inner_iff (σ : Substitution sig) : innerRead σ ↔ EquivB (σ.image x) a := by
  rw [search_iff exportedOpenMatchSelect_correct exportedCompoundPartitions_correct
    exportedCommOrientations_correct exportedCancelCommon_correct innerSearch σ]
  change EquivB (.ac true (σ.image x) (σ.image x)) (.ac true a a) ↔ _
  constructor
  · intro e
    rcases (AtomicACPair.equiv_iff true a a _ _ rfl rfl).mp e.symm with ⟨h,_⟩ | ⟨h,_⟩ <;> exact h.symm
  · intro h
    exact .ac_congr true h h

private def lhs : Term sig := .ac false (h xx) (.var x)
private def rhs (tail : Bool) : Term sig := .ac false (h aa) (.atom tail)
private def pos (i : Nat) : UInt64 := if i = 0 then 0 else 1
private def decode (tail : Bool) (w : UInt64) : Term sig := if w = 0 then h aa else .atom tail
private def subject (tail : Bool) (i : Nat) := decode tail (pos i)

private def outer (tail : Bool) : Layout false lhs (rhs tail) where
  rigid := [h xx]
  m := 1
  vars := vars
  occ := [zero]
  subject := subject tail
  k := 1
  n := 2
  pack is := {
    rhs := (is.map pos).toArray
    decode := decode tail
    represents := by simp [subject,List.map_map,Function.comp_def]
    faithful := by
      intro i hi j hj same
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp (by simpa using hi)
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp (by simpa using hj)
      by_cases a : u = 0 <;> by_cases b : v = 0 <;> simp [pos,decode,h,a,b] at same ⊢ }
  count := rfl
  used := by decide
  patternLayout := .refl _
  subjectLayout := .refl _
  rigidHead _ mem := by obtain rfl := List.mem_singleton.mp mem; trivial
  subjectHead i _ := by by_cases z : i = 0 <;> simp [subject,pos,decode,z,h,CompoundOffset.Fixed]
  le := Eq
  antisymmetric _ _ hab _ := hab
  canonical i _ := by
    by_cases z : i = 0
    · simp only [subject,pos,decode,z,ite_true]
      apply CanonicalTree.Canonical.free
      intro _
      apply CanonicalTree.Canonical.ac (rest := [])
      · intro u hu
        simp only [a,List.mem_cons,List.not_mem_nil,or_false,or_self] at hu
        exact hu ▸ CanonicalTree.Canonical.atom _
      · intro u hu
        simp only [a,List.mem_cons,List.not_mem_nil,or_false,or_self] at hu
        subst u; trivial
      · simp [a]
    · simp [subject,pos,decode,z]; exact .atom _

private def child (_ subject : Term sig) : Observation sig :=
  match subject with
  | .free _ _ => fun σ => ∀ _ : Fin 1, innerRead σ
  | _ => fun _ => False

private abbrev outerRead (b : Bool) := (outer b).read flat (rows 1) child
private theorem outerSearch (tail : Bool) : S lhs (rhs tail) (outerRead tail) := by
  apply Search.ac (outer tail) (rows 1) (by change select 1 2 = some (rows 1); apply Option.eq_some_of_isSome; decide +kernel)
  intro r hr i _
  obtain rfl := List.mem_singleton.mp hr
  by_cases z : i = 0
  · subst i
    exact .free () (fun _ => innerSearch)
  · change S (h xx) (subject tail i) (child (h xx) (subject tail i))
    simp [subject,pos,decode,z,child]
    exact .clash _ _ (by intro v e; cases e) (by intro e; cases e)

-- The surrounding occurrence selects exactly one root branch and shares x
-- with the inner partition. Replacing the last a by b rules out every match.
example (tail : Bool) (σ : Substitution sig) :
    Matching.Matches [⟨lhs,rhs tail⟩] σ ↔ EquivB (σ.image x) a ∧ tail = false := by
  have law := exportedRecursiveACMatch_correct (outerSearch tail) lhs (rhs tail) (.refl _) (.refl _) [] σ
  simp only [Matching.Matches,List.not_mem_nil,false_implies,implies_true,and_true] at law
  change Matching.Matches [⟨lhs,rhs tail⟩] σ ↔ _
  rw [show Matching.Matches [⟨lhs,rhs tail⟩] σ ↔ outerRead tail σ from law]
  have suffix : OpenMatchAdapter.Remainder flat false (m := 1) vars [zero] ([1].map (subject tail))
      ((outer tail).pack [1]) σ ↔ EquivB (σ.image x) (.atom tail) := by
    change (∃ t, some (.atom tail) = some t ∧ Subsort t.rootSort x.sort ∧ EquivB (σ.image x) t) ↔ _
    simp only [Option.some.injEq,exists_eq_left']
    exact ⟨And.right,fun e => ⟨.pub_msg,e⟩⟩
  constructor
  · rintro ⟨is,mem,read⟩
    have allowed : (OpenMatchSelect.decoded (rows 1)).all (fun row => [[0,1],[1,0]].contains row) = true := by decide +kernel
    rcases List.mem_cons.mp (List.contains_iff_mem.mp (List.all_eq_true.mp allowed is mem)) with rfl | other
    · have xa := (inner_iff σ).mp (read.1 0)
      have xt := suffix.mp read.2
      exact ⟨xa,Head.atom.inj (xt.symm.trans xa).head_eq⟩
    · obtain rfl := List.mem_singleton.mp other
      exact False.elim read.1
  · rintro ⟨xa,rfl⟩
    exact ⟨[0,1],by decide +kernel,fun _ => (inner_iff σ).mpr xa,suffix.mpr xa⟩

end Tamarin.RecursiveACMatchTests
