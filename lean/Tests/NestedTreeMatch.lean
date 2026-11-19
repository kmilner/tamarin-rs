import TamarinCI

namespace Tamarin.NestedTreeMatchTests
open NestedTreeMatch

private abbrev sig : Signature where
  FreeSym := Unit
  CSym := Unit
  ACSym := Unit
  Atom := Bool
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .pub

private def a : Term sig := .atom false
private def b : Term sig := .atom true
private def x : Variable := ⟨7,.msg⟩
private def y : Variable := ⟨9,.msg⟩
private def c (l r : Term sig) := Term.comm (sig := sig) () l r
private def h (t : Term sig) := Term.free (sig := sig) () (fun _ => t)
private abbrev op := Executable.commOrientations
private def enc : Encoding sig where
  key _ _ := 0
  priority _ := 0
  valid _ := ⟨by simp,by simp⟩

-- Both C orientations stay live under a free head, including when all four
-- rigid-head codes collide. The surrounding shared occurrence chooses x=b.
private theorem shared (σ : Substitution sig) :
    Reads op enc σ (h (c (.var x) (.var y))) (h (c a b)) ∧ EquivB (σ.image x) b ↔
      EquivB (σ.image x) b ∧ EquivB (σ.image y) a := by
  let le := fun (_ _ : Term sig) => True
  have pat : Pattern (h (c (.var x) (.var y))) := .free _ (fun _ => .comm _ (.var x) (.var y))
  have sub : Canonical le (h (c a b)) := .free _ (fun _ => .comm _ (.atom _) (.atom _) trivial)
  rw [reads_iff exportedCommOrientations_correct enc pat sub σ]
  have inv := Matching.free_equiv_iff (sig := sig) ()
    (fun _ => σ.apply (c (.var x) (.var y))) (fun _ => c a b)
  rw [show EquivB (σ.apply (h (c (.var x) (.var y)))) (h (c a b)) ↔
      EquivB (σ.apply (c (.var x) (.var y))) (c a b) from
    inv.trans ⟨fun child => child ⟨0,by decide⟩,fun child _ => child⟩]
  change (EquivB (.comm () (σ.image x) (σ.image y)) (.comm () a b) ∧ _) ↔ _
  rw [Commutative.equiv_iff (sig := sig) () _ _ a b]
  refine ⟨?_,fun ⟨xb,ya⟩ => ⟨Or.inr ⟨xb,ya⟩,xb⟩⟩
  rintro ⟨(⟨xa,_⟩ | ⟨_,ya⟩),xb⟩
  · cases (xa.symm.trans xb).head_eq
  · exact ⟨xb,ya⟩

private def rigid := h (c (.var x) (.var y))
private def lhs : Term sig := .ac () rigid (.var x)
private def tree := h (c a b)
private def rhs : Term sig := .ac () tree b
private def pos (i : Nat) : UInt64 := if i = 0 then 1 else 0
private def term (i : UInt64) := if i = 1 then tree else b
private def subject (i : Nat) := term (pos i)
private def words (is : List Nat) : OpenMatchAdapter.Words (is.map subject) where
  rhs := (is.map pos).toArray
  decode := term
  represents := by simp [subject,List.map_map,Function.comp_def]
  faithful := by
    intro i hi j hj he
    obtain ⟨ni,_,rfl⟩ := List.mem_map.mp (by simpa using hi)
    obtain ⟨nj,_,rfl⟩ := List.mem_map.mp (by simpa using hj)
    by_cases il : ni = 0 <;> by_cases jl : nj = 0 <;> simp [pos,il,jl,term,b,tree,h] at he ⊢

private def order (u v : Term sig) := u = v ∨ (u = a ∧ v = b)
private theorem anti (u v) : order u v → order v u → u = v := by
  rintro (eq | ⟨rfl,rfl⟩) inv
  · exact eq
  · rcases inv with eq | ⟨eq,_⟩ <;> cases eq
private def vars (_ : Fin 1) := x
private def occ : List (Fin 1) := [0]
private def rows := (Executable.openMatchSelect 1 2).getD #[]

-- Interpret all three actual exports for H(C(x,y))+x = H(C(a,b))+b.
-- In the successful selector arm only the crossed C orientation shares the
-- outer remainder binding x=b.
example (σ : Substitution sig) :
    Matching.Matches [⟨lhs,rhs⟩] σ ↔ EquivB (σ.image x) b ∧ EquivB (σ.image y) a := by
  have complete := exportedNestedTreeMatch_correct (s := sig) order anti enc () lhs rhs [rigid] 1 vars occ
    subject 1 2 words rfl (by decide) (.refl _) (.refl _)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ⟨fun _ => rfl,.free _ (fun _ => .comm _ (.var x) (.var y))⟩)
    (by intro i hi; by_cases iz : i = 0
        · subst i; exact .free _ (fun _ => .comm _ (.atom _) (.atom _) (Or.inr ⟨rfl,rfl⟩))
        · simp [subject,term,pos,iz]; exact .atom _)
    rows (by apply Option.eq_some_of_isSome; decide +kernel) lhs rhs (.refl _) (.refl _) [] σ
  simp only [Matching.Matches,List.not_mem_nil,false_implies,implies_true,true_and] at complete
  rw [show Matching.Matches [⟨lhs,rhs⟩] σ ↔ _ from complete]
  have tail : OpenMatchAdapter.Remainder (m := 1) Executable.flatACMatch () vars occ
      ([1].map subject) (words [1]) σ ↔ EquivB (σ.image x) b := by
    change (∃ t, some b = some t ∧ Subsort t.rootSort x.sort ∧ EquivB (σ.image x) t) ↔ _
    simp only [Option.some.injEq,exists_eq_left']
    exact ⟨And.right,fun e => ⟨.pub_msg,e⟩⟩
  constructor
  · rintro ⟨is,member,read⟩
    have live : (OpenMatchSelect.decoded rows).all (fun z => [[0,1],[1,0]].contains z) = true := by decide +kernel
    rcases List.mem_cons.mp (List.contains_iff_mem.mp (List.all_eq_true.mp live is member)) with rfl | other
    · exact (shared σ).mp ⟨read.1,tail.mp read.2⟩
    · obtain rfl := List.mem_singleton.mp other
      exact False.elim read.1
  · intro values
    obtain ⟨selected,remainder⟩ := (shared σ).mpr values
    exact ⟨[0,1],by decide +kernel,selected,tail.mpr remainder⟩

-- Equal variables in both children cannot bind distinct atoms by choosing
-- a different C orientation for each occurrence.
example (σ : Substitution sig) : ¬ Reads op enc σ (c (.var x) (.var x)) (c a b) := by
  let le := fun (_ _ : Term sig) => True
  have sub : Canonical le (c a b) := .comm _ (.atom _) (.atom _) trivial
  have pat : Pattern (c (.var x) (.var x)) := .comm _ (.var _) (.var _)
  rw [reads_iff exportedCommOrientations_correct enc pat sub σ]
  change ¬ EquivB (.comm () (σ.image x) (σ.image x)) (.comm () a b)
  rw [Commutative.equiv_iff (sig := sig) () _ _ a b]
  rintro (⟨xa,xb⟩ | ⟨xb,xa⟩) <;> cases (xa.symm.trans xb).head_eq

-- Structural interning before C canonicalization would treat these as two
-- different atoms in an AC partition.
private def rank : Term sig → Nat
  | .atom false => 0
  | _ => 1
private def le (u v : Term sig) := rank u ≤ rank v
private instance : DecidableRel le := fun a b => inferInstanceAs (Decidable (rank a ≤ rank b))
example : normalize le (h (c b a)) = normalize le (h (c a b)) := rfl
example : h (c b a) ≠ h (c a b) := by
  intro eq
  have same := congrArg (fun t : Term sig => match t with
    | .free _ xs => rank (match xs ⟨0,by exact Nat.zero_lt_one⟩ with | .comm _ a _ => a | u => u)
    | _ => 2) eq
  cases same

end Tamarin.NestedTreeMatchTests
