import TamarinCI

namespace Tamarin.OpenMatchTests
open Matching

private def sig : Signature where
  FreeSym := Unit
  CSym := Empty
  ACSym := Unit
  Atom := Bool
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort := Empty.elim
  acSort _ := .msg
  atomSort _ := .pub
private instance : DecidableEq sig.ACSym := inferInstanceAs (DecidableEq Unit)

private def x : Variable := ⟨4,.msg⟩
private def y : Variable := ⟨5,.msg⟩
private def hash (t : Term sig) : Term sig := .free () (fun _ => t)
private def a : Term sig := .atom false
private def b : Term sig := .atom true
private def h (p s : Term sig) := Equation.mk p s
private def rigid := [hash (.var x)]
private def loose : List (Term sig) := [.var y]
private def pattern : Term sig := .ac () (.var y) (hash (.var x))
private def subject : Term sig := .ac () (hash a) (hash b)
private def atPos (i : Nat) := if i = 0 then hash a else hash b
private def pending := [h (.var x) b]
private instance : DecidableEq sig.FreeSym := inferInstanceAs (DecidableEq Unit)
private instance : DecidableEq sig.Atom := inferInstanceAs (DecidableEq Bool)

private def raw := (Executable.openMatchSelect 1 2).getD #[]
private theorem ran : Executable.openMatchSelect 1 2 = some raw := by
  apply Option.eq_some_of_isSome
  decide +kernel
private theorem semantic (ρ : Substitution sig) :
    Matches (h pattern subject :: pending) ρ ↔
      Matches ([h (hash (.var x)) (hash a), h (.var y) (hash b)] ++ pending) ρ ∨
      Matches ([h (hash (.var x)) (hash b), h (.var y) (hash a)] ++ pending) ρ := by
  have checked : OpenMatch.Correct Executable.openMatchSelect := exportedOpenMatch_correct
  have all := checked () pattern subject rigid loose atPos 1 2
    rfl (List.Perm.swap _ _ []) (List.Perm.refl _) (by
      intro t ht
      obtain rfl := List.mem_singleton.mp ht
      intro ρ; rfl) (by
      intro i hi
      change Cancellation.flatten () (atPos i) = [Cancellation.classOf (atPos i)]
      unfold atPos
      split <;> rfl) raw ran pending ρ
  have rows (row) : row ∈ OpenMatchSelect.decoded raw ↔ row ∈ [[0,1],[1,0]] := by
    constructor
    · intro member
      have allowed : (OpenMatchSelect.decoded raw).all (fun row => [[0,1],[1,0]].contains row) = true := by
        decide +kernel
      exact List.contains_iff_mem.mp (List.all_eq_true.mp allowed row member)
    · intro member
      rcases List.mem_cons.mp member with rfl | rest
      · decide +kernel
      · obtain rfl := List.mem_singleton.mp rest; decide +kernel
  have left : OpenMatch.branch () loose atPos rigid [0,1] =
      some [h (hash (.var x)) (hash a), h (.var y) (hash b)] := rfl
  have right : OpenMatch.branch () loose atPos rigid [1,0] =
      some [h (hash (.var x)) (hash b), h (.var y) (hash a)] := rfl
  simpa only [h,rows,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,
    exists_eq_left,exists_eq_left',left,right,Option.some.injEq] using all

private theorem hash_match (ρ : Substitution sig) (s : Term sig) :
    EquivB (ρ.apply (hash (.var x))) (hash s) ↔ EquivB (ρ.image x) s := by
  have iff := Matching.free_equiv_iff (sig := sig) () (fun _ => ρ.image x) (fun _ => s)
  exact iff.trans ⟨fun h => h ⟨0,by decide⟩, fun h _ => h⟩

-- The hypothesis from the separate pending equation chooses the crossed
-- assignment. Selecting child and remainder matches independently would
-- incorrectly admit the other branch.
example (ρ : Substitution sig) :
    Matches (h pattern subject :: pending) ρ ↔
      EquivB (ρ.image x) b ∧ EquivB (ρ.image y) (hash a) := by
  rw [semantic]
  simp only [pending,List.cons_append,List.nil_append,Matches,h,List.forall_mem_cons,
    List.not_mem_nil,false_implies,implies_true,and_true,hash_match]
  change (_ ∧ _ ∧ EquivB (ρ.image x) b) ∨ (EquivB (ρ.image x) b ∧ _ ∧ _) ↔ _
  constructor
  · rintro (⟨xa,_,xb⟩ | ⟨xb,ya,_⟩)
    · have wrong := (xa.symm.trans xb).head_eq
      cases wrong
    · exact ⟨xb,ya⟩
  · rintro ⟨xb,ya⟩
    exact Or.inr ⟨xb,ya,xb⟩

-- The AC theory has no unit. When all subject slots are consumed, a
-- nonempty remaining pattern rejects that assignment; an empty one finishes.
#guard (OpenMatch.branch () loose atPos rigid [0]).isNone
example : OpenMatch.branch () [] atPos rigid [0] = some [h (hash (.var x)) (hash a)] := rfl

private def key (i : Nat) : UInt64 := if i = 0 then 0 else if i = 1 then 1 else 2
private def term (u : UInt64) : Term sig := if u = 0 then b else if u = 1 then hash a else a
private def factors (i : Nat) := term (key i)
private def code : Term sig → UInt64
  | .atom v => if (show Bool from v) = true then 0 else 2
  | _ => 1

private def pack (is : List Nat) : OpenMatchAdapter.Words (is.map factors) where
  rhs := (is.map key).toArray
  decode := term
  represents := by simp [factors,List.map_map,Function.comp_def]
  faithful := by
    intro i hi j hj eq
    have recover (z) (hz : z ∈ (is.map key).toArray.toList) : code (term z) = z := by
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp (by simpa using hz)
      unfold key; split <;> first | rfl | split <;> rfl
    exact (recover i hi).symm.trans ((congrArg code eq).trans (recover j hj))

private def vars (i : Fin 2) := if i = 0 then x else y
private def occ : List (Fin 2) := [0,1]
private def fullP : Term sig := .ac () (hash (.var x)) (.ac () (.var x) (.var y))
private def fullS : Term sig := .ac () b (.ac () (hash a) a)
private def out := (Executable.openMatchSelect 1 3).getD #[]
private theorem joint (ρ : Substitution sig) :
    Matches [h fullP fullS] ρ ↔
      ∃ row ∈ OpenMatchSelect.decoded out, OpenMatchAdapter.Arm
        (fun is => OpenMatchAdapter.Remainder (sig := sig) (m := 2) Executable.flatACMatch () vars occ (is.map factors) (pack is) ρ)
        factors ρ rigid row := by
  have verified : OpenMatchAdapter.Correct Executable.openMatchSelect Executable.flatACMatch :=
    exportedOpenMatchAdapter_correct
  have runs : Executable.openMatchSelect 1 3 = some out := by
    apply Option.eq_some_of_isSome
    decide +kernel
  have hc := verified () fullP fullS rigid 2 vars occ factors 1 3 pack rfl (by decide) (.refl _) (.refl _)
    (by
      intro p hp; obtain rfl := List.mem_singleton.mp hp
      exact ⟨fun _ => rfl,FreeTreeMatch.Pattern.free (sig := sig) () (fun _ => .var x)⟩)
    (by
      intro i hi
      unfold factors term; split
      · exact CompoundMatching.FreeGround.atom (sig := sig) true
      · split
        · exact CompoundMatching.FreeGround.free (sig := sig) () (fun _ => CompoundMatching.FreeGround.atom (sig := sig) false)
        · exact CompoundMatching.FreeGround.atom (sig := sig) false) out runs [] ρ
  simpa only [Matches,h,List.not_mem_nil,false_implies,implies_true,true_and] using hc

-- The selected compound is the middle subject occurrence. Of the two flat
-- answer rows for the remaining occurrences, only the crossed allocation
-- agrees with the binding for x obtained inside the selected compound.
private theorem crossed (ρ : Substitution sig) (hx : ρ.image x = a) (hy : ρ.image y = b) :
    Matches [h fullP fullS] ρ := by
  apply (joint ρ).mpr
  have sel : [1,0,2] ∈ OpenMatchSelect.decoded out ∨ [1,2,0] ∈ OpenMatchSelect.decoded out := by decide +kernel
  obtain ⟨rest,selected,order⟩ : ∃ rest, 1 :: rest ∈ OpenMatchSelect.decoded out ∧
      (rest = [0,2] ∨ rest = [2,0]) := sel.elim
        (fun h => ⟨_,h,Or.inl rfl⟩) (fun h => ⟨_,h,Or.inr rfl⟩)
  refine ⟨1 :: rest,selected,?_,?_,[[2],[0]],?_,?_⟩
  · apply (FreeTreeMatch.agrees_iff (FreeTreeMatch.Pattern.free (sig := sig) () (fun _ => .var x))
      (CompoundMatching.FreeGround.free (sig := sig) () (fun _ => CompoundMatching.FreeGround.atom (sig := sig) false)) ρ).mpr
    exact (hash_match ρ a).mpr (hx ▸ .refl _)
  · rcases order with rfl | rfl <;> decide
  · rcases order with rfl | rfl <;> decide +kernel
  · change ∀ i : Fin 2, _
    intro i
    have small : i.val < 2 := i.isLt
    have split : i = 0 ∨ i = 1 := by apply (show i.val = 0 ∨ i.val = 1 from by omega).imp <;> exact fun h => Fin.ext h
    rcases split with rfl | rfl
    · exact ⟨a,rfl,.pub_msg,hx ▸ .refl _⟩
    · exact ⟨b,rfl,.pub_msg,hy ▸ .refl _⟩

example (ρ : Substitution sig) :
    Matches [h fullP fullS] ρ ↔ ρ.image x = a ∧ ρ.image y = b := by
  refine ⟨?_,fun ⟨hx,hy⟩ => crossed ρ hx hy⟩
  intro sol
  obtain ⟨row,member,arm⟩ := (joint ρ).mp sol
  have allowed : (OpenMatchSelect.decoded out).all
      (fun row => [[0,1,2],[0,2,1],[2,0,1],[2,1,0],[1,0,2],[1,2,0]].contains row) = true := by decide +kernel
  have live := List.contains_iff_mem.mp (List.all_eq_true.mp allowed row member)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at live
  have viable : ∃ rest, row = 1 :: rest ∧ (rest = [0,2] ∨ rest = [2,0]) := by
    rcases live with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ⟨_,rfl,Or.inl rfl⟩ | exact ⟨_,rfl,Or.inr rfl⟩
                    | obtain ⟨⟨_,impossible,_⟩,_⟩ := arm; cases impossible
  obtain ⟨rest,rfl,order⟩ := viable
  obtain ⟨⟨bs,bsRead,bindings⟩,_,rows,mem,images⟩ := arm
  have readTree : FreeTreeMatch.read (hash (.var x)) (factors 1) = some [(x,a)] := rfl
  obtain rfl := Option.some.inj (bsRead.symm.trans readTree)
  have hx : ρ.image x = a := (bindings (x,a) List.mem_cons_self).2
  have partitions : (CompoundPartitions.Packet (Executable.flatACMatch 2 #[0,1] #[] (pack rest).rhs)).all
      (fun rs => [[[0],[2]],[[2],[0]]].contains rs) = true := by
    rcases order with rfl | rfl <;> decide +kernel
  have choices := List.contains_iff_mem.mp (List.all_eq_true.mp partitions rows mem)
  rcases List.mem_cons.mp choices with rfl | tail
  · obtain ⟨_,read,_,wrong⟩ := images (⟨0,by decide⟩ : Fin 2)
    change some b = some _ at read
    cases Option.some.inj read
    change EquivB (ρ.image x) b at wrong
    rw [hx] at wrong
    cases wrong.head_eq
  · obtain rfl := List.mem_singleton.mp tail
    obtain ⟨_,read,_,agree⟩ := images (⟨1,by decide⟩ : Fin 2)
    change some b = some _ at read
    cases Option.some.inj read
    change EquivB (ρ.image y) b at agree
    exact ⟨hx,((CompoundMatching.FreeGround.atom (sig := sig) true).rigid _ agree.symm).symm⟩
example : ¬ FreeTreeMatch.Valid [(x,a),(x,b)] := by
  rintro ⟨_,same⟩
  cases same x a b (by simp) (by simp)

end Tamarin.OpenMatchTests
