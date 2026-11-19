import Tamarin.CompoundPartitions
import Tamarin.FlatMatchCandidateProofs
import Tamarin.OpenMatchCancellation
import Tamarin.CancelCommonCandidateProofs

namespace Tamarin.CompoundPartitionTests
open CompoundPartitions

private abbrev sig : Signature where
  Atom := Unit
  FreeSym := Unit
  CSym := Empty
  ACSym := Unit
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort := Empty.elim
  acSort _ := .msg
  atomSort _ := .pub

private def a : Term sig := .atom ()
private def h : Term sig := .free () (fun _ => a)
private def d (i : UInt64) := if i = 0 then a else h
private def x : Variable := ⟨0,.pub⟩
private def y : Variable := ⟨1,.msg⟩
private def vars (i : Fin 2) := if i = 0 then x else y
private def occ : List (Fin 2) := [0,0,1]
private def rhs : Array UInt64 := #[0,0,1,1]
private def valid : List (List UInt64) := [[0],[1,1]]
private def invalid : List (List UInt64) := [[1],[0,0]]
private def out := Executable.flatACMatch 2 #[0,0,1] #[] rhs

-- Check row membership independently of the optimization's enumeration order.
private theorem numeric (r : List (List UInt64)) : r ∈ Packet out ↔ r = invalid ∨ r = valid := by
  have eq : r ∈ Packet out ↔ r ∈ FlatMatchSearch.solve 2 [0,0,1] ([] : List UInt64) rhs.toList :=
    (FlatMatchCandidateProofs.exported ..).trans (FlatMatchSearch.mem_solve ..).symm
  have spec : FlatMatchSearch.solve 2 [0,0,1] ([] : List UInt64) rhs.toList = [invalid, valid] := by decide +kernel
  rw [eq,spec]
  simp

private theorem closed (i : UInt64) : CompoundMatching.FreeGround (d i) := by
  unfold d
  split
  · exact CompoundMatching.FreeGround.atom (sig := sig) ()
  · exact CompoundMatching.FreeGround.free (sig := sig) () (fun _ => CompoundMatching.FreeGround.atom (sig := sig) ())

-- The two word partitions can assign either the literal or H(a) to the repeated
-- variable. Only the literal fits its declared Pub sort.
example (σ : Substitution sig) :
    ACResidual.Holds () σ (occ.map (fun i => .var (vars i))) (rhs.toList.map d) ↔
      EquivB (σ.image x) a ∧ EquivB (σ.image y) (.ac () h h) := by
  have verified : Correct Executable.flatACMatch := correct FlatMatchCandidateProofs.exported
  have rows := verified.freeGround () d 2 vars occ rhs (by decide) (fun i _ => closed i) (by
    intro i hi j hj
    have casesOf (k : UInt64) (hk : k ∈ rhs.toList) : k = 0 ∨ k = 1 := by
      simpa [rhs] using hk
    rcases casesOf i hi with rfl | rfl <;> rcases casesOf j hj with rfl | rfl <;> simp [d,a,h]) σ
  refine rows.trans ?_
  constructor
  · rintro ⟨rs,mem,images⟩
    rcases (numeric _).mp mem with rfl | rfl
    · obtain ⟨t,read,sort,_⟩ := images (0 : Fin 2)
      change some h = some t at read
      cases read
      change Subsort .msg .pub at sort
      cases sort
    · obtain ⟨t,read,_,hx⟩ := images (0 : Fin 2)
      obtain ⟨u,read',_,hy⟩ := images (1 : Fin 2)
      change some a = some t at read
      change some (.ac () h h) = some u at read'
      cases read; cases read'
      exact ⟨hx,hy⟩
  · rintro ⟨hx,hy⟩
    refine ⟨valid,(numeric _).mpr (.inr rfl),fun i => ?_⟩
    change Fin 2 at i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact ⟨a,rfl,.refl _,hx⟩
    · exact ⟨.ac () h h,rfl,.refl _,hy⟩

-- One subject occurrence of H(a) cannot discharge two closed copies, even
-- when an open pattern in between them can match H(a).
example (σ : Substitution sig) :
    ¬ ACResidual.Holds () σ [h,.var y,h] [h,a] := by
  have verified : OpenMatchCancellation.Correct Executable.cancelCommon :=
    OpenMatchCancellation.correct CancelCommonCandidateProofs.correct
  obtain ⟨missing,rest,out,spec⟩ := verified () d #[1,1] #[1,0] (fun i _ => closed i) (by
    intro i hi j hj
    have hi' : i = 1 := by simpa using hi
    have hj' : j = 1 ∨ j = 0 := by simpa using hj
    rcases hi' with rfl
    rcases hj' with rfl | rfl <;> simp [d,h,a])
  have order : [h,.var y,h].Perm ([h,h] ++ [.var y]) := by
    exact (List.Perm.swap _ _ []).cons _
  intro sol
  have empty := ((spec _ [.var y] order σ).mp sol).1
  obtain ⟨common,left,right,packet,hl,hr,_⟩ := CancelCommonCandidateProofs.correct #[1,1] #[1,0]
  have head := congrArg (fun (p : Array (Array UInt64)) => p[0]!.toList) (packet.symm.trans out)
  have leftEmpty : left = [] := by simpa [empty] using head
  have p : ([1,1] : List UInt64).Perm common := by simpa [leftEmpty] using hl
  have len : 2 = common.length + right.length := by simpa using hr.length_eq
  have zero : right.length = 0 := by have := p.length_eq; simp at this; omega
  have q : ([1,0] : List UInt64).Perm common := by simpa [List.length_eq_zero_iff.mp zero] using hr
  have impossible := (q.trans p.symm).mem_iff.mp (show 0 ∈ ([1,0] : List UInt64) by decide)
  simp at impossible

end Tamarin.CompoundPartitionTests
