import TamarinRuntime.DHTower
import Tamarin.DHPeer
import Tamarin.FlatMatchSearch

/-! The linked function receives only the number of positive exponent
occurrences. Specify its result by interpreting every returned instruction
and comparing the resulting base expressions, independently of row order. -/
namespace Tamarin.Rewriting.DHTower.Packet
open DHPeer

inductive Arg where | peer | base | pos | neg | factor (occurrence : Nat)
  deriving DecidableEq
abbrev Image := Expr Arg
abbrev Kernel := UInt64 → Option (Array (Array UInt64))

def step (stack : List Image) (op : UInt64) : Option (List Image) :=
  match op, stack with
  | 0, xs => some (.var .peer :: xs)
  | 2, xs => some (.var .base :: xs)
  | 3, xs => some (.var .pos :: xs)
  | 4, xs => some (.var .neg :: xs)
  | 5, xs => some (.neutral :: xs)
  | 6, x :: xs => some (.inv x :: xs)
  | 7, y :: x :: xs => some (.mul x y :: xs)
  | 8, y :: x :: xs => some (.pow x y :: xs)
  | i, xs => if 9 ≤ i.toNat then some (.var (.factor (i.toNat-9)) :: xs) else none

def decode (r : Array UInt64) : Option Image := do
  let [t] ← r.toList.foldlM step [] | none
  return t

def product (i : Nat) (tail : List Nat) : Image :=
  tail.foldl (fun a j => .mul a (.var (.factor j))) (.var (.factor i))

/-- Optional positive and negative remainders describe the old exponent.
Every selected occurrence contributes one negative copy. -/
def cancel (selected : Image) (pos neg : Bool) : Image :=
  let mag := if neg then Expr.mul (.var Arg.neg) selected else selected
  let old := if pos then Expr.mul (.var Arg.pos) (.inv mag) else .inv mag
  .pow (.var .base) old

def Allowed (n : Nat) (t : Image) : Prop :=
  t = .var .peer ∨ t = .neutral ∨ t = .pow (.var .base) (.var .pos) ∨
    ∃ i tail, (i :: tail).Sublist (List.range n) ∧ ∃ pos neg, t = cancel (product i tail) pos neg

/-- Widths two through eight are required for present callers. A candidate
may admit additional widths. Every packet it returns has the same exact
meaning, irrespective of the admission decision or enumeration order. -/
structure Correct (run : Kernel) : Prop where
  required : ∀ n, 2 ≤ n.toNat ∧ n.toNat ≤ 8 → (run n).isSome
  describes : ∀ n rows, run n = some rows →
    (∀ row ∈ rows, (decode row).isSome) ∧
      ∀ t, (∃ row ∈ rows, decode row = some t) ↔ Allowed n.toNat t

private theorem push (i : Nat) (h : i < 8) (xs : List Image) :
    step xs (9+i).toUInt64 = some (.var (.factor i) :: xs) := by
  have small : (9+i).toUInt64.toNat = 9+i := by simp [Nat.toUInt64,UInt64.toNat_ofNat',Nat.mod_eq_of_lt (show 9+i < 2^64 by omega)]
  unfold step
  split <;> simp_all <;> omega

private theorem fold_product (js : List Nat) (bounded : ∀ j ∈ js, j < 8) (x : Image) (xs : List Image) :
    (js.flatMap (fun j => [(9+j).toUInt64, 7])).foldlM step (x :: xs) =
      some (js.foldl (fun a j => .mul a (.var (.factor j))) x :: xs) := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldlM_cons,
      push j (bounded j (by simp)), List.foldl_cons]
    exact ih (fun k hk => bounded _ (by simp [hk])) _

private theorem decoded (i : Nat) (is : List Nat) (bounded : ∀ j ∈ i :: is, j < 8) :
    let rs := DHTowerCandidate.cancellation (i::is)
    rs.map decode = [some (cancel (product i is) true false), some (cancel (product i is) false false),
      some (cancel (product i is) true true), some (cancel (product i is) false true)] := by
  have base (xs) : step xs 2 = some (.var .base :: xs) := rfl
  have pos (xs) : step xs 3 = some (.var .pos :: xs) := rfl
  have neg (xs) : step xs 4 = some (.var .neg :: xs) := rfl
  simp only [DHTowerCandidate.cancellation, decode, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.foldlM_cons, List.foldlM_append,
    base, pos, neg, push i (bounded i (by simp)), bind, Option.bind,
    fold_product is (fun j h => bounded j (by simp [h]))]
  rfl

private theorem cancel_mem (i : Nat) (is : List Nat) (bounded : ∀ j ∈ i :: is, j < 8) (o : Option Image) :
    (∃ row ∈ DHTowerCandidate.cancellation (i::is), decode row = o) ↔
    ∃ pos neg, o = some (cancel (product i is) pos neg) := by
  rw [← List.mem_map (f := decode), decoded i is bounded]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Bool.exists_bool]
  grind only

theorem correct : Correct DHTowerCandidate.images := by
  constructor
  · intro n bound
    simp [DHTowerCandidate.images,bound]
  · intro n rows ran
    have bound : 2 ≤ n.toNat ∧ n.toNat ≤ 8 := by
      apply Classical.byContradiction
      intro h
      simp [DHTowerCandidate.images,h] at ran
    simp only [DHTowerCandidate.images,bound] at ran
    obtain rfl := Option.some.inj ran
    constructor
    · intro r mem
      simp only [List.mem_toArray,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap] at mem
      rcases mem with (rfl|rfl|rfl)|⟨g,hg,hr⟩
      · rfl
      · rfl
      · rfl
      cases g with
      | nil => contradiction
      | cons i js =>
        have sub := (FlatMatchSearch.mem_sublists ..).mp hg
        obtain ⟨p,z,h⟩ := (cancel_mem i js (fun j hj => Nat.lt_of_lt_of_le (List.mem_range.mp (sub.subset hj)) bound.2) _).mp ⟨r,hr,rfl⟩
        rw [h]; rfl
    · intro t
      constructor
      · rintro ⟨r,hm,dec⟩
        simp only [List.mem_toArray,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap] at hm
        rcases hm with (rfl|rfl|rfl)|⟨g,hg,hr⟩
        · exact .inl (Option.some.inj dec.symm)
        · exact .inr (.inl (Option.some.inj dec.symm))
        · exact .inr (.inr (.inl (Option.some.inj dec.symm)))
        cases g with
        | nil => contradiction
        | cons i js =>
          have sub := (FlatMatchSearch.mem_sublists ..).mp hg
          obtain ⟨p,z,h⟩ := (cancel_mem i js (fun j hj => Nat.lt_of_lt_of_le (List.mem_range.mp (sub.subset hj)) bound.2) _).mp ⟨r,hr,dec⟩
          exact .inr (.inr (.inr ⟨i,js,sub,p,z,Option.some.inj h⟩))
      · rintro (rfl|rfl|rfl|⟨i,js,sub,p,z,rfl⟩)
        · exact ⟨#[0],by simp,rfl⟩
        · exact ⟨#[5],by simp,rfl⟩
        · exact ⟨#[2,3,8],by simp,rfl⟩
        obtain ⟨r,mem,hr⟩ := (cancel_mem i js (fun j hj => Nat.lt_of_lt_of_le (List.mem_range.mp (sub.subset hj)) bound.2) _).mpr ⟨p,z,rfl⟩
        exact ⟨r,List.mem_toArray.mpr (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,(FlatMatchSearch.mem_sublists ..).mpr sub,mem⟩)),hr⟩

end Tamarin.Rewriting.DHTower.Packet
