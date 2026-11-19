import Tamarin.OpenMatch
import Tamarin.CompoundPartitions
import Tamarin.FreeTreeMatch

/-! Composition of the two numeric exports for matching rigid free patterns and
a remaining variable inventory under AC. The caller can intern the remaining
subject anew for each selector row. -/
namespace Tamarin.OpenMatchAdapter
open Matching CompoundMatching
variable {sig : Signature}

/-- A per-call interner preserves occurrences and only needs to separate terms
that appear in this call. -/
structure Words (xs : List (Term sig)) where
  rhs : Array UInt64
  decode : UInt64 → Term sig
  represents : rhs.toList.map decode = xs
  faithful : ∀ i ∈ rhs.toList, ∀ j ∈ rhs.toList, decode i = decode j → i = j

/-- Decode the three cases implemented by the adapter. A lone occurrence has
one forced image, while multiple occurrences use the flat partition export. -/
def Remainder (flat : SortedMatch.Flat) (f : sig.ACSym) {m : UInt64} (vars : Fin m.toNat → Variable)
    (occ : List (Fin m.toNat)) (xs : List (Term sig)) (words : Words xs) (σ : Substitution sig) : Prop :=
  match occ with
  | [] => xs = []
  | [i] => ∃ t, ACRepresentation.decode f xs = some t ∧
      Subsort t.rootSort (vars i).sort ∧ EquivB (σ.image (vars i)) t
  | _ :: _ :: _ =>
    occ.length ≤ xs.length ∧
    ∃ rows ∈ CompoundPartitions.Packet (flat m (occ.map (fun i => i.val.toUInt64)).toArray #[] words.rhs),
      ∀ i, ∃ t, ACRepresentation.decode f ((CompoundPartitions.row rows i.val).map words.decode) = some t ∧
        Subsort t.rootSort (vars i).sort ∧ EquivB (σ.image (vars i)) t

theorem long_enough (f : sig.ACSym) (σ : Substitution sig) (left right : List (Term sig))
    (factors : ∀ t ∈ right, Cancellation.flatten f t = [Cancellation.classOf t]) (h : OpenMatch.Holds f left right σ) : left.length ≤ right.length := by
  have nonempty (t : Term sig) : 0 < (Cancellation.flatten f (σ.apply t)).length := by
    apply List.length_pos_iff.mpr
    intro empty
    have e := Cancellation.fold_flatten f (σ.apply t)
    rw [empty] at e; cases e
  have bound (ls : List (Term sig)) : ls.length ≤ (ls.flatMap fun t => Cancellation.flatten f (σ.apply t)).length := by
    induction ls with
    | nil => simp
    | cons t ts ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      have hb := nonempty t
      omega
  have groundSize : (right.flatMap (Cancellation.flatten f)).length = right.length := by
    have same : right.flatMap (Cancellation.flatten f) = right.map Cancellation.classOf := by
      clear h
      induction right with
      | nil => rfl
      | cons t ts ih =>
        simp only [List.flatMap_cons, List.map_cons, factors t List.mem_cons_self,
          List.singleton_append, ih (fun x hx => factors x (List.mem_cons_of_mem _ hx))]
    simp [same]
  exact (((OpenMatch.holds_iff ..).mp h).length_eq.trans groundSize) ▸ bound left

theorem remainder_iff {flat} (checked : CompoundPartitions.Correct flat)
    (f : sig.ACSym) {m : UInt64} (vars : Fin m.toNat → Variable) (occ : List (Fin m.toNat))
    (used : ∀ i, i ∈ occ) (xs : List (Term sig)) (words : Words xs)
    (ground : ∀ t ∈ xs, t.Ground) (factor : ∀ t ∈ xs, Cancellation.flatten f t = [Cancellation.classOf t])
    (ident : ∀ a ∈ xs, ∀ b ∈ xs, EquivB a b → a = b) (σ : Substitution sig) :
    OpenMatch.Holds f (occ.map (fun i => .var (vars i))) xs σ ↔ Remainder flat f vars occ xs words σ := by
  cases occ with
  | nil => cases xs <;> simp [OpenMatch.Holds,OpenMatch.residual,ACRepresentation.decode,Remainder,Matches]
  | cons i is =>
    cases is with
    | nil =>
      cases xs with
      | nil => simp [OpenMatch.Holds,OpenMatch.residual,ACRepresentation.decode,Remainder]
      | cons t ts =>
        simp only [List.map_cons,List.map_nil,OpenMatch.Holds,OpenMatch.residual,ACRepresentation.decode,
          Option.some.injEq,exists_eq_left',Matches,List.mem_singleton,forall_eq,Remainder]
        constructor
        · intro same
          exact ⟨Term.rootSort_equiv same ▸ Term.rootSort_le (σ.sorted _),same⟩
        · exact And.right
    | cons j js =>
      let occ := i :: j :: js
      let loose : List (Term sig) := occ.map (fun k => .var (vars k))
      have shared : OpenMatch.Holds f loose xs σ ↔ ACResidual.Holds f σ loose xs := by
        rw [OpenMatch.holds_iff,ACResidual.holds_iff]
        have same : xs.flatMap (fun t => Cancellation.flatten f (σ.apply t)) = xs.flatMap (Cancellation.flatten f) := by
          rw [List.flatMap_def,List.flatMap_def]
          apply congrArg List.flatten
          exact List.map_congr_left fun t ht => congrArg _ ((ground t ht).apply_eq σ)
        rw [same]
      have sub (i) (hi : i ∈ words.rhs.toList) : words.decode i ∈ xs := by
        exact (congrArg (fun ls => words.decode i ∈ ls) words.represents).mp (List.mem_map_of_mem hi)
      have parts := checked f words.decode m vars occ words.rhs used (fun i h => ground _ (sub i h))
        (fun i h => factor _ (sub i h))
        (fun i hi j hj eq => words.faithful i hi j hj (ident _ (sub i hi) _ (sub j hj) eq)) σ
      rw [words.represents] at parts
      constructor
      · intro hm
        obtain ⟨rows,mem,values⟩ := parts.mp (shared.mp hm)
        refine ⟨by simpa [loose,occ] using long_enough f σ loose xs factor hm,rows,mem,fun i => ?_⟩
        obtain ⟨t,dec,eq⟩ := values i
        exact ⟨t,dec,Term.rootSort_equiv eq ▸ Term.rootSort_le (σ.sorted _),eq⟩
      · rintro ⟨_,rows,mem,values⟩
        apply shared.mpr (parts.mpr ⟨rows,mem,fun i => ?_⟩)
        obtain ⟨t,dec,_,eq⟩ := values i
        exact ⟨t,dec,eq⟩

/-- Each selected free child contributes its positional bindings to the same
substitution used to interpret the variable rows. -/
def ArmWith (agrees : Term sig → Term sig → Prop) (rest : List Nat → Prop)
    (s : Nat → Term sig) : List (Term sig) → List Nat → Prop
  | [], is => rest is
  | _ :: _, [] => False
  | p :: ps, i :: is => agrees p (s i) ∧ ArmWith agrees rest s ps is

abbrev Arm [DecidableEq sig.FreeSym] [DecidableEq sig.Atom] (rest : List Nat → Prop)
    (s : Nat → Term sig) (σ : Substitution sig) := ArmWith (FreeTreeMatch.Agrees σ) rest s

theorem arm_iff (f : sig.ACSym) (rigid loose : List (Term sig)) (s : Nat → Term sig) (is : List Nat)
    (σ : Substitution sig) (agrees : Term sig → Term sig → Prop)
    (exactChild : ∀ p ∈ rigid, ∀ i ∈ is, agrees p (s i) ↔ EquivB (σ.apply p) (s i))
    (R : List Nat → Prop) (res : ∀ js, js ⊆ is → (OpenMatch.Holds f loose (js.map s) σ ↔ R js)) :
    (∃ q, OpenMatch.branch f loose s rigid is = some q ∧ Matches q σ) ↔ ArmWith agrees R s rigid is := by
  induction rigid generalizing is with
  | nil => exact res is (fun _ a => a)
  | cons p ps ih =>
    cases is with
    | nil => simp [OpenMatch.branch,ArmWith]
    | cons i is =>
      simp only [OpenMatch.branch,Option.map_eq_some_iff,ArmWith]
      rw [exactChild p List.mem_cons_self i List.mem_cons_self,
        ← ih is (fun p hp i hi => exactChild p (List.mem_cons_of_mem _ hp) i (List.mem_cons_of_mem _ hi))
          (fun js sub => res js (fun j hj => List.mem_cons_of_mem i (sub hj)))]
      constructor
      · rintro ⟨_,⟨q,hq,rfl⟩,sol⟩
        exact ⟨sol _ List.mem_cons_self, q,hq,fun e he => sol e (List.mem_cons_of_mem _ he)⟩
      · rintro ⟨he,q,hq,m⟩
        exact ⟨_,⟨q,hq,rfl⟩,fun e hh => (List.mem_cons.mp hh).elim (fun eq => eq ▸ he) (m e)⟩

/-- Compose independently verified child matching and partition enumeration for
any closed atomic subject representation with structural identities reflecting B. -/
theorem compose {select flat} (sel : OpenMatchSelect.Correct select) (part : CompoundPartitions.Correct flat)
    [DecidableEq sig.ACSym] (f : sig.ACSym) (p t : Term sig) (rigid : List (Term sig))
    (m : UInt64) (vars : Fin m.toNat → Variable) (occ : List (Fin m.toNat)) (s : Nat → Term sig) (k n : UInt64)
    (pack : (is : List Nat) → Words (is.map s)) (len : k.toNat = rigid.length) (used : ∀ i, i ∈ occ)
    (pl : (rigid ++ occ.map (fun i => Term.var (vars i))).Perm (ACRepresentation.flatten f p))
    (sl : ((List.range n.toNat).map s).Perm (ACRepresentation.flatten f t))
    (atomic : ∀ a ∈ rigid, AtomicACPair.Atomic f a)
    (ground : ∀ i < n.toNat, (s i).Ground)
    (factor : ∀ i < n.toNat, Cancellation.flatten f (s i) = [Cancellation.classOf (s i)])
    (reflects : ∀ i < n.toNat, ∀ j < n.toNat, EquivB (s i) (s j) → s i = s j)
    (out) (ran : select k n = some out) (pending : Problem sig) (σ : Substitution sig)
    (agrees : Term sig → Term sig → Prop)
    (child : ∀ r ∈ rigid, ∀ i < n.toNat, agrees r (s i) ↔ EquivB (σ.apply r) (s i)) :
    Matches (⟨p,t⟩ :: pending) σ ↔ Matches pending σ ∧
      ∃ row ∈ OpenMatchSelect.decoded out, ArmWith agrees (fun is =>
        Remainder flat f vars occ (is.map s) (pack is) σ) s rigid row := by
  rw [OpenMatch.correct sel f p t rigid _ s k n len pl sl atomic factor out ran pending σ]
  let loose : List (Term sig) := occ.map fun i => .var (vars i)
  have joint (row) (hr : row ∈ OpenMatchSelect.decoded out) := by
    have lt (i) (hi : i ∈ row) := List.mem_range.mp ((sel.perm ran hr).mem_iff.mp hi)
    apply arm_iff f rigid loose s row σ agrees (fun p hp i hi => child p hp i (lt i hi))
      (fun is => Remainder flat f vars occ (is.map s) (pack is) σ)
    intro js sub
    have live (t) (ht : t ∈ js.map s) : ∃ i, i < n.toNat ∧ s i = t := by
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
      exact ⟨i,lt i (sub hi),rfl⟩
    apply remainder_iff part f vars occ used _ (pack js) _ _ _ σ
    · intro t ht; obtain ⟨i,hi,rfl⟩ := live t ht; exact ground i hi
    · intro t ht; obtain ⟨i,hi,rfl⟩ := live t ht; exact factor i hi
    · intro t ht u hu; obtain ⟨i,hi,rfl⟩ := live t ht; obtain ⟨j,hj,rfl⟩ := live u hu
      exact reflects i hi j hj
  constructor
  · rintro ⟨row,mem,q,hq,sol⟩
    exact ⟨fun e he => sol e (List.mem_append_right _ he),row,mem,
      (joint row mem).mp ⟨q,hq,fun e he => sol e (List.mem_append_left _ he)⟩⟩
  · rintro ⟨keep,row,mem,arm⟩
    obtain ⟨q,hq,sol⟩ := (joint row mem).mpr arm
    exact ⟨row,mem,q,hq,fun e he => (List.mem_append.mp he).elim (sol e) (keep e)⟩

def Correct (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] [DecidableEq s.FreeSym] [DecidableEq s.Atom]
    (f : s.ACSym) (p t : Term s) (rigid : List (Term s)) (m : UInt64) (vars : Fin m.toNat → Variable)
    (occ : List (Fin m.toNat)) (subject : Nat → Term s) (k n : UInt64)
    (pack : (is : List Nat) → Words (is.map subject)),
    k.toNat = rigid.length → (∀ i, i ∈ occ) →
    (rigid ++ occ.map (fun i => Term.var (vars i))).Perm (ACRepresentation.flatten f p) →
    ((List.range n.toNat).map subject).Perm (ACRepresentation.flatten f t) →
    (∀ a ∈ rigid, AtomicACPair.Atomic f a ∧ FreeTreeMatch.Pattern a) →
    (∀ i < n.toNat, FreeGround (subject i)) →
    ∀ out, select k n = some out → ∀ (pending : Problem s) (σ : Substitution s),
      Matches (⟨p,t⟩ :: pending) σ ↔ Matches pending σ ∧
        ∃ row ∈ OpenMatchSelect.decoded out,
          Arm (fun is => Remainder flat f vars occ (is.map subject) (pack is) σ) subject σ rigid row

theorem correct {select flat} (sel : OpenMatchSelect.Correct select) (part : CompoundPartitions.Correct flat) :
    Correct select flat := by
  intro sig _ _ _ f p t rigid m vars occ s k n pack len used pl sl pat ground out ran pending σ
  apply compose sel part f p t rigid m vars occ s k n pack len used pl sl (fun a h => (pat a h).1)
    (fun i h => (ground i h).ground) (fun i h => (ground i h).factor f)
    (fun i hi _ _ eq => (ground i hi).rigid _ eq) out ran pending σ (FreeTreeMatch.Agrees σ)
    (fun r hr i hi => FreeTreeMatch.agrees_iff (pat r hr).2 (ground i hi) σ)

end Tamarin.OpenMatchAdapter
