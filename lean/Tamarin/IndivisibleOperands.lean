import Tamarin.ProjectedOperands
import Tamarin.AtomicACPair

/-! Some operands of an AC system are indivisible under every sorted
substitution. A reconciled branch must use exactly one witness occurrence
in those columns. This applies to each covering selection independently
of the order of emission, renaming, and all other pending equations. -/
namespace Tamarin.IndivisibleOperands
open Homogeneous ACSystem
variable {sig : Signature} {n : Nat}

/-- Each set bit asserts a fact about the original operand after any
substitution. Unset bits carry no information. -/
def SoundMask (f : sig.ACSym) (term : Fin n → Term sig) (mask : Fin n → Bool) : Prop :=
  ∀ i, mask i = true → AtomicACPair.Atomic f (term i)

def keeps (mask : Fin n → Bool) (a : Arm) : Bool :=
  (List.finRange n).all fun i => !mask i || (a[i.val]?.map Array.size == some 1)

theorem keeps_iff (mask : Fin n → Bool) (a : Arm) :
    keeps mask a = true ↔ ∀ i, mask i = true → ∃ row, a[i.val]? = some row ∧ row.size = 1 := by
  simp [keeps]; grind

/-- Use multiplicity, even when the same witness ordinal occurs more than once. -/
theorem arm_length (gs : List (ACBasis.Vec n)) (js : List (Fin gs.length)) (i : Fin n) :
    (arm gs js)[i.val]?.map Array.size = some ((js.map (fun j => gs.get j i)).sum) := by
  simp [arm,List.length_flatMap]

theorem selection_iff (gs : List (ACBasis.Vec n)) (js : List (Fin gs.length)) (mask : Fin n → Bool) :
    keeps mask (arm gs js) = true ↔ ∀ i, mask i = true → (js.map (fun j => gs.get j i)).sum = 1 := by
  simp [keeps,arm_length]; grind

private theorem bind_mem {α β} (xs : List α) (read : α → Option β) {ys : List β}
    (ok : xs.mapM read = some ys) {x : α} (hit : x ∈ xs) :
    ∃ y ∈ ys, read x = some y := by
  induction xs generalizing ys with
  | nil => simp at hit
  | cons a xs ih =>
    cases start : read a with
    | none => simp [start] at ok
    | some b =>
      cases tail : xs.mapM read with
      | none => simp [start,tail] at ok
      | some bs =>
        obtain rfl : b :: bs = ys := by simpa [start,tail] using ok
        rcases List.mem_cons.mp hit with rfl | ht
        · exact ⟨b,List.mem_cons_self,start⟩
        · obtain ⟨y,hy,ry⟩ := ih tail ht
          exact ⟨y,List.mem_cons_of_mem b hy,ry⟩

/-- Reassociation, permutation and witness renaming cannot turn a product
of two or more witness occurrences into an indivisible operand. -/
private theorem decoded_length (f : sig.ACSym) (operand t : Term sig) (w : List Variable)
    (atomic : AtomicACPair.Atomic f operand) (read : ACRepresentation.decode f (w.map Term.var) = some t)
    (δ : Substitution sig) (ok : EquivB (δ.apply t) (δ.apply operand)) : w.length = 1 := by
  cases w with
  | nil => simp [ACRepresentation.decode] at read
  | cons a as =>
    cases as with
    | nil => rfl
    | cons b bs =>
      have h : .ac f (.var a) (ACRepresentation.fold f (.var b) (bs.map Term.var)) = t :=
        Option.some.inj read
      exact False.elim (AtomicACPair.atomic_ne_product atomic _ _ δ (h ▸ ok))

private theorem raw_column (f : sig.ACSym) (operand : Term sig) (w : UInt64 → Variable)
    (a : Arm) (i : Nat) {t : Term sig} (read : OperandAbstraction.decodeImage f w a i = some t)
    (atomic : AtomicACPair.Atomic f operand) (δ : Substitution sig)
    (ok : EquivB (δ.apply t) (δ.apply operand)) : ∃ row, a[i]? = some row ∧ row.size = 1 := by
  cases h : a[i]? with
  | none => simp [OperandAbstraction.decodeImage,h] at read
  | some row =>
    refine ⟨row,rfl,?_⟩
    cases v : row.toList.map w with
    | nil => simp [OperandAbstraction.decodeImage,h,v] at read
    | cons x xs =>
      have shape : (ACSystem.Side.mk x xs).term f = t := by
        simpa [OperandAbstraction.decodeImage,h,v] using read
      have same : ACRepresentation.decode f ((row.toList.map w).map Term.var) = some t := by
        rw [v,←shape]
        rfl
      simpa using decoded_length f operand t _ atomic same δ ok

/-- Reconciliation takes place before checking the operand mask. Every
denoting arm is therefore retained without assumptions about how its
numeric matrix was searched or which witnesses happen to be shared. -/
theorem keeps_of_reconciled {f : sig.ACSym} {rows : List ACSystem.Row}
    (fr : Frame f rows n) (θ : Substitution sig) (w : UInt64 → Variable)
    (mask : Fin n → Bool) (sound : SoundMask f (fun i => θ.image (fr.names i)) mask)
    {a : Arm} {q : Problem sig} (read : OperandAbstraction.decodeResidual fr θ w a = some q)
    {δ : Substitution sig} (sol : q.Solves δ) : keeps mask a = true := by
  apply (keeps_iff ..).mpr
  intro i marked
  obtain ⟨e,he,entry⟩ := bind_mem _ _ read (List.mem_finRange i)
  cases image : OperandAbstraction.decodeImage f w a i.val with
  | none => simp [image] at entry
  | some t =>
    obtain rfl : (⟨t,θ.image (fr.names i)⟩ : Equation sig) = e := by simpa [image] using entry
    exact raw_column f _ w a _ image (sound i marked) δ (sol _ he)

/-- The projected representation prefixes the column index to each row.
Only the suffix length counts witness occurrences. -/
def keepsTagged (mask : Fin n → Bool) (a : Arm) : Bool :=
  a.toList.all fun row => match row.toList with
    | [] => false
    | tag :: rest => if h : tag.toNat < n then !mask ⟨tag.toNat,h⟩ || rest.length == 1 else false

theorem keeps_tagArm (a : Arm) (mask : Fin a.size → Bool) (rank : UInt64 → UInt64)
    (fits : a.size < UInt64.size) :
    keepsTagged mask (AnswerProjection.tagArm rank a) = keeps mask a := by
  apply Bool.eq_iff_iff.mpr
  rw [keeps_iff]
  simp only [keepsTagged,List.all_eq_true,AnswerProjection.tagArm,Array.toList_ofFn,List.mem_ofFn]
  have same (i : Fin a.size) : i.val.toUInt64.toNat = i.val :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans i.isLt fits)
  constructor
  · intro h i m
    have hi := h _ ⟨i,rfl⟩
    refine ⟨a[i],by simp,?_⟩
    simpa [same i,i.isLt,m] using hi
  · rintro h _ ⟨i,rfl⟩
    by_cases m : mask i
    · obtain ⟨r,hr,sz⟩ := h i m
      have eq : a[i] = r := by simpa using hr
      simp [same i,i.isLt,m,eq,sz]
    · simp [same i,i.isLt,m]

theorem keepsTagged_of_reconciled (f : sig.ACSym) (term : Fin n → Term sig)
    (name : UInt64 → Variable) (order : ProjectedBindings.Order) (mask : Fin n → Bool)
    (sound : SoundMask f term mask) {a : Arm} {q : Problem sig}
    (read : ProjectedOperands.readArm term f name order a = some q)
    {δ : Substitution sig} (sol : q.Solves δ) : keepsTagged mask a = true := by
  apply List.all_eq_true.mpr
  intro row hr
  obtain ⟨e,he,entry⟩ := bind_mem _ _ read hr
  cases form : row.toList with
  | nil => simp [ProjectedOperands.readRow,form] at entry
  | cons tag rest =>
    by_cases bound : tag.toNat < n
    · let i : Fin n := ⟨tag.toNat,bound⟩
      by_cases marked : mask i = true
      · cases dec : ACRepresentation.decode f ((order.arrange (rest.map name)).map Term.var) with
        | none => simp [ProjectedOperands.readRow,form,bound,dec] at entry
        | some t =>
          obtain rfl : (⟨t,term i⟩ : Equation sig) = e := by
            simpa [ProjectedOperands.readRow,form,bound,i,dec] using entry
          have len := decoded_length f (term i) t _ (sound i marked) dec δ (sol _ he)
          rw [(order.perm _).length_eq,List.length_map] at len
          simp [bound,marked,i,len]
      · simp [i] at marked
        simp [bound,marked]
    · simp [ProjectedOperands.readRow,form,bound] at entry

/-- Filtering a factored worklist preserves its full denotation, including
already-bound variables and arbitrary other pending equations. Only an arm
with a single substitution solving every residual can witness a denotation. -/
theorem filter_denotes (family : List Arm) (read : Arm → Option (Problem sig))
    (keep : Arm → Bool)
    (required : ∀ a ∈ family, ∀ q, read a = some q → ∀ δ, q.Solves δ → keep a = true)
    (pending : Problem sig) (obs : Variable → Prop) (bindings ρ : Substitution sig) :
    (∃ a ∈ family.filter keep, ∃ q, read a = some q ∧ Residual.Denotes obs (q ++ pending) bindings ρ) ↔
    ∃ a ∈ family, ∃ q, read a = some q ∧ Residual.Denotes obs (q ++ pending) bindings ρ := by
  constructor
  · rintro ⟨a,ha,q,hq,den⟩
    exact ⟨a,(List.mem_filter.mp ha).1,q,hq,den⟩
  · rintro ⟨a,ha,q,hq,den⟩
    obtain ⟨δ,sol,agrees⟩ := den
    exact ⟨a,List.mem_filter.mpr ⟨ha,required a ha q hq δ (fun e he => sol e (List.mem_append_left _ he))⟩,
      q,hq,δ,sol,agrees⟩

/-- In particular, a sound residual solver contributes exactly the same
ordered substitution list after masking. Any CompleteSet property for the
unfiltered factored family transfers along this equality. -/
theorem filter_answers (family : List Arm) (read : Arm → Option (Problem sig))
    (keep : Arm → Bool)
    (required : ∀ a ∈ family, ∀ q, read a = some q → ∀ δ, q.Solves δ → keep a = true)
    (pending : Problem sig) (solve : Problem sig → List (Substitution sig))
    (sound : ∀ a ∈ family, ∀ q, read a = some q → ∀ δ ∈ solve (q ++ pending), (q ++ pending).Solves δ) :
    let answers := fun a => (read a).toList.flatMap (fun q => solve (q ++ pending))
    (family.filter keep).flatMap answers = family.flatMap answers := by
  dsimp only
  induction family with
  | nil => rfl
  | cons a rest ih =>
    have tail := ih (fun b hb => required b (List.mem_cons_of_mem _ hb))
                    (fun b hb => sound b (List.mem_cons_of_mem _ hb))
    cases k : keep a with
    | true => simp [k,tail]
    | false =>
      cases h : read a with
      | none => simp [k,h,tail]
      | some q =>
        have empty : solve (q ++ pending) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro δ hd
          have sol := sound a List.mem_cons_self q h δ hd
          exact Bool.noConfusion (k.symm.trans (required a List.mem_cons_self q h δ
            (fun e he => sol e (List.mem_append_left _ he))))
        simp [k,h,tail,empty]

end Tamarin.IndivisibleOperands
