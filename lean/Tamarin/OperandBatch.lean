import Tamarin.OperandAbstraction
import Tamarin.OperandUnification

/-! A flat residual batch contains column IDs, not AC terms. A column can stand for
any sorted term, including a shared compound containing variables. The only term
identity assumption is that looking up each supplied ID recovers that operand. -/
namespace Tamarin.OperandBatch
open ACSystem Homogeneous
variable {sig : Signature} {n : Nat} (base : Nat)

/-- AC has no empty product. A singleton side also represents an equation
between two existing operands that was absorbed into the batch. -/
structure Side (n : Nat) where
  first : Fin n
  rest : List (Fin n)

def Side.ids (s : Side n) := s.first :: s.rest

abbrev Row (n : Nat) := Side n × Side n

def column (f : sig.ACSym) (i : Fin n) : Variable := ⟨base + i.val, sig.acSort f⟩

def Side.abstract (s : Side n) (f : sig.ACSym) : ACSystem.Side :=
  ⟨column base f s.first, s.rest.map (column base f)⟩

def abstractRows (f : sig.ACSym) (rows : List (Row n)) : List ACSystem.Row :=
  rows.map fun (l,r) => ⟨l.abstract base f, r.abstract base f⟩

def Side.words (s : Side n) : Array UInt64 := (s.ids.map (fun i => i.val.toUInt64)).toArray

def sides (rows : List (Row n)) := (rows.flatMap fun (l,r) => [l.words, r.words]).toArray

def used (rows : List (Row n)) := rows.flatMap fun (l,r) => l.ids ++ r.ids

theorem abstract_vars (f : sig.ACSym) (rows : List (Row n)) :
    variables (abstractRows base f rows) = (used rows).map (column base f) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨l,r⟩
    simpa only [abstractRows, variables, used, List.map_cons, List.flatMap_cons,
      List.map_append, Side.ids, ACSystem.Side.vars, Side.abstract] using
      congrArg ((l.ids.map (column base f) ++ r.ids.map (column base f)) ++ ·) ih

def frame (f : sig.ACSym) (rows : List (Row n)) (allUsed : ∀ i, i ∈ used rows) :
    Frame f (abstractRows base f rows) n where
  names := column base f
  index v := if h : v.id-base < n then some ⟨v.id-base,h⟩ else none
  inverse i := by simp [column, i.isLt]
  live v hv := by
    rw [abstract_vars] at hv
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hv
    exact ⟨i,hi⟩
  used i := by rw [abstract_vars]; exact List.mem_map_of_mem (allUsed i)
  sorts _ := rfl

def operands (f : sig.ACSym) (term : Fin n → Term sig)
    (typed : ∀ i, HasSort (term i) (sig.acSort f)) : Substitution sig where
  image v := if h : base ≤ v.id ∧ v.id-base < n ∧ v.sort = sig.acSort f then term ⟨v.id-base,h.2.1⟩ else .var v
  support := List.ofFn (column (n := n) base f)
  outside v absent := by
    split
    · next h =>
      exfalso
      exact absent (List.mem_ofFn.mpr ⟨⟨v.id-base,h.2.1⟩, by
        cases v; simp only [column, Variable.mk.injEq]; exact ⟨Nat.add_sub_of_le h.1, h.2.2.symm⟩⟩)
    · rfl
  sorted v := by
    split
    · next h => exact Eq.mp (congrArg (HasSort (term ⟨v.id-base,h.2.1⟩)) h.2.2.symm) (typed _)
    · exact .var v

theorem operand_at (f : sig.ACSym) (term : Fin n → Term sig) (typed) (i : Fin n) :
    (operands base f term typed).image (column base f i) = term i := by simp [operands, column, i.isLt]

private theorem same_count {w : UInt64} (f : sig.ACSym) (xs : List (Fin w.toNat)) (i : Fin w.toNat) :
    (xs.map (fun j => j.val.toUInt64)).count i.val.toUInt64 =
      (xs.map (column base f)).count (column base f i) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    have eq : j.val.toUInt64 = i.val.toUInt64 ↔ column base f j = column base f i := by
      have h (a : Fin w.toNat) : a.val.toUInt64.toNat = a.val :=
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans a.isLt w.toNat_lt_size)
      constructor
      · intro e; exact congrArg (column base f) (Fin.ext ((h j).symm.trans ((congrArg UInt64.toNat e).trans (h i))))
      · intro e; exact congrArg Nat.toUInt64 (Nat.add_left_cancel (show base + j.val = base + i.val from congrArg Variable.id e))
    simp only [List.map_cons, List.count_cons, beq_iff_eq, eq, ih]

private theorem counts_side {w : UInt64} (f : sig.ACSym) (s : Side w.toNat) :
    GraphMatrix.counts w s.words.toList = sideWords (column (n := w.toNat) base f) (s.abstract base f) := by
  unfold GraphMatrix.counts sideWords
  apply congrArg Array.ofFn
  funext i
  simpa [Side.words, Side.abstract, Side.ids, ACSystem.Side.vars] using congrArg Nat.toUInt64 (same_count base f s.ids i)

theorem counts_rows {w : UInt64} (f : sig.ACSym) (rows : List (Row w.toNat)) :
    ((sides rows).map (fun a => GraphMatrix.counts w a.toList)).toList =
      matrixWords (column (n := w.toNat) base f) (abstractRows base f rows) := by
  induction rows with
  | nil => simp [sides, abstractRows, matrixWords]
  | cons row rows ih =>
    rcases row with ⟨l,r⟩
    simp only [sides, Array.toList_map] at ih ⊢
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons,
      abstractRows, matrixWords, counts_side base f, ih]

/-- The referenced operands are the factors obtained by flattening the original term
at this operator. Permutation admits arbitrary storage and traversal orders. -/
def Side.Represents [DecidableEq sig.ACSym] (s : Side n) (f : sig.ACSym)
    (term : Fin n → Term sig) (t : Term sig) : Prop :=
  (s.ids.map term).Perm (ACRepresentation.flatten f t)

inductive Represents [DecidableEq sig.ACSym] (f : sig.ACSym) (term : Fin n → Term sig) :
    List (Row n) → Problem sig → Prop where
  | nil : Represents f term [] []
  | cons {l r : Side n} {e : Equation sig} {rs es} :
      l.Represents f term e.lhs → r.Represents f term e.rhs →
      Represents f term rs es → Represents f term ((l,r)::rs) (e::es)

private theorem instantiate (f : sig.ACSym) (term : Fin n → Term sig) (typed) (s : Side n) :
    (operands base f term typed).apply ((s.abstract base f).term f) =
      ACRepresentation.fold f (term s.first) (s.rest.map term) := by
  rcases s with ⟨i,is⟩
  induction is generalizing i with
  | nil => exact operand_at base f term typed i
  | cons j js ih =>
    change Term.ac f ((operands base f term typed).image (column base f i)) _ = .ac f (term i) _
    rw [operand_at]
    exact congrArg _ (ih j)

private theorem represents_side [DecidableEq sig.ACSym] (f : sig.ACSym)
    (term : Fin n → Term sig) (typed) {s : Side n} {t : Term sig}
    (h : s.Represents f term t) : EquivB ((operands base f term typed).apply ((s.abstract base f).term f)) t := by
  obtain ⟨u, hu, equiv⟩ := ACRepresentation.flatten_correct f t
  exact (ACRepresentation.decode_perm f h _ _ (by rw [instantiate]; rfl) hu).trans equiv

/-- Substituting the compound operands back into the counted equations preserves every
solution of the selected equations, with arbitrary remaining work and retained bindings. -/
theorem selected_iff [DecidableEq sig.ACSym] (f : sig.ACSym) (term : Fin n → Term sig) (typed)
    {rows : List (Row n)} {selected} (layout : Represents f term rows selected) (δ : Substitution sig) :
    selected.Solves δ ↔ ((problem f (abstractRows base f rows)).substitute (operands base f term typed)).Solves δ := by
  induction layout with
  | nil => rfl
  | cons left right _ ih =>
    have hl := (represents_side base f term typed left).subst δ.image
    have hr := (represents_side base f term typed right).subst δ.image
    change (∀ eq ∈ _::_, _) ↔ (∀ eq ∈ _ :: _, _)
    simp only [List.mem_cons, forall_eq_or_imp]
    exact and_congr ⟨fun sol => hl.trans (sol.trans hr.symm), fun sol => hl.symm.trans (sol.trans hr)⟩ ih

/-- The matrix solver reads the exact multiplicity of every column in every
side. The word bound follows from admission of the actual operand packet. -/
theorem read_matrix {w : UInt64} (f : sig.ACSym) (rows : List (Row w.toNat))
    (allUsed : ∀ i, i ∈ used rows) (admitted : OperandCounts.Admitted w (sides rows)) :
    readRows w.toNat (OperandUnification.matrix w (sides rows)).toList =
      some ((abstractRows base f rows).map (ACBasis.encode (column (n := w.toNat) base f))) := by
  rw [OperandUnification.matrix, counts_rows base f]
  apply read_matrixWords _ _ (frame base f rows allUsed).live
  intro row hr s hs i
  obtain ⟨⟨l,r⟩, hrow, rfl⟩ := List.mem_map.mp hr
  have size (a : Side w.toNat) (mem : a.words ∈ sides rows) :
      (a.abstract base f).vars.length < 2^64 := by
    have bound := (admitted.2.2.2.2 _ mem).2.1
    simpa [Side.words, Side.ids, Side.abstract, ACSystem.Side.vars] using bound
  have mem : ∀ t ∈ [l.words,r.words], t ∈ sides rows := by
    intro t ht
    exact List.mem_toArray.mpr (List.mem_flatMap.mpr ⟨(l,r), hrow,ht⟩)
  apply Nat.lt_of_le_of_lt List.count_le_length
  rcases List.mem_cons.mp hs with hs | hs
  · subst s; exact size l (mem _ (by simp))
  · obtain rfl := List.mem_singleton.mp hs
    exact size r (mem _ (by simp))

/-- A completed compound-operand call splits the original worklist into the
returned branches, including pending equations and accumulated bindings.
This takes a faithful lookup of term occurrences. Neither the coefficient
matrix nor the equivalent instantiated problem is assumed from the caller. -/
theorem nested {run solve} (bridge : OperandUnification.Refines run solve)
    (kernel : OperandAbstraction.NestedLifting solve) [DecidableEq sig.ACSym]
    (f : sig.ACSym) {width : UInt64} (rows : List (Row width.toNat)) (allUsed : ∀ i, i ∈ used rows)
    (term : Fin width.toNat → Term sig) (typed : ∀ i, HasSort (term i) (sig.acSort f))
    {selected : Problem sig} (layout : Represents f term rows selected)
    (pending original : Problem sig) (partition : original.Perm (selected ++ pending))
    {out} (ran : run width (sides rows) = some out)
    (observe : Variable → Prop) (bindings : Substitution sig) (witness : UInt64 → Variable)
    (inj : Function.Injective witness) (sorts : ∀ j, (witness j).sort = sig.acSort f)
    (columnsFresh : ∀ j, witness j ∉ variables (abstractRows base f rows))
    (operandsFresh : ∀ j i, ¬ (term i).Occurs (witness j))
    (pendingFresh : ∀ j, ¬ pending.Occurs (witness j))
    (retained : ∀ j x, observe x → ¬ (bindings.image x).Occurs (witness j)) :
    let decode := OperandAbstraction.decodeResidual (frame base f rows allUsed) (operands base f term typed) witness
    (∀ a ∈ out.toList, (decode a).isSome) ∧
    ∀ ρ, Residual.Denotes observe original bindings ρ ↔
      ∃ a ∈ out.toList, ∃ q, decode a = some q ∧ Residual.Denotes observe (q ++ pending) bindings ρ := by
  obtain ⟨adm,_,returned⟩ := (bridge ..).mp ran
  have split := kernel f _ width (frame base f rows allUsed) _ (read_matrix base f rows allUsed adm) out returned
    (operands base f term typed) pending observe bindings witness inj sorts columnsFresh (by
      rintro j (⟨v,hv,occ⟩ | occ)
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
        exact operandsFresh j i (by simpa only [frame,operand_at] using occ)
      · exact pendingFresh j occ) retained
  refine ⟨split.1, fun ρ => ?_⟩
  rw [Residual.perm observe partition]
  apply Iff.trans _ (split.2 ρ)
  apply Residual.equivalent
  intro δ
  simp only [Problem.Solves, List.mem_append, or_imp, forall_and]
  exact and_congr (selected_iff base f term typed layout δ) Iff.rfl

end Tamarin.OperandBatch
