import TamarinRuntime.ResidualVariable
import Tamarin.Residual
import Tamarin.WholeProblem
import Tamarin.VariablePermutation

namespace Tamarin.ResidualVariable
open WholeProblem Residual
variable {sig : Signature}

/-- IDs identify the full variables live in this pair. The inventory can be in
any order, including the order produced by a flattened or sorted AC node. -/
def Correct (solve : Kernel) : Prop :=
  ∀ {s : Signature} (v : Variable) (t : Term s), HasSort t t.rootSort →
    ∀ (put : Variable → UInt64), (∀ w ∈ t.variables, put w = put v → w = v) →
    ∀ (ids : Array UInt64), ids.toList.Perm (t.variables.map put) →
    ∀ right : Bool,
    let action := solve right (put v) (sortWord v.sort) (kind t) (sortWord t.rootSort) ids
    if right then Justified action t (.var v) else Justified action (.var v) t

/-- Invalid wire records cannot be interpreted as a clash or as an answer.
The two identities of the same root variable must also agree on their sort. -/
def Malformed (key keySort : UInt64) (k : UInt8) (valueSort : UInt64) (ids : Array UInt64) : Prop :=
  keySort > 4 ∨ valueSort > 4 ∨ k > 4 ∨
  (k = 0 ∧ (ids.size ≠ 1 ∨ (key ∈ ids ∧ keySort ≠ valueSort))) ∨
  (k = 1 ∧ ids.size ≠ 0)

def RejectsMalformed (solve : Kernel) : Prop :=
  ∀ right key keySort k valueSort ids, Malformed key keySort k valueSort ids →
    solve right key keySort k valueSort ids = 255

theorem run_rejectsMalformed : RejectsMalformed run := by
  intro right key ks k vs ids bad
  unfold run
  split
  · next valid =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
    obtain ⟨⟨⟨kv,vv⟩,tv⟩,shapeOk⟩ := valid
    rcases bad with h | h | h | ⟨r,h | ⟨used,mismatch⟩⟩ | ⟨r,h⟩
    · exact False.elim ((UInt64.not_lt.mpr kv) h)
    · exact False.elim ((UInt64.not_lt.mpr vv) h)
    · exact False.elim ((UInt8.not_lt.mpr tv) h)
    · simp [shape, r, h] at shapeOk
    · simp [r,used,mismatch]
    · simp [shape, r, Array.isEmpty, h] at shapeOk
  · rfl

private theorem swap_justified {a b : Term sig} {code} (h : Justified code a b) :
    Justified (swap code) b a := by
  cases h with
  | defer => exact .defer ..
  | clash h => exact .clash (fun σ e => h σ e.symm)
  | discard h => exact .discard h.symm
  | bindLeft v _ h o => exact .bindRight v _ h o
  | bindRight v _ h o => exact .bindLeft v _ h o
  | positional => exact .positional ..
  | orientations => exact .orientations ..

private theorem sort_bound (s : SortId) : sortWord s ≤ 4 := by cases s <;> decide
private theorem kind_bound (t : Term sig) : kind t ≤ 4 := by cases t <;> simp [kind]
private theorem fits (a b : SortId) : Whole.subsort (sortWord a) (sortWord b) = Subsort.check a b := by
  cases a <;> cases b <;> rfl

theorem run_correct : Correct run := by
  intro s v t typed put faithful ids layout right
  have occurs : ids.contains (put v) = true ↔ t.Occurs v := by
    rw [Array.contains_iff_mem, ← Array.mem_toList_iff, layout.mem_iff, List.mem_map]
    constructor
    · rintro ⟨w, hw, eq⟩
      exact (t.mem_variables v).mp (faithful w hw eq ▸ hw)
    · intro h
      exact ⟨v, (t.mem_variables v).mpr h, rfl⟩
  have shapeOk : shape (kind t) ids = true := by
    have len := layout.length_eq
    cases t with
    | var w =>
      change (ids.size == 1) = true
      exact beq_iff_eq.mpr (by simpa only [Term.variables, List.map_cons, List.map_nil,
        List.length_cons, List.length_nil, Array.length_toList] using len)
    | atom a =>
      change ids.isEmpty = true
      simpa [Array.isEmpty, Term.variables] using len
    | _ => rfl
  simp only [run, sort_bound, kind_bound, decide_true, shapeOk, Bool.true_and, ite_true]
  by_cases isVar : ∃ w, t = Term.var w
  · obtain ⟨w,rfl⟩ := isVar
    have mem : ids.contains (put v) = true ↔ v = w := occurs
    by_cases eq : v = w
    · subst w
      have hit := mem.mpr rfl
      simp only [kind, Term.rootSort, BEq.rfl, Bool.true_and, hit, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ite_false]
      cases right <;> exact Justified.discard (EquivB.refl _)
    · have miss : ids.contains (put v) = false := Bool.eq_false_iff.mpr (fun h => eq (mem.mp h))
      have h := (step_correct (s := s) (Input.vars v w) false (fun a => False.elim (eq (Term.var.inj a))) (by simp)).1
      simp only [kind, Term.rootSort, BEq.rfl, Bool.true_and, miss, Bool.false_and, Bool.false_eq_true, ite_false, fits, Bool.not_true]
      cases right
      · exact h
      · exact swap_justified h
  · have rigid : kind t ≠ 0 := by cases t <;> simp_all [kind]
    have h := (step_correct (Input.left v t rigid typed _ occurs) false
      (fun e => False.elim (isVar ⟨v,e.symm⟩)) (by simp)).1
    have hk : (kind t == 0) = false := by simpa using rigid
    simp only [hk,Bool.false_and,Bool.false_eq_true,ite_false,Bool.not_false,Bool.true_and,fits]
    cases right
    · exact h
    · exact swap_justified h

end Tamarin.ResidualVariable
