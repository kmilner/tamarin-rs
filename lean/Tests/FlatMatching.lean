import TamarinCI

namespace Tamarin.FlatMatching.Tests
open FlatMatchSearch

-- Distinct variables enumerate both partitions; repeated occurrences share a row.
example : (solve 2 [0, 1] [] ([11, 12] : List UInt64)).length = 2 := by decide
example : solve 1 [0, 0] [] ([11, 12] : List UInt64) = [] := by decide
example : solve 1 [0, 0] [] ([11, 11] : List UInt64) = [[[11]]] := by decide
example : (solve 2 [0, 0, 1] [] ([11, 11, 12, 12] : List UInt64)).length = 2 := by decide
example : (solve 3 [0, 1, 2] [] ([11, 12, 13] : List UInt64)).length = 6 := by decide
example : solve 2 [0, 1] [11] ([11, 12] : List UInt64) = [] := by decide

-- Numeric export inputs also include out-of-range IDs and unobserved rows.
-- Preserve the full fixed row denotation even outside Rust's admitted tables.
example : [[11, 12]] ∈ RuntimeCandidate.flatMatch 1 [0, 1] [] [11, 12] := by decide
example : [[11], [11, 12]] ∈ RuntimeCandidate.flatMatch 2 [0] [12] [11, 12] := by decide

-- No unit: every variable must receive a nonempty product.
example : solve 2 [0, 1] [] ([11] : List UInt64) = [] := by decide

-- The fixed contract rejects vacuous success/failure implementations.
example : ¬ (FlatMatchBackend.mk (fun _ _ _ _ => [])).Correct := by
  intro h
  have hm := (h 1 [0] [] [11] [[11]]).mpr
    ⟨rfl, by simp, by simp [expand]⟩
  cases hm

-- Full sorted semantic coverage is proved independently of executable examples.
example {sig : Signature} [DecidableEq sig.Atom] (f : sig.ACSym) {n : Nat}
    (vars : Fin n → Variable) (occ : List (Fin n)) (tail rhs : List sig.Atom)
    (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (hi : Function.Injective vars) (ho : ∀ i, i ∈ occ)
    (hq : queryLeaves vars occ tail ≠ []) (hr : rhs ≠ []) :
    Matching.Complete [⟨pattern f (queryLeaves vars occ tail), FlatAC.term f rhs⟩]
      (fun _ => True) (answers f vars occ tail rhs hv hs) :=
  complete f vars occ tail rhs hv hs hi ho hq hr

-- No equation identifies different AC roots when merging shared bindings.
example (a b : Term Pairing.signature) : ¬ EquivB (sig := Pairing.signature) (.ac 0 a b) (.ac 1 a b) := by
  intro h
  have he := h.head_eq
  cases he

-- The proof for all branch joins is independent of the flat search algorithm.
example {sig : Signature} (p q : Problem sig) (left right : List (Substitution sig))
    (hl : Matching.Complete p (fun _ => True) left)
    (hr : Matching.Complete q (fun _ => True) right) :
    Matching.Complete (p ++ q) (fun _ => True) (Matching.join p q left right) :=
  Matching.join_complete p q left right hl hr

end Tamarin.FlatMatching.Tests
