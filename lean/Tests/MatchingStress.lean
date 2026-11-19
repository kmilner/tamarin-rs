import TamarinCI

/-! Exhaustive finite-model test of the flat matching contract. The oracle
represents a free commutative semigroup on two generators by pairs of natural
numbers with positive sum. It enumerates multiplicities directly. It does
not call the reference search, list permutation, or AC term constructors. -/
namespace Tamarin.MatchingStress

/-- For every accepted candidate and arbitrary word tables, a row vector in
the specified representation occurs exactly when it conserves each atom.
This characterization applies beyond the finite test alphabet below. -/
theorem counted_iff (backend : FlatMatchBackend) (h : backend.Correct)
    (n : Nat) (occ : List Nat) (tail rhs : List UInt64) (rows : List (List UInt64))
    (size : rows.length = n) (shape : ∀ row ∈ rows, row ≠ [] ∧ row.Sublist rhs) :
    rows ∈ backend.run n occ tail rhs ↔ ∀ atom,
      (occ.map (fun i => (rows[i]?.getD []).count atom)).sum + tail.count atom = rhs.count atom := by
  simp only [h n occ tail rhs rows, size, true_and, List.perm_iff_count,
    List.count_append, FlatMatchSearch.expand, List.count_flatMap, Function.comp_def]
  exact ⟨And.right, fun h => ⟨shape, h⟩⟩

-- A one-atom table can represent the request [0,0], whereas a global
-- injection of UInt64 into Unit is impossible.
private def oneAtom : IdentityTable Unit := ⟨[()], by decide⟩

example : ¬ ∃ f : UInt64 → Unit, Function.Injective f := by
  rintro ⟨f, hf⟩
  have bad : (0 : UInt64) = 1 := hf (Subsingleton.elim (f 0) (f 1))
  contradiction

example (rows : List (List Unit)) :
    rows ∈ (RuntimeCandidate.flatMatcher.run 1 [0, 0] [] [0, 0]).map
      (List.map (List.map (oneAtom.wordAtom ()))) ↔
    rows ∈ FlatMatchSearch.solve 1 [0, 0] [] [(), ()] := by
  apply FlatMatchCandidateProofs.correct.decoded_rows (oneAtom.wordAtom ()) oneAtom.atomWord
  intro id hid
  apply oneAtom.live_word_roundtrip
  simp at hid
  subst id
  decide

-- Checking only subject IDs would miss collisions with a literal in the tail.
-- Word 1 in the tail prevents a match. Aliasing both words manufactures one.
example : FlatMatchSearch.solve 1 [0] [1] ([0, 0] : List UInt64) = [] := by decide
example : FlatMatchSearch.solve 1 [0] [()] [(), ()] = [[[()]]] := by decide

-- Dropping all but the first answer always preserves row soundness. For a
-- two-variable query, the fixed contract individually requires both images.
private def firstOnly : FlatMatchBackend where
  run := fun n occ tail rhs => (RuntimeCandidate.flatMatcher.run n occ tail rhs).take 1

example : ¬ firstOnly.Correct := by
  intro h
  have left := (h 2 [0, 1] [] [3, 7] [[3], [7]]).mpr (by decide)
  have right := (h 2 [0, 1] [] [3, 7] [[7], [3]]).mpr (by decide)
  have cannot : ¬ ([[3], [7]] ∈ firstOnly.run 2 [0, 1] [] [3, 7] ∧
    [[7], [3]] ∈ firstOnly.run 2 [0, 1] [] [3, 7]) := by decide
  exact cannot ⟨left, right⟩

-- Counting each variable only once can prune a sound assignment whose
-- image fills two separate occurrences in the subject.
private def countOnce : FlatMatchBackend where
  run := fun n occ tail rhs => (RuntimeCandidate.flatMatcher.run n occ tail rhs).filter
    (fun rows => (FlatMatchSearch.expand rows occ.eraseDups).length + tail.length == rhs.length)

example : ¬ countOnce.Correct := by
  intro h
  have kept := (h 1 [0, 0] [] [0, 1, 0, 1] [[0, 1]]).mpr (by decide)
  exact (by decide : [[0, 1]] ∉ countOnce.run 1 [0, 0] [] [0, 1, 0, 1]) kept

-- The wire contract observes both subsequences of the interleaved input.
-- Rust canonicalizes their AC images after decoding.
example : [[0, 1]] ∈ RuntimeCandidate.flatMatcher.run 1 [0, 0] [] [0, 1, 0, 1] ∧
    [[1, 0]] ∈ RuntimeCandidate.flatMatcher.run 1 [0, 0] [] [0, 1, 0, 1] := by decide

private def high : UInt64 := 18446744073709551615
private abbrev Bag := Nat × Nat

private def words (alphabet : List UInt64) : Nat → List (List UInt64)
  | 0 => [[]]
  | len + 1 => (words alphabet len).flatMap fun xs => alphabet.map (· :: xs)

private def bag (xs : List UInt64) : Bag := (xs.count 0, xs.count high)

private def images (subject : Bag) : List Bag :=
  (List.range (subject.1 + 1)).flatMap fun a =>
    ((List.range (subject.2 + 1)).filter (fun b => a + b > 0)).map fun b => (a, b)

private def assignments (domain : List Bag) : Nat → List (List Bag)
  | 0 => [[]]
  | n + 1 => (assignments domain n).flatMap fun rows => domain.map (· :: rows)

private def instantiate (rows : List Bag) (occ : List UInt64) (tail : Bag) : Bag :=
  (rows.zipIdx).foldl (fun (acc : Bag) (row, index) =>
    let k := occ.count (UInt64.ofNat index)
    (acc.1 + k * row.1, acc.2 + k * row.2)) tail

def run : IO Unit := do
  let alphabet := [0, high]
  let mut queries := 0
  let mut satisfying := 0
  let mut unsatisfiable := 0
  let mut ambiguous := 0
  for len in [2, 3, 4] do
    for subject in words alphabet len do
      let target := bag subject
      for n in [0, 1, 2, 3] do
        let ids := (List.range n).map UInt64.ofNat
        let valuations := assignments (images target) n
        for k in List.range 5 do
          for occ in words ids k do
            if !ids.all (fun id => occ.contains id) then continue
            for t in List.range 3 do
              if k + t < 2 then continue
              for tail in words alphabet t do
                let expected := valuations.filter fun vs => instantiate vs occ (bag tail) == target
                let out := Executable.flatACMatch (UInt64.ofNat n) occ.toArray tail.toArray subject.toArray
                let rows := out.toList.map (fun arm => arm.toList.map Array.toList)
                let actual := rows.map (List.map bag)
                let shape := rows.all fun arm => arm.length == n && arm.all fun row =>
                  !row.isEmpty && row.all (fun a => alphabet.contains a)
                unless shape && expected.all actual.contains && actual.all expected.contains do
                  throw (IO.userError s!"n={n} occurrences={occ} tail={tail} subject={subject}\nexpected {expected}\nactual {rows}")
                queries := queries + 1
                satisfying := satisfying + expected.length
                if expected.isEmpty then unsatisfiable := unsatisfiable + 1
                if expected.length > 1 then ambiguous := ambiguous + 1
  IO.println s!"{queries} queries, {satisfying} distinct assignments summed over queries, {unsatisfiable} unsatisfiable, {ambiguous} with multiple answers"
  unless queries == 13412 && ambiguous > 0 && unsatisfiable > 0 do throw (IO.userError "incomplete stress matrix")

end Tamarin.MatchingStress

def main : IO Unit := Tamarin.MatchingStress.run
