import Std

/-! Deliberately simple complete reference search. Candidate optimizations may
replace this search, but CI fixes its semantic matching obligations separately.
Rows are indexed by request-local variable IDs, never by raw Rust LVar.idx.
-/
namespace Tamarin.FlatMatchSearch

def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => let rest := sublists as; rest ++ rest.map (a :: ·)

def choices {α : Type} (rhs : List α) : Nat → List (List (List α))
  | 0 => [[]]
  | n + 1 => (sublists rhs).filter (fun xs => !xs.isEmpty) |>.flatMap
      (fun row => (choices rhs n).map (row :: ·))

def expand {α : Type} (rows : List (List α)) (occurrences : List Nat) : List α :=
  occurrences.flatMap (fun i => rows[i]?.getD [])

def solve {α : Type} [DecidableEq α] (n : Nat) (occurrences : List Nat)
    (tail rhs : List α) : List (List (List α)) :=
  ((choices rhs n).filter (fun rows => decide ((expand rows occurrences ++ tail).Perm rhs))).eraseDups

end Tamarin.FlatMatchSearch
