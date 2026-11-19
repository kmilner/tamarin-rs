import Tamarin.ACSpanWhole

open Tamarin Tamarin.ACBasis Tamarin.ACBasis.SpanCertificate

private def make {n : Nat} (z : Fin n → Int) : Row n :=
  Row.ofWeights (fun i => (z i).toNat) (fun i => (-(z i)).toNat)

private abbrev Point := Int × Int
private def asRow (p : Point) : Row 2 := make (fun i => if i.val = 0 then p.1 else p.2)
private def det (a b : Point) := a.1*b.2 - a.2*b.1

-- The determinant gives an independent decision in dimension two.
private def expected (a b t : Point) := det a b != 0 || t == (0,0) ||
  ((a != (0,0) || b != (0,0)) && det a t == 0 && det b t == 0)

private def orientations : List Point :=
  ([-2,0,2] : List Int).flatMap fun a => ([-3,0,3] : List Int).map (a,·)

private def diagonal (n i : Nat) : Row n := make (fun j => if j.val = i then 1 else 0)
private def fractional (a b c : Int) : Row 4 := make (fun i => #[a,b,c,0][i.val]!)
private def wideGoal : Row 96 := make (fun i => if i.val % 3 = 1 then -1 else 2)

private def x : Whole.Tree := .leaf 0 0 2
private def z : Whole.Tree := .leaf 0 1 2
private def first : Whole.Tree := .app 4 2 [x,z]
private def second : Whole.Tree := .app 4 2 [x,z,z]
private def observations := [(first,first),(second,second)]

private theorem canonical_observations : ACSpanOverlap.canonicalPairs observations = observations := by
  have a : Whole.canonical first = first := by
    change Whole.Tree.app 4 2 (Whole.order [x,z]) = _
    rw [Whole.order,List.mergeSort_of_pairwise (by decide +kernel)]
    rfl
  have b : Whole.canonical second = second := by
    change Whole.Tree.app 4 2 (Whole.order [x,z,z]) = _
    rw [Whole.order,List.mergeSort_of_pairwise (by decide +kernel)]
    rfl
  simp [observations,ACSpanOverlap.canonicalPairs,a,b]

-- The four open columns refer to different row substitutions. Twice the
-- first observed equation minus the second forces the two images of x equal.
example : ACSpanWhole.Admitted observations x x := by
  unfold ACSpanWhole.Admitted
  rw [canonical_observations]
  refine ⟨by decide +kernel,.inl ⟨2,by decide +kernel,?_,?_⟩⟩
  · apply within_of_bound _ _ 4096
    · decide +kernel
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · decide +kernel
      · rcases List.mem_cons.mp hr with rfl | hr
        · decide +kernel
        · obtain rfl := List.mem_singleton.mp hr
          decide +kernel
    · exact four_magnitudes _ (by decide +kernel)
  · exact ⟨⟨1,[2,-1]⟩,(check_iff ..).mp (by decide +kernel)⟩

def main : IO Unit := do
  for a in orientations do
    for b in orientations do
      for tx in ([-3,-1,0,1,3] : List Int) do
        for ty in ([-2,0,2] : List Int) do
          let q := (tx,ty)
          let rs := [asRow a,asRow b]
          let result := run rs (asRow q)
          unless result.isSome == expected a b q do throw <| IO.userError s!"determinant disagreement on {a},{b},{q}"
          if let some c := result then
            unless check rs (asRow q) c do throw <| IO.userError "invalid span certificate"
  let a := fractional 2 0 0
  let b := fractional 0 (-3) 0
  let c := fractional 1 2 6
  let q := fractional 1 0 1
  for rs in [[a,b,c],[c,a,b],[b,c,a],[a,a,b,c,b]] do
    let some witness := run rs q | throw <| IO.userError "missed three-dimensional span"
    unless check rs q witness && witness.scale.natAbs > 1 do throw <| IO.userError "incorrect rational combination"
    unless (run rs (diagonal 4 3)).isNone do throw <| IO.userError "spurious consequence in a free coordinate"
  let pivots := (List.range 64).map (diagonal 96)
  unless (run pivots (diagonal 96 63)).isSome do throw <| IO.userError "missing rank-64 consequence"
  unless (run pivots wideGoal).isNone do throw <| IO.userError "spurious rank-64 consequence"
  -- Optimizers can extend the coefficient range whenever they can certify the result.
  let huge := [asRow (2^256,0)]
  let target := asRow (1,0)
  if let some w := run huge target then
    unless check huge target w do throw <| IO.userError "invalid wide coefficient certificate"
  IO.println "Checked 1,215 determinant cases, rational combinations and rank-64 systems."
