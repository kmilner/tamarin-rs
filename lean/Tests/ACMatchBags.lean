import Tamarin.ACMatchBagsRefinement

namespace Tamarin.Matching.ACBags.Tests

-- X+X+Y and X+Y+Y both have a match against a+a+b when asked separately.
-- A single assignment across both rows would have to give a nonintegral
-- multiplicity of a to each variable.
private def left : List Bool × List Bool := ([true,true,false],[true,true,false])
private def right : List Bool × List Bool := ([true,false,false],[true,true,false])

example : Feasible [left] := by
  refine ⟨fun k => [k],by simp,?_⟩
  simp [left]

example : Feasible [right] := by
  refine ⟨fun k => [!k],by simp,?_⟩
  simp [right]
  decide

example : ¬Feasible [left,right] := by
  rintro ⟨im,_,both⟩
  have p := (both left (by simp)).count_eq true
  have q := (both right (by simp)).count_eq true
  simp [left,right,List.count_append] at p q
  omega

end Tamarin.Matching.ACBags.Tests
