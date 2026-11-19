import Std

namespace Tamarin.Residual

/-- A free/C residual step. The caller retains the terms and the worklist.
Kinds agree with WholeSyntax. Fits flags concern binding a variable on that
side, and occurs reports a variable inside the opposite operand. -/
abbrev Kernel := UInt8 → UInt8 → Bool → Bool → Bool → Bool → Bool → UInt8

def step : Kernel := fun left right equal sameHead fitsLeft fitsRight occurs =>
  if equal then 2
  else if left == 0 || right == 0 then
    if occurs then 1 else if fitsLeft then 3 else if fitsRight then 4 else 1
  else if !sameHead then 1
  else if left == 1 then 2
  else if left == 2 then 5
  else if left == 3 then 6
  else 0

end Tamarin.Residual
