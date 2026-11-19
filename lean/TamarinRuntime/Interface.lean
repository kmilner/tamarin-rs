import Std

namespace Tamarin

/-- Stable numeric ABI operations for the current flat-AC fragment.
The implementation carries no proof fields at runtime. CI requires a separate
`FlatACBackend.Correct` witness for these exact functions. -/
structure FlatACBackend where
  equal : Array UInt64 → Array UInt64 → UInt8
  residual : Array UInt64 → Array UInt64 → Array UInt64

/-- Recipe ABI for the initial pairing fragment. 1 = identity variants,
3 = identity plus a fresh pair binding; project returns child 1 or 2.
Rust recognizes the fragment and reifies recipes, which remains trusted code. -/
structure PairingBackend where
  variants : Bool → UInt8
  project : Bool → UInt8

/-- Recipe for a recognized reflexive conjunction: 2 = identity, 1 = unsat,
0 = unsupported. The contract requires completion on recognized inputs. -/
structure ReflexiveBackend where
  solve : Bool → UInt8

/-- Complete flat matching. Each answer has one nonempty atom row for every
request-local variable ID; occurrences retain repeats. No proof fields at runtime. -/
structure FlatMatchBackend where
  run : Nat → List Nat → List UInt64 → List UInt64 → List (List (List UInt64))

end Tamarin
