/-! Numeric input from Rust for XOR, pairing and symmetric encryption. -/
namespace Tamarin.XorConstructorWire

def declarations : Array UInt64 := #[4, 0, 2, 2, 2, 2, 2, 1, 0, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 5, 2, 2, 2, 2, 2, 6, 1, 2, 2]

def nodes : Array (Array UInt64) := #[
  #[0, 0, 2],
  #[0, 1, 2],
  #[4, 0, 0, 1],
  #[2, 1],
  #[2, 3, 0, 1],
  #[2, 2, 4],
  #[2, 5, 0, 1],
  #[2, 4, 6, 1],
  #[2, 6, 4],
  #[4, 0, 0, 0],
  #[4, 0, 0, 0, 1],
  #[4, 0, 0, 3]
]

def ruleRoots : Array UInt64 := #[5, 0, 7, 0, 8, 1, 9, 3, 10, 1, 11, 0]

def observationRoots : Array UInt64 := #[2, 3]

end Tamarin.XorConstructorWire
