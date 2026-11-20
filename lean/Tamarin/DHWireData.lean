/-! Numeric packet produced by Rust for the five DH operator observations.
The physical_dh_table_matches_the_lean_presentation regression checks every word. -/
namespace Tamarin.DHWire

def declarations : Array UInt64 := #[2, 0, 2, 2, 2, 2, 2, 1, 1, 2, 2, 2, 2, 0, 2, 2, 3, 0, 2, 4, 4, 2, 2, 2, 2]

def nodes : Array (Array UInt64) := #[
  #[0, 0, 2],
  #[0, 1, 2],
  #[2, 0, 0, 1],
  #[0, 2, 2],
  #[2, 1, 3],
  #[2, 2],
  #[2, 3],
  #[4, 4, 0, 1],
  #[2, 0, 0, 5],
  #[2, 0, 6, 0],
  #[2, 0, 2, 3],
  #[4, 4, 1, 3],
  #[2, 0, 0, 11],
  #[2, 1, 0],
  #[2, 1, 13],
  #[2, 1, 5],
  #[4, 4, 1, 13],
  #[2, 1, 16],
  #[2, 1, 1],
  #[4, 4, 0, 18],
  #[4, 4, 0, 1, 13],
  #[4, 4, 0, 13],
  #[4, 4, 0, 5],
  #[2, 1, 7],
  #[4, 4, 1, 3, 23],
  #[4, 4, 3, 13],
  #[4, 4, 1, 23],
  #[4, 4, 3, 13, 18],
  #[4, 4, 3, 23],
  #[4, 4, 13, 18]
]

def ruleRoots : Array UInt64 := #[8, 0, 9, 6, 10, 12, 14, 0, 15, 5, 17, 19, 20, 1, 21, 5, 22, 0, 24, 25, 26, 13, 27, 28, 29, 23]

def observationRoots : Array UInt64 := #[2, 4, 5, 6, 7]

end Tamarin.DHWire
