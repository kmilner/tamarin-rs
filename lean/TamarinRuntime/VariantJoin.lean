namespace Tamarin.VariantJoinCandidate

def keep (row : Array UInt64) : Option UInt64 :=
  if row.contains 0 then some 0 else if row.toList.all (· == 1) then some 1 else none

/-- One flag per unifier. An unresolved row defers the entire pair, unless
another entry in that same row witnesses a redex. -/
def run (rows : Array (Array UInt64)) : Option (Array UInt64) :=
  (rows.toList.mapM keep).map List.toArray

end Tamarin.VariantJoinCandidate
