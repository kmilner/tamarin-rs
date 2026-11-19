namespace Tamarin.ReductionGraph

/-- Rows are numbered in DFS completion order. The first completed row is
the candidate normal form. A forward or out-of-range target fails the check. -/
def run (rows : Array (Array UInt64)) : Bool :=
  rows.size > 0 && rows.size.all fun i _ =>
    (i == 0 || !rows[i].isEmpty) && rows[i].all (fun j => j.toNat < i)

end Tamarin.ReductionGraph
