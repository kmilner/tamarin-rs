import Tamarin.BilinearTableWire
import Tamarin.DHWireSymbols
import Tamarin.DHWireData
import Tamarin.TablePresentation

namespace Tamarin.BilinearTableTests

private def decls := DHWire.declarations ++ #[2,35,2,2,2,2, 3,91,2,2,2,2, 3,84,2,2,2,2]

-- The three rules have independent variable IDs. The commutative map and
-- scalar product use the opposite operand order on the two sides.
private def nodes : Array (Array UInt64) := #[
  #[0,901,2], #[0,501,2], #[0,28,2], #[0,66,2], #[0,38,2], #[0,100,2], #[0,71,2],
  #[2,2], #[2,35,7,0], #[2,35,2,3], #[2,35,1,9], #[4,4,2,1], #[2,35,11,3],
  #[2,35,5,6], #[3,91,13,4], #[3,91,6,4], #[2,0,15,5], #[3,84,13,4]]

private def roots : Array UInt64 := #[14,16,10,12,8,0]

private def check (ns : Array (Array UInt64)) (es : Array UInt64) := Id.run do
  let some ⟨d,ts⟩ := TotalUnifyWire.graph decls ns | return false
  let symbol (k id : UInt64) : Option (TotalUnifyWire.Symbol d.decls k) :=
    if h : (TotalUnifyWire.decl d.decls k id).isSome then some ⟨id,h⟩ else none
  let some pow := symbol 2 0 | return false
  let some inv := symbol 2 1 | return false
  let some one := symbol 2 2 | return false
  let some neutral := symbol 2 3 | return false
  let some mul := symbol 4 4 | return false
  let some dh := DHWire.readSymbols (d := d) pow inv one neutral mul | return false
  let some rs := TotalUnifyWire.equations ts es.toList | return false
  let some schema := (BilinearTable.detect dh rs).head? | return false
  return schema.ops.pmult.val == 35 && schema.ops.emap.val == 91 &&
    TablePresentation.Agrees (schema.rows dh) (rs.filter fun r => schema.owns (Rewriting.ConstructorVariants.head r.lhs))

#guard check nodes roots
-- The earlier candidate mentions a different map that has no extract equation.
#guard check nodes (#[17,16] ++ roots)
-- An input copied into the wrong position on the RHS fails exact agreement.
#guard !check (nodes.set! 12 #[2,35,11,1]) roots
#guard !check (nodes.set! 16 #[2,0,15,4]) roots
-- Sharing distinct schema slots or narrowing a declared Msg variable to Pub fails.
#guard !check (nodes.set! 1 #[0,28,2]) roots
#guard !check (nodes.set! 4 #[0,38,0]) roots

end Tamarin.BilinearTableTests
