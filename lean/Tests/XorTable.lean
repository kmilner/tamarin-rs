import Tamarin.XorTableWire

namespace Tamarin.XorTableTests

-- Four variables have unrelated IDs. The duplicate, unit and triple equations
-- consequently cannot borrow a variable assignment from each other.
private def decls : Array UInt64 := #[2,37,0,2, 4,91,2,2,2,2]
private def nodes : Array (Array UInt64) := #[
  #[0,103,2], #[0,7,2], #[0,803,2], #[0,21,2], #[2,37],
  #[4,91,0,0], #[4,91,4,1], #[4,91,3,2,2], #[4,91,2,2], #[4,91,8,3],
  #[4,91,2,3], #[4,91,10,2]]

private def check (ds : Array UInt64) (ns : Array (Array UInt64)) (es : Array UInt64) := Id.run do
  let some ⟨_,rs⟩ := TotalUnifyWire.input ds ns es | return false
  let some schema := XorTable.detect rs | return false
  return XorTable.accepts (XorTable.liftSchema schema) (fun | .ac _ => 2 | _ => 1) 0 (TableAmbient.liftRules rs)

-- The triple is tested in flat, left-grouped, and interleaved forms. The
-- provided unit has its constant on the left. Each ordering of the equations
-- denotes the same presentation; adding an existing equation does too.
#guard ([7,9,11] : List UInt64).all fun i =>
  let d := [5,4]; let u := [6,1]; let t := [i,3]
  [[d,u,t],[u,d,t],[t,u,d],[t,d,u],[d,t,u],[u,t,d],[d,u,t,t]].all fun rows =>
    check decls nodes rows.flatten.toArray

-- Keep the same symbols and all variable sort tags, while replacing the
-- repeated triple argument or returning that repeated argument.
#guard !check decls (nodes.set! 7 #[4,91,2,3,3]) #[5,4,6,1,7,3]
#guard !check decls nodes #[5,4,6,1,7,2]

-- Subsorts constrain which redexes exist. A Pub-only duplicate parameter
-- leaves all general-message duplicates outside the protected presentation.
#guard !check decls (nodes.set! 0 #[0,103,0]) #[5,4,6,1,7,3]
#guard !check (decls.set! 3 3) nodes #[5,4,6,1,7,3]

end Tamarin.XorTableTests
