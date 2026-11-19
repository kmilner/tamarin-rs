import TamarinCI

namespace Tamarin.IdentityTable.Tests
open Tamarin.IdentityTable

def empty : IdentityTable VariableKey := ⟨[], by simp⟩
def x : VariableKey := ⟨[120], .msg, UInt64.ofNat (UInt64.size - 1)⟩
def y : VariableKey := ⟨[121], .msg, UInt64.ofNat (UInt64.size - 1)⟩
def z : VariableKey := ⟨[120], .fresh, UInt64.ofNat (UInt64.size - 1)⟩
def table : IdentityTable VariableKey := ((empty.intern x).1.intern y).1

example : (empty.intern x).2 = 0 := by decide
example : (table.intern x).2 = 0 := by decide
example : (table.intern y).2 = 1 := by decide
example : (table.intern z).2 = 2 := by decide
example : table.decode 2 = none := by decide
example : table.decode 0 = some x := by decide
example : table.decode 1 = some y := by decide
example : table.encode z = none := by decide
example : (table.intern z).1.decode 0 = table.decode 0 := intern_preserves table z 0 (by decide)
example : (table.intern z).1.decode (table.intern z).2 = some z := intern_decode table z
end Tamarin.IdentityTable.Tests
