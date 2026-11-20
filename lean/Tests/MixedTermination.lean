import Tamarin.DHMixedTermination
import Tamarin.DHWire
import Tamarin.DHConstructorExtension

/-! Extend the captured DH packet with the equations from native_mixed_subterms.spthy
and one extra ground definition. Node references 0, 1, 5 are x, y, and the DH unit. -/
namespace Tamarin.MixedTerminationTests
open Rewriting DHPeer SubtermDecrease
set_option maxHeartbeats 64000000
set_option maxRecDepth 8192

-- bag/2 [AC], peel/1, check/2, marker/0, ok/0, pair/2, fst/1, snd/1, later/0.
private def ds := DHWire.declarations ++ #[
  4,5,2,2,2,2, 2,6,1,2,2, 2,7,2,2,2,2, 2,8,0,2, 2,9,0,2,
  2,10,2,2,2,2, 2,11,1,2,2, 2,12,1,2,2, 2,13,0,2]
private def ns := DHWire.nodes ++ #[
  #[2,8], #[2,9], #[4,5,0,30], #[2,6,32], #[2,7,0,0], #[2,10,31,30],
  #[2,11,35], #[2,10,0,1], #[2,11,37], #[2,12,37], #[2,13], #[2,7,31,31], #[2,1,41]]
-- peel(bag(x,marker)) -> x; check(x,x) -> fst(pair(ok,marker));
-- fst(pair(x,y)) -> x; snd(pair(x,y)) -> y; later -> inv(check(ok,ok)).
private def roots := DHWire.ruleRoots ++ #[33,0, 34,36, 38,0, 39,1, 40,42]
private def packet := TableWire.input ds ns roots #[40]
private def parsed := packet.get (by decide +kernel)
abbrev dict := parsed.1
abbrev rules := parsed.2.1

private def interpreted := DHWire.readSymbols (d := dict) ⟨0,by decide +kernel⟩ ⟨1,by decide +kernel⟩
  ⟨2,by decide +kernel⟩ ⟨3,by decide +kernel⟩ ⟨4,by decide +kernel⟩
def symbols := interpreted.get (by decide +kernel)
def keys (i : Fin 3) : Variable := ⟨i.val,.msg⟩

private def tier (id : UInt64) : Nat := if id == 7 then 1 else if id == 13 then 2 else 0

def level : Head dict.sig → Nat
  | .free f => tier f.val
  | _ => 0

private theorem decreasingTable : SymbolWeight.decreasing (weights ExactTable.weight rules level) rules :=
  decreasing (by intro h; cases h <;> simp [ExactTable.weight] <;> split <;> decide)
    ((accepts_iff ExactTable.weight level rules).mp (by decide +kernel))

example : WellFounded (fun b a => StepModulo (ruleRoot rules) a b) := SymbolWeight.terminating decreasingTable
example {a b : Term parsed.1.sig} (step : StepModulo (ruleRoot rules) a b) (k : SortId) (ht : HasSort a k) :
    HasSort b k := TableDecrease.sortPreserving (by decide +kernel : TableDecrease.sorted rules) step k ht

-- On this table, the same certificate supports all-path convergence and a
-- finite covering variant family for every tuple, including open terms. The
-- proposer obtains its weights directly from the table.
abbrev ambientRules := TableAmbient.liftRules rules

theorem complete : ReferenceReduction.Bound ambientRules ∧
    MaudeOperations.CanonicalPresentation (ruleRoot ambientRules) ∧ MaudeOperations.FiniteVariantProperty (ruleRoot ambientRules) :=
  ConstructorExtension.accepts_sound (DHWire.liftSymbols symbols) keys (fun _ => rfl)
    (fun _ _ eq => Fin.ext (congrArg Variable.id eq))
    (weight := defaultWeight ExactTable.weight ambientRules) (fuel := 4) (by decide +kernel)

-- The unmodified DH weights cannot orient the growing check or later rows.
#guard !SymbolWeight.decreasing ExactTable.weight rules
-- A new alternative check(x,x) -> later closes a cycle. Its ground instances
-- return to later under one additional inverse on every lap.
#guard Id.run do
  let some ⟨_,rs,_⟩ := TableWire.input ds ns (roots ++ #[34,40]) #[40] | return false
  let tiers : Head _ → Nat := fun h => match h with
    | .free f => tier f.val
    | _ => 0
  return !accepts ExactTable.weight tiers rs && !SymbolWeight.decreasing (defaultWeight ExactTable.weight rs) rs

end Tamarin.MixedTerminationTests
