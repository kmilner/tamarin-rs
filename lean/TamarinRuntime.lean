import TamarinRuntime.Candidate
import TamarinRuntime.BinaryCancellation
import TamarinRuntime.XorMatchings
import TamarinRuntime.Whole
import TamarinRuntime.FactorCheck
import TamarinRuntime.Residual
import TamarinRuntime.ResidualVariable
import TamarinRuntime.ResidualRigid
import TamarinRuntime.GraphUnification
import TamarinRuntime.AnswerProjection
import TamarinRuntime.SortedMatch
import TamarinRuntime.OpenMatchSelect
import TamarinRuntime.CollectorMultiplicity
import TamarinRuntime.ACPivot
import TamarinRuntime.VariantJoin
import TamarinRuntime.DHPeer
import TamarinRuntime.DHExponent
import TamarinRuntime.DHTower
import TamarinRuntime.ACSubgroups
import TamarinRuntime.ReductionGraph
import TamarinRuntime.OperandUnification
import TamarinRuntime.OperandRefinement

/-!
Fixed native export wrapper. Cargo builds this target without the proof/audit
harness. TamarinCI separately verifies these exact entry points before merge.
-/
namespace Tamarin.Executable

@[export tamarin_flat_ac_equal]
def flatACEqual (lhs rhs : Array UInt64) : UInt8 :=
  RuntimeCandidate.backend.equal lhs rhs

@[export tamarin_flat_ac_residual]
def flatACResidual (tail rhs : Array UInt64) : Array UInt64 :=
  RuntimeCandidate.backend.residual tail rhs

@[export tamarin_pairing_variants]
def pairingVariants (hasProjection : Bool) : UInt8 :=
  RuntimeCandidate.pairing.variants hasProjection

@[export tamarin_pairing_project]
def pairingProject (first : Bool) : UInt8 :=
  RuntimeCandidate.pairing.project first

@[export tamarin_reflexive_unify]
def reflexiveUnify (recognized : Bool) : UInt8 :=
  RuntimeCandidate.reflexive.solve recognized

@[export tamarin_flat_ac_match]
def flatACMatch (n : UInt64) (occurrences tail rhs : Array UInt64) : Array (Array (Array UInt64)) :=
  (RuntimeCandidate.flatMatcher.run n.toNat (occurrences.toList.map UInt64.toNat)
    tail.toList rhs.toList).toArray.map (fun answer => answer.toArray.map List.toArray)

@[export tamarin_ac_pivot]
def acPivot (size : UInt64) : Option (Array (Array UInt64)) := ACPivotCandidate.run size

@[export tamarin_select_joined_variants]
def selectJoinedVariants (rows : Array (Array UInt64)) : Option (Array UInt64) :=
  VariantJoinCandidate.run rows

@[export tamarin_dh_peer_images]
def dhPeerImages (power : Bool) : Option (Array (Array UInt64)) := DHPeerCandidate.images power

@[export tamarin_dh_exponent_images]
def dhExponentImages (u : Unit) : Array (Array UInt64) := DHExponentCandidate.images u

@[export tamarin_dh_tower_images]
def dhTowerImages (width : UInt64) : Option (Array (Array UInt64)) := DHTowerCandidate.images width

@[export tamarin_reduction_graph]
def reductionGraph (rows : Array (Array UInt64)) : Bool := ReductionGraph.run rows

@[export tamarin_ac_subgroups]
def acSubgroups (n : UInt64) : Option (Array (Array UInt64)) := ACSubgroups.run n

@[export tamarin_collector_possible]
def collectorPossible (occ residual : Array UInt64) : Bool := CollectorMultiplicity.run occ residual

@[export tamarin_open_match_select]
def openMatchSelect (rigid subject : UInt64) : Option (Array (Array UInt64)) :=
  OpenMatchSelect.run rigid subject

@[export tamarin_sorted_ac_match]
def sortedACMatch (acSort : UInt64) (varSort atomSort occ tail rhs : Array UInt64) :
    Option (Array (Array (Array UInt64))) :=
  SortedMatch.runWith flatACMatch acSort varSort atomSort occ tail rhs

@[export tamarin_shared_offset]
def sharedOffset (a b : UInt64) : Array (Array (Array UInt64)) :=
  RuntimeCandidate.sharedOffset a b

@[export tamarin_rigid_allocation]
def rigidAllocation (reversed : Bool) : Array (Array (Array UInt64)) :=
  RuntimeCandidate.rigidAllocation reversed

@[export tamarin_comm_orientations]
def commOrientations (a b c d : UInt64) (priority : UInt8) : UInt8 :=
  RuntimeCandidate.commOrientations a b c d priority

@[export tamarin_residual_rigid]
def residualRigid (lk : UInt8) (lh : UInt64) (ls : Array UInt64)
    (rk : UInt8) (rh : UInt64) (rs : Array UInt64) : UInt8 :=
  ResidualRigid.run lk lh ls rk rh rs

@[export tamarin_residual_variable]
def residualVariable (right : Bool) (key keySort : UInt64) (kind : UInt8)
    (valueSort : UInt64) (ids : Array UInt64) : UInt8 :=
  ResidualVariable.run right key keySort kind valueSort ids

@[export tamarin_residual_step]
def residualStep (l r : UInt8) (equal sameHead fitsL fitsR occurs : Bool) : UInt8 :=
  Residual.step l r equal sameHead fitsL fitsR occurs

@[export tamarin_xor_odd]
def xorOdd (count : UInt64) : Bool := RuntimeCandidate.xorOdd count

@[export tamarin_sort_clash]
def sortClash (left right : Array UInt64) : Bool :=
  RuntimeCandidate.sortClash left right

@[export tamarin_xor_branches]
def xorBranches (same : Bool) : UInt8 :=
  RuntimeCandidate.xorBranches same

@[export tamarin_binary_cancellation_rows]
def binaryCancellationRows (_ : Unit) : Array (Array UInt64) :=
  BinaryCancellationCandidate.rows

@[export tamarin_mixed_cancellation_rows]
def mixedCancellationRows (_ : Unit) : Array (Array UInt64) :=
  BinaryCancellationCandidate.mixedRows

@[export tamarin_xor_matchings]
def xorMatchings (width : UInt64) : Option (Array (Array UInt64)) :=
  XorMatchingCandidate.run width

@[export tamarin_exclude_root]
def excludeRoot (rows : Array (Array UInt64)) (args : Array UInt64) : Bool :=
  RuntimeCandidate.excludeRoot rows args

@[export tamarin_exclude_ac_factors]
def excludeACFactors (rows : Array (Array UInt64)) (heads : Array UInt64) : Bool :=
  RuntimeCandidate.excludeACFactors rows heads

@[export tamarin_constructor_variant]
def constructorVariant (roots used : Array UInt64) : Bool :=
  RuntimeCandidate.constructorVariant roots used

@[export tamarin_reduce_rule_slot]
def reduceRuleSlot (slot : UInt64) (keys subjects : Array UInt64) : Array UInt64 :=
  RuntimeCandidate.reduceRuleSlot slot keys subjects

@[export tamarin_ground_variant]
def groundVariant (holes anchors deps : Array UInt64) (rigid : Bool) : UInt8 :=
  RuntimeCandidate.groundVariant holes anchors deps rigid

@[export tamarin_cancel_common]
def cancelCommon (lhs rhs : Array UInt64) : Array (Array UInt64) :=
  RuntimeCandidate.cancelCommon lhs rhs

@[export tamarin_whole_unify]
def wholeUnify (decls : Array UInt64) (nodes : Array (Array UInt64)) (equations : Array UInt64) :
    Array (Array UInt64) :=
  Whole.run decls nodes equations

@[export tamarin_check_factors]
def checkFactors (decls : Array UInt64) (nodes : Array (Array UInt64))
    (original bindings residual : Array UInt64) : Bool :=
  FactorCheck.run decls nodes original bindings residual

@[export tamarin_homogeneous_unify]
def homogeneousUnify (width : UInt64) (m : Homogeneous.Matrix) : Option Homogeneous.Answers :=
  Homogeneous.solve width m

@[export tamarin_graph_homogeneous_unify]
def graphHomogeneousUnify (width symbol sort : UInt64) (decls : Array UInt64)
    (nodes : Array (Array UInt64)) (roots : Array UInt64) : Option Homogeneous.Answers :=
  GraphUnification.run width symbol sort decls nodes roots

@[export tamarin_operand_refine]
def operandRefine (sides : Array UInt64) : Array UInt64 := OperandRefinementCandidate.keep sides

@[export tamarin_operand_unify]
def operandUnify (width : UInt64) (sides : Array (Array UInt64)) : Option Homogeneous.Answers :=
  OperandUnification.runWith OperandCounts.run homogeneousUnify width sides

@[export tamarin_project_answers]
def projectAnswers (width : UInt64) (answers : Homogeneous.Answers) : Option Homogeneous.Answers :=
  AnswerProjection.project width answers

end Tamarin.Executable
