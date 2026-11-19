#!/usr/bin/env python3
"""Negative integration checks for the actual root-module build audit.

Each probe elaborates a temporary copy of TamarinCI.lean with one additional
declaration before its audit. Production files are never modified. The
implemented_by probe has a kernel proof of logical correctness, so rejecting
it specifically tests the gap between logical and executable definitions.
"""

from pathlib import Path
import os
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (ROOT / "TamarinCI.lean").read_text()
def obligation(name: str) -> str:
    """Copy one CI theorem without accidentally importing intervening gates."""
    start = SOURCE.index(f"theorem {name}")
    return SOURCE[start:SOURCE.index("\n\n", start) + 1]


# Assemble exports and their proof obligations in one temporary module, so
# mutations check the current source rather than an old imported .olean.
RUNTIME = (ROOT / "TamarinRuntime.lean").read_text()
PROOFS = (ROOT / "Tamarin/Executable.lean").read_text()
imports = list(dict.fromkeys(
    line for line in (RUNTIME + PROOFS).splitlines()
    if line.startswith("import ") and line != "import TamarinRuntime"
))
EXECUTABLE = "\n".join(imports) + "\n" + "\n".join(
    line for line in (RUNTIME + "\n" + PROOFS).splitlines()
    if not line.startswith("import ")
)
# Assemble the pairing candidate proof and fixed export obligation without
# importing the compiled wrappers: mutations must test these exact definitions.
PAIRING_PROOFS = (ROOT / "Tamarin/PairingCandidateProofs.lean").read_text()
EXECUTABLE = "import Tamarin.PairingContract\n" + EXECUTABLE + "\n" + "\n".join(
    line for line in PAIRING_PROOFS.splitlines() if not line.startswith("import ")
) + """
theorem exportedPairing_correct : Tamarin.PairingBackend.Correct
    { variants := Tamarin.Executable.pairingVariants,
      project := Tamarin.Executable.pairingProject } :=
  Tamarin.PairingCandidateProofs.correct
theorem exportedPairing_sharedCorrect : Tamarin.PairingBackend.SharedCorrect
    { variants := Tamarin.Executable.pairingVariants,
      project := Tamarin.Executable.pairingProject } :=
  exportedPairing_correct.shared
"""
REFLEXIVE_PROOFS = (ROOT / "Tamarin/ReflexiveCandidateProofs.lean").read_text()
EXECUTABLE = "import Tamarin.Reflexive\n" + EXECUTABLE + "\n" + "\n".join(
    line for line in REFLEXIVE_PROOFS.splitlines() if not line.startswith("import ")
) + """
theorem exportedReflexive_correct : Tamarin.ReflexiveBackend.Correct
    { solve := Tamarin.Executable.reflexiveUnify } :=
  Tamarin.ReflexiveCandidateProofs.correct
"""
MATCH_PROOFS = (ROOT / "Tamarin/FlatMatchCandidateProofs.lean").read_text()
EXECUTABLE = "import Tamarin.FlatMatchContract\n" + EXECUTABLE + "\n" + "\n".join(
    line for line in MATCH_PROOFS.splitlines() if not line.startswith("import ")
)
offset_obligation = SOURCE[SOURCE.index("theorem exportedSharedOffset_correct"):
                          SOURCE.index("theorem exportedSharedOffset_semantic")]
EXECUTABLE = ("import Tamarin.SharedOffsetCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + offset_obligation + "end Tamarin\n")
factor_start = SOURCE.index("theorem exportedACFactorExclusion_correct")
factor_obligation = SOURCE[factor_start:SOURCE.index("\n\n", factor_start) + 1]
EXECUTABLE = ("import Tamarin.ACFactorExclusion\n" + EXECUTABLE + "\nnamespace Tamarin\n"
              + factor_obligation + "end Tamarin\n")
root_start = SOURCE.index("theorem exportedRootExclusion_correct")
root_obligation = SOURCE[root_start:SOURCE.index("\n\n", root_start) + 1]
EXECUTABLE = ("import Tamarin.RootExclusion\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + root_obligation + "end Tamarin\n")
constructor_obligation = SOURCE[SOURCE.index("theorem exportedConstructorVariant_correct"):
                               SOURCE.index("theorem exportedConstructorVariant_semantic")]
EXECUTABLE = ("import Tamarin.ConstructorVariantCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + constructor_obligation + "end Tamarin\n")
reduction_obligation = SOURCE[SOURCE.index("theorem exportedRuleReduction_correct"):
                             SOURCE.index("theorem exportedRuleReduction_semantic")]
EXECUTABLE = ("import Tamarin.RuleReductionCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + reduction_obligation + "end Tamarin\n")
ground_start = SOURCE.index("theorem exportedGroundDecision_correct")
ground_decision = SOURCE[ground_start:SOURCE.index("\n\n", ground_start) + 1]
EXECUTABLE = ("import Tamarin.GroundVariantCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + ground_decision + "end Tamarin\n")
cancel_common_start = SOURCE.index("theorem exportedCancelCommon_correct")
cancel_common = SOURCE[cancel_common_start:SOURCE.index("\n\n", cancel_common_start) + 1]
EXECUTABLE = ("import Tamarin.CancelCommonCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + cancel_common + "end Tamarin\n")
rigid_start = SOURCE.index("theorem exportedRigidAllocation_correct")
rigid_obligation = SOURCE[rigid_start:SOURCE.index("\n\n", rigid_start) + 1]
EXECUTABLE = ("import Tamarin.RigidAllocationCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + rigid_obligation + "end Tamarin\n")
whole_start = SOURCE.index("theorem exportedWholeUnify_correct")
whole_obligation = SOURCE[whole_start:SOURCE.index("\n\n", whole_start) + 1]
EXECUTABLE = ("import Tamarin.WholeContract\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + whole_obligation + "end Tamarin\n")
xor_start = SOURCE.index("theorem exportedXorBranches_correct")
xor_obligation = SOURCE[xor_start:SOURCE.index("\n\n", xor_start) + 1]
EXECUTABLE = ("import Tamarin.XorCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + xor_obligation + "end Tamarin\n")
clash_start = SOURCE.index("theorem exportedSortClash_correct")
clash_obligation = SOURCE[clash_start:SOURCE.index("\n\n", clash_start) + 1]
EXECUTABLE = ("import Tamarin.SortClashCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + clash_obligation + "end Tamarin\n")
comm_obligation = obligation("exportedCommOrientations_correct") + obligation("exportedCommOrientations_bound")
EXECUTABLE = ("import Tamarin.CommutativeCandidateProofs\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + comm_obligation + "end Tamarin\n")
MARKER = "open Lean in\nrun_cmd do"
PROBES = [
    (
        "unproved_export",
        "@[export tamarin_unproved] def Tamarin.AuditProbe.unproved : Nat := 0\n",
        "Unapproved project export",
    ),
    (
        "duplicate_export",
        "@[export tamarin_flat_ac_equal] def Tamarin.AuditProbe.unproved "
        "(_ _ : Array UInt64) : UInt8 := 1\n",
        "Unapproved project export",
    ),
    (
        "changed_export_mapping",
        "attribute [export tamarin_wrong_equal] Tamarin.Executable.flatACEqual\n",
        "Cannot add attribute `[export]`",
    ),
    (
        "implemented_by",
        """
namespace Tamarin.AuditProbe
def wrong (_ : Nat) : Nat := 0
@[implemented_by wrong] def verified (n : Nat) : Nat := n
theorem verified_correct (n : Nat) : verified n = n := rfl
end Tamarin.AuditProbe
""",
        "unchecked implemented_by replacement",
    ),
    (
        "extern",
        """
namespace Tamarin.AuditProbe
@[extern "audit_probe_untrusted"] def verified (n : Nat) : Nat := n
theorem verified_correct (n : Nat) : verified n = n := rfl
end Tamarin.AuditProbe
""",
        "unchecked extern implementation",
    ),
    (
        "value_initializer",
        """
namespace Tamarin.AuditProbe
def wrong : IO Nat := pure 0
@[init wrong] def verified : Nat := 1
theorem verified_correct : verified = 1 := rfl
end Tamarin.AuditProbe
""",
        "unchecked runtime initializer",
    ),
    (
        "builtin_initializer",
        """
namespace Tamarin.AuditProbe
def wrong : IO Nat := pure 0
@[builtin_init wrong] def verified : Nat := 1
theorem verified_correct : verified = 1 := rfl
end Tamarin.AuditProbe
""",
        "unchecked runtime initializer",
    ),
    (
        "outside_namespace",
        """
namespace OtherNamespace
def wrong (_ : Nat) : Nat := 0
@[implemented_by wrong] def verified (n : Nat) : Nat := n
end OtherNamespace
""",
        "unchecked implemented_by replacement",
    ),
    (
        "unsafe",
        "unsafe def Tamarin.AuditProbe.unchecked : Nat := 0\n",
        "unsafe project declaration",
    ),
    (
        "axiom",
        "axiom Tamarin.AuditProbe.assumed : False\n",
        "depends on unapproved axiom",
    ),
    (
        "private_axiom",
        "namespace OtherNamespace\nprivate axiom assumed : False\nend OtherNamespace\n",
        "depends on unapproved axiom",
    ),
]

EXPORT_MUTATIONS = [
    (
        "empty_products_treated_as_equal",
        "  RuntimeCandidate.backend.equal lhs rhs",
        "  if lhs.isEmpty && rhs.isEmpty then 2 else RuntimeCandidate.backend.equal lhs rhs",
        "theorem flatAC_empty_inputs",
    ),
    (
        "ground_false_unsat",
        "def flatACEqual (lhs rhs : Array UInt64) : UInt8 :=\n"
        "  RuntimeCandidate.backend.equal lhs rhs",
        "def flatACEqual (lhs rhs : Array UInt64) : UInt8 := 1",
        "theorem flatACEqual_correct",
    ),
    (
        "ground_always_unsupported",
        "def flatACEqual (lhs rhs : Array UInt64) : UInt8 :=\n"
        "  RuntimeCandidate.backend.equal lhs rhs",
        "def flatACEqual (lhs rhs : Array UInt64) : UInt8 := 0",
        "theorem flatACEqual_completes",
    ),
    (
        "residual_false_unsat",
        "def flatACResidual (tail rhs : Array UInt64) : Array UInt64 :=\n"
        "  RuntimeCandidate.backend.residual tail rhs",
        "def flatACResidual (tail rhs : Array UInt64) : Array UInt64 :=\n  #[1]",
        "theorem flatACResidual_empty_complete",
    ),
    (
        "residual_always_unsupported",
        "def flatACResidual (tail rhs : Array UInt64) : Array UInt64 :=\n"
        "  RuntimeCandidate.backend.residual tail rhs",
        "def flatACResidual (tail rhs : Array UInt64) : Array UInt64 :=\n  #[0]",
        "theorem flatACResidual_completes",
    ),
]


EXPORT_MUTATIONS.extend([
    (
        "pairing_drops_narrowing_branch",
        "def pairingVariants (hasProjection : Bool) : UInt8 :=\n"
        "  RuntimeCandidate.pairing.variants hasProjection",
        "def pairingVariants (hasProjection : Bool) : UInt8 := 1",
        "theorem exportedPairing_correct",
    ),
    (
        "pairing_always_unsupported",
        "def pairingVariants (hasProjection : Bool) : UInt8 :=\n"
        "  RuntimeCandidate.pairing.variants hasProjection",
        "def pairingVariants (hasProjection : Bool) : UInt8 := 0",
        "theorem exportedPairing_correct",
    ),
    (
        "pairing_wrong_projection",
        "def pairingProject (first : Bool) : UInt8 :=\n"
        "  RuntimeCandidate.pairing.project first",
        "def pairingProject (first : Bool) : UInt8 := 1",
        "theorem exportedPairing_correct",
    ),
])

EXPORT_MUTATIONS.extend([
    (
        "reflexive_false_unsat",
        "def reflexiveUnify (recognized : Bool) : UInt8 :=\n"
        "  RuntimeCandidate.reflexive.solve recognized",
        "def reflexiveUnify (recognized : Bool) : UInt8 := 1",
        "theorem exportedReflexive_correct",
    ),
    (
        "reflexive_always_unsupported",
        "def reflexiveUnify (recognized : Bool) : UInt8 :=\n"
        "  RuntimeCandidate.reflexive.solve recognized",
        "def reflexiveUnify (recognized : Bool) : UInt8 := 0",
        "theorem exportedReflexive_correct",
    ),
])


MATCH_RUN = (
    "  (RuntimeCandidate.flatMatcher.run n.toNat (occurrences.toList.map UInt64.toNat)\n"
    "    tail.toList rhs.toList)"
)
EXPORT_MUTATIONS.extend([
    ("matching_drops_all_branches", MATCH_RUN, "  ([] : List (List (List UInt64)))",
     "theorem exported (n : UInt64)"),
    ("matching_returns_empty_binding", MATCH_RUN, "  ([[[]]] : List (List (List UInt64)))",
     "theorem exported (n : UInt64)"),
    ("matching_keeps_only_first_branch", MATCH_RUN, "  (" + MATCH_RUN.strip() + ".take 1)",
     "theorem exported (n : UInt64)"),
])

OFFSET_RUN = "  RuntimeCandidate.sharedOffset a b"
EXPORT_MUTATIONS.extend([
    ("offset_loses_ground_branch", OFFSET_RUN, "  #[#[#[b, 0], #[a, 0]]]",
     "theorem exportedSharedOffset_correct"),
    ("offset_loses_shared_branch", OFFSET_RUN, "  #[#[#[b], #[a]]]",
     "theorem exportedSharedOffset_correct"),
    ("offset_splits_shared_witness", OFFSET_RUN, "  #[#[#[b], #[a]], #[#[b, 0], #[a, 1]]]",
     "theorem exportedSharedOffset_correct"),
])

FACTOR_RUN = "  RuntimeCandidate.excludeACFactors rows heads"
EXPORT_MUTATIONS.extend([
    ("ac_exclusion_skips_rule", FACTOR_RUN,
     "  RuntimeCandidate.excludeACFactors (rows.extract 0 1) heads",
     "theorem exportedACFactorExclusion_correct"),
    ("ac_exclusion_ignores_last_factor", FACTOR_RUN,
     "  RuntimeCandidate.excludeACFactors rows (heads.extract 0 1)",
     "theorem exportedACFactorExclusion_correct"),
    ("ac_exclusion_uses_wildcard_as_missing_head", FACTOR_RUN,
     "  rows.all fun row => row.any fun k => !heads.contains k",
     "theorem exportedACFactorExclusion_correct"),
    ("ac_exclusion_always_defers", FACTOR_RUN, "  false",
     "theorem exportedACFactorExclusion_correct"),
])

ROOT_RUN = "  RuntimeCandidate.excludeRoot rows args"
EXPORT_MUTATIONS.extend([
    ("root_exclusion_skips_overlapping_rules", ROOT_RUN,
     "  RuntimeCandidate.excludeRoot (rows.extract 0 1) args",
     "theorem exportedRootExclusion_correct"),
    ("root_exclusion_always_defers", ROOT_RUN, "  false",
     "theorem exportedRootExclusion_correct"),
])

CONSTRUCTOR_RUN = "  RuntimeCandidate.constructorVariant roots used"
EXPORT_MUTATIONS.extend([
    ("constructors_ignore_rule_roots", CONSTRUCTOR_RUN, "  true",
     "theorem exportedConstructorVariant_correct"),
    ("constructors_always_decline", CONSTRUCTOR_RUN, "  false",
     "theorem exportedConstructorVariant_correct"),
    ("constructors_check_only_first_operator", CONSTRUCTOR_RUN,
     "  RuntimeCandidate.constructorVariant roots (used.extract 0 1)",
     "theorem exportedConstructorVariant_correct"),
])

REDUCTION_RUN = "  RuntimeCandidate.reduceRuleSlot slot keys subjects"
EXPORT_MUTATIONS.extend([
    ("reduction_ignores_repeated_slot", REDUCTION_RUN, "  subjects.extract 0 1",
     "theorem exportedRuleReduction_correct"),
    ("reduction_never_returns_result", REDUCTION_RUN, "  #[]",
     "theorem exportedRuleReduction_correct"),
])


GROUND_VARIANT_RUN = "  RuntimeCandidate.groundVariant holes anchors deps rigid"
EXPORT_MUTATIONS.extend([
    ("ground_variant_forgets_captured_inputs", GROUND_VARIANT_RUN,
     "  RuntimeCandidate.groundVariant holes anchors #[] rigid", "theorem exportedGroundDecision_correct"),
    ("ground_variant_merges_anchor_slots", GROUND_VARIANT_RUN,
     "  RuntimeCandidate.groundVariant holes #[] deps rigid", "theorem exportedGroundDecision_correct"),
    ("ground_variant_accepts_nonrigid", GROUND_VARIANT_RUN,
     "  RuntimeCandidate.groundVariant holes anchors deps true", "theorem exportedGroundDecision_correct"),
    ("ground_variant_never_completes", GROUND_VARIANT_RUN,
     "  0", "theorem exportedGroundDecision_correct"),
])


CANCEL_COMMON_RUN = "  RuntimeCandidate.cancelCommon lhs rhs"
EXPORT_MUTATIONS.extend([
    ("cancel_common_leaves_overlap", CANCEL_COMMON_RUN, "  #[lhs, rhs]",
     "theorem exportedCancelCommon_correct"),
    ("cancel_common_drops_multiplicity", CANCEL_COMMON_RUN,
     "  RuntimeCandidate.cancelCommon lhs.toList.eraseDups.toArray rhs.toList.eraseDups.toArray",
     "theorem exportedCancelCommon_correct"),
    ("cancel_common_swaps_sides", CANCEL_COMMON_RUN, "  RuntimeCandidate.cancelCommon rhs lhs",
     "theorem exportedCancelCommon_correct"),
])


homogeneous_start = SOURCE.index("theorem exportedHomogeneousUnify_correct")
homogeneous_obligation = SOURCE[homogeneous_start:SOURCE.index("\n\n", homogeneous_start) + 1]
EXECUTABLE = ("import Tamarin.HomogeneousContract\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + homogeneous_obligation + "end Tamarin\n")
residual_start = SOURCE.index("theorem exportedResidualStep_correct")
residual_obligation = SOURCE[residual_start:SOURCE.index("\n\n", residual_start) + 1]
EXECUTABLE = ("import Tamarin.Residual\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + residual_obligation + "end Tamarin\n")
RESIDUAL_STEP = "  Residual.step l r equal sameHead fitsL fitsR occurs"
EXPORT_MUTATIONS.extend([
    ("residual_binds_a_cycle", RESIDUAL_STEP,
     "  Residual.step l r equal sameHead fitsL fitsR false", "theorem exportedResidualStep_correct"),
    ("residual_comm_is_positional", RESIDUAL_STEP,
     "  if l == 3 && r == 3 then 5 else Residual.step l r equal sameHead fitsL fitsR occurs",
     "theorem exportedResidualStep_correct"),
    ("residual_closes_unresolved_ac", RESIDUAL_STEP,
     "  if l == 4 && r == 4 then 1 else Residual.step l r equal sameHead fitsL fitsR occurs",
     "theorem exportedResidualStep_correct"),
])

rigid_obligation = obligation("exportedResidualRigid_correct") + obligation("exportedResidualRigid_rejectsMalformed")
EXECUTABLE = ("import Tamarin.ResidualRigid\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + rigid_obligation + "end Tamarin\n")
RIGID_STEP = "  ResidualRigid.run lk lh ls rk rh rs"
EXPORT_MUTATIONS.extend([
    ("rigid_ignores_symbol", RIGID_STEP, RIGID_STEP.replace("rk rh rs", "rk lh rs"),
     "theorem exportedResidualRigid_correct"),
    ("rigid_ignores_children", RIGID_STEP, RIGID_STEP.replace("rh rs", "rh ls"),
     "theorem exportedResidualRigid_correct"),
    ("rigid_collapses_ac_multiplicity", RIGID_STEP,
     "  ResidualRigid.run lk lh ls.toList.eraseDups.toArray rk rh rs.toList.eraseDups.toArray",
     "theorem exportedResidualRigid_correct"),
    ("rigid_simulates_clash_on_bad_input", RIGID_STEP,
     "  let action := ResidualRigid.run lk lh ls rk rh rs\n  if action == 255 then 1 else action",
     "theorem exportedResidualRigid_rejectsMalformed"),
])

variable_start = SOURCE.index("theorem exportedResidualVariable_correct")
variable_end = SOURCE.index("theorem exportedResidualVariable_rejectsMalformed")
variable_obligation = SOURCE[variable_start:SOURCE.index("\n\n", variable_end) + 1]
EXECUTABLE = ("import Tamarin.ResidualVariable\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + variable_obligation + "end Tamarin\n")
VARIABLE_STEP = "  ResidualVariable.run right key keySort kind valueSort ids"
EXPORT_MUTATIONS.extend([
    ("variable_malformed_becomes_clash", VARIABLE_STEP,
     "  let action := ResidualVariable.run right key keySort kind valueSort ids\n  if action == 255 then 1 else action",
     "theorem exportedResidualVariable_rejectsMalformed"),
    ("variable_ignores_proper_occurrences", VARIABLE_STEP, VARIABLE_STEP.replace("valueSort ids",
     "valueSort (if kind == 0 then ids else #[])"), "theorem exportedResidualVariable_correct"),
    ("variable_confuses_binding_directions", VARIABLE_STEP, VARIABLE_STEP.replace("run right", "run false"),
     "theorem exportedResidualVariable_correct"),
    ("variable_ignores_required_sort", VARIABLE_STEP, VARIABLE_STEP.replace("key keySort", "key 2"),
     "theorem exportedResidualVariable_correct"),
])

HOMOGENEOUS_RUN = "  Homogeneous.solve width m"
EXPORT_MUTATIONS.extend([
    ("homogeneous_drops_sound_branches", HOMOGENEOUS_RUN,
     "  (Homogeneous.solve width m).map (fun arms => arms.extract 0 1)",
     "theorem exportedHomogeneousUnify_correct"),
    ("homogeneous_always_defers", HOMOGENEOUS_RUN, "  none",
     "theorem exportedHomogeneousUnify_correct"),
])

graph_start = SOURCE.index("theorem exportedGraphHomogeneous_correct")
graph_obligation = SOURCE[graph_start:SOURCE.index("\n\n", graph_start) + 1]
EXECUTABLE = ("import Tamarin.GraphUnification\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + graph_obligation + "end Tamarin\n")
GRAPH_RUN = "  GraphUnification.run width symbol sort decls nodes roots"
EXPORT_MUTATIONS.extend([
    ("graph_ignores_simultaneous_equations", GRAPH_RUN,
     "  GraphUnification.run width symbol sort decls nodes (roots.extract 0 2)",
     "theorem exportedGraphHomogeneous_correct"),
    ("graph_loses_repeated_operands", GRAPH_RUN,
     "  GraphUnification.run width symbol sort decls (nodes.map fun row => "
     "if row[0]? == some 4 then row.extract 0 4 else row) roots",
     "theorem exportedGraphHomogeneous_correct"),
    ("graph_always_defers", GRAPH_RUN, "  none", "theorem exportedGraphHomogeneous_correct"),
])

selection_start = SOURCE.index("theorem exportedOpenMatchSelect_correct")
selection_contract = SOURCE[selection_start:SOURCE.index("\n\n", selection_start) + 1]
EXECUTABLE = ("import Tamarin.OpenMatchSelect\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + selection_contract + "end Tamarin\n")
SELECT = "  OpenMatchSelect.run rigid subject"
EXECUTABLE = ("import Tamarin.CollectorMultiplicityMatching\n" + EXECUTABLE + "\nnamespace Tamarin\n"
              + obligation("exportedCollectorPossible_correct") + "end Tamarin\n")
COLLECTOR_TEST = " := CollectorMultiplicity.run occ residual"
EXPORT_MUTATIONS.extend([
    ("collector_discards_valid_matches", COLLECTOR_TEST, " := false", "theorem exportedCollectorPossible_correct"),
    ("collector_misses_required_clashes", COLLECTOR_TEST, " := true", "theorem exportedCollectorPossible_correct"),
    ("open_match_reuses_an_occurrence", SELECT,
     "  (OpenMatchSelect.run rigid subject).map (fun out => out.map (fun row => row.map fun _ => 0))",
     "theorem exportedOpenMatchSelect_correct"),
    ("open_match_drops_remainder", SELECT,
     "  (OpenMatchSelect.run rigid subject).map (fun out => out.map (fun row => row.extract 0 rigid.toNat))",
     "theorem exportedOpenMatchSelect_correct"),
    ("open_match_keeps_one_assignment", SELECT,
     "  (OpenMatchSelect.run rigid subject).map (fun out => out.extract 0 1)",
     "theorem exportedOpenMatchSelect_correct"),
    ("open_match_deferral_as_clash", SELECT, "  some #[]", "theorem exportedOpenMatchSelect_correct"),
])

pivot_start = SOURCE.index("theorem exportedACPivot_correct")
pivot_contract = SOURCE[pivot_start:SOURCE.index("\n\n", pivot_start) + 1]
EXECUTABLE = ("import Tamarin.ACPivotPacket\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + pivot_contract + "end Tamarin\n")
PIVOT = " := ACPivotCandidate.run size"
EXPORT_MUTATIONS.extend([
    ("pivot_drops_shared_remainder", PIVOT,
     " := (ACPivotCandidate.run size).map (fun rows => rows.eraseIdxIfInBounds 1)",
     "theorem exportedACPivot_correct"),
    ("pivot_ignores_an_occurrence", PIVOT,
     " := ACPivotCandidate.run (size - 1)", "theorem exportedACPivot_correct"),
])

join_start = SOURCE.index("theorem exportedJoinSelection_correct")
join_contract = SOURCE[join_start:SOURCE.index("\n\n", join_start) + 1]
EXECUTABLE = ("import Tamarin.VariantJoinSelect\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + join_contract + "end Tamarin\n")
JOIN = "  VariantJoinCandidate.run rows"
EXPORT_MUTATIONS.extend([
    ("join_keeps_reducible_rows", JOIN, "  some (rows.map fun _ => 1)", "theorem exportedJoinSelection_correct"),
    ("join_truncates_unifiers", JOIN, "  VariantJoinCandidate.run (rows.extract 0 1)", "theorem exportedJoinSelection_correct"),
    ("join_closes_unknown_rows", JOIN, "  some ((VariantJoinCandidate.run rows).getD #[])",
     "theorem exportedJoinSelection_correct"),
])

peer_start = SOURCE.index("theorem exportedDHPeerImages_correct")
peer_end = SOURCE.index("theorem exportedDHPeerImages_ordered", peer_start)
peer_contract = SOURCE[peer_start:SOURCE.index("\n\n", peer_end) + 1]
EXECUTABLE = ("import Tamarin.DHPeerPrograms\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + peer_contract + "end Tamarin\n")
PEER = ":= DHPeerCandidate.images power"
EXPORT_MUTATIONS.extend([
    ("dh_peer_reverses_public_order", PEER,
     ":= (DHPeerCandidate.images power).map Array.reverse", "theorem exportedDHPeerImages_ordered"),
    ("dh_peer_drops_cancellation", PEER,
     ":= (DHPeerCandidate.images power).map (fun rows => rows.extract 0 4)", "theorem exportedDHPeerImages_correct"),
    ("dh_peer_uses_independent_exponent", PEER,
     ":= (DHPeerCandidate.images power).map (fun rows => rows.map (fun row => row.map (fun k => if k == 1 then 4 else k)))",
     "theorem exportedDHPeerImages_correct"),
])

exponent_start = SOURCE.index("theorem exportedDHExponentImages_correct")
exponent_contract = SOURCE[exponent_start:SOURCE.index("\n\n", exponent_start) + 1]
EXECUTABLE = ("import Tamarin.DHExponentPacket\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + exponent_contract + "end Tamarin\n")
EXPONENT = ":= DHExponentCandidate.images u"
EXPORT_MUTATIONS.extend([
    ("dh_exponent_loses_unit", EXPONENT,
     ":= (DHExponentCandidate.images u).filter (fun row => row != #[9])",
     "theorem exportedDHExponentImages_correct"),
    ("dh_exponent_does_not_share_factor", EXPONENT,
     ":= (DHExponentCandidate.images u).map (fun row => row.map (fun x => if x == 1 then 4 else x))",
     "theorem exportedDHExponentImages_correct"),
])

tower_start = SOURCE.index("theorem exportedDHTowerImages_correct")
tower_contract = SOURCE[tower_start:SOURCE.index("\n\n", tower_start) + 1]
EXECUTABLE = ("import Tamarin.DHTowerPacket\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + tower_contract + "end Tamarin\n")
TOWER = ":= DHTowerCandidate.images width"
EXPORT_MUTATIONS.extend([
    ("dh_tower_appends_undecodable_row", TOWER,
     ":= (DHTowerCandidate.images width).map (fun rows => rows.push #[7])",
     "theorem exportedDHTowerImages_correct"),
    ("dh_tower_loses_last_occurrence", TOWER, ":= DHTowerCandidate.images (width - 1)",
     "theorem exportedDHTowerImages_correct"),
    ("dh_tower_aliases_two_factors", TOWER,
     ":= (DHTowerCandidate.images width).map (fun rows => rows.map (fun row => row.map (fun x => if x == 10 then 9 else x)))",
     "theorem exportedDHTowerImages_correct"),
])

subgroup_start = SOURCE.index("theorem exportedACSubgroups_correct")
subgroup_contract = SOURCE[subgroup_start:SOURCE.index("\n\n", subgroup_start) + 1]
EXECUTABLE = ("import Tamarin.ACSubgroups\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + subgroup_contract + "end Tamarin\n")
SUBGROUP = ":= ACSubgroups.run n"
EXPORT_MUTATIONS.extend([
    ("subgroups_only_check_full_product", SUBGROUP,
     ":= some #[(List.range n.toNat |>.map Nat.toUInt64).toArray]", "theorem exportedACSubgroups_correct"),
    ("subgroups_drop_one_operand", SUBGROUP,
     ":= ACSubgroups.run (n - 1)", "theorem exportedACSubgroups_correct"),
    ("subgroups_always_defer", SUBGROUP, ":= none", "theorem exportedACSubgroups_correct"),
])

sorted_match_start = SOURCE.index("theorem exportedSortedACMatch_correct")
sorted_match_contract = SOURCE[sorted_match_start:SOURCE.index("\n\n", sorted_match_start) + 1]
EXECUTABLE = ("import Tamarin.SortedMatch\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + sorted_match_contract + "end Tamarin\n")
SORTED_MATCH = "  SortedMatch.runWith flatACMatch acSort varSort atomSort occ tail rhs"
EXPORT_MUTATIONS.extend([
    ("sorted_match_keeps_ill_sorted_rows", SORTED_MATCH,
     "  some (flatACMatch varSort.size.toUInt64 occ tail rhs)", "theorem exportedSortedACMatch_correct"),
    ("sorted_match_retags_singletons", SORTED_MATCH,
     SORTED_MATCH.replace("varSort atomSort occ", "varSort (atomSort.map fun _ => acSort) occ"),
     "theorem exportedSortedACMatch_correct"),
    ("sorted_match_drops_repeats", SORTED_MATCH,
     SORTED_MATCH.replace("occ tail", "occ.toList.eraseDups.toArray tail"), "theorem exportedSortedACMatch_correct"),
    ("sorted_match_defers_all", SORTED_MATCH, "  none", "theorem exportedSortedACMatch_correct"),
])

operand_refine_start = SOURCE.index("theorem exportedOperandRefine_correct")
operand_refine_contract = SOURCE[operand_refine_start:SOURCE.index("\n\n", operand_refine_start) + 1]
EXECUTABLE = ("import Tamarin.OperandRefinement\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + operand_refine_contract + "end Tamarin\n")
OPERAND_REFINE = ":= OperandRefinementCandidate.keep sides"
EXPORT_MUTATIONS.extend([
    ("operand_refinement_drops_equations", OPERAND_REFINE, ":= #[]",
     "theorem exportedOperandRefine_correct"),
    ("operand_refinement_returns_operand_ids", OPERAND_REFINE, ":= sides",
     "theorem exportedOperandRefine_correct"),
])

operand_start = SOURCE.index("theorem exportedOperandUnify_refines")
operand_obligation = SOURCE[operand_start:SOURCE.index("\n\n", operand_start) + 1]
EXECUTABLE = ("import Tamarin.OperandUnification\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + operand_obligation + "end Tamarin\n")
OPERAND = "  OperandUnification.runWith OperandCounts.run homogeneousUnify width sides"
EXPORT_MUTATIONS.extend([
    ("operand_counts_drop_repeats", OPERAND,
     OPERAND.replace("width sides", "width (sides.map fun row => row.toList.eraseDups.toArray)"),
     "theorem exportedOperandUnify_refines"),
    ("operand_drops_equation", OPERAND, OPERAND.replace("width sides", "width (sides.extract 0 2)"),
     "theorem exportedOperandUnify_refines"),
    ("operand_treats_deferral_as_clash", OPERAND, "  some #[]", "theorem exportedOperandUnify_refines"),
])

projection_start = SOURCE.index("theorem exportedAnswerProjection_correct")
projection_obligation = SOURCE[projection_start:SOURCE.index("\n\n", projection_start) + 1]
EXECUTABLE = ("import Tamarin.AnswerProjection\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + projection_obligation + "end Tamarin\n")
PROJECT = "  AnswerProjection.project width answers"
EXPORT_MUTATIONS.extend([
    ("projection_restarts_witnesses_each_arm", PROJECT,
     "  do return (← answers.toList.mapM (fun a => AnswerProjection.project width #[a])).foldl (· ++ ·) #[]",
     "theorem exportedAnswerProjection_correct"),
    ("projection_discards_column_tags", PROJECT,
     "  (AnswerProjection.project width answers).map (fun arms => "
     "arms.map (fun a => a.map (fun r => r.extract 1 r.size)))",
     "theorem exportedAnswerProjection_correct"),
    ("projection_collapses_distinct_witnesses", PROJECT,
     "  AnswerProjection.project width (answers.map fun a => a.map fun r => r.map fun _ => 0)",
     "theorem exportedAnswerProjection_correct"),
    ("projection_always_fails", PROJECT, "  none", "theorem exportedAnswerProjection_correct"),
])

factor_start = SOURCE.index("theorem exportedCheckFactors_correct")
factor_end = SOURCE.index("\n\n", SOURCE.index("theorem exportedCheckFactors_required"))
EXECUTABLE = ("import Tamarin.FactorAdmission\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + SOURCE[factor_start:factor_end] + "\nend Tamarin\n")
FACTOR_RUN = "  FactorCheck.run decls nodes original bindings residual"
EXPORT_MUTATIONS.extend([
    ("factor_accepts_unchecked_original", FACTOR_RUN, "  true", "theorem exportedCheckFactors_correct"),
    ("factor_drops_residual_tail", FACTOR_RUN,
     "  FactorCheck.run decls nodes original bindings (residual.extract 0 2)",
     "theorem exportedCheckFactors_correct"),
    ("factor_always_defers", FACTOR_RUN, "  false", "theorem exportedCheckFactors_required"),
    ("factor_skips_binding_replay", FACTOR_RUN,
     "  FactorCheck.runWith FactorCheck.direct decls nodes original bindings residual",
     "theorem exportedCheckFactors_chain"),
])

WHOLE_RUN = "  Whole.run decls nodes equations"
EXPORT_MUTATIONS.extend([
    ("whole_ignores_tail_equations", WHOLE_RUN, "  Whole.run decls nodes (equations.extract 0 2)",
     "theorem exportedWholeUnify_correct"),
    ("whole_truncates_flat_ac_rows", WHOLE_RUN,
     "  Whole.run decls (nodes.map fun r => if r[0]? == some 4 then r.extract 0 4 else r) equations",
     "theorem exportedWholeUnify_correct"),
    ("whole_fails_open_queries", WHOLE_RUN, "  #[#[1]]", "theorem exportedWholeUnify_correct"),
    ("whole_always_defers", WHOLE_RUN, "  #[#[0]]", "theorem exportedWholeUnify_correct"),
])

EXECUTABLE = ("import Tamarin.BinaryCancellationPacket\n" + EXECUTABLE + "\nnamespace Tamarin\n"
              + obligation("exportedBinaryCancellationRows_correct") + "end Tamarin\n")
BINARY_ROWS = "  BinaryCancellationCandidate.rows"
EXECUTABLE = ("import Tamarin.MixedCancellationRows\n" + EXECUTABLE + "\nnamespace Tamarin\n"
              + obligation("exportedMixedCancellationRows_correct") + "end Tamarin\n")
MIXED_ROWS = "  BinaryCancellationCandidate.mixedRows"
EXPORT_MUTATIONS.extend([
    ("mixed_cancellation_omits_diagonal", MIXED_ROWS, MIXED_ROWS + ".extract 1 9",
     "theorem exportedMixedCancellationRows_correct"),
    ("mixed_cancellation_decouples_value", MIXED_ROWS,
     MIXED_ROWS + ".map (fun row => row.set! 3 row[2]!)", "theorem exportedMixedCancellationRows_correct"),
    ("binary_cancellation_omits_overlap", BINARY_ROWS, BINARY_ROWS + ".extract 0 6",
     "theorem exportedBinaryCancellationRows_correct"),
    ("binary_cancellation_breaks_value_sharing", BINARY_ROWS,
     BINARY_ROWS + ".map (fun row => row.set! 2 0)", "theorem exportedBinaryCancellationRows_correct"),
])

xor_matching_start = SOURCE.index("theorem exportedXorMatchings_correct")
xor_matching_contract = SOURCE[xor_matching_start:SOURCE.index("\n\n", xor_matching_start) + 1]
EXECUTABLE = ("import Tamarin.XorMatchings\n" + EXECUTABLE
              + "\nnamespace Tamarin\n" + xor_matching_contract + "end Tamarin\n")
XOR_MATCHINGS = "  XorMatchingCandidate.run width"
EXPORT_MUTATIONS.extend([
    ("xor_matchings_drop_a_pair", XOR_MATCHINGS,
     "  (XorMatchingCandidate.run width).map (fun rows => rows.extract 0 1)",
     "theorem exportedXorMatchings_correct"),
    ("xor_matchings_change_width", XOR_MATCHINGS, "  XorMatchingCandidate.run (width - 1)",
     "theorem exportedXorMatchings_correct"),
    ("xor_matchings_turn_deferral_into_empty", XOR_MATCHINGS,
     "  some ((XorMatchingCandidate.run width).getD #[])",
     "theorem exportedXorMatchings_correct"),
])
EXECUTABLE += "\nnamespace Tamarin\n" + obligation("exportedXorOdd_correct") + "end Tamarin\n"
EXPORT_MUTATIONS.append((
    "xor_keeps_nonzero_multiplicities", ":= RuntimeCandidate.xorOdd count",
    ":= count != 0", "theorem exportedXorOdd_correct",
))

XOR_RUN = "  RuntimeCandidate.xorBranches same"
EXPORT_MUTATIONS.extend([
    ("xor_omits_diagonal", XOR_RUN, "  1", "theorem exportedXorBranches_correct"),
    ("xor_drops_open_case", XOR_RUN, "  2", "theorem exportedXorBranches_correct"),
    ("xor_identity_on_equal_inputs", XOR_RUN, "  3", "theorem exportedXorBranches_correct"),
])

CLASH_RUN = "  RuntimeCandidate.sortClash left right"
EXPORT_MUTATIONS.extend([
    ("sort_clash_false_unsat", CLASH_RUN, "  true", "theorem exportedSortClash_correct"),
    ("sort_clash_ignores_disjoint_sort", CLASH_RUN, "  false", "theorem exportedSortClash_correct"),
])

COMM_RUN = "  RuntimeCandidate.commOrientations a b c d priority"
EXPORT_MUTATIONS += [
    ("comm_spends_budget_on_duplicates", COMM_RUN, "  3", "theorem exportedCommOrientations_bound"),
    ("comm_loses_crossed_orientation", COMM_RUN, "  1", "theorem exportedCommOrientations_correct"),
    ("comm_confuses_swapped_alignment", COMM_RUN,
     "  RuntimeCandidate.commOrientations a b d c priority", "theorem exportedCommOrientations_correct"),
    ("comm_truncates_unknown_status", COMM_RUN, "  7", "theorem exportedCommOrientations_correct"),
]
RIGID_RUN = "  RuntimeCandidate.rigidAllocation reversed"
EXPORT_MUTATIONS.extend([
    ("allocation_omits_singleton_case", RIGID_RUN,
     "  (RuntimeCandidate.rigidAllocation reversed).extract 1 4",
     "theorem exportedRigidAllocation_correct"),
    ("allocation_aliases_two_witnesses", RIGID_RUN,
     "  (RuntimeCandidate.rigidAllocation reversed).map (fun arm => "
     "arm.map (fun row => row.map (fun id => if id == 2 then 1 else id)))",
     "theorem exportedRigidAllocation_correct"),
    ("allocation_breaks_shared_witness", RIGID_RUN,
     "  (RuntimeCandidate.rigidAllocation reversed).set! 2 #[#[0,1],#[2],#[3,2]]",
     "theorem exportedRigidAllocation_correct"),
    ("allocation_treats_reverse_as_empty", RIGID_RUN,
     "  if reversed then #[] else RuntimeCandidate.rigidAllocation false",
     "theorem exportedRigidAllocation_correct"),
])


def main() -> None:
    assert SOURCE.count(MARKER) == 1, "root audit marker changed"
    with tempfile.TemporaryDirectory(prefix="tamarin-audit-") as directory:
        allowed = """
namespace Tamarin.AuditProbe
def reference (n : Nat) : Nat := n + n
def optimized (n : Nat) : Nat := 2 * n
@[csimp] theorem optimized_correct : reference = optimized := by
  funext n
  simp [reference, optimized, Nat.two_mul]
end Tamarin.AuditProbe
"""
        path = Path(directory) / "checked_optimization.lean"
        path.write_text(SOURCE.replace(MARKER, allowed + "\n" + MARKER))
        result = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        print("accepted proved csimp optimization")
        for label, declarations, expected in PROBES:
            path = Path(directory) / f"{label}.lean"
            path.write_text(SOURCE.replace(MARKER, declarations + "\n" + MARKER))
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            output = result.stdout + result.stderr
            assert result.returncode != 0 and expected in output, (
                f"{label} was not rejected by its intended audit check:\n{output}"
            )
            print(f"rejected {label}")

        # Production kernels are imported modules. In particular, initializer
        # metadata must survive serialization before the root can audit it.
        imported_env = os.environ.copy()
        imported_env["LEAN_PATH"] = directory + os.pathsep + imported_env.get("LEAN_PATH", "")
        for label, declarations, expected in PROBES:
            if label not in {"implemented_by", "extern", "value_initializer"}:
                continue
            module = Path(directory) / "ImportedProbe.lean"
            module.write_text("import Lean\n" + declarations)
            compiled = subprocess.run(
                ["lake", "env", "lean", "-R", directory, "-o",
                 str(module.with_suffix(".olean")), str(module)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            assert compiled.returncode == 0, compiled.stdout + compiled.stderr
            path = Path(directory) / "AuditImport.lean"
            path.write_text("import ImportedProbe\n" + SOURCE)
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                env=imported_env,
                text=True,
                capture_output=True,
                check=False,
            )
            output = result.stdout + result.stderr
            assert result.returncode != 0 and expected in output, (
                f"imported {label} was not rejected by its intended audit check:\n{output}"
            )
            print(f"rejected imported {label}")

        # Local execution builds can compile an unproved candidate. The same
        # candidate must not typecheck as the verified backend required by CI.
        path = Path(directory) / "UnprovedCandidate.lean"
        local_candidate = """
import TamarinRuntime.Interface
namespace Trial
def backend : Tamarin.FlatACBackend where
  equal := fun _ _ => 1
  residual := fun _ _ => #[1]
end Trial
"""
        path.write_text(local_candidate)
        result = subprocess.run(
            ["lake", "env", "lean", "-R", directory, "-c", str(path.with_suffix(".c")), str(path)],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        print("local runtime build accepts unproved candidate")
        path.write_text(local_candidate.replace(
            "import TamarinRuntime.Interface", "import Tamarin.CandidateProofs"
        ) + """
example : Tamarin.FlatACBackend.Correct Trial.backend :=
  Tamarin.CandidateProofs.correct
""")
        result = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        output = result.stdout + result.stderr
        assert result.returncode != 0 and "Type mismatch" in output and "Trial.backend" in output, output
        print("CI contract rejects unproved candidate")

        path = Path(directory) / "unmutated_exports.lean"
        path.write_text(EXECUTABLE)
        baseline = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, text=True, capture_output=True, check=False,
        )
        assert baseline.returncode == 0, baseline.stdout + baseline.stderr
        print("unmutated export obligations compile")

        for label, original, replacement, theorem in EXPORT_MUTATIONS:
            assert EXECUTABLE.count(original) == 1, f"export source changed: {label}"
            source = EXECUTABLE.replace(original, replacement)
            start = source.index(theorem)
            end = source.find("\ntheorem ", start + len(theorem))
            if end < 0:
                end = len(source)
            first_line = source[:start].count("\n") + 1
            last_line = source[:end].count("\n") + 1
            path = Path(directory) / f"{label}.lean"
            path.write_text(source)
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            output = result.stdout + result.stderr
            error_lines = [int(n) for n in re.findall(r":(\d+):\d+: error:", output)]
            assert result.returncode != 0 and any(
                first_line <= line <= last_line for line in error_lines
            ), f"{label} did not break its {theorem} obligation:\n{output}"
            print(f"rejected {label} at {theorem}")


if __name__ == "__main__":
    main()
