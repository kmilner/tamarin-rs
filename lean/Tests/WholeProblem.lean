import TamarinRuntime
import Tamarin.WholeContract

namespace Tamarin.WholeTests
open Executable

-- AC 11, AC 12, C 11 and free 11 are distinct. The free operator accepts
-- two Msg inputs. No names in the kernel designate a Tamarin builtin.
private def ds : Array UInt64 := #[4,11,2,2,2,2, 4,12,2,2,2,2, 3,11,2,2,2,2, 2,11,2,2,2,2]
private def ns : Array (Array UInt64) :=
  #[#[0,7,1], #[1,7,0], #[1,8,0], #[4,11,0,1], #[4,11,3,2],
    #[4,11,2,1], #[4,11,5,0], #[3,11,6,3], #[3,11,3,4],
    #[2,11,7,1], #[2,11,8,1], #[4,12,0,1], #[2,11,1,8],
    #[4,11,1,2], #[4,11,2,2]]

#guard wholeUnify ds ns #[9,10,4,6,7,8] == #[#[2]]
#guard wholeUnify ds ns #[3,11] == #[#[0]]
#guard wholeUnify ds ns #[9,12] == #[#[0]]
#guard wholeUnify ds ns #[0,1] == #[#[0]]
#guard wholeUnify ds ns #[0,1,13,14] == #[#[1]]
#guard wholeUnify ds ns #[13,14,0,1] == #[#[1]]
#guard wholeUnify #[] #[] #[] == #[#[2]]
-- Rejecting a legal packet cannot move it into the malformed-input branch
-- by changing the executable decoder. Even an empty system must complete.
example {sig : Signature} (c : WholeProblem.Codec sig) {run : WholeProblem.Kernel}
    (drops : run #[] #[] #[] = #[#[0]]) : ¬ WholeProblem.Correct run := by
  intro correct
  obtain ⟨out, h, _, complete⟩ := correct.valid c [] [] #[] #[] #[] []
    (by simp [Whole.Wire.decodeProblem, Whole.declarations, Whole.decodeNodes, Whole.readEquations]) .nil (by simp [WholeProblem.Faithful])
  obtain ⟨_, rfl⟩ := complete (.inl (by simp [WholeProblem.AllEqual]))
  rw [drops] at h
  simp [WholeProblem.reply] at h

-- Truncated declarations/queries, undeclared heads, forward edges, crossed
-- sorts and malformed arities must all defer, even on reflexive roots.
#guard wholeUnify #[4,11,2,2,2] ns #[0,0] == #[#[0]]
#guard wholeUnify (ds ++ ds) ns #[0,0] == #[#[0]]
#guard wholeUnify ds ns #[0] == #[#[0]]
#guard wholeUnify ds ns #[99,99] == #[#[0]]
#guard wholeUnify ds #[#[2,0]] #[0,0] == #[#[0]]
#guard wholeUnify ds #[#[4,11,0,0]] #[0,0] == #[#[0]]
#guard wholeUnify ds #[#[1,0,3],#[4,11,0,0]] #[1,1] == #[#[0]]
#guard wholeUnify ds #[#[0,0,1],#[3,11,0]] #[1,1] == #[#[0]]
#guard wholeUnify ds #[#[9,1,0]] #[0,0] == #[#[0]]

-- A flat row and its binary bracketing can appear inside the same C/free
-- contexts. The fourth child in row 19 changes only the ground multiplicity.
private def flat := ns ++ #[#[4,11,0,1,2], #[3,11,3,15], #[2,11,16,1],
  #[4,11,1,1,2,2], #[4,11,1,1,2,1]]
#guard wholeUnify ds flat #[15,4, 17,9] == #[#[2]]
#guard wholeUnify ds flat #[18,19] == #[#[1]]
#guard wholeUnify ds flat #[15,18] == #[#[0]]
-- Check every child even when comparing a row to itself. C stays binary.
#guard wholeUnify ds (ns.push #[4,11]) #[15,15] == #[#[0]]
#guard wholeUnify ds (ns.push #[4,11,0]) #[15,15] == #[#[0]]
#guard wholeUnify ds (ns.push #[4,11,0,1,15]) #[15,15] == #[#[0]]
#guard wholeUnify ds (ns ++ #[#[1,9,3], #[4,11,0,1,15]]) #[16,16] == #[#[0]]
#guard wholeUnify ds (ns.push #[3,11,0,1,2]) #[15,15] == #[#[0]]
#guard wholeUnify ds (ns.push #[2,11,0,1,2]) #[15,15] == #[#[0]]

end Tamarin.WholeTests
