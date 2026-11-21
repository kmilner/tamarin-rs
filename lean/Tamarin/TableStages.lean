import Std

/-! The host keeps the first terminal reply and retries status 3. It can pick
any sequence of intermediate budgets before the last representable stage. -/
namespace Tamarin.TableStages

abbrev Wire := Array (Array UInt64)

def firstTerminal (stage : UInt64 → Wire) (last : UInt64) : List UInt64 → Wire
  | [] => stage last
  | n :: ns =>
    let w := stage n
    if w = #[#[3]] then firstTerminal stage last ns else w

theorem completes {stage : UInt64 → Wire} {good : Wire → Prop} {last : UInt64}
    (lastGood : good (stage last)) (earlier : List UInt64)
    (progress : ∀ n ∈ earlier, good (stage n) ∨ stage n = #[#[3]]) :
    good (firstTerminal stage last earlier) := by
  induction earlier with
  | nil => exact lastGood
  | cons n ns ih =>
    simp only [firstTerminal]
    split
    · exact ih fun m hm => progress m (List.mem_cons_of_mem _ hm)
    · next terminal => exact (progress n List.mem_cons_self).resolve_right terminal

end Tamarin.TableStages
