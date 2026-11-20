namespace Tamarin.SharedOffset

abbrev Packet := Array (Array (Array UInt64))

/-- The contract permits different branch order and any choice of witness ID.
A disagreement between its two occurrences would change the represented answer. -/
def PacketCorrect (run : UInt64 → UInt64 → Packet) : Prop :=
  ∀ a b, a ≠ b → ∃ w, (run a b).toList.Perm
    [#[#[b], #[a]], #[#[b, w], #[a, w]]]

end Tamarin.SharedOffset
