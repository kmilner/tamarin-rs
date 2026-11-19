namespace Tamarin.RigidAllocation

abbrev Arm := Array (Array UInt64)

/-- Rows bind x, y and z in that order. Zero represents the rigid factor,
and each positive value names a witness local to one answer. -/
def shortX (v : UInt64) : Arm := #[#[0], #[v], #[v]]
def shortY (v : UInt64) : Arm := #[#[v], #[0], #[v]]
def longX (u v : UInt64) : Arm := #[#[0, u], #[v], #[u, v]]
def longY (u v : UInt64) : Arm := #[#[v], #[0, u], #[u, v]]

/-- A complete packet admits arbitrary branch order and independent witness
names in each answer. Distinct witnesses in a long answer range independently. -/
def PacketCorrect (run : Bool → Array Arm) : Prop :=
  ∀ reversed, ∃ s t u v w k : UInt64,
    s ≠ 0 ∧ t ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ w ≠ 0 ∧ k ≠ 0 ∧ w ≠ k ∧
      (run reversed).toList.Perm [shortX s, shortY t, longX u v, longY w k]

end Tamarin.RigidAllocation
