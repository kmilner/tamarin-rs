import Tamarin.DHPeerPlain

/-! Products of arbitrary irreducible message operands have at most one
normal form modulo B under the active DH group equations. -/
namespace Tamarin.Rewriting.DHPeer.Balance
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

theorem Inventory.of_buckets (mul : MulBucket E) (inv : InverseBucket E)
    (unit : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one) : Inventory E := by
  refine ⟨mul.1,?_⟩
  intro eq mem h
  rcases h with h|h|h
  · rcases mul.2 eq mem h with std|⟨k,_,same⟩
    · exact .inl std
    · exact .inr ⟨k,same⟩
  · obtain ⟨k,_,same⟩ := inv.2 eq mem h
    exact .inr ⟨k,same⟩
  · exact False.elim (unit eq mem h)

theorem Inventory.product_unique (inventory : Inventory E) {p e : Term sig}
    (hp : HasSort p .msg) (he : HasSort e .msg)
    (np : Normal (ruleRoot T.rules) p) (ne : Normal (ruleRoot T.rules) e)
    {x y} (nx : NormalForm (ruleRoot T.rules) (.ac s.mul p e) x)
    (ny : NormalForm (ruleRoot T.rules) (.ac s.mul p e) y) : EquivB x y := by
  classical
  have sorted : HasSort (.ac s.mul p e) .msg :=
    s.mulSort ▸ HasSort.ac s.mul _ _ (s.mulSort ▸ hp) (s.mulSort ▸ he)
  apply normal_unique inventory E.presentation (fun _ => plain_of_inverse E) _ (nx.2.2 .msg sorted)
    (ny.2.2 .msg sorted) nx.2.1 ny.2.1 nx.1 ny.1
  intro k
  obtain ⟨a,ha⟩ := defined s _ k np
  obtain ⟨b,hb⟩ := defined s _ k ne
  exact ⟨a+b,by change read s _ k (s.product.mul p e) = _; rw [read_mul,ha,hb]; rfl⟩

theorem Inventory.peer_unique_msg (inventory : Inventory E) (pow : PowerBucket T)
    (unitNormal : Normal (ruleRoot T.rules) s.product.one)
    {Y r u v : Term sig} (sy : HasSort Y .msg) (sr : HasSort r .msg) (nonunit : head r ≠ .free s.one)
    (ny : Normal (ruleRoot T.rules) Y) (nr : Normal (ruleRoot T.rules) r)
    (nu : NormalForm (ruleRoot T.rules) (s.power Y r) u)
    (nv : NormalForm (ruleRoot T.rules) (s.power Y r) v) : EquivB u v :=
  pow.peer_unique_msg unitNormal
    (fun _ hp np _ _ _ => inventory.product_unique hp sr np nr)
    sy sr nonunit ny nr nu nv

theorem Inventory.peer_unique (inventory : Inventory E) (pow : PowerBucket T)
    (unitNormal : Normal (ruleRoot T.rules) s.product.one)
    {Y r u v : Term sig} (sy : HasSort Y .msg) (sr : HasSort r .fresh)
    (ny : Normal (ruleRoot T.rules) Y) (nr : Normal (ruleRoot T.rules) r)
    (nu : NormalForm (ruleRoot T.rules) (s.power Y r) u)
    (nv : NormalForm (ruleRoot T.rules) (s.power Y r) v) : EquivB u v :=
  pow.peer_unique unitNormal
    (fun _ _ hp he np ne _ _ _ => inventory.product_unique hp (.widen he .fresh_msg) np ne)
    sy sr ny nr nu nv

end Tamarin.Rewriting.DHPeer.Balance
