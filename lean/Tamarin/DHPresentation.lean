import Tamarin.DHOperatorBounds

/-! The thirteen oriented equations emitted by Tamarin's Diffie–Hellman builtin.
A table can use its own variable names and order, and its signature can contain
additional constructors. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants Balance ShortVariantPaths
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- The positive membership of each of the thirteen rules is recorded by
`Table` and `ExtraTable`. This converse excludes other active equations. -/
def ExactTable (E : ExtraTable T) : Prop :=
  ∀ eq ∈ T.rules, (∃ r : Rule, eq = r.instantiate s (fun i => .var (T.actual r i))) ∨
    ∃ r : ExtraRule, eq = r.instantiate s (fun i => .var (E.actual r i))

/-- The four interpreted heads have only the DH rules. Other heads may
carry arbitrary equations. The rule inventories also require genuine presence
of each DH schema, through the positive fields of `T` and `E`. -/
structure ProtectedTable (E : ExtraTable T) : Prop where
  apps : ∀ eq ∈ T.rules, Application eq.lhs
  atHead : ∀ eq ∈ T.rules, (head eq.lhs = .free s.pow ∨ head eq.lhs = .free s.inv ∨
      head eq.lhs = .free s.one ∨ head eq.lhs = .ac s.mul) →
    (∃ r : Rule, eq = r.instantiate s (fun i => .var (T.actual r i))) ∨
    ∃ r : ExtraRule, eq = r.instantiate s (fun i => .var (E.actual r i))

namespace ExactTable
variable (tab : ExactTable E)
include tab

theorem apps : ∀ r ∈ T.rules, Application r.lhs := by
  intro eq mem
  rcases tab eq mem with ⟨r,rfl⟩ | ⟨r,rfl⟩ <;> cases r <;> trivial

theorem heads {r} (mem : r ∈ T.rules) :
    head r.lhs = .ac s.mul ∨ head r.lhs = .free s.inv ∨ head r.lhs = .free s.pow := by
  rcases tab r mem with ⟨r,rfl⟩ | ⟨r,rfl⟩ <;> cases r <;> first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl)

theorem protectedTable : ProtectedTable E := ⟨tab.apps,fun r mem _ => tab r mem⟩

theorem absent {h : Head sig} (m : h ≠ .ac s.mul) (i : h ≠ .free s.inv) (p : h ≠ .free s.pow) :
    h ∉ ruleHeads T.rules := by
  rintro mem
  obtain ⟨r,hr,eq⟩ := List.mem_map.mp mem
  rcases tab.heads hr with lhs|lhs|lhs <;> first
    | exact m (eq.symm.trans lhs) | exact i (eq.symm.trans lhs) | exact p (eq.symm.trans lhs)

end ExactTable

namespace ProtectedTable
variable (tab : ProtectedTable E)
include tab

omit tab in
private theorem neArity {f g : sig.FreeSym} (h : sig.arity f ≠ sig.arity g) : Head.free f ≠ Head.free g :=
  fun eq => h (congrArg sig.arity (Head.free.inj eq))

theorem power : PowerBucket T := by
  refine ⟨tab.apps,fun eq mem atHead => ?_⟩
  have diff : Head.free s.inv ≠ .free s.pow := neArity (by simp [s.invArity,s.powArity])
  rcases tab.atHead eq mem (.inl atHead) with ⟨r,rfl⟩ | ⟨r,rfl⟩ <;> cases r
  all_goals first
    | exact ⟨.expOne,.inl rfl,rfl⟩ | exact ⟨.tower,.inr (.inl rfl),rfl⟩ | exact ⟨.neutral,.inr (.inr rfl),rfl⟩
    | contradiction | cases atHead

theorem inverse : InverseBucket E := by
  refine ⟨tab.apps,fun eq mem atHead => ?_⟩
  have diff : Head.free s.pow ≠ .free s.inv := neArity (by simp [s.invArity,s.powArity])
  rcases tab.atHead eq mem (.inr (.inl atHead)) with ⟨r,rfl⟩ | ⟨r,rfl⟩ <;> cases r
  all_goals first
    | exact ⟨.invInv,.inl rfl,rfl⟩ | exact ⟨.invOne,.inr (.inl rfl),rfl⟩ | exact ⟨.pull,.inr (.inr rfl),rfl⟩
    | contradiction | cases atHead

theorem product : MulBucket E := by
  refine ⟨tab.apps,fun eq mem atHead => ?_⟩
  rcases tab.atHead eq mem (.inr (.inr (.inr atHead))) with ⟨r,rfl⟩ | ⟨r,rfl⟩ <;> cases r
  all_goals first
    | exact .inl ⟨.inverse,.inl rfl,rfl⟩ | exact .inl ⟨.inverseRest,.inr (.inl rfl),rfl⟩
    | exact .inl ⟨.inside,.inr (.inr (.inl rfl)),rfl⟩ | exact .inl ⟨.insideRest,.inr (.inr (.inr rfl)),rfl⟩
    | exact .inr ⟨.mulOne,.inl rfl,rfl⟩ | exact .inr ⟨.join,.inr (.inl rfl),rfl⟩ | exact .inr ⟨.joinRest,.inr (.inr rfl),rfl⟩
    | cases atHead

private theorem noUnit : Head.free s.one ∉ ruleHeads T.rules := by
  intro mem
  obtain ⟨eq,hm,hd⟩ := List.mem_map.mp mem
  have pi : Head.free s.pow ≠ .free s.one := neArity (by simp [s.powArity,s.oneArity])
  have ii : Head.free s.inv ≠ .free s.one := neArity (by simp [s.invArity,s.oneArity])
  rcases tab.atHead eq hm (.inr (.inr (.inl hd))) with ⟨r,rfl⟩ | ⟨r,rfl⟩ <;> cases r <;>
    first | contradiction | cases hd

theorem unit : Normal (ruleRoot T.rules) s.product.one :=
  constructor_node_normal T.rules tab.apps s.product.one tab.noUnit (fun i => Fin.elim0 (s.oneArity ▸ i))

theorem inventory : Inventory E := by
  refine ⟨tab.apps,fun eq mem hd => ?_⟩
  rcases hd with h|h|h
  · rcases tab.product.2 eq mem h with base|⟨r,_,same⟩
    · exact .inl base
    · exact .inr ⟨r,same⟩
  · obtain ⟨r,_,same⟩ := tab.inverse.2 eq mem h
    exact .inr ⟨r,same⟩
  · exact False.elim (tab.noUnit (h ▸ List.mem_map_of_mem (f := fun r => head r.lhs) mem))

end ProtectedTable

namespace ExactTable
variable (tab : ExactTable E)
include tab

theorem power : PowerBucket T := tab.protectedTable.power
theorem inverse : InverseBucket E := tab.protectedTable.inverse
theorem product : MulBucket E := tab.protectedTable.product
theorem unit : Normal (ruleRoot T.rules) s.product.one := tab.protectedTable.unit
theorem inventory : Inventory E := tab.protectedTable.inventory

/-- A DH rule has only Msg-sorted variables and every instantiated left side
has sort Msg. Kind-level free-headed redexes with an ill-sorted operand
therefore cannot fire. -/
theorem root_typed {a b} (h : ruleRoot T.rules a b) : HasSort a .msg := by
  obtain ⟨r,mem,σ,rfl,rfl⟩ := h
  rcases tab r mem with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · exact (DHPeer.Expr.sorted s _ (fun i => T.actualSort r i ▸ HasSort.var _) _).subst σ.image σ.sorted
  · exact (DHPeer.Expr.sorted s _ (fun i => E.sorted r i ▸ HasSort.var _) _).subst σ.image σ.sorted

end ExactTable

private theorem free_redex_typed (pow : PowerBucket T) (inv : InverseBucket E) {f : sig.FreeSym}
    (active : f = s.pow ∨ f = s.inv) {xs : Fin (sig.arity f) → Term sig} {out}
    (step : ruleRoot T.rules (.free f xs) out) : HasSort (.free f xs) .msg := by
  obtain ⟨r,mem,σ,origin,_⟩ := step
  have hd := (instance_head r (pow.1 r mem) σ).symm.trans (congrArg head origin.symm)
  rw [origin]
  rcases active with rfl|rfl
  · obtain ⟨r,_,rfl⟩ := pow.2 r mem hd
    exact (DHPeer.Expr.sorted s _ (fun i => T.actualSort r i ▸ HasSort.var _) _).subst σ.image σ.sorted
  · obtain ⟨r,_,rfl⟩ := inv.2 r mem hd
    exact (DHPeer.Expr.sorted s _ (fun i => E.sorted r i ▸ HasSort.var _) _).subst σ.image σ.sorted

theorem MulBucket.redex_typed (mul : MulBucket E) {a b : Term sig} (headIs : head a = .ac s.mul)
    (step : ruleRoot T.rules a b) : HasSort a .msg := by
  obtain ⟨r,mem,σ,rfl,rfl⟩ := step
  have hd := (instance_head r (mul.1 r mem) σ).symm.trans headIs
  rcases mul.2 r mem hd with ⟨r,_,rfl⟩ | ⟨r,_,rfl⟩
  · exact (DHPeer.Expr.sorted s _ (fun i => T.actualSort r i ▸ HasSort.var _) _).subst σ.image σ.sorted
  · exact (DHPeer.Expr.sorted s _ (fun i => E.sorted r i ▸ HasSort.var _) _).subst σ.image σ.sorted

private theorem unsorted_free {f : sig.FreeSym} {xs : Fin (sig.arity f) → Term sig}
    (typed : ∀ {ys : Fin (sig.arity f) → Term sig} {b}, ruleRoot T.rules (.free f ys) b → HasSort (.free f ys) .msg)
    (normal : ∀ i, Normal (ruleRoot T.rules) (xs i)) (ill : ¬ HasSort (.free f xs) .msg) :
    Normal (ruleRoot T.rules) (.free f xs) := by
  apply normal_free_no_root normal
  intro ys agree b step
  exact ill (Term.checkSort_sound _ _ ((SortClash.check_equiv (EquivB.free f xs ys agree) .msg).symm ▸
    Term.checkSort_complete (typed step)))

theorem free_head_paths [DecidableEq sig.ACSym] (inventory : Inventory E) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one) (pow : PowerBucket T)
    (f : sig.FreeSym) (active : f = s.pow ∨ f = s.inv) : ∃ k, ∀ xs, (∀ i, Normal (ruleRoot T.rules) (xs i)) →
    ∃ u, Path (ruleRoot T.rules) k (.free f xs) u ∧ Normal (ruleRoot T.rules) u := by
  classical
  rcases active with p|h
  · subst f
    obtain ⟨k,run⟩ := power_paths inventory mul inv unit pow
    refine ⟨k,fun xs norm => ?_⟩
    by_cases typed : HasSort (.free s.pow xs) .msg
    · obtain ⟨b,e,same⟩ := splitPower s (t := .free s.pow xs) rfl
      obtain ⟨hb,he⟩ := DHTower.pow_types (same ▸ typed)
      have nf : ∀ i : Fin (sig.arity s.pow), Normal (ruleRoot T.rules) (if i.val=0 then b else e) := by
        have args := Term.free.inj same
        cases args.2
        exact norm
      obtain ⟨y,_,path,ny⟩ := run b e hb he (nf ⟨0,by rw [s.powArity]; decide⟩) (nf ⟨1,by rw [s.powArity]; decide⟩)
      exact ⟨y,same ▸ path,ny⟩
    · exact ⟨_,.basis (.refl _),unsorted_free (fun step => free_redex_typed pow inv (.inl rfl) step) norm typed⟩
  · subst f
    obtain ⟨k,run⟩ := inverse_paths inventory mul inv unit
    refine ⟨k,fun xs norm => ?_⟩
    by_cases typed : HasSort (.free s.inv xs) .msg
    · let i : Fin (sig.arity s.inv) := ⟨0,by rw [s.invArity]; decide⟩
      have same : s.product.inv (xs i) = .free s.inv xs := by
        apply congrArg (Term.free _); funext j
        apply congrArg xs; apply Fin.ext; have := j.isLt; have := s.invArity; change 0 = j.val; omega
      have child : HasSort (xs i) .msg := by
        have checks := Term.checkSort_complete typed
        simp only [Term.checkSort,Bool.and_eq_true,List.all_eq_true] at checks
        simpa [s.invInput] using Term.checkSort_sound _ _ (checks.2 i (List.mem_finRange i))
      obtain ⟨y,_,path,ny⟩ := run _ child (norm i)
      exact ⟨y,same ▸ path,ny⟩
    · exact ⟨_,.basis (.refl _),unsorted_free (fun step => free_redex_typed pow inv (.inr rfl) step) norm typed⟩

namespace ExactTable
variable (tab : ExactTable E)
include tab

theorem free_paths [DecidableEq sig.ACSym] (f : sig.FreeSym) : ∃ k, ∀ xs, (∀ i, Normal (ruleRoot T.rules) (xs i)) →
    ∃ u, Path (ruleRoot T.rules) k (.free f xs) u ∧ Normal (ruleRoot T.rules) u := by
  classical
  by_cases a : f = s.pow ∨ f = s.inv
  · exact free_head_paths tab.inventory tab.product tab.inverse tab.unit tab.power f a
  have p : f ≠ s.pow := fun eq => a (.inl eq)
  have h : f ≠ s.inv := fun eq => a (.inr eq)
  exact ⟨0,fun xs norm => ⟨_,.basis (.refl _),constructor_node_normal _ tab.apps _
    (tab.absent (by intro x; cases x) (fun e => h (Head.free.inj e)) (fun e => p (Head.free.inj e))) norm⟩⟩

end ExactTable

end Tamarin.Rewriting.DHPeer

namespace Tamarin.Rewriting.DHPeer.Schemas

/-! Construct the same presentation in any concrete symbol dictionary. The
slot assignment can follow the caller's variable numbering. -/
private def std : List Rule := [.expOne,.tower,.neutral,.inverse,.inverseRest,.inside,.insideRest]
private def extra : List ExtraRule := [.mulOne,.invInv,.invOne,.join,.pull,.joinRest]
variable {sig : Signature} (s : Symbols sig) (v : Fin 3 → Variable)
  (typed : ∀ i, (v i).sort = .msg) (injective : ∀ i j, v i = v j → i = j)

def rules : List (Equation sig) :=
  std.map (fun r => r.instantiate s (fun i => .var (v i))) ++
  extra.map (fun r => r.instantiate s (fun i => .var (v i)))

def T : Table s where
  rules := rules s v
  actual _ := v
  actualSort _ := typed
  distinct _ := injective
  present r := List.mem_append_left _ (List.mem_map_of_mem
    (f := fun r : Rule => r.instantiate s (fun i => .var (v i))) (by cases r <;> decide : r ∈ std))

def E : ExtraTable (T s v typed injective) where
  actual _ := v
  sorted _ := typed
  distinct _ := injective
  present r := List.mem_append_right _ (List.mem_map_of_mem
    (f := fun r : ExtraRule => r.instantiate s (fun i => .var (v i))) (by cases r <;> decide : r ∈ extra))

theorem exactTable : ExactTable (E s v typed injective) := by
  intro eq h
  rcases List.mem_append.mp h with h|h <;> obtain ⟨r,_,rfl⟩ := List.mem_map.mp h
  · exact .inl ⟨r,rfl⟩
  · exact .inr ⟨r,rfl⟩

end Tamarin.Rewriting.DHPeer.Schemas

namespace Tamarin.Rewriting.DHPeer.Builtin

inductive Free where | power | inverse | unit | neutral deriving DecidableEq

abbrev sig : Signature where
  FreeSym := Free
  CSym := Empty
  ACSym := Unit
  Atom := Nat × SortId
  arity | .power => 2 | .inverse => 1 | .unit | .neutral => 0
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort := Empty.elim
  acSort _ := .msg
  atomSort := Prod.snd

def s : Symbols sig := ⟨.power,.inverse,.unit,.neutral,(),rfl,rfl,rfl,rfl,
  fun _ => rfl,fun _ => rfl,rfl,rfl,rfl,rfl,rfl⟩

private def v (i : Fin 3) : Variable := ⟨i.val+1,.msg⟩
private theorem typed (i : Fin 3) : (v i).sort = .msg := rfl
private theorem injective (i j : Fin 3) (h : v i = v j) : i = j :=
  Fin.ext (Nat.succ.inj (congrArg Variable.id h))

def rules := Schemas.rules s v
def T := Schemas.T s v typed injective
def E := Schemas.E s v typed injective
theorem exactTable : ExactTable E := Schemas.exactTable s v typed injective

end Tamarin.Rewriting.DHPeer.Builtin
