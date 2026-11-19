import Tamarin.DHExponentCallerOps
import Tamarin.DHExponentCallerTuple
import Tamarin.DHExponentSymbolic

/-! Completeness of the live packet for joint observations of one free
message exponent and its extension by a common stable positive factor.
Bases can differ, share variables, and depend on the exponent. -/
namespace Tamarin.Rewriting.DHExponent.Caller
open DHPeer ConstructorVariants VariantJoin
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem fromBase {g e : Term sig} {v} (h : g.Occurs v) : (s.power g e).Occurs v :=
  ⟨⟨0,by rw [s.powArity]; decide⟩,h⟩

private theorem baseVariables (o : Operation sig) (s : Symbols sig) (y r : Term sig) :
    o.All fun g => ∀ v, g.Occurs v → (o.input s y r).Occurs v := by
  cases o with
  | product => trivial
  | before | after => exact fun _ h => fromBase h
  | tower => exact fun _ h => fromBase (fromBase h)

private theorem baseInstances {o : Operation sig} (stable : o.All (StableBase s (ruleRoot T.rules)))
    {ρ : Substitution sig} (hn : Normalized (ruleRoot T.rules) ρ) :
    (o.map ρ.apply).All fun g => HasSort g .msg ∧ Normal (ruleRoot T.rules) g ∧
        head g ≠ .free s.pow ∧ head g ≠ .free s.neutral :=
  Operation.map_all stable (fun _ h => ⟨h.1.subst _ ρ.sorted,h.2 ρ hn⟩)

private theorem symbolicArm (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (q : DHPeer.Query sig)
    (stable : StableFactor s (ruleRoot T.rules) q.exponent) (k : DHExponent.Branch) :
    Normalized (ruleRoot T.rules) (subst q s k) ∧ ∀ o : Operation sig, o.All (StableBase s (ruleRoot T.rules)) →
      NormalForm (ruleRoot T.rules) ((subst q s k).apply (o.input s (q.symbolic .peer) q.exponent)) (value q s k o) := by
  have vars := (constructor_normal _ pow.1).1
  have initial : Normal (ruleRoot T.rules) q.exponent ∧ Factor s q.exponent := by simpa using stable .identity vars
  have apart : ¬EquivB (q.symbolic .pos) q.exponent := by
    intro eq
    have occurs : q.exponent.Occurs (q.var .pos) := by
      cases h : q.exponent <;> rw [h] at eq <;> cases eq.head_eq; rfl
    exact q.disjoint _ occurs (.inr (.inl rfl))
  have sy := q.toNames.typed (sig := sig) .peer
  obtain ⟨normal,real⟩ := symbolic pow mul inv unit (q.var .peer) (q.var .pos) (q.var .neg) q.exponent sy
    (q.toNames.typed .pos) (q.toNames.typed .neg) q.sortedExponent initial.1 initial.2
    (fun h => by cases q.distinct .pos .neg h) apart k
  have normalized : Normalized (ruleRoot T.rules) (subst q s k) := by
    intro x; change Normal _ (if _ then _ else _)
    split <;> first | exact normal | exact vars _
  refine ⟨normalized,fun o admissible => ?_⟩
  rw [apply_input,show (subst q s k).apply (q.symbolic .peer) = k.image.eval s (symbolicEnv q) from Substitution.binding_image_self ..,
    show (subst q s k).apply q.exponent = q.exponent from Substitution.binding_apply_of_not_occurs _ _ _ _ q.independent]
  exact operationForm pow real (k.image.sorted s _ (symbolicTyped q)) q.sortedExponent normal _ (baseInstances admissible normalized)

private theorem classifyTuple {packet : Array (Array UInt64)} (ok : Packet.Correct packet) (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (inventory : Balance.Inventory E)
    (q : DHPeer.Query sig) (factor : StableFactor s (ruleRoot T.rules) q.exponent)
    {A : Type} (ops : A → Operation sig) (bases : ∀ a, (ops a).All (StableBase s (ruleRoot T.rules)))
    {keys : List Variable} (apart : ∀ v ∈ keys, ¬q.witness v)
    (includes : ∀ a v, ((ops a).input s (q.symbolic .peer) q.exponent).Occurs v → v ∈ keys)
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) (outs : A → Term sig)
    (actual : ∀ a, NormalForm (ruleRoot T.rules) (ρ.apply ((ops a).input s (q.symbolic .peer) q.exponent)) (outs a)) :
    ∃ k ∈ Packet.emitted packet, ∃ δ : Substitution sig, Normalized (ruleRoot T.rules) δ ∧
      (∀ i : Key keys, EquivB (ρ.image i.val) (δ.apply ((subst q s k).image i.val))) ∧
      ∀ a, EquivB (outs a) (δ.apply (value q s k (ops a))) := by
  have sy : HasSort (ρ.image (q.var .peer)) .msg := by simpa only [q.sorted,Slot.sort] using ρ.sorted (q.var .peer)
  have sr := q.sortedExponent.subst _ ρ.sorted
  obtain ⟨nr,fr⟩ := factor ρ hn
  obtain ⟨k,p,n,real⟩ := classify mul inv unit sy (hn _) sr nr fr
  let δ := witnessAssignment q ρ p n (real.typed .pos) (real.typed .neg)
  obtain ⟨nd,orig,eq⟩ := assignment q ρ hn p n (real.typed .pos) (real.typed .neg) (real.normal .pos) (real.normal .neg)
  have agree (v) (hv : v ∈ keys) : EquivB (ρ.image v) ((δ.compose (subst q s k)).image v) := by
    change EquivB _ (δ.apply ((subst q s k).image v))
    by_cases same : v = q.var .peer
    · subst v; rw [subst,Substitution.binding_image_self,Expr.subst_eval,show (fun i => δ.apply (symbolicEnv q i)) = _ from eq]
      exact real.image
    · change EquivB _ (δ.apply (if v = q.var .peer then _ else .var v))
      rw [ite_eq_right same]; change EquivB _ (δ.image v)
      rw [show δ.image v = _ from orig v (apart _ hv)]; exact .refl _
  refine ⟨k,Packet.mem_emitted ok k,δ,nd,fun i => agree _ i.property,?_⟩
  intro a
  let o := ops a
  have bs := baseInstances (bases a) hn
  have predicted := operationForm pow real sy sr (hn _) (o.map ρ.apply) bs
  have concrete := actual a
  rw [apply_input] at concrete
  have out := operationUnique pow inventory unit sy sr (hn _) nr _ (Operation.all_mono bs (fun _ h => ⟨h.1,h.2.1⟩)) concrete predicted
  rw [apply_output,show (fun i => δ.apply (symbolicEnv q i)) = _ from eq]
  refine out.trans (output_equiv _ _ _ _ _ o ?_)
  exact Operation.all_mono (baseVariables o s (q.symbolic .peer) q.exponent)
    (fun g occurs => g.subst_equiv _ _ (fun v hv => agree _ (includes a v (occurs v hv))))

/-- A successful export denotes the full variants of the original tuple,
including any independently ordered duplicate slots and uniform reductions.
Opening each emitted row uses one simultaneous caller-supplied renaming. -/
def Semantic (packet : Array (Array UInt64)) : Prop :=
  (∀ row ∈ packet, ∃ k ∈ Packet.emitted packet, Packet.decode row = some k.image) ∧
  ∀ {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    (_ : PowerBucket T) (_ : MulBucket E) (_ : InverseBucket E)
    (_ : ∀ eq ∈ T.rules, head eq.lhs ≠ .free s.one)
    (q : DHPeer.Query sig) (_ : StableFactor s (ruleRoot T.rules) q.exponent)
    {A : Type} (ops : A → Operation sig) (_ : ∀ a, (ops a).All (StableBase s (ruleRoot T.rules)))
    {keys : List Variable} (_ : ∀ v ∈ keys, ¬q.witness v)
    (rows : List (Row sig (Key keys) A))
    (_ : ∀ k ∈ Packet.emitted packet, ∃ r ∈ rows, (row keys (subst q s) (fun k a => value q s k (ops a)) k).Relabels r)
    (_ : ∀ r ∈ rows, ∃ k ∈ Packet.emitted packet, (row keys (subst q s) (fun k a => value q s k (ops a)) k).Relabels r)
    (slots : List (Sum A (Term sig))) (_ : ∀ a, .inl a ∈ slots)
    (repr : Term sig → Term sig)
    (_ : ∀ t, .inr t ∈ slots → StableVariants.Representative (ruleRoot T.rules) t (repr t))
    (_ : ∀ v, v ∈ keys ↔ Observed (slots.map (packedInput (fun a => (ops a).input s (q.symbolic .peer) q.exponent))) v)
    (avoid : List Variable) (_ : ∀ r ∈ rows, ∀ v, r.Uses v → v ∉ keys ++ avoid),
    ∃ sorted : ∀ r ∈ rows, r.Sorted,
      let query := slots.map (packedInput (fun a => (ops a).input s (q.symbolic .peer) q.exponent))
      let answers := packRows rows sorted slots repr
      CompleteVariants (ruleRoot T.rules) query answers ∧ ∀ a ∈ answers,
        a.Reconstructible (ruleRoot T.rules) query ∧ a.Safe query avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

theorem certified {packet : Array (Array UInt64)} (ok : Packet.Correct packet) : Semantic packet := by
  refine ⟨fun _ h => Packet.interpreted ok h,?_⟩
  intro sig s T E pow mul inv one q factor A ops bases keys apart rows allRows onlyRows slots used repr uniform scope avoid fresh
  let op a := (ops a).input s (q.symbolic .peer) q.exponent
  have includes (a v) (h : (op a).Occurs v) : v ∈ keys :=
    (scope v).mpr ⟨_,List.mem_map_of_mem (f := packedInput op) (used a),h⟩
  have unit := normalConstant _ pow.1 _ s.oneArity one
  have inventory := Balance.Inventory.of_buckets mul inv one
  have arm := symbolicArm pow mul inv unit q factor
  apply pack (Packet.emitted packet) (subst q s) op (fun k a => value q s k (ops a))
    (fun a => operationTyped q s (ops a) (Operation.all_mono (bases a) (fun _ h => h.1))) (constructor_normal _ pow.1).1
    (fun k _ => (arm k).1) (fun k _ a => (arm k).2 _ (bases a))
    (classifyTuple ok pow mul inv unit inventory q factor ops bases apart includes) _
    rows allRows onlyRows slots used repr uniform scope avoid fresh
  intro ρ hn a u v hu hv
  change NormalForm _ (ρ.apply ((ops a).input _ _ _)) _ at hu hv
  rw [apply_input] at hu hv
  have sy : HasSort (ρ.image (q.var .peer)) .msg := by simpa only [q.sorted,Slot.sort] using ρ.sorted (q.var .peer)
  exact operationUnique pow inventory unit sy (q.sortedExponent.subst _ ρ.sorted) (hn _) (factor ρ hn).1 _
    (Operation.all_mono (baseInstances (bases a) hn) (fun _ h => ⟨h.1,h.2.1⟩)) hu hv

end Tamarin.Rewriting.DHExponent.Caller
