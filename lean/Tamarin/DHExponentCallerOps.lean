import Tamarin.DHExponent
import Tamarin.DHPeerComplete
import Tamarin.VariantJoinPacked

namespace Tamarin.Rewriting.DHExponent.Caller
open DHPeer ConstructorVariants
variable {sig : Signature}

inductive Operation (sig : Signature) where
  | product (reversed : Bool)
  | before (base : Term sig)
  | after (base : Term sig) (reversed : Bool)
  | tower (base : Term sig)

def Operation.map (f : Term sig → Term sig) : Operation sig → Operation sig
  | .product rev => .product rev
  | .before g => .before (f g)
  | .after g rev => .after (f g) rev
  | .tower g => .tower (f g)

def Operation.All (f : Term sig → Prop) : Operation sig → Prop
  | .product _ => True
  | .before g | .after g _ | .tower g => f g

def orderedProduct (s : Symbols sig) (rev : Bool) (y r : Term sig) : Term sig :=
  if rev then s.product.mul r y else s.product.mul y r

def Operation.input (s : Symbols sig) (y r : Term sig) : Operation sig → Term sig
  | .product rev => orderedProduct s rev y r
  | .before g => s.power g y
  | .after g rev => s.power g (orderedProduct s rev y r)
  | .tower g => s.power (s.power g y) r

def Operation.output (s : Symbols sig) (k : DHExponent.Branch) (v : Slot → Term sig) : Operation sig → Term sig
  | .product _ => k.result.eval s v
  | .before g => if k = .unit then g else s.power g (k.image.eval s v)
  | .after g _ | .tower g => if k = .cancelAll then g else s.power g (k.result.eval s v)

def symbolicEnv (q : DHPeer.Query sig) := env (q.symbolic .peer) q.exponent (q.symbolic .pos) (q.symbolic .neg)

theorem symbolicTyped (q : DHPeer.Query sig) (i : Slot) : HasSort (symbolicEnv q i) .msg := by
  cases i <;> first | exact q.sortedExponent | apply q.toNames.typed

def subst (q : DHPeer.Query sig) (s : Symbols sig) (k : DHExponent.Branch) : Substitution sig :=
  .binding (q.var .peer) (k.image.eval s (symbolicEnv q)) (q.sorted .peer ▸ k.image.sorted s _ (symbolicTyped q))

def value (q : DHPeer.Query sig) (s : Symbols sig) (k : DHExponent.Branch) (o : Operation sig) :=
  (o.map (subst q s k).apply).output s k (symbolicEnv q)

theorem apply_pow (s : Symbols sig) (σ : Substitution sig) (g e : Term sig) :
    σ.apply (s.power g e) = s.power (σ.apply g) (σ.apply e) := by
  apply congrArg (Term.free s.pow); funext i
  change σ.apply (if _ then _ else _) = (if _ then _ else _)
  split <;> rfl

theorem apply_input (s : Symbols sig) (σ : Substitution sig) (y r : Term sig) (o : Operation sig) :
    σ.apply (o.input s y r) = (o.map σ.apply).input s (σ.apply y) (σ.apply r) := by
  cases o <;> simp only [Operation.input,Operation.map,apply_pow]
  all_goals cases ‹Bool› <;> rfl

theorem apply_output (q : DHPeer.Query sig) (s : Symbols sig) (δ : Substitution sig) (k : DHExponent.Branch) (o : Operation sig) :
    δ.apply (value q s k o) =
      (o.map (δ.compose (subst q s k)).apply).output s k (fun i => δ.apply (symbolicEnv q i)) := by
  cases o <;> simp only [value,Operation.map,Operation.output,Substitution.apply_compose]
  all_goals first | exact Expr.subst_eval .. | split <;> simp only [apply_pow,Expr.subst_eval]

theorem equiv_pow (s : Symbols sig) {a b c d : Term sig} (h : EquivB a b) (h' : EquivB c d) :
    EquivB (s.power a c) (s.power b d) := by
  apply EquivB.free; intro i; split <;> assumption

theorem output_equiv (s : Symbols sig) (k : DHExponent.Branch) (v : Slot → Term sig)
    (f h : Term sig → Term sig) (o : Operation sig) (eq : o.All fun g => EquivB (f g) (h g)) :
    EquivB ((o.map f).output s k v) ((o.map h).output s k v) := by
  cases o <;> simp only [Operation.map,Operation.output,Operation.All] at *
  all_goals first | exact .refl _ | split <;> first | exact eq | exact equiv_pow _ eq (.refl _)

def StableBase (s : Symbols sig) (R : Root sig) (g : Term sig) : Prop :=
  HasSort g .msg ∧ ∀ ρ : Substitution sig, Normalized R ρ →
    Normal R (ρ.apply g) ∧ head (ρ.apply g) ≠ .free s.pow ∧ head (ρ.apply g) ≠ .free s.neutral

def witnessAssignment (q : DHPeer.Query sig) (ρ : Substitution sig) (p n : Term sig)
    (sp : HasSort p .msg) (sn : HasSort n .msg) : Substitution sig where
  image v := if v = q.var .pos then p else if v = q.var .neg then n else ρ.image v
  support := q.var .pos :: q.var .neg :: ρ.support
  outside := by intro v hv; simp_all [ρ.outside]
  sorted := by
    intro v; split
    · next eq => simpa [eq,q.sorted,Slot.sort] using sp
    · split
      · next eq => simpa [eq,q.sorted,Slot.sort] using sn
      · exact ρ.sorted v

theorem assignment (q : DHPeer.Query sig) {R : Root sig} (ρ : Substitution sig) (hn : Normalized R ρ)
    (p n : Term sig) (sp sn) (np : Normal R p) (nn : Normal R n) :
    let δ := witnessAssignment q ρ p n sp sn
    Normalized R δ ∧ (∀ v, ¬q.witness v → δ.image v = ρ.image v) ∧
    (fun i => δ.apply (symbolicEnv q i)) = env (ρ.image (q.var .peer)) (ρ.apply q.exponent) p n := by
  intro δ
  have orig (v) (h : ¬q.witness v) : δ.image v = ρ.image v := by
    simp only [Names.witness,not_or] at h
    simp [δ,witnessAssignment,h.2.1,h.2.2]
  refine ⟨?_,orig,?_⟩
  · intro v; change Normal R (if _ then _ else if _ then _ else _)
    split <;> first | assumption | split <;> first | assumption | exact hn _
  · have eq (i j) : q.var i = q.var j ↔ i = j := ⟨q.distinct i j,congrArg q.var⟩
    have factor : δ.apply q.exponent = ρ.apply q.exponent :=
      Term.subst_eq_of_agree _ _ _ (fun v hv => orig v (q.disjoint v hv))
    funext i
    cases i <;> first | exact factor | simp [symbolicEnv,env,Names.symbolic,Substitution.apply,Term.subst,δ,witnessAssignment,eq]


variable {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem nfBasis {R : Root sig} {t u v : Term sig} (eq : EquivB t u) (h : NormalForm R u v) :
    NormalForm R t v := by
  refine ⟨(Reduces.basis eq).trans h.1,h.2.1,?_⟩
  intro k typed; apply h.2.2
  exact Term.checkSort_sound _ _ (SortClash.check_equiv eq k ▸ Term.checkSort_complete typed)

theorem operationForm (pow : PowerBucket T) {y r k v}
    (h : Realizes s (ruleRoot T.rules) y r k v) (sy : HasSort y .msg) (sr : HasSort r .msg)
    (ny : Normal (ruleRoot T.rules) y) (o : Operation sig)
    (bases : o.All fun g => HasSort g .msg ∧ Normal (ruleRoot T.rules) g ∧
        head g ≠ .free s.pow ∧ head g ≠ .free s.neutral) :
    NormalForm (ruleRoot T.rules) (o.input s y r) (o.output s k v) := by
  cases o with
  | product rev =>
    cases rev
    · exact h.product
    · exact nfBasis (.ac_swap ..) h.product
  | before g => exact Realizes.beforeForm pow h sy ny bases.1 bases.2.1 bases.2.2.1 bases.2.2.2
  | after g rev =>
    have forward := Realizes.afterForm pow h sy sr bases.1 bases.2.1 bases.2.2.1 bases.2.2.2
    cases rev
    · exact forward
    · exact nfBasis (equiv_pow s (.refl _) (.ac_swap ..)) forward
  | tower g => exact Realizes.towerForm pow h sy sr bases.1 bases.2.1 bases.2.2.1 bases.2.2.2

theorem operationUnique (pow : PowerBucket T) (inv : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one) {y r u v}
    (sy : HasSort y .msg) (sr : HasSort r .msg) (ny : Normal (ruleRoot T.rules) y) (nr : Normal (ruleRoot T.rules) r)
    (o : Operation sig) (bases : o.All fun g => HasSort g .msg ∧ Normal (ruleRoot T.rules) g)
    (hu : NormalForm (ruleRoot T.rules) (o.input s y r) u) (hv : NormalForm (ruleRoot T.rules) (o.input s y r) v) :
    EquivB u v := by
  cases o with
  | product rev =>
    cases rev
    · exact inv.product_unique sy sr ny nr hu hv
    · exact inv.product_unique sr sy nr ny hu hv
  | before g => exact before_unique pow inv unit sy bases.1 ny bases.2 hu hv
  | after g rev =>
    cases rev
    · exact after_unique pow inv unit sy sr bases.1 ny nr bases.2 hu hv
    · exact after_unique pow inv unit sr sy bases.1 nr ny bases.2 hu hv
  | tower g => exact tower_unique pow inv unit sy sr bases.1 ny nr bases.2 hu hv

theorem Operation.map_all {o : Operation sig} {p h : Term sig → Prop} {f : Term sig → Term sig}
    (pred : o.All p) (transform : ∀ g, p g → h (f g)) : (o.map f).All h := by
  cases o <;> first | trivial | apply transform _ pred

theorem Operation.all_mono {o : Operation sig} {p h : Term sig → Prop}
    (pred : o.All p) (transform : ∀ g, p g → h g) : o.All h := by
  cases o <;> first | trivial | apply transform _ pred

theorem operationTyped (q : DHPeer.Query sig) (s : Symbols sig) (o : Operation sig)
    (bases : o.All fun g => HasSort g .msg) :
    let t := o.input s (q.symbolic .peer) q.exponent; HasSort t t.rootSort := by
  have sy := q.toNames.typed (sig := sig) .peer
  have sr := q.sortedExponent
  have prod (rev) : HasSort (orderedProduct s rev (q.symbolic .peer) q.exponent) .msg := by
    cases rev <;> apply s.mulSort ▸ HasSort.ac _ _ _ <;> first | exact s.mulSort ▸ sy | exact s.mulSort ▸ sr
  cases o with
  | product rev =>
    cases rev <;> apply HasSort.ac <;> first | exact s.mulSort ▸ sy | exact s.mulSort ▸ sr
  | before g => change HasSort _ (sig.outputSort s.pow); rw [s.powSort]; exact DHTower.powerSorted bases sy
  | after g rev => change HasSort _ (sig.outputSort s.pow); rw [s.powSort]; exact DHTower.powerSorted bases (prod rev)
  | tower g => change HasSort _ (sig.outputSort s.pow); rw [s.powSort]; exact DHTower.powerSorted (DHTower.powerSorted bases sy) sr

end Tamarin.Rewriting.DHExponent.Caller
