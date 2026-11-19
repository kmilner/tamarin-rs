import Tamarin.DHPeerQuery

/-! The fresh-variable specialization of the general received-power query.
The narrow sort guarantees that a normalized exponent is one positive factor. -/
namespace Tamarin.Rewriting.DHPeer
variable {sig : Signature}

def Names.freshQuery (q : Names) : Query sig where
  toNames := q
  exponent := q.symbolic .fresh
  sortedExponent := q.typed .fresh
  independent := fun h => by cases q.distinct .peer .fresh h
  disjoint := by
    intro v h
    obtain rfl : v = q.var .fresh := h
    rintro (hb|hp|hn)
    · cases q.distinct _ _ hb
    · cases q.distinct _ _ hp
    · cases q.distinct _ _ hn

theorem Names.fresh_env (q : Names) : (q.freshQuery (sig := sig)).env = q.symbolic := by
  funext i; cases i <;> rfl

def Names.subst (q : Names) (s : Symbols sig) (k : Branch) : Substitution sig :=
  Substitution.binding (q.var .peer) (k.pair.1.eval s q.symbolic)
    (q.sorted .peer ▸ k.pair.1.sorted s _ q.typed)

def Names.input (q : Names) (s : Symbols sig) : Observation sig → Term sig
  | .power => s.power (q.symbolic .peer) (q.symbolic .fresh)
  | .context t => t

def Names.value (q : Names) (s : Symbols sig) (k : Branch) : Observation sig → Term sig
  | .power => k.pair.2.eval s q.symbolic
  | .context t => (q.subst s k).apply t

def Names.arm (q : Names) (s : Symbols sig) (k : Branch) (os : List (Observation sig)) : Variant sig :=
  ⟨q.subst s k, os.map (q.value s k)⟩


private theorem freshSubst (q : Names) (s : Symbols sig) (k : Branch) :
    q.freshQuery.subst s k = q.subst s k := by simp only [Query.subst,Names.subst,q.fresh_env]; rfl

private theorem freshInput (q : Names) (s : Symbols sig) : q.freshQuery.input s = q.input s := by
  funext o; cases o <;> rfl

private theorem freshValue (q : Names) (s : Symbols sig) (k : Branch) :
    q.freshQuery.value s k = q.value s k := by
  funext o; cases o <;> simp [Query.value,Names.value,freshSubst,q.fresh_env]

private theorem freshArm (q : Names) (s : Symbols sig) (os : List (Observation sig)) (k : Branch) :
    q.freshQuery.arm s k os = q.arm s k os := by simp [Query.arm,Names.arm,freshSubst,freshValue]

private theorem Names.imageSort (q : Names) (ρ : Substitution sig) (i : Slot) :
    HasSort (ρ.image (q.var i)) i.sort := q.sorted i ▸ ρ.sorted (q.var i)

private theorem freshClassify [DecidableEq sig.ACSym] (q : Names) (s : Symbols sig) (R : Root sig)
    (ρ : Substitution sig) (hn : Normalized R ρ) :
    ∃ k env, Realizes s R (ρ.image (q.var .peer)) (ρ.image (q.var .fresh)) k env :=
  classify s R _ _ (q.imageSort ρ .peer) (q.imageSort ρ .fresh) (hn _) (hn _)

/-- A single arm and a single normalized witness assignment realize the
original joint query. On the received power the value is reached by a genuine
DH rewrite path; on other observations it is the input instance modulo B.
Normality/uniqueness of the resulting values are separate obligations. -/
theorem factorTuple [DecidableEq sig.ACSym] {s : Symbols sig} (T : Table s) (q : Names)
    (os : List (Observation sig)) (fresh : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) :
    ∃ k ∈ arms, ∃ δ : Substitution sig, Normalized (ruleRoot T.rules) δ ∧
      Substitution.AgreesOn (Observed (os.map (q.input s))) ρ (δ.compose (q.subst s k)) ∧
      Realizes s (ruleRoot T.rules) (ρ.image (q.var .peer)) (ρ.image (q.var .fresh)) k
        (fun i => δ.apply (q.symbolic i)) ∧
      ∀ o ∈ os, Reduces (ruleRoot T.rules) (ρ.apply (q.input s o)) (δ.apply (q.value s k o)) := by
  obtain ⟨k,hk,δ,hd,ha,hr,hp⟩ := q.freshQuery.factorTuple T (freshClassify q s _) os fresh ρ hn
  refine ⟨k,hk,δ,hd,?_,?_,?_⟩
  · simpa only [freshInput,freshSubst] using ha
  · rw [q.fresh_env] at hr
    exact hr
  · simpa only [freshInput,freshValue] using hp

/-- Term-level obligations on an exact DH rewrite table. Uniqueness is needed
only for powers whose two children are already normal and whose new exponent
has sort Fresh. The tuple proof supplies all substitutions and all answers. -/
structure PowerNormalForms [DecidableEq sig.ACSym] (s : Symbols sig) (R : Root sig) (q : Names) : Prop where
  variables : Normalized R Substitution.identity
  bases : ∀ k : Branch, Normal R (k.pair.1.eval s q.symbolic)
  values : ∀ k : Branch, Normal R (k.pair.2.eval s q.symbolic)
  classified : ∀ {Y r k env}, Realizes s R Y r k env → HasSort r .fresh →
    Normal R (k.pair.2.eval s env)
  unique : ∀ {Y r}, HasSort Y .msg → HasSort r .fresh → Normal R Y → Normal R r →
    ∀ {u v}, NormalForm R (s.power Y r) u → NormalForm R (s.power Y r) v → EquivB u v

private theorem PowerNormalForms.fresh [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig} {q : Names}
    (f : PowerNormalForms s R q) : q.freshQuery.Forms s R := by
  exact ⟨f.variables,by simpa only [q.fresh_env] using f.bases,by simpa only [q.fresh_env] using f.values,
    freshClassify q s R, fun {ρ} _ _ _ h => f.classified h (q.imageSort ρ .fresh),
    fun {ρ} hn _ _ => f.unique (q.imageSort ρ .peer) (q.imageSort ρ .fresh) (hn _) (hn _)⟩

/-- Discharging localized DH normal-form obligations certifies all seven full
packed answers, including shared-witness completeness and substitution-only
reconstruction under the specification used by Rust. -/
theorem complete [DecidableEq sig.ACSym] {s : Symbols sig} (T : Table s) (q : Names)
    (forms : PowerNormalForms s (ruleRoot T.rules) q) (os : List (Observation sig))
    (fresh : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (contexts : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t) :
    CompleteVariants (ruleRoot T.rules) (os.map (q.input s)) (arms.map fun k => q.arm s k os) ∧
    ∀ a ∈ arms.map (fun k => q.arm s k os), a.Reconstructible (ruleRoot T.rules) (os.map (q.input s)) := by
  simpa only [freshInput,freshArm] using q.freshQuery.complete T forms.fresh os fresh contexts

/-- All return variables are either observed in the tuple or the three
reserved witnesses. This also covers variables introduced into a context
by the peer substitution. -/
theorem Names.safe (q : Names) (s : Symbols sig) (os : List (Observation sig)) (power : .power ∈ os)
    (avoid : List Variable) (fresh : ∀ v, q.witness v → v ∉ avoid) (k : Branch) :
    (q.arm s k os).Safe (os.map (q.input s)) avoid := by
  simpa only [freshArm,freshInput] using q.freshQuery.safe s os power avoid fresh k

/-- Every returned peer substitution is already solved. The unchanged arm
maps the peer to itself; the other six use only the original fresh variable
and the three witnesses in its range. -/
theorem Names.idempotent (q : Names) (s : Symbols sig) (k : Branch) (v : Variable) :
    (q.subst s k).apply ((q.subst s k).image v) = (q.subst s k).image v := by
  simpa only [freshSubst] using q.freshQuery.idempotent s k v

end Tamarin.Rewriting.DHPeer
