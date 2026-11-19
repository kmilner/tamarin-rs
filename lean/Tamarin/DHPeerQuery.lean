import Tamarin.DHPeerNames
import Tamarin.StableVariants

/-! The caller's exponent is a term. Every occurrence in the query, in the
peer image, and in the returned values uses the same simultaneous substitution.
Only the three arm-local witnesses may be specialized independently. -/
namespace Tamarin.Rewriting.DHPeer
variable {sig : Signature}

structure Query (sig : Signature) extends Names where
  exponent : Term sig
  sortedExponent : HasSort exponent .msg
  independent : ¬exponent.Occurs (var .peer)
  disjoint : ∀ v, exponent.Occurs v → ¬toNames.witness v

def Query.env (q : Query sig) (i : Slot) : Term sig :=
  if i = .fresh then q.exponent else q.symbolic i

theorem Query.typed (q : Query sig) (i : Slot) : HasSort (q.env i) .msg := by
  unfold env; split
  · exact q.sortedExponent
  · exact q.toNames.typed i
def Query.subst (q : Query sig) (s : Symbols sig) (k : Branch) : Substitution sig :=
  Substitution.binding (q.var .peer) (k.pair.1.eval s q.env)
    (q.sorted .peer ▸ k.pair.1.sorted s _ q.typed)

def Query.input (q : Query sig) (s : Symbols sig) : Observation sig → Term sig
  | .power => s.power (q.env .peer) (q.env .fresh)
  | .context t => t

def Query.value (q : Query sig) (s : Symbols sig) (k : Branch) : Observation sig → Term sig
  | .power => k.pair.2.eval s q.env
  | .context t => (q.subst s k).apply t

def Query.arm (q : Query sig) (s : Symbols sig) (k : Branch) (os : List (Observation sig)) : Variant sig :=
  ⟨q.subst s k, os.map (q.value s k)⟩

private def specialize (q : Names) (ρ : Substitution sig) (env : Slot → Term sig)
    (ht : ∀ i, HasSort (env i) .msg) : Substitution sig where
  image v := if v = q.var .base then env .base else if v = q.var .pos then env .pos
             else if v = q.var .neg then env .neg else ρ.image v
  support := [q.var .base, q.var .pos, q.var .neg] ++ ρ.support
  outside := by
    intro v hv
    simp only [List.cons_append,List.nil_append,List.mem_cons,not_or] at hv
    simp [hv.1,hv.2.1,hv.2.2.1,ρ.outside v hv.2.2.2]
  sorted := by
    intro v
    split
    · next h => simpa [h,q.sorted,Slot.sort] using ht .base
    · split
      · next h => simpa [h,q.sorted,Slot.sort] using ht .pos
      · split
        · next h => simpa [h,q.sorted,Slot.sort] using ht .neg
        · exact ρ.sorted v

private theorem Query.extended [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig} (q : Query sig)
    (ρ : Substitution sig) (hn : Normalized R ρ) {k : Branch} {env}
    (h : Realizes s R (ρ.image (q.var .peer)) (ρ.apply q.exponent) k env) :
    ∃ δ : Substitution sig, Normalized R δ ∧
      (∀ i, δ.apply (q.env i) = env i) ∧ ∀ v, ¬q.witness v → δ.image v = ρ.image v := by
  let δ := specialize q.toNames ρ env h.typed
  have original (v) (hv : ¬ q.witness v) : δ.image v = ρ.image v := by
    simp only [Names.witness,not_or] at hv
    simp [δ,specialize,hv.1,hv.2.1,hv.2.2]
  refine ⟨δ, ?_, ?_, original⟩
  · intro v
    simp only [δ,specialize]; split <;> first | exact h.normal _ | split <;> first | exact h.normal _ | split <;> first | exact h.normal _ | exact hn v
  · intro i
    by_cases fresh : i = .fresh
    · subst i
      change δ.apply q.exponent = env .fresh
      rw [h.fresh]
      exact Term.subst_eq_of_agree _ _ _ (fun v hv => original v (q.disjoint v hv))
    · have eq (j : Slot) : q.var i = q.var j ↔ i = j := ⟨q.distinct i j, congrArg q.var⟩
      simp only [Query.env,ite_eq_right fresh,Names.symbolic,Substitution.apply,Term.subst,δ,specialize,eq]
      cases i <;> simp_all [h.peer]

theorem Query.apply_power (q : Query sig) (s : Symbols sig) (ρ : Substitution sig) :
    ρ.apply (q.input s .power) = s.power (ρ.image (q.var .peer)) (ρ.apply q.exponent) :=
  (Expr.pow peer r).subst_eval s q.env ρ

/-- Term-level facts for the power in this query. Classification, normality
and uniqueness are stated at the caller's actual exponent instance. -/
structure Query.Forms [DecidableEq sig.ACSym] (q : Query sig) (s : Symbols sig) (R : Root sig) : Prop where
  variables : Normalized R Substitution.identity
  bases : ∀ k : Branch, Normal R (k.pair.1.eval s q.env)
  values : ∀ k : Branch, Normal R (k.pair.2.eval s q.env)
  classify : ∀ ρ : Substitution sig, Normalized R ρ →
    ∃ k env, Realizes s R (ρ.image (q.var .peer)) (ρ.apply q.exponent) k env
  normal : ∀ {ρ : Substitution sig}, Normalized R ρ → ∀ {k env},
    Realizes s R (ρ.image (q.var .peer)) (ρ.apply q.exponent) k env → Normal R (k.pair.2.eval s env)
  unique : ∀ {ρ : Substitution sig}, Normalized R ρ → ∀ {u v},
    NormalForm R (s.power (ρ.image (q.var .peer)) (ρ.apply q.exponent)) u →
    NormalForm R (s.power (ρ.image (q.var .peer)) (ρ.apply q.exponent)) v → EquivB u v
/-- A single arm and a single normalized witness assignment realize the
original joint query. On the received power the value is reached by a genuine
DH rewrite path; on other observations it is the input instance modulo B.
Normality/uniqueness of the resulting values are separate obligations. -/
theorem Query.factorTuple [DecidableEq sig.ACSym] {s : Symbols sig} (q : Query sig) (T : Table s)
    (classes : ∀ ρ : Substitution sig, Normalized (ruleRoot T.rules) ρ → ∃ k env, Realizes s (ruleRoot T.rules) (ρ.image (q.var .peer)) (ρ.apply q.exponent) k env)
    (os : List (Observation sig)) (fresh : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (ρ : Substitution sig) (hn : Normalized (ruleRoot T.rules) ρ) :
    ∃ k ∈ arms, ∃ δ : Substitution sig, Normalized (ruleRoot T.rules) δ ∧
      Substitution.AgreesOn (Observed (os.map (q.input s))) ρ (δ.compose (q.subst s k)) ∧
      Realizes s (ruleRoot T.rules) (ρ.image (q.var .peer)) (ρ.apply q.exponent) k
        (fun i => δ.apply (q.env i)) ∧
      ∀ o ∈ os, Reduces (ruleRoot T.rules) (ρ.apply (q.input s o)) (δ.apply (q.value s k o)) := by
  obtain ⟨k,env,h⟩ := classes ρ hn
  obtain ⟨δ,nd,slot,original⟩ := q.extended ρ hn h
  have read (e : Expr Slot) : δ.apply (e.eval s q.env) = e.eval s env := by
    rw [e.subst_eval]; exact congrArg (e.eval s) (funext slot)
  have agree : Substitution.AgreesOn (Observed (os.map (q.input s))) ρ (δ.compose (q.subst s k)) := by
    intro v obs
    change EquivB _ (δ.apply ((q.subst s k).image v))
    by_cases eq : v = q.var .peer
    · subst v; simp only [Query.subst,Substitution.binding,ite_true,read]
      exact h.base
    · simp only [Query.subst,Substitution.binding,ite_eq_right eq,Substitution.apply,Term.subst,original _ (fresh _ obs)]
      exact .refl _
  refine ⟨k, by cases k <;> simp [arms],δ,nd,agree,?_,?_⟩
  · rw [funext slot]; exact h
  · intro o ho
    cases o with
    | power =>
      rw [q.apply_power]
      change Reduces _ _ (δ.apply (k.pair.2.eval s q.env))
      rw [read]
      exact h.reduces T
    | context t =>
      change Reduces _ (ρ.apply t) (δ.apply ((q.subst s k).apply t))
      rw [← Substitution.apply_compose]
      exact .basis (t.subst_equiv _ _ fun v hv => agree v ⟨_,List.mem_map_of_mem (f := q.input s) ho,hv⟩)


private theorem powerForm {s : Symbols sig} {R : Root sig} {Y r u : Term sig}
    (red : Reduces R (s.power Y r) u) (normal : Normal R u) (typed : HasSort u .msg) :
    NormalForm R (s.power Y r) u :=
  ⟨red, normal, fun _ hs => .widen typed (s.powSort ▸ Term.rootSort_le hs)⟩

private theorem Query.normalized [DecidableEq sig.ACSym] {s : Symbols sig} {R : Root sig}
    (q : Query sig) (forms : q.Forms s R) (k : Branch) : Normalized R (q.subst s k) := by
  intro v
  simp only [Query.subst, Substitution.binding]
  split
  · exact forms.bases k
  · exact forms.variables v

private theorem Query.fixes_exponent (q : Query sig) (s : Symbols sig) (k : Branch) :
    (q.subst s k).apply q.exponent = q.exponent := by
  apply Eq.trans (Term.subst_eq_of_agree _ Term.var _ ?_) (Term.subst_id _)
  intro v inExp
  have ne : v ≠ q.var .peer := fun eq => q.independent (eq ▸ inExp)
  simp [Query.subst,Substitution.binding,ne]

private theorem Query.symbolic_power (q : Query sig) (s : Symbols sig) (k : Branch) :
    (q.subst s k).apply (q.input s .power) = s.power (k.pair.1.eval s q.env) q.exponent := by
  rw [q.apply_power,q.fixes_exponent]
  simp [Query.subst,Substitution.binding]

private theorem armSound [DecidableEq sig.ACSym] {s : Symbols sig} (T : Table s) (q : Query sig)
    (forms : q.Forms s (ruleRoot T.rules)) (os : List (Observation sig))
    (contexts : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t)
    (k : Branch) : (q.arm s k os).Sound (ruleRoot T.rules) (os.map (q.input s)) := by
  have norm := q.normalized forms k
  refine ⟨norm, aligned_maps os (q.input s) (q.value s k) ?_⟩
  intro o ho
  cases o with
  | power =>
    rw [show (q.arm s k os).subst = q.subst s k from rfl, q.symbolic_power]
    exact powerForm (T.reaches q.env q.typed k) (forms.values k) (k.pair.2.sorted s _ q.typed)
  | context t => exact ⟨.basis (.refl _), contexts t ho _ norm, fun _ hn => hn⟩

/-- Discharging localized DH normal-form obligations certifies all seven full
packed answers, including shared-witness completeness and substitution-only
reconstruction under the specification used by Rust. -/
theorem Query.complete [DecidableEq sig.ACSym] {s : Symbols sig} (T : Table s) (q : Query sig)
    (forms : q.Forms s (ruleRoot T.rules)) (os : List (Observation sig))
    (fresh : ∀ v, Observed (os.map (q.input s)) v → ¬q.witness v)
    (contexts : ∀ t, .context t ∈ os → StableVariants.Stable (ruleRoot T.rules) t) :
    CompleteVariants (ruleRoot T.rules) (os.map (q.input s)) (arms.map fun k => q.arm s k os) ∧
    ∀ a ∈ arms.map (fun k => q.arm s k os), a.Reconstructible (ruleRoot T.rules) (os.map (q.input s)) := by
  constructor
  · constructor
    · intro a ha
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      exact armSound T q forms os contexts k
    · intro ρ hn values nfs
      obtain ⟨k,hk,δ,nd,agree,instanceOf,path⟩ := q.factorTuple T forms.classify os fresh ρ hn
      refine ⟨q.arm s k os, List.mem_map_of_mem (f := fun k => q.arm s k os) hk,δ,nd,agree,?_⟩
      apply aligned_values os (q.input s) (q.value s k) values nfs
      intro o ho u nf
      have red := path o ho
      cases o with
      | power =>
        rw [q.apply_power] at red nf
        apply forms.unique hn nf
        apply powerForm red
        · change Normal _ (δ.apply (k.pair.2.eval s q.env))
          rw [Expr.subst_eval]
          exact forms.normal hn instanceOf
        · change HasSort (δ.apply (k.pair.2.eval s q.env)) .msg
          rw [Expr.subst_eval]
          exact k.pair.2.sorted s _ instanceOf.typed
      | context t =>
        have normal := contexts t ho ρ hn
        exact (normal_reduces_equiv nf.1 normal).symm.trans (normal_reduces_equiv red normal)
  · intro a ha
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    have norm := q.normalized forms k
    apply Variant.reconstructible_of_unique (armSound T q forms os contexts k)
    intro t ht u v hu hv
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ht
    cases o with
    | power =>
      change NormalForm _ ((q.subst s k).apply (q.input s .power)) _ at hu hv
      rw [q.apply_power] at hu hv
      exact forms.unique norm hu hv
    | context t =>
      have normal := contexts t ho _ norm
      exact (normal_reduces_equiv hu.1 normal).symm.trans (normal_reduces_equiv hv.1 normal)



private theorem occursSlot (s : Symbols sig) (env : Slot → Term sig) (e : Expr Slot) (w : Variable)
    (occ : (e.eval s env).Occurs w) : ∃ i, (env i).Occurs w := by
  induction e with
  | var i => exact ⟨i,occ⟩
  | pow a b ia ib =>
    obtain ⟨i,hi⟩ := occ
    change Term.Occurs w (if _ then _ else _) at hi
    split at hi <;> first | exact ia hi | exact ib hi
  | mul a b ia ib => exact occ.elim ia ib
  | inv _ ih => exact ih occ.choose_spec
  | one => exact Fin.elim0 (s.oneArity ▸ occ.choose)
  | neutral => exact Fin.elim0 (s.neutralArity ▸ occ.choose)

/-- All return variables are either observed in the tuple or the three
reserved witnesses. This also covers variables introduced into a context
by the peer substitution. -/
theorem Query.safe (q : Query sig) (s : Symbols sig) (os : List (Observation sig)) (power : .power ∈ os)
    (avoid : List Variable) (fresh : ∀ v, q.witness v → v ∉ avoid) (k : Branch) :
    (q.arm s k os).Safe (os.map (q.input s)) avoid := by
  have present := List.mem_map_of_mem (f := q.input s) power
  let i0 : Fin (sig.arity s.pow) := ⟨0,by rw [s.powArity]; decide⟩
  let i1 : Fin (sig.arity s.pow) := ⟨1,by rw [s.powArity]; decide⟩
  have seen : Observed (os.map (q.input s)) (q.var .peer) := ⟨_,present,i0,rfl⟩
  have slot (i : Slot) (w : Variable) (hw : (q.env i).Occurs w) :
      Observed (os.map (q.input s)) w ∨ w ∉ avoid := by
    cases i with
    | peer => exact .inl (hw ▸ seen)
    | fresh => exact .inl ⟨_,present,i1,hw⟩
    | base => exact .inr (hw ▸ fresh _ (.inl rfl))
    | pos => exact .inr (hw ▸ fresh _ (.inr (.inl rfl)))
    | neg => exact .inr (hw ▸ fresh _ (.inr (.inr rfl)))
  have safeImage (v) (obs : Observed (os.map (q.input s)) v) (w) (occ : ((q.subst s k).image v).Occurs w) :
      Observed (os.map (q.input s)) w ∨ w ∉ avoid := by
    by_cases h : v = q.var .peer
    · simp only [Query.subst, Substitution.binding, h,ite_true] at occ
      obtain ⟨i,hi⟩ := occursSlot _ q.env _ _ occ
      exact slot i w hi
    · simp only [Query.subst,Substitution.binding,ite_eq_right h,Term.Occurs] at occ
      exact .inl (occ ▸ obs)
  constructor
  · intro v missing
    have apart : v ≠ q.var .peer := fun eq => missing (eq ▸ seen)
    simp [Query.arm,Query.subst,Substitution.binding,apart]
  · exact safeImage
  · intro t ht w occ
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp ht
    cases o with
    | power =>
      obtain ⟨i,hi⟩ := occursSlot _ q.env _ _ occ
      exact slot i w hi
    | context t =>
      obtain ⟨v,hv,hw⟩ := (q.subst s k).occurs_in_image t w occ
      exact safeImage v ⟨_,List.mem_map_of_mem (f := q.input s) ho,hv⟩ w hw

/-- Every returned peer substitution is already solved. The unchanged arm
maps the peer to itself. The other six may mention any variables of the
caller’s exponent and the three witnesses. -/
theorem Query.idempotent (q : Query sig) (s : Symbols sig) (k : Branch) (v : Variable) :
    (q.subst s k).apply ((q.subst s k).image v) = (q.subst s k).image v := by
  have other (i : Slot) (apart : i ≠ .peer) : (q.subst s k).apply (q.env i) = q.env i := by
    by_cases eq : i = .fresh
    · subst i; exact q.fixes_exponent s k
    rw [Query.env,ite_eq_right eq]
    have h : q.var i ≠ q.var .peer := fun eq => apart (q.distinct _ _ eq)
    simp [Names.symbolic,Query.subst,Substitution.binding,Substitution.apply,Term.subst,h]
  by_cases eq : v = q.var .peer
  · subst v
    have bound : (q.subst s k).image (q.var .peer) = k.pair.1.eval s q.env := by simp [Query.subst,Substitution.binding]
    rw [bound,Expr.subst_eval]
    have hb := other .base (by decide)
    have hp := other .pos (by decide)
    have hn := other .neg (by decide)
    have hr := other .fresh (by decide)
    cases k <;> first | exact bound | simp [Branch.pair,Expr.eval,hb,hp,hn,hr]
  · simp [Query.subst,Substitution.binding,eq,Substitution.apply,Term.subst]

end Tamarin.Rewriting.DHPeer
