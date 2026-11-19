import Tamarin.ACFactorExclusion
import Tamarin.RootExclusion
import Tamarin.ACRepresentation
import Tamarin.Cancellation

/-! A stable term remains normal after *every normalized substitution*.
Rule-table head exclusions compose with this property under constructors.
At AC heads, exclusion applies to every possible regrouping of the factors. -/
namespace Tamarin.Rewriting.StableVariants
open ConstructorVariants
variable {s : Signature} {R : Root s}

def Stable (R : Root s) (t : Term s) : Prop :=
  ∀ ρ : Substitution s, Normalized R ρ → Normal R (ρ.apply t)

theorem constructors (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (t : Term s) (absent : ∀ h ∈ operators t, h ∉ ruleHeads rules) :
    Stable (ruleRoot rules) t := (constructor_normal rules apps).2 t absent

theorem freeContext (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (absent : .free f ∉ ruleHeads rules)
    (children : ∀ i, Stable (ruleRoot rules) (xs i)) : Stable (ruleRoot rules) (.free f xs) :=
  fun ρ hn => constructor_node_normal rules apps _ absent (fun i => children i ρ hn)

theorem commContext (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.CSym) (a b : Term s) (absent : .comm f ∉ ruleHeads rules)
    (ha : Stable (ruleRoot rules) a) (hb : Stable (ruleRoot rules) b) :
    Stable (ruleRoot rules) (.comm f a b) := fun ρ hn =>
  constructor_node_normal rules apps _ absent ⟨ha ρ hn, hb ρ hn⟩

theorem acContext (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (a b : Term s) (absent : .ac f ∉ ruleHeads rules)
    (ha : Stable (ruleRoot rules) a) (hb : Stable (ruleRoot rules) b) :
    Stable (ruleRoot rules) (.ac f a b) := fun ρ hn =>
  constructor_node_normal rules apps _ absent ⟨ha ρ hn, hb ρ hn⟩

/-- A narrow variable stays a leaf when no operator can return its sort or a
subsort. It may become an atom or another variable under substitution. -/
theorem narrow_leaf (v : Variable) (ρ : Substitution s)
    (hf : ∀ f, ¬ Subsort (s.outputSort f) v.sort)
    (hc : ∀ f, ¬ Subsort (s.cSort f) v.sort)
    (ha : ∀ f, ¬ Subsort (s.acSort f) v.sort) :
    ¬ Application (ρ.image v) := by
  have sorted := Term.rootSort_le (ρ.sorted v)
  cases e : ρ.image v with
  | var | atom => exact id
  | free f _ => exact False.elim (hf f (by simpa only [e, Term.rootSort] using sorted))
  | comm f _ _ => exact False.elim (hc f (by simpa only [e, Term.rootSort] using sorted))
  | ac f _ _ => exact False.elim (ha f (by simpa only [e, Term.rootSort] using sorted))

theorem narrow_word (v : Variable) (word : Head s → UInt64)
    (vars : ∀ w, word (.var w) = 0) (atoms : ∀ a, word (.atom a) = 0)
    (leaves : ∀ ρ : Substitution s, ¬ Application (ρ.image v)) (ρ : Substitution s) :
    word (head (ρ.image v)) = word (head (.var v)) := by
  have h := leaves ρ
  cases e : ρ.image v with
  | var w => exact (vars w).trans (vars v).symm
  | atom a => exact (atoms a).trans (vars v).symm
  | free | comm | ac => exact False.elim (h (e ▸ trivial))

theorem freeExcluded {run} (check : RootExclusion.Correct run)
    (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.FreeSym) (xs : Fin (s.arity f) → Term s)
    (children : ∀ i, Stable (ruleRoot rules) (xs i)) (code : Head s → UInt64)
    (fixed : ∀ ρ : Substitution s, ∀ i, code (head (ρ.apply (xs i))) = code (head (xs i)))
    (rows : Array (Array UInt64))
    (allRules : ∀ p rhs, (⟨.free f p, rhs⟩ : Equation s) ∈ rules →
      (Array.ofFn fun i => RootExclusion.required code (p i)) ∈ rows)
    (ok : run rows (Array.ofFn fun i => code (head (xs i))) = true) :
    Stable (ruleRoot rules) (.free f xs) := by
  intro ρ hn
  apply (RootExclusion.normal check rules apps f (fun i => ρ.apply (xs i))
    (fun i => children i ρ hn) code rows allRules ?_).2.1
  simpa only [fixed] using ok

section AC
variable [DecidableEq s.ACSym]
open ACRepresentation

private theorem classes (f : s.ACSym) (t : Term s) :
    Cancellation.flatten f t = (flatten f t).map Cancellation.classOf := by
  induction t with
  | ac g a b ia ib =>
    by_cases eq : f = g
    · subst g; simp [Cancellation.flatten_ac, flatten, ia, ib]
    · simp [Cancellation.flatten, flatten, eq]
  | _ => rfl

/-- B-equivalence preserves every factor property invariant under B,
even if the binary association exposing a redex differs from the input. -/
private theorem transfer {f : s.ACSym} {t u : Term s} (e : EquivB t u)
    (P : Term s → Prop) (invariant : ∀ a b, EquivB a b → P a → P b)
    (ht : ∀ a ∈ flatten f t, P a) : ∀ b ∈ flatten f u, P b := by
  intro b hb
  have perm := Cancellation.flatten_equiv f e
  simp only [classes] at perm
  obtain ⟨a, ha, he⟩ := List.mem_map.mp (perm.mem_iff.mpr (List.mem_map_of_mem hb))
  exact invariant a b (Quotient.exact he) (ht a ha)

private theorem flatten_apply (f : s.ACSym) (t : Term s) (ρ : Substitution s) :
    flatten f (ρ.apply t) = (flatten f t).flatMap (fun u => flatten f (ρ.apply u)) := by
  induction t with
  | ac g a b ia ib =>
    by_cases eq : f = g
    · subst g
      change flatten f (.ac f _ _) = _
      simp only [flatten, ite_true, List.flatMap_append]
      exact congrArg (fun l => l ++ _) ia |>.trans (congrArg (_ ++ ·) ib)
    · simp [Substitution.apply, Term.subst, flatten, eq]
  | var | atom | comm | free => simp [flatten]

private theorem alien (f : s.ACSym) (t : Term s) (h : head t ≠ .ac f) :
    flatten f t = [t] := by
  cases t with
  | ac g a b =>
    have hn : f ≠ g := fun e => h (e ▸ rfl)
    simp [flatten, hn]
  | _ => rfl

/-- Every AC subgroup draws its factors from the same allowed inventory.
An alien factor is individually normal; a subgroup can only step at its
root or inside a smaller subgroup. -/
private theorem noStep (f : s.ACSym) (P : Term s → Prop)
    (blocked : ∀ a b, head a = .ac f → (∀ t ∈ flatten f a, P t) → ¬ R a b)
    {a b : Term s} (step : Step R a b) :
    ¬ (∀ t ∈ flatten f a, P t ∧ Normal R t) := by
  induction step with
  | @root a b hr =>
    intro all
    by_cases hh : head a = .ac f
    · exact blocked a b hh (fun t ht => (all t ht).1) hr
    · exact (all a (by simp [alien f a hh])).2 b ⟨_,_,.refl _,.root hr,.refl _⟩
  | @ac_left g a b c hs ih =>
    intro all
    by_cases eq : g = f
    · subst g
      exact ih (fun t ht => all t (by simp [flatten,ht]))
    · exact (all (.ac g a c) (by simp [flatten, Ne.symm eq])).2 _ ⟨_,_,.refl _,.ac_left _ _ hs,.refl _⟩
  | @ac_right g a b c hs ih =>
    intro all
    by_cases eq : g = f
    · subst g
      exact ih (fun t ht => all t (by simp [flatten,ht]))
    · exact (all (.ac g a b) (by simp [flatten, Ne.symm eq])).2 _ ⟨_,_,.refl _,.ac_right _ _ hs,.refl _⟩
  | free g ys i hs _ =>
    intro all
    exact (all _ (by simp [flatten])).2 _ ⟨_,_,.refl _,.free _ _ _ hs,.refl _⟩
  | @comm_left g a b c hs _ =>
    intro all
    exact (all (.comm g a c) (by simp [flatten])).2 _ ⟨_,_,.refl _,.comm_left _ _ hs,.refl _⟩
  | @comm_right g a b c hs _ =>
    intro all
    exact (all (.comm g a b) (by simp [flatten])).2 _ ⟨_,_,.refl _,.comm_right _ _ hs,.refl _⟩

/-- Every active rule at this head is represented, and every requested code
in its row is the head of a rigid factor of the rule pattern. -/
def Buckets (rules : List (Equation s)) (f : s.ACSym) (code : Head s → UInt64)
    (rows : Array (Array UInt64)) : Prop :=
  ∀ r ∈ rules, head r.lhs = .ac f → ∃ row ∈ rows, ∀ k ∈ row, k ≠ 0 →
    ∃ t ∈ flatten f r.lhs, RootExclusion.required code t = k

theorem acNormal (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (query : Term s) (code : Head s → UInt64)
    (rows : Array (Array UInt64)) (heads : Array UInt64)
    (factors : ∀ t ∈ flatten f query, Normal (ruleRoot rules) t)
    (fixed : ∀ t ∈ flatten f query, code (head t) ∈ heads)
    (buckets : Buckets rules f code rows)
    {run} (checked : ACFactorExclusion.Correct run) (ok : run rows heads = true) :
    Normal (ruleRoot rules) query := by
  intro u ⟨a,b,eq,step,_⟩
  let P := fun t : Term s => code (head t) ∈ heads
  apply noStep f P (R := ruleRoot rules) ?_ step
  · apply transfer eq (fun t => P t ∧ Normal (ruleRoot rules) t)
      (fun t u h ⟨hp,hn⟩ => ⟨by change code (head u) ∈ heads; rw [← show head t = head u from h.head_eq]; exact hp, (normal_equiv _ h).mp hn⟩)
    intro t ht
    exact ⟨fixed t ht, factors t ht⟩
  · rintro a b hh all ⟨r,hm,τ,rfl,_⟩
    obtain ⟨row,hr,items⟩ := buckets r hm ((instance_head r (apps r hm) τ) ▸ hh)
    obtain ⟨k,hk,nz,missing⟩ := (checked rows heads).mp ok row hr
    obtain ⟨t,ht,hk'⟩ := items k hk nz
    have survives : code (head (τ.apply t)) = k := by
      cases t <;> simp_all [RootExclusion.required]
      all_goals assumption
    have tAlien : head t ≠ .ac f := by
      intro e
      have : ∀ w ∈ flatten f r.lhs, head w ≠ .ac f := by
        induction r.lhs with
        | ac g a b ia ib =>
          by_cases he : f = g
          · subst g; simp only [flatten,ite_true,List.mem_append,or_imp,forall_and]; exact ⟨ia,ib⟩
          · simp only [flatten,ite_eq_right he,List.mem_singleton,forall_eq]; intro h; exact he (Head.ac.inj h).symm
        | var | atom | free | comm => simp only [flatten,List.mem_singleton,forall_eq]; intro h; cases h
      exact this t ht e
    have alienAfter : head (τ.apply t) ≠ .ac f := by
      cases t <;> first | exact tAlien | simp_all [RootExclusion.required]
    apply missing
    rw [← survives]
    apply all
    rw [flatten_apply]
    exact List.mem_flatMap.mpr ⟨t, ht, by simp [alien f _ alienAfter]⟩

theorem acExcluded (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (query : Term s) (code : Head s → UInt64)
    (rows : Array (Array UInt64)) (heads : Array UInt64)
    (factors : ∀ t ∈ flatten f query, Stable (ruleRoot rules) t)
    (fixed : ∀ t ∈ flatten f query, ∀ ρ : Substitution s,
      head (ρ.apply t) ≠ .ac f ∧ code (head (ρ.apply t)) ∈ heads)
    (buckets : Buckets rules f code rows)
    {run} (checked : ACFactorExclusion.Correct run) (ok : run rows heads = true) :
    Stable (ruleRoot rules) query := by
  intro ρ hn
  have actual : ∀ t ∈ flatten f (ρ.apply query),
      Normal (ruleRoot rules) t ∧ code (head t) ∈ heads := by
    rw [flatten_apply]
    intro t ht
    obtain ⟨v,hv,hm⟩ := List.mem_flatMap.mp ht
    obtain rfl := List.mem_singleton.mp ((alien f _ (fixed v hv ρ).1) ▸ hm)
    exact ⟨factors v hv ρ hn, (fixed v hv ρ).2⟩
  exact acNormal rules apps f _ code rows heads
    (fun t ht => (actual t ht).1) (fun t ht => (actual t ht).2) buckets checked ok
end AC

/-- Each symbolic replacement characterizes all normal results, uniformly
in the caller substitution. No right-side variable escapes the query. -/
structure Representative (R : Root s) (t n : Term s) : Prop where
  normal : ∀ ρ : Substitution s, Normalized R ρ → NormalForm R (ρ.apply t) (ρ.apply n)
  unique : ∀ ρ : Substitution s, Normalized R ρ → ∀ u, NormalForm R (ρ.apply t) u → EquivB u (ρ.apply n)
  variables : ∀ v, n.Occurs v → t.Occurs v

theorem stableRepresentative {t : Term s} (hs : Stable R t) : Representative R t t :=
  ⟨fun ρ hn => ⟨.basis (.refl _), hs ρ hn, fun _ h => h⟩,
   fun ρ hn _ nf => (normal_reduces_equiv nf.1 (hs ρ hn)).symm, fun _ h => h⟩

/-- One normalized substitution explains all components of the returned tuple,
including repeated inputs and variables shared across transformed values. -/
theorem tuple (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (q : List (Term s)) (n : Term s → Term s)
    (cert : ∀ t ∈ q, Representative (ruleRoot rules) t (n t)) (avoid : List Variable) :
    let answer : Variant s := ⟨.identity, q.map n⟩
    CompleteVariants (ruleRoot rules) q [answer] ∧ answer.Safe q avoid ∧
      answer.Reconstructible (ruleRoot rules) q := by
  have idn := (constructor_normal rules apps).1
  have sound : (Variant.mk Substitution.identity (q.map n)).Sound (ruleRoot rules) q := by
    refine ⟨idn, aligned_map _ q n ?_⟩
    intro t ht
    simpa using (cert t ht).normal .identity idn
  refine ⟨⟨fun a ha => (List.mem_singleton.mp ha) ▸ sound, ?_⟩, ?_, ?_⟩
  · intro ρ hn values aligned
    exact ⟨_, List.mem_singleton_self _, ρ, hn, fun _ _ => .refl _,
      aligned.map_right n (fun t ht u hu => (cert t ht).unique ρ hn u hu)⟩
  · refine ⟨fun _ _ => rfl, fun _ hv _ hw => Or.inl (hw ▸ hv), ?_⟩
    intro t ht w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    exact Or.inl ⟨_,ha,(cert a ha).variables _ hw⟩
  · intro values aligned
    apply aligned.map_right n
    intro t ht u hu
    simpa using (cert t ht).unique .identity idn u hu

end Tamarin.Rewriting.StableVariants
