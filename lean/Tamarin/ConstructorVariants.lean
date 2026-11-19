import Tamarin.Rewriting
import Tamarin.GroundACEquality

/-! Constructor variants for a whole finite rewrite table. A constructor may
be free, commutative or AC. Substitutions may introduce arbitrary normal terms,
including terms containing defined symbols. -/
namespace Tamarin.Rewriting
variable {sig : Signature} {R : Root sig}

theorem normal_free_child (f : sig.FreeSym) (xs : Fin (sig.arity f) → Term sig)
    (hn : Normal R (.free f xs)) (i : Fin (sig.arity f)) : Normal R (xs i) := by
  intro u ⟨a, b, ha, hs, _⟩
  let ys := fun j => if j = i then a else xs j
  have he : EquivB (.free f xs) (.free f ys) := .free _ _ _ (by
    intro j; by_cases h : j = i
    · subst j; simpa [ys] using ha
    · simpa [ys, h] using (EquivB.refl (xs j)))
  have step : Step R (ys i) b := by simpa [ys] using hs
  exact hn _ ⟨_, _, he, .free f ys i step, .refl _⟩

theorem normal_ac_children (f : sig.ACSym) {a b : Term sig}
    (h : Normal R (.ac f a b)) : Normal R a ∧ Normal R b :=
  ⟨fun _ ⟨_, _, he, hs, _⟩ => h _ ⟨_, _, .ac_congr f he (.refl b), .ac_left f b hs, .refl _⟩,
   fun _ ⟨_, _, he, hs, _⟩ => h _ ⟨_, _, .ac_congr f (.refl a) he, .ac_right f a hs, .refl _⟩⟩

theorem normal_comm_children (f : sig.CSym) {a b : Term sig}
    (h : Normal R (.comm f a b)) : Normal R a ∧ Normal R b :=
  ⟨fun _ ⟨_, _, he, hs, _⟩ => h _ ⟨_, _, .comm_congr f he (.refl b), .comm_left f b hs, .refl _⟩,
   fun _ ⟨_, _, he, hs, _⟩ => h _ ⟨_, _, .comm_congr f (.refl a) he, .comm_right f a hs, .refl _⟩⟩

/-- Any reduction starting at an irreducible term consists solely of B-equivalences.
This does not require confluence or termination of the rule table. -/
theorem normal_reduces_equiv {t u : Term sig} (h : Reduces R t u) :
    Normal R t → EquivB t u := by
  induction h with
  | basis h => exact fun _ => h
  | step h => exact fun hn => False.elim (hn _ h)
  | trans h k ih ik =>
    intro hn; have he := ih hn
    exact he.trans (ik ((normal_equiv _ he).mp hn))
  | free f a b _ ih => exact fun hn => .free f a b (fun i => ih i (normal_free_child _ _ hn i))
  | comm f _ _ ih ik =>
    exact fun hn => .comm_congr f
      (ih (normal_comm_children f hn).1) (ik (normal_comm_children f hn).2)
  | ac f _ _ ih ik =>
    exact fun hn => .ac_congr f
      (ih (normal_ac_children f hn).1) (ik (normal_ac_children f hn).2)

namespace ConstructorVariants

def head (t : Term sig) := (headModel sig).eval Head.var t

/-- Normal leaves surrounded by constructors. The B laws can rearrange these
contexts, including reassociating a subtree supplied by a substitution. -/
private inductive Built (R : Root sig) (safe : Head sig → Prop) : Term sig → Prop
  | leaf {t} : Normal R t → Built R safe t
  | free (f xs) : safe (.free f) → (∀ i, Built R safe (xs i)) → Built R safe (.free f xs)
  | comm (f) {a b} : safe (.comm f) → Built R safe a → Built R safe b → Built R safe (.comm f a b)
  | ac (f) {a b} : safe (.ac f) → Built R safe a → Built R safe b → Built R safe (.ac f a b)

variable {safe : Head sig → Prop}

private theorem built_ac_children {f : sig.ACSym} {a b : Term sig}
    (h : Built R safe (.ac f a b)) : Built R safe a ∧ Built R safe b := by
  cases h with
  | leaf hn => exact ⟨.leaf (normal_ac_children _ hn).1, .leaf (normal_ac_children _ hn).2⟩
  | ac _ _ ha hb => exact ⟨ha, hb⟩

private theorem built_equiv {t u : Term sig} (h : EquivB t u) :
    Built R safe t ↔ Built R safe u := by
  have leaf {s t : Term sig} (e : EquivB s t) (hn : Normal R s) :
      Built R safe t := .leaf ((normal_equiv _ e).mp hn)
  induction h with
  | refl => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | free f a b e ih =>
    constructor
    · intro h; cases h with
      | leaf hn => exact leaf (.free f a b e) hn
      | free _ _ hf hc => exact .free _ _ hf (fun i => (ih i).mp (hc i))
    · intro h; cases h with
      | leaf hn => exact leaf (.free f b a (fun i => (e i).symm)) hn
      | free _ _ hf hc => exact .free _ _ hf (fun i => (ih i).mpr (hc i))
  | ac_congr f e g ih ik =>
    constructor
    · intro h; cases h with
      | leaf hn => exact leaf (.ac_congr f e g) hn
      | ac _ hf a b => exact .ac _ hf (ih.mp a) (ik.mp b)
    · intro h; cases h with
      | leaf hn => exact leaf (.ac_congr f e.symm g.symm) hn
      | ac _ hf a b => exact .ac _ hf (ih.mpr a) (ik.mpr b)
  | comm_congr f e g ih ik =>
    constructor
    · intro h; cases h with
      | leaf hn => exact leaf (.comm_congr f e g) hn
      | comm _ hf a b => exact .comm _ hf (ih.mp a) (ik.mp b)
    · intro h; cases h with
      | leaf hn => exact leaf (.comm_congr f e.symm g.symm) hn
      | comm _ hf a b => exact .comm _ hf (ih.mpr a) (ik.mpr b)
  | ac_swap f a b =>
    constructor <;> intro h <;> cases h with
    | leaf hn => exact leaf (.ac_swap f _ _) hn
    | ac _ hf a b => exact .ac _ hf b a
  | comm_swap f a b =>
    constructor <;> intro h <;> cases h with
    | leaf hn => exact leaf (.comm_swap f _ _) hn
    | comm _ hf a b => exact .comm _ hf b a
  | ac_assoc f a b c =>
    constructor
    · intro h; cases h with
      | leaf hn => exact leaf (.ac_assoc f _ _ _) hn
      | ac _ hf ab c =>
        obtain ⟨a,b⟩ := built_ac_children ab
        exact .ac _ hf a (.ac _ hf b c)
    · intro h; cases h with
      | leaf hn => exact leaf (EquivB.ac_assoc f _ _ _).symm hn
      | ac _ hf a bc =>
        obtain ⟨b,c⟩ := built_ac_children bc
        exact .ac _ hf (.ac _ hf a b) c

private theorem no_step {t u : Term sig} (hs : Step R t u)
    (disjoint : ∀ a b, R a b → ¬ safe (head a)) : ¬ Built R safe t := by
  induction hs with
  | root hr => intro h; cases h with
    | leaf hn => exact hn _ ⟨_, _, .refl _, .root hr, .refl _⟩
    | free _ _ hf _ | ac _ hf _ _ | comm _ hf _ _ => exact disjoint _ _ hr hf
  | free f args i hs ih => intro h; cases h with
    | leaf hn => exact normal_free_child _ _ hn i _ ⟨_, _, .refl _, hs, .refl _⟩
    | free _ _ _ hc => exact ih (hc i)
  | ac_left f _ hs ih => intro h; exact ih (built_ac_children h).1
  | ac_right f _ hs ih => intro h; exact ih (built_ac_children h).2
  | comm_left f _ hs ih => intro h; cases h with
    | leaf hn => exact (normal_comm_children f hn).1 _ ⟨_, _, .refl _, hs, .refl _⟩
    | comm _ _ a _ => exact ih a
  | comm_right f _ hs ih => intro h; cases h with
    | leaf hn => exact (normal_comm_children f hn).2 _ ⟨_, _, .refl _, hs, .refl _⟩
    | comm _ _ _ b => exact ih b

def operators : Term sig → List (Head sig)
  | .var _ | .atom _ => []
  | .free f xs => .free f :: (List.ofFn fun i => operators (xs i)).flatten
  | .ac f a b => .ac f :: operators a ++ operators b
  | .comm f a b => .comm f :: operators a ++ operators b

private theorem build (t : Term sig) (ρ : Substitution sig) (hn : Normalized R ρ)
    (atoms : ∀ a, Normal R (.atom a)) (ht : ∀ f ∈ operators t, safe f) :
    Built R safe (ρ.apply t) := by
  induction t with
  | var v => exact .leaf (hn v)
  | atom a => exact .leaf (atoms a)
  | free f xs ih =>
    exact .free f _ (ht _ (by simp [operators])) (fun i => ih i (fun s hs =>
      ht s (by simp [operators]; exact Or.inr ⟨_, ⟨i, rfl⟩, hs⟩)))
  | ac f _ _ ih ik =>
    exact .ac f (ht _ (by simp [operators]))
      (ih (fun s hs => ht s (by simp [operators, hs]))) (ik (fun s hs => ht s (by simp [operators, hs])))
  | comm f _ _ ih ik =>
    exact .comm f (ht _ (by simp [operators]))
      (ih (fun s hs => ht s (by simp [operators, hs]))) (ik (fun s hs => ht s (by simp [operators, hs])))

def ruleHeads (rules : List (Equation sig)) := rules.map (fun r => head r.lhs)

def Application : Term sig → Prop
  | .var _ | .atom _ => False
  | _ => True

theorem instance_head (r : Equation sig) (hr : Application r.lhs) (ρ : Substitution sig) :
    head (ρ.apply r.lhs) = head r.lhs := by
  cases h : r.lhs <;> simp_all [Application] <;> rfl

/-- Constructor contexts preserve irreducibility for every normalized substitution,
even in a table with unrelated, nonconfluent rules. -/
theorem constructor_normal (rules : List (Equation sig))
    (apps : ∀ r ∈ rules, Application r.lhs) :
    Normalized (ruleRoot rules) Substitution.identity ∧
    ∀ t : Term sig, (∀ f ∈ operators t, f ∉ ruleHeads rules) →
      ∀ ρ, Normalized (ruleRoot rules) ρ → Normal (ruleRoot rules) (ρ.apply t) := by
  let R := ruleRoot rules
  have blocked (a b : Term sig) (hr : R a b) : head a ∈ ruleHeads rules := by
    obtain ⟨r, hm, σ, rfl, _⟩ := hr
    exact (instance_head r (apps r hm) σ) ▸ List.mem_map_of_mem hm
  have literal (t : Term sig) (hl : ∀ s, EquivB t s → s = t)
      (notApp : ¬ Application t) : Normal R t := by
    intro u ⟨s, v, he, hs, _⟩
    have ht := hl s he; subst s
    cases hs with
    | root hr =>
      obtain ⟨r, hm, σ, he, _⟩ := hr
      apply notApp
      rw [he]
      have ha := apps r hm
      cases h : r.lhs <;> simp [h, Application] at ha <;> trivial
    | _ => exact notApp trivial
  have vars (v : Variable) : Normal R (.var v) := literal _ (by
    intro s h; cases s <;> cases h.head_eq; rfl) (by simp [Application])
  have atoms (a : sig.Atom) : Normal R (.atom a) := literal _ (by
    intro s h; cases s <;> cases h.head_eq; rfl) (by simp [Application])
  refine ⟨vars, ?_⟩
  intro t absent ρ hn _ ⟨_, _, he, hs, _⟩
  exact no_step hs (fun a b hr hn => hn (blocked a b hr))
    ((built_equiv he).mp (build t ρ hn atoms absent))

/-- A rule-free application of irreducible children is irreducible modulo B,
including when associativity exposes a different grouping of its children. -/
theorem constructor_node_normal (rules : List (Equation sig))
    (apps : ∀ r ∈ rules, Application r.lhs) (t : Term sig)
    (absent : head t ∉ ruleHeads rules)
    (children : match t with
      | .free _ xs => ∀ i, Normal (ruleRoot rules) (xs i)
      | .comm _ a b | .ac _ a b => Normal (ruleRoot rules) a ∧ Normal (ruleRoot rules) b
      | _ => True) : Normal (ruleRoot rules) t := by
  have built : Built (ruleRoot rules) (fun h => h ∉ ruleHeads rules) t := by
    cases t with
    | free f xs => exact .free f xs absent (fun i => .leaf (children i))
    | comm f a b => exact .comm f absent (.leaf children.1) (.leaf children.2)
    | ac f a b => exact .ac f absent (.leaf children.1) (.leaf children.2)
    | var v => exact .leaf ((constructor_normal rules apps).1 v)
    | atom a =>
      obtain ⟨vars, ctor⟩ := constructor_normal rules apps
      exact .leaf (ctor (.atom a) (by simp [operators]) Substitution.identity vars)
  intro u ⟨_, _, he, hs, _⟩
  apply no_step hs _ ((built_equiv he).mp built)
  rintro _ _ ⟨r, hr, σ, rfl, _⟩ hn
  exact hn ((instance_head r (apps r hr) σ) ▸ List.mem_map_of_mem hr)

theorem identity_variants (rules : List (Equation sig)) (query : List (Term sig))
    (apps : ∀ r ∈ rules, Application r.lhs)
    (absent : ∀ t ∈ query, ∀ f ∈ operators t, f ∉ ruleHeads rules)
    (avoid : List Variable) :
    let answer : Variant sig := ⟨Substitution.identity, query⟩
    CompleteVariants (ruleRoot rules) query [answer] ∧ answer.Safe query avoid := by
  let R := ruleRoot rules
  obtain ⟨vars, constructors⟩ := constructor_normal rules apps
  have stable (t) (ht : t ∈ query) (ρ) (hn : Normalized R ρ) : Normal R (ρ.apply t) :=
    constructors t (absent t ht) ρ hn
  have ident (t) (ht : t ∈ query) : NormalForm R (Substitution.identity.apply t) t := by
    rw [Substitution.apply_identity]
    exact ⟨.basis (.refl _), by simpa using stable t ht Substitution.identity vars, fun _ h => h⟩
  constructor
  · constructor
    · intro ans ha; obtain rfl := List.mem_singleton.mp ha
      exact ⟨vars, by simpa using aligned_map _ query id ident⟩
    · intro ρ hn values hv
      refine ⟨_, List.mem_singleton_self _, ρ, hn, fun _ _ => .refl _, ?_⟩
      induction query generalizing values with
      | nil => cases values <;> exact hv
      | cons t ts ih =>
        cases values with
        | nil => exact hv
        | cons u us =>
          exact ⟨(normal_reduces_equiv hv.1.1 (stable t (by simp) ρ hn)).symm,
            ih (fun t ht => absent t (List.mem_cons_of_mem _ ht))
              (fun t ht => stable t (List.mem_cons_of_mem _ ht))
              (fun t ht => ident t (List.mem_cons_of_mem _ ht)) us hv.2⟩
  · exact Variant.safe_identity query avoid

/-- Only a positive decision returns the singleton identity variant. A negative
decision delegates the entire query to narrowing. Both directions are required. -/
def DecisionCorrect (run : Array UInt64 → Array UInt64 → Bool) : Prop :=
  ∀ roots used, run roots used = true ↔ ∀ w ∈ used.toList, w ∉ roots.toList

theorem encoded_identity {run} (hc : DecisionCorrect run) (rules : List (Equation sig))
    (query : List (Term sig)) (roots used : Array UInt64) (encode : Head sig → UInt64)
    (apps : ∀ r ∈ rules, Application r.lhs)
    (hr : ∀ f ∈ ruleHeads rules, encode f ∈ roots.toList)
    (hu : ∀ t ∈ query, ∀ f ∈ operators t, encode f ∈ used.toList)
    (ok : run roots used = true) (avoid : List Variable) :
    let answer : Variant sig := ⟨Substitution.identity, query⟩
    CompleteVariants (ruleRoot rules) query [answer] ∧ answer.Safe query avoid :=
  identity_variants rules query apps (fun t ht f hf hm =>
    (hc roots used).mp ok _ (hu t ht f hf) (hr f hm)) avoid

end ConstructorVariants
end Tamarin.Rewriting
