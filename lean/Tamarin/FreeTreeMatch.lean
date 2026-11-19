import Tamarin.CompoundMatching
import Tamarin.FreshSubstitution

/-! Exact finite bindings for matching a free-constructor pattern against a closed
free term. A variable can occupy an entire tree. Every occurrence is recorded
before repeated bindings are reconciled. -/
namespace Tamarin.FreeTreeMatch
open Matching CompoundMatching
variable {sig : Signature}

inductive Pattern : Term sig → Prop where
  | var (v : Variable) : Pattern (.var v)
  | atom (a : sig.Atom) : Pattern (.atom a)
  | free (f : sig.FreeSym) {args} (children : ∀ i, Pattern (args i)) : Pattern (.free f args)

abbrev Table (s : Signature) := List (Variable × Term s)

private def gather {α : Type} : List (Option (List α)) → Option (List α)
  | [] => some []
  | h :: t => do return (← h) ++ (← gather t)

def read [DecidableEq sig.FreeSym] [DecidableEq sig.Atom] : Term sig → Term sig → Option (Table sig)
  | .var v, t => some [(v,t)]
  | .atom a, .atom b => if a = b then some [] else none
  | .free f xs, .free g ys =>
    if eq : f = g then
      gather (List.ofFn fun i => read (xs i) (ys (eq ▸ i)))
    else none
  | _,_ => none
termination_by structural p _ => p

private def Every {α} (P : α → Prop) (reply : Option (List α)) :=
  ∃ xs, reply = some xs ∧ ∀ x ∈ xs, P x

private theorem every_gather {α} (P : α → Prop) (xs : List (Option (List α))) :
    Every P (gather xs) ↔ ∀ r ∈ xs, Every P r := by
  induction xs with
  | nil => simp [gather,Every]
  | cons h t ih =>
    simp only [List.forall_mem_cons,← ih]
    cases h with
    | none => simp [gather,Every]
    | some l =>
      cases g : gather t with
      | none => simp [gather,Every,g]
      | some r =>
        simp [gather,Every,g,List.mem_append,or_imp,forall_and]

private theorem gathered {α} {xs : List (Option (List α))} {entries} (h : gather xs = some entries) :
    (∀ part ∈ xs, ∃ ys, part = some ys) ∧
    (∀ a, a ∈ entries ↔ ∃ ys, some ys ∈ xs ∧ a ∈ ys) := by
  induction xs generalizing entries with
  | nil => cases Option.some.inj h; simp
  | cons op tail ih =>
    cases op with
    | none => cases h
    | some ys =>
      cases rec : gather tail with
      | none => simp [gather, rec] at h
      | some zs =>
        obtain rfl : ys ++ zs = entries := Option.some.inj (by simpa [gather,rec] using h)
        obtain ⟨ok,mem⟩ := ih rec
        constructor
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | ht
          · exact ⟨ys,rfl⟩
          · exact ok p ht
        · intro a
          simp only [List.mem_append, mem, List.mem_cons, Option.some.injEq, or_and_right,
            exists_or, exists_eq_left]

private theorem read_agrees [DecidableEq sig.FreeSym] [DecidableEq sig.Atom]
    {p t : Term sig} (hp : Pattern p) (ht : FreeGround t) (σ : Substitution sig) :
    EquivB (σ.apply p) t ↔ Every (fun e : Variable × Term sig => σ.image e.1 = e.2) (read p t) := by
  induction hp generalizing t with
  | var v =>
    simp only [read,Every,Option.some.injEq,exists_eq_left',List.mem_singleton,forall_eq]
    exact ⟨fun e => (ht.rigid _ e.symm).symm, fun e => e ▸ .refl _⟩
  | atom a =>
    cases ht with
    | atom b =>
      by_cases h : a = b
      · subst b; simp [read,Every]; exact .refl _
      · simp [read,Every,h]
        exact fun he => h (Head.atom.inj he.head_eq)
    | free f _ => simp [read,Every]; intro h; cases h.head_eq
  | @free f xs hc ih =>
    cases ht with
    | atom a => simp [read,Every]; intro h; cases h.head_eq
    | @free g ys hs =>
      by_cases h : f = g
      · subst g
        have read_free : read (.free f xs) (.free f ys) =
            gather (List.ofFn fun i => read (xs i) (ys i)) := by simp [read]
        rw [read_free,every_gather]
        refine (Matching.free_equiv_iff (sig := sig) f (fun i => σ.apply (xs i)) ys).trans ⟨?_,?_⟩
        · intro agreeing part mem
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
          exact (ih i (hs i)).mp (agreeing i)
        · intro all i
          exact (ih i (hs i)).mpr (all _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
      · simp [read,h,Every]
        intro eq
        exact h (Head.free.inj eq.head_eq)

private theorem read_domain [DecidableEq sig.FreeSym] [DecidableEq sig.Atom]
    {p t : Term sig} (hp : Pattern p) (ht : FreeGround t) {rows : Table sig} (hr : read p t = some rows) :
    ∀ v, v ∈ rows.map Prod.fst ↔ p.Occurs v := by
  induction hp generalizing t rows with
  | var v => cases Option.some.inj hr; simp [Term.Occurs]
  | atom a =>
    cases ht with
    | atom b =>
      by_cases eq : a = b
      · subst b
        have h : [] = rows := by simpa [read] using hr
        subst rows; simp [Term.Occurs]
      · simp [read,eq] at hr
    | free => cases hr
  | @free f xs hc ih =>
    cases ht with
    | atom => cases hr
    | @free g ys hs =>
      by_cases eq : f = g
      · subst g
        simp [read] at hr
        obtain ⟨all,mem⟩ := gathered hr
        intro v
        constructor
        · intro hv
          obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
          obtain ⟨r,hpart,hr⟩ := (mem e).mp he
          obtain ⟨i,hi⟩ := List.mem_ofFn.mp hpart
          exact ⟨i,(ih i (hs i) hi _).mp (List.mem_map_of_mem hr)⟩
        · rintro ⟨i,hi⟩
          obtain ⟨r,hpart⟩ := all _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
          obtain ⟨e,he,rfl⟩ := List.mem_map.mp ((ih i (hs i) hpart v).mpr hi)
          exact List.mem_map_of_mem ((mem e).mpr ⟨r, List.mem_ofFn.mpr ⟨i,hpart⟩,he⟩)
      · simp [read,eq] at hr

/-- The output table has the sort of every pattern key and gives identical
ground terms to every repeated occurrence of that key. -/
def Valid (bs : Table sig) :=
  (∀ v t, (v,t) ∈ bs → HasSort t v.sort) ∧
  (∀ v t u, (v,t) ∈ bs → (v,u) ∈ bs → t = u)

theorem valid_iff_rootSort (bs : Table sig)
    (typed : ∀ v t, (v,t) ∈ bs → HasSort t t.rootSort) :
    Valid bs ↔ (∀ v t, (v,t) ∈ bs → Subsort t.rootSort v.sort) ∧
      (∀ v t u, (v,t) ∈ bs → (v,u) ∈ bs → t = u) :=
  ⟨fun ⟨hs,consistent⟩ => ⟨fun v t h => Term.rootSort_le (hs v t h),consistent⟩,
   fun ⟨hs,consistent⟩ => ⟨fun v t h => .widen (typed v t h) (hs v t h),consistent⟩⟩

/-- All gathered bindings agree with a single sorted substitution, even when a
key occurs in another child, another pair, or the residual AC inventory. -/
def Agrees [DecidableEq sig.FreeSym] [DecidableEq sig.Atom] (σ : Substitution sig) (p t : Term sig) :=
  ∃ bs, read p t = some bs ∧ ∀ e ∈ bs, Subsort e.2.rootSort e.1.sort ∧ σ.image e.1 = e.2

theorem agrees_iff [DecidableEq sig.FreeSym] [DecidableEq sig.Atom] {p t : Term sig}
    (hp : Pattern p) (ht : FreeGround t) (σ : Substitution sig) :
    Agrees σ p t ↔ EquivB (σ.apply p) t := by
  rw [read_agrees hp ht σ]
  constructor
  · rintro ⟨bs,h,vals⟩
    exact ⟨bs,h,fun e he => (vals e he).2⟩
  · rintro ⟨bs,h,vals⟩
    refine ⟨bs,h,fun e he => ?_⟩
    have same : σ.image e.1 = e.2 := vals e he
    exact ⟨same ▸ Term.rootSort_le (σ.sorted e.1),same⟩

noncomputable def answers [DecidableEq sig.FreeSym] [DecidableEq sig.Atom] (p t : Term sig) :
    List (Substitution sig) := by
  classical
  exact match read p t with
    | none => []
    | some bs => if h : Valid bs then [Substitution.fromBindings bs h.1] else []

theorem complete [DecidableEq sig.FreeSym] [DecidableEq sig.Atom] {p t : Term sig}
    (pattern : Pattern p) (subject : FreeGround t) :
    Matching.Complete [⟨p,t⟩] (fun _ => True) (answers p t) := by
  classical
  have eq (σ : Substitution sig) : Matches [⟨p,t⟩] σ ↔
      Every (fun e : Variable × Term sig => σ.image e.1 = e.2) (read p t) := by
    simpa [Matches] using read_agrees pattern subject σ
  cases hr : read p t with
  | none =>
    simp only [answers,hr]
    apply (Matching.empty_iff ..).mpr
    rintro ⟨σ,matchσ,_⟩
    obtain ⟨bs,hb,_⟩ := (eq σ).mp matchσ
    simp_all
  | some bs =>
    have dom := read_domain pattern subject hr
    by_cases ok : Valid bs
    · simp only [answers,hr,dite_eq_left ok]
      let σ := Substitution.fromBindings bs ok.1
      have bound (v u) (mem : (v,u) ∈ bs) : σ.image v = u :=
        Substitution.lookupBinding_eq_of_mem bs ok.2 v u mem
      constructor
      · rintro τ mem
        obtain rfl : τ = σ := List.mem_singleton.mp mem
        refine ⟨(eq _).mpr ⟨bs,hr,fun (v,t) he => bound v t he⟩, ?_⟩
        intro v hv
        apply Substitution.lookupBinding_outside
        intro h
        exact hv ⟨⟨_,List.mem_singleton_self _,(dom v).mp h⟩,trivial⟩
      · intro ρ hm _
        obtain ⟨as,ha,vals⟩ := (eq ρ).mp hm
        obtain rfl := Option.some.inj (ha.symm.trans hr)
        refine ⟨σ,List.mem_singleton_self _,?_⟩
        rintro v ⟨e,he,hv⟩
        obtain rfl := List.mem_singleton.mp he
        obtain ⟨⟨w,u⟩,hu,rfl⟩ := List.mem_map.mp ((dom v).mpr hv)
        rw [vals _ hu, bound _ _ hu]
        exact .refl _
    · simp only [answers,hr,dite_eq_right ok]
      apply (Matching.empty_iff ..).mpr
      rintro ⟨σ,hm,_⟩
      obtain ⟨as,ha,vals⟩ := (eq σ).mp hm
      obtain rfl := Option.some.inj (ha.symm.trans hr)
      apply ok
      refine ⟨?_,fun v t u ht hu => (vals (v,t) ht).symm.trans (vals (v,u) hu)⟩
      intro v u hu
      have he : σ.image v = u := vals (v,u) hu
      exact he ▸ σ.sorted v

end Tamarin.FreeTreeMatch
