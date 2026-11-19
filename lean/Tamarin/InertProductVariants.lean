import Tamarin.InertProductReduction
import Tamarin.VariantJoinSubsumption

/-! Joint variants at an inert C or AC head. The original operands can share
caller variables, have indistinguishable heads, or expose further AC factors.
Wrapping can identify formerly distinct rows; final subsumption therefore
compares the projected product as well as every remaining coordinate. -/
namespace Tamarin.Rewriting.VariantJoin.InertProduct
open ConstructorVariants
variable {s : Signature} {I A : Type} {R : Root s}

def wrap (op : Term s → Term s → Term s) (parts : Sum A Bool → Term s) : Option A → Term s
  | none => op (parts (.inr false)) (parts (.inr true))
  | some a => parts (.inl a)

def project (op : Term s → Term s → Term s) (q : Row s I (Sum A Bool)) : Row s I (Option A) :=
  ⟨q.input,wrap op q.value⟩

structure Constructor (R : Root s) (op : Term s → Term s → Term s) : Prop where
  subst : ∀ (δ : Substitution s) x y, δ.apply (op x y) = op (δ.apply x) (δ.apply y)
  congr : ∀ {x y x' y'}, EquivB x x' → EquivB y y' → EquivB (op x y) (op x' y')
  children : ∀ x y, Normal R (op x y) → Normal R x ∧ Normal R y

/-- The operation is allowed to rearrange or regroup its results. Only the
forward congruence law is needed. An inverse from values to ordered slots
would incorrectly require AC products to be injective. -/
theorem exact {op : Term s → Term s → Term s} (opLaw : Constructor R op)
    (terms : Sum A Bool → Term s) (ids : I → Variable) (rows : List (Row s I (Sum A Bool)))
    (family : Exact R ids terms rows)
    (forms : ∀ (ρ : Substitution s), Normalized R ρ → ∀ u, NormalForm R (ρ.apply (wrap op terms none)) u ↔
      ∃ l r, NormalForm R (ρ.apply (terms (.inr false))) l ∧
        NormalForm R (ρ.apply (terms (.inr true))) r ∧ EquivB (op l r) u) :
    Exact R ids (wrap op terms) (rows.map (project op)) := by
  intro ρ hn y ny
  constructor
  · intro h
    obtain ⟨l,r,nl,nr,e⟩ := (forms ρ hn _).mp (h none)
    let parts : Sum A Bool → Term s := Sum.elim (fun a => y (some a)) (fun b => if b then r else l)
    have normal k : NormalForm R (ρ.apply (terms k)) (parts k) := by
      cases k with
      | inl a => exact h (some a)
      | inr b => cases b <;> first | exact nl | exact nr
    obtain ⟨q,hq,δ,nδ,fit⟩ := (family ρ hn parts (fun k => (normal k).2.1)).mp normal
    refine ⟨_,List.mem_map_of_mem hq,δ,nδ,fit.inputs,?_⟩
    intro k
    cases k with
    | some a => exact fit.values (.inl a)
    | none =>
      change EquivB _ (δ.apply (op _ _))
      rw [opLaw.subst]
      exact e.symm.trans (opLaw.congr (fit.values (.inr false)) (fit.values (.inr true)))
  · rintro ⟨_,mem,δ,nδ,fit⟩
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp mem
    let parts k := δ.apply (q.value k)
    have eq : EquivB (y none) (op (parts (.inr false)) (parts (.inr true))) := by
      simpa only [project,wrap,opLaw.subst,parts] using fit.values none
    have kids := opLaw.children _ _ ((normal_equiv _ eq).mp (ny none))
    have ns k : Normal R (parts k) := by
      cases k with
      | inl a => exact (normal_equiv _ (fit.values (some a))).mp (ny (some a))
      | inr b => cases b <;> first | exact kids.1 | exact kids.2
    have hs := (family ρ hn parts ns).mpr ⟨q,hq,δ,nδ,fit.inputs,fun _ => .refl _⟩
    intro k
    cases k with
    | none => exact (forms ρ hn _).mpr ⟨_,_,hs (.inr false),hs (.inr true),eq.symm⟩
    | some a =>
      have nf := hs (.inl a)
      have ev := (fit.values (some a)).symm
      exact ⟨nf.1.trans (.basis ev),ny _,fun j h => Term.checkSort_sound _ _
        ((SortClash.check_equiv ev j) ▸ Term.checkSort_complete (nf.2.2 j h))⟩

/-- Normalizing the shared tuple filters every input image and operand.
Rebuilding an inert product preserves the normality of the whole row. -/
theorem project_normal (op : Term s → Term s → Term s)
    (build : ∀ l r, Normal R l → Normal R r → Normal R (op l r))
    (q : Row s I (Sum A Bool)) (h : q.IsNormal R) : (project op q).IsNormal R := by
  refine ⟨h.1,?_⟩
  intro k
  cases k with
  | none => exact build _ _ (h.2 (.inr false)) (h.2 (.inr true))
  | some a => exact h.2 (.inl a)

theorem ac_normal (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (inert : Head.ac f ∉ ruleHeads rules) (q : Row s I (Sum A Bool))
    (h : q.IsNormal (ruleRoot rules)) : (project (.ac f) q).IsNormal (ruleRoot rules) :=
  project_normal (.ac f) (fun _ _ l r => constructor_node_normal rules apps _ inert ⟨l,r⟩) q h

theorem comm_normal (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.CSym) (inert : Head.comm f ∉ ruleHeads rules) (q : Row s I (Sum A Bool))
    (h : q.IsNormal (ruleRoot rules)) : (project (.comm f) q).IsNormal (ruleRoot rules) :=
  project_normal (.comm f) (fun _ _ l r => constructor_node_normal rules apps _ inert ⟨l,r⟩) q h

/-- Wrapping pointwise-functional children remains functional even when
several ordered decompositions denote the same parent. -/
theorem unique {op : Term s → Term s → Term s} (opLaw : Constructor R op) {t a b : Term s}
    (forms : ∀ u, NormalForm R t u ↔ ∃ l r, NormalForm R a l ∧ NormalForm R b r ∧ EquivB (op l r) u)
    (left : ∀ x y, NormalForm R a x → NormalForm R a y → EquivB x y)
    (right : ∀ x y, NormalForm R b x → NormalForm R b y → EquivB x y) :
    ∀ u v, NormalForm R t u → NormalForm R t v → EquivB u v := by
  intro u v nu nv
  obtain ⟨l,r,hl,hr,eu⟩ := (forms _).mp nu
  obtain ⟨m,n,hm,hn,ev⟩ := (forms _).mp nv
  exact eu.symm.trans ((opLaw.congr (left _ _ hl hm) (right _ _ hr hn)).trans ev)

theorem acConstructor (f : s.ACSym) : Constructor R (.ac f) :=
  ⟨fun _ _ _ => rfl, EquivB.ac_congr f,fun _ _ => normal_ac_children f⟩

theorem commConstructor (f : s.CSym) : Constructor R (.comm f) :=
  ⟨fun _ _ _ => rfl, EquivB.comm_congr f,fun _ _ => normal_comm_children f⟩

/-- Slot admission uses the declared sort or stable normality under *all*
normalized caller substitutions, including substitutions shared by both slots. -/
def Admits (R : Root s) (k : SortId) (t : Term s) :=
  HasSort t k ∧ ∀ ρ : Substitution s, Normalized R ρ → Rewriting.InertProduct.Slot R k (ρ.apply t)

theorem admits_of_check (rules : List (Equation s)) (k : SortId) (t : Term s) (typed : HasSort t k)
    (guard : (∀ ρ : Substitution s, Normalized (ruleRoot rules) ρ → Normal (ruleRoot rules) (ρ.apply t)) ∨
      Application t ∧ t.rootSort = k) : Admits (ruleRoot rules) k t := by
  refine ⟨typed,fun ρ hn => ?_⟩
  rcases guard with stable|⟨app,sort⟩
  · exact .inl (stable ρ hn)
  · apply Or.inr
    rw [←sort]
    cases t with
    | free | comm | ac => rfl
    | atom | var => exact app.elim

theorem ac [DecidableEq s.ACSym] (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.ACSym) (inert : Head.ac f ∉ ruleHeads rules) (terms : Sum A Bool → Term s)
    (admit : ∀ b, Admits (ruleRoot rules) (s.acSort f) (terms (.inr b)))
    (ids : I → Variable) (rows : List (Row s I (Sum A Bool))) (family : Exact (ruleRoot rules) ids terms rows) :
    Exact (ruleRoot rules) ids (wrap (.ac f) terms) (rows.map (project (.ac f))) := by
  apply exact (acConstructor f) terms ids rows family
  intro ρ hn u
  exact Rewriting.InertProduct.ac_forms rules apps f inert _ _ u
    ((admit false).1.subst ρ.image ρ.sorted) ((admit true).1.subst ρ.image ρ.sorted)
    ((admit false).2 ρ hn) ((admit true).2 ρ hn)

theorem comm (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (f : s.CSym) (inert : Head.comm f ∉ ruleHeads rules) (terms : Sum A Bool → Term s)
    (admit : ∀ b, Admits (ruleRoot rules) (s.cSort f) (terms (.inr b)))
    (ids : I → Variable) (rows : List (Row s I (Sum A Bool))) (family : Exact (ruleRoot rules) ids terms rows) :
    Exact (ruleRoot rules) ids (wrap (.comm f) terms) (rows.map (project (.comm f))) := by
  apply exact (commConstructor f) terms ids rows family
  intro ρ hn u
  exact Rewriting.InertProduct.comm_forms rules apps f inert _ _ u
    ((admit false).1.subst ρ.image ρ.sorted) ((admit true).1.subst ρ.image ρ.sorted)
    ((admit false).2 ρ hn) ((admit true).2 ρ hn)

end Tamarin.Rewriting.VariantJoin.InertProduct
