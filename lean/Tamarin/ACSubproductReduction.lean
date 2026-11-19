import Tamarin.ACSubgroups
import Tamarin.NarrowingFrontier

/-! Reduction by arbitrary active equations at AC subproducts. The same
untouched complement must appear in both ends of a step. Complete successor
sets can be explored in any order, without assuming confluence of the theory. -/
namespace Tamarin.Rewriting.ACSubproductReduction
open ConstructorVariants
variable {s : Signature} {R : Root s}

def plug (f : s.ACSym) (rest : Option (Term s)) (value : Term s) : Term s :=
  match rest with
  | none => value
  | some t => .ac f value t

private def extend (f : s.ACSym) (rest : Option (Term s)) (t : Term s) : Option (Term s) :=
  some (plug f rest t)

private theorem extend_equiv (f : s.ACSym) (rest : Option (Term s)) (v t : Term s) :
    EquivB (.ac f (plug f rest v) t) (plug f (extend f rest t) v) := by
  cases rest with
  | none => exact .refl _
  | some u => exact (EquivB.ac_assoc f v u t).trans (.ac_congr f (.refl _) (.ac_swap f u t))

/-- A concrete rule occurrence and its entire untouched residual context. -/
def Occurrence (R : Root s) (f : s.ACSym) (a b : Term s) : Prop :=
  ∃ p q rest, head p = .ac f ∧ R p q ∧ EquivB a (plug f rest p) ∧ EquivB (plug f rest q) b

private def Context (f : s.ACSym) (P : Term s → Term s → Prop) (a b : Term s) : Prop :=
  ∃ p q rest, P p q ∧ EquivB a (plug f rest p) ∧ EquivB (plug f rest q) b

private theorem left_context (f : s.ACSym) {P : Term s → Term s → Prop} {a b}
    (h : Context f P a b) (c : Term s) : Context f P (.ac f a c) (.ac f b c) := by
  obtain ⟨p,q,k,fire,l,r⟩ := h
  exact ⟨p,q,extend f k c,fire,(EquivB.ac_congr f l (.refl c)).trans (extend_equiv ..),
    (extend_equiv ..).symm.trans (.ac_congr f r (.refl c))⟩

private theorem Context.rebase {f : s.ACSym} {P : Term s → Term s → Prop} {a b a' b'}
    (h : Context f P a b) (l : EquivB a' a) (r : EquivB b b') : Context f P a' b' := by
  obtain ⟨p,q,k,h,before,after⟩ := h
  exact ⟨p,q,k,h,l.trans before,after.trans r⟩

/-- A step either fires a root rule at a subproduct, or rewrites one
opaque operand. Either case retains exactly the same complement. -/
private theorem inside (f : s.ACSym) {a b : Term s} (step : Step R a b) :
    Context f (fun p q => (head p = .ac f ∧ R p q) ∨ (head p ≠ .ac f ∧ StepModulo R p q)) a b := by
  have operand {p q : Term s} (ne : head p ≠ .ac f) (child : Step R p q) :
      Context f (fun p q => (head p = .ac f ∧ R p q) ∨ (head p ≠ .ac f ∧ StepModulo R p q)) p q :=
    ⟨p,q,none,.inr ⟨ne,_,_,.refl _,child,.refl _⟩,.refl _,.refl _⟩
  induction step with
  | @root p q hit =>
    by_cases h : head p = .ac f
    · exact ⟨p,q,none,.inl ⟨h,hit⟩,.refl _,.refl _⟩
    · exact operand h (.root hit)
  | @ac_left g a b c st ih =>
    by_cases same : f = g
    · subst g; exact left_context f ih c
    · exact operand (fun h => same (Head.ac.inj h).symm) (.ac_left g c st)
  | @ac_right g c a b st ih =>
    by_cases same : f = g
    · subst g; exact (left_context f ih c).rebase (.ac_swap ..) (.ac_swap ..)
    · exact operand (fun h => same (Head.ac.inj h).symm) (.ac_right g c st)
  | free g xs i st _ => exact operand (by intro h; cases h) (.free g xs i st)
  | comm_left g c st _ => exact operand (by intro h; cases h) (.comm_left g c st)
  | comm_right g c st _ => exact operand (by intro h; cases h) (.comm_right g c st)

private noncomputable def residue (f : s.ACSym) : Option (Term s) → List (Cancellation.Class s)
  | none => []
  | some k => Cancellation.flatten f k

private theorem flatten_plug (f : s.ACSym) (k : Option (Term s)) (p : Term s) :
    Cancellation.flatten f (plug f k p) = Cancellation.flatten f p ++ residue f k := by
  cases k <;> simp [plug,residue,Cancellation.flatten_ac]

/-- Replacing equivalent selected bags gives equivalent successor products
only when the complements agree as well. The common original product fixes
that complement, even in the presence of repeated equal occurrences. -/
theorem same_context (f : s.ACSym) {a p q : Term s} {l r : Option (Term s)}
    (left : EquivB a (plug f l p)) (right : EquivB a (plug f r q)) (pieces : EquivB p q)
    (v : Term s) : EquivB (plug f l v) (plug f r v) := by
  have h := Cancellation.flatten_equiv f (left.symm.trans right)
  rw [flatten_plug,flatten_plug] at h
  have rest := (List.perm_append_left_iff _).mp
    (h.trans ((Cancellation.flatten_equiv f pieces).symm.append_right _))
  apply Cancellation.equiv_of_flatten_perm f
  rw [flatten_plug,flatten_plug]
  exact rest.append_left _

theorem plug_congr (f : s.ACSym) (k : Option (Term s)) {p q : Term s}
    (e : EquivB p q) : EquivB (plug f k p) (plug f k q) := by
  cases k with
  | none => exact e
  | some u => exact .ac_congr f e (.refl u)

/-- A single child step uses a factor from the original flattened array,
possibly returning a whole product at the outer head. -/
def FactorStep [DecidableEq s.ACSym] (R : Root s) (f : s.ACSym) (a b : Term s) : Prop :=
  ∃ p ∈ ACRepresentation.flatten f a, ∃ q rest,
    StepModulo R p q ∧ EquivB a (plug f rest p) ∧ EquivB (plug f rest q) b

theorem lift_step (f : s.ACSym) (k : Option (Term s)) {a b : Term s}
    (st : StepModulo R a b) : StepModulo R (plug f k a) (plug f k b) := by
  obtain ⟨p,q,before,step,after⟩ := st
  cases k with
  | none => exact ⟨p,q,before,step,after⟩
  | some t => exact ⟨_,_,.ac_congr f before (.refl _),.ac_left f t step,.ac_congr f after (.refl _)⟩

theorem all_steps_iff [DecidableEq s.ACSym] (f : s.ACSym) (a b : Term s) :
    StepModulo R a b ↔ Occurrence R f a b ∨ FactorStep R f a b := by
  constructor
  · rintro ⟨p,q,l,st,r⟩
    obtain ⟨x,y,k,fire,before,after⟩ := (inside f st).rebase l r
    rcases fire with root|⟨ne,st⟩
    · exact .inl ⟨x,y,k,root.1,root.2,before,after⟩
    · have atom : Cancellation.flatten f x = [Cancellation.classOf x] := by
        cases x with
        | ac g a b =>
          have h : f ≠ g := fun eq => ne (eq ▸ rfl)
          simp [Cancellation.flatten,h]
        | _ => rfl
      have has := Cancellation.flatten_equiv f before
      rw [flatten_plug,atom] at has
      have mem := has.mem_iff.mpr (List.mem_cons_self (a := Cancellation.classOf x))
      rw [DHProduct.classes] at mem
      obtain ⟨u,hu,eu⟩ := List.mem_map.mp mem
      have eq : EquivB u x := Quotient.exact eu
      obtain ⟨p,q,l,st,r⟩ := st
      exact .inr ⟨u,hu,y,k,⟨p,q,eq.trans l,st,r⟩,before.trans (plug_congr f _ eq.symm),after⟩
  · rintro (⟨p,q,k,_,hit,l,r⟩|⟨p,_,q,k,hit,l,r⟩)
    · obtain ⟨x,y,before,st,after⟩ := lift_step f k (show StepModulo R p q from ⟨_,_,.refl _,.root hit,.refl _⟩)
      exact ⟨x,y,l.trans before,st,after.trans r⟩
    · obtain ⟨x,y,before,st,after⟩ := lift_step f k hit
      exact ⟨x,y,l.trans before,st,after.trans r⟩

/-- A driver may visit the original array in any order. For each index
it restores the actual complement, preserving all multiplicities. Equivalent
occurrences can share the list of possible child rewrites. -/
theorem factor_steps_iff [DecidableEq s.ACSym] {I : Type} (f : s.ACSym)
    (a b : Term s) (factor : I → Term s) (rest : I → Option (Term s))
    (layout : ∀ i, ∃ p ∈ ACRepresentation.flatten f a, EquivB (factor i) p)
    (coverage : ∀ p ∈ ACRepresentation.flatten f a, ∃ i, EquivB (factor i) p)
    (whole : ∀ i, EquivB a (plug f (rest i) (factor i)))
    (next : I → List (Term s))
    (edges : ∀ i q, StepModulo R (factor i) q ↔ ∃ v ∈ next i, EquivB v q) :
    FactorStep R f a b ↔ ∃ i, ∃ v ∈ next i, EquivB (plug f (rest i) v) b := by
  constructor
  · rintro ⟨p,hp,q,k,⟨l,r,before,step,after⟩,original,out⟩
    obtain ⟨i,eq⟩ := coverage p hp
    obtain ⟨v,hm,hit⟩ := (edges i q).mp ⟨l,r,eq.trans before,step,after⟩
    exact ⟨i,v,hm,(plug_congr f _ hit).trans ((same_context f (whole i) original eq q).trans out)⟩
  · rintro ⟨i,v,hm,out⟩
    obtain ⟨p,hp,eq⟩ := layout i
    obtain ⟨l,r,before,step,after⟩ := (edges i v).mpr ⟨v,hm,.refl _⟩
    exact ⟨p,hp,v,rest i,⟨l,r,eq.symm.trans before,step,after⟩,(whole i).trans (plug_congr f _ eq),out⟩

/-- At a free head one semantic step either fires a root rule or changes
exactly one original argument. A canonical representation can replace that
one slot and retain all the others. -/
theorem free_steps_iff (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (b : Term s) :
    StepModulo R (.free f xs) b ↔
      (∃ ys v, (∀ j, EquivB (xs j) (ys j)) ∧ R (.free f ys) v ∧ EquivB v b) ∨
      ∃ i v, StepModulo R (xs i) v ∧ EquivB (.free f (fun j => if j = i then v else xs j)) b := by
  constructor
  · rintro ⟨a,c,l,step,r⟩
    obtain ⟨ys,rfl,eq⟩ := free_equiv_view l
    cases step with
    | root hit => exact .inl ⟨ys,_,eq,hit,r⟩
    | free _ _ i child =>
      refine .inr ⟨i,_,⟨_,_,eq i,child,.refl _⟩,(EquivB.free f _ _ ?_).trans r⟩
      intro j
      by_cases e : j = i
      · simp [e]; exact .refl _
      · simpa [e] using eq j
  · rintro (⟨ys,v,hs,hit,r⟩|⟨i,v,⟨p,q,l,st,r⟩,out⟩)
    · exact ⟨_,_,.free f _ _ hs,.root hit,r⟩
    · let args j := if j = i then p else xs j
      have hs : Step R (args i) q := by simpa [args] using st
      refine ⟨_,_,EquivB.free f xs args ?_,Step.free f args i hs,(EquivB.free f _ _ ?_).trans out⟩
      · intro j
        by_cases e : j = i
        · subst j; simpa [args] using l
        · simp [args,e]; exact .refl _
      · intro j
        by_cases e : j = i
        · simpa [e] using r
        · simp [args,e]; exact .refl _

/-- Under irreducible factors all semantic steps are subproduct root steps. -/
theorem step_iff [DecidableEq s.ACSym] (f : s.ACSym) (a b : Term s)
    (normal : ∀ t ∈ ACRepresentation.flatten f a, Normal R t) :
    StepModulo R a b ↔ Occurrence R f a b := by
  rw [all_steps_iff f a b]
  exact ⟨fun h => h.elim id (fun ⟨p,hp,q,_,step,_⟩ => (normal p hp q step).elim),Or.inl⟩

/-- A completed directional match enumerates the rule's simultaneous
captures on its LHS. Unused variables do not constrain its implementation. -/
structure RuleMatches (r : Equation s) (subject : Term s) (answers : List (Substitution s)) : Prop where
  sound : ∀ θ ∈ answers, EquivB (θ.apply r.lhs) subject
  complete : ∀ σ : Substitution s, EquivB (σ.apply r.lhs) subject →
    ∃ θ ∈ answers, Substitution.AgreesOn r.lhs.Occurs σ θ

/-- A complete public directional match supplies the required rule
instances even when an arbitrary semantic substitution also binds variables
outside this rule. -/
theorem RuleMatches.of_complete {r : Equation s} {t : Term s} {arms}
    (h : Matching.Complete [⟨r.lhs,t⟩] (fun _ => True) arms) : RuleMatches r t arms := by
  let p : Problem s := [⟨r.lhs,t⟩]
  constructor
  · intro θ hm; exact (h.sound θ hm).1 _ (List.mem_singleton_self _)
  · intro σ eq
    let μ := Matching.merge p σ Substitution.identity
    have agree : Substitution.AgreesOn (Matching.Observed p) σ μ := by
      intro v hv; simp [μ,Matching.merge,hv]; exact .refl _
    have matchP : Matching.Matches p σ := by simpa [p,Matching.Matches] using eq
    have scope : Matching.Scoped p (fun _ => True) μ := by
      intro v hv
      have off : ¬ Matching.Observed p v := fun hv' => hv ⟨hv',trivial⟩
      simp [μ,Matching.merge,off,Substitution.identity]
    obtain ⟨θ,hm,hθ⟩ := h.covers μ (Matching.matches_of_agrees matchP (fun v hv => (agree v hv).symm)) scope
    refine ⟨θ,hm,fun v hv => ?_⟩
    have seen : Matching.Observed p v := ⟨_,List.mem_singleton_self _,hv⟩
    exact (agree v seen).trans (hθ v seen)

/-- The driver decodes a row of positions into a nonempty product and its
untouched complement. A successful rule substitution produces the rewritten
product in precisely this context. -/
def Returned (f : s.ACSym) (rows : Array (Array UInt64)) (rules : List (Equation s))
    (rest : List UInt64 → Option (Term s))
    (answers : List UInt64 → Equation s → List (Substitution s)) (b : Term s) : Prop :=
  ∃ row : List UInt64, row.toArray ∈ rows ∧ ∃ r ∈ rules, head r.lhs = .ac f ∧
    ∃ θ ∈ answers row r, EquivB (plug f (rest row) (θ.apply r.rhs)) b

/-- All completed subgroup and matching calls, in any order, generate
exactly the root and subproduct steps. The query variables are rigid. -/
def Successors (select : ACSubgroups.Kernel) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] {n : UInt64} {rows} (_ : select n = some rows)
    (f : s.ACSym) (rules : List (Equation s)) (_ : ∀ r ∈ rules, Application r.lhs)
    (_ : ∀ r ∈ rules, head r.lhs = .ac f → ∀ v, r.rhs.Occurs v → r.lhs.Occurs v)
    (a b : Term s)
    (d : UInt64 → Cancellation.Class s)
    (_ : (Cancellation.flatten f a).Perm (((List.range n.toNat).map Nat.toUInt64).map d))
    (piece : List UInt64 → Term s) (rest : List UInt64 → Option (Term s))
    (_ : ∀ row : List UInt64, row.toArray ∈ rows → (Cancellation.flatten f (piece row)).Perm (row.map d))
    (_ : ∀ row : List UInt64, row.toArray ∈ rows → EquivB a (plug f (rest row) (piece row)))
    (answers : List UInt64 → Equation s → List (Substitution s))
    (_ : ∀ row : List UInt64, row.toArray ∈ rows → ∀ r ∈ rules, head r.lhs = .ac f →
      RuleMatches r (piece row) (answers row r)),
    Occurrence (ruleRoot rules) f a b ↔ Returned f rows rules rest answers b

theorem successors_iff {select} (ok : ACSubgroups.Correct select) : Successors select := by
  intro s inst n rows ran f rules apps rhsScope a b d layout piece rest dec whole answers hits
  constructor
  · rintro ⟨_,_,k,hd,⟨r,hr,σ,rfl,rfl⟩,l,right⟩
    have group := Cancellation.flatten_equiv f l
    rw [flatten_plug] at group
    obtain ⟨row,hm,perm⟩ := ACSubgroups.covers ok ran d (group.symm.trans layout) (ACSubgroups.binary hd)
    have eq := (Cancellation.equiv_of_flatten_perm f ((dec row hm).trans perm)).symm
    have hhead := (instance_head r (apps r hr) σ).symm.trans hd
    obtain ⟨θ,mem,agree⟩ := (hits row hm r hr hhead).complete σ eq
    have e := r.rhs.subst_equiv σ.image θ.image (fun v hv => agree v (rhsScope r hr hhead v hv))
    exact ⟨row,hm,r,hr,hhead,θ,mem,(plug_congr f _ e.symm).trans
      ((same_context f l (whole row hm) eq _).symm.trans right)⟩
  · rintro ⟨row,hm,r,hr,hd,θ,mem,right⟩
    exact ⟨_,_,rest row,(instance_head r (apps r hr) θ).trans hd,⟨r,hr,θ,rfl,rfl⟩,
      (whole row hm).trans (plug_congr f _ ((hits row hm r hr hd).sound θ mem).symm),right⟩

/-- Matching a fresh additional operand against the whole product describes
every proper context without enumerating the positions of its complement.
A separate unextended match represents the empty complement. -/
def pattern (f : s.ACSym) (z : Variable) (r : Equation s) : Bool → Equation s
  | false => r
  | true => ⟨.ac f r.lhs (.var z), .ac f r.rhs (.var z)⟩

private theorem RuleMatches.outputs {rule : Equation s} {a : Term s} {answers}
    (h : RuleMatches rule a answers) (bound : ∀ v, rule.rhs.Occurs v → rule.lhs.Occurs v)
    (b : Term s) :
    (∃ σ : Substitution s, EquivB (σ.apply rule.lhs) a ∧ EquivB (σ.apply rule.rhs) b) ↔
      ∃ θ ∈ answers, EquivB (θ.apply rule.rhs) b := by
  constructor
  · rintro ⟨σ,l,r⟩
    obtain ⟨θ,hm,agree⟩ := h.complete σ l
    exact ⟨θ,hm,(rule.rhs.subst_equiv _ _ (fun v hv => (agree v (bound v hv)).symm)).trans r⟩
  · rintro ⟨θ,hm,r⟩; exact ⟨θ,h.sound _ hm,r⟩

/-- At a sorted product, the plain rule and its one-variable extension
denote exactly the same concrete successors as matching an arbitrary
subbag. The bound remainder is shared by both sides of the rule. -/
theorem occurrence_iff_instances (f : s.ACSym)
    (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (scope : ∀ r ∈ rules, head r.lhs = .ac f → ∀ v, r.rhs.Occurs v → r.lhs.Occurs v)
    (a b : Term s) (typed : HasSort a (s.acSort f))
    (z : Equation s → Variable) (sort : ∀ r ∈ rules, (z r).sort = s.acSort f)
    (fresh : ∀ r ∈ rules, ¬r.lhs.Occurs (z r)) :
    Occurrence (ruleRoot rules) f a b ↔ ∃ r ∈ rules, head r.lhs = .ac f ∧ ∃ ext,
      ∃ τ : Substitution s, EquivB a (τ.apply (pattern f (z r) r ext).lhs) ∧
        EquivB (τ.apply (pattern f (z r) r ext).rhs) b := by
  constructor
  · rintro ⟨_,_,k,hd,⟨r,hr,σ,rfl,rfl⟩,l,right⟩
    have hhead := (instance_head r (apps r hr) σ).symm.trans hd
    refine ⟨r,hr,hhead,?_⟩
    cases k with
    | none => exact ⟨false,σ,l,right⟩
    | some t =>
      have shape : (Term.ac f (σ.apply r.lhs) t).checkSort (s.acSort f) = true :=
        SortClash.check_equiv l _ ▸ Term.checkSort_complete typed
      simp only [Term.checkSort,Bool.and_eq_true] at shape
      obtain ⟨η,el,er⟩ := RootNarrowing.extend_assignment r.lhs r.rhs (scope r hr hhead) f
        (z r) (fresh r hr) σ t (sort r hr ▸ Term.checkSort_sound _ _ shape.2)
      exact ⟨true,η,el ▸ l,er ▸ right⟩
  · rintro ⟨r,hr,hd,ext,θ,l,right⟩
    have root : ruleRoot rules (θ.apply r.lhs) (θ.apply r.rhs) := ⟨r,hr,θ,rfl,rfl⟩
    have hhead := (instance_head r (apps r hr) θ).trans hd
    cases ext with
    | false => exact ⟨_,_,none,hhead,root,l,right⟩
    | true => exact ⟨_,_,some (θ.image (z r)),hhead,root,l,right⟩

theorem extended_successors_iff [DecidableEq s.ACSym] (f : s.ACSym)
    (rules : List (Equation s)) (apps : ∀ r ∈ rules, Application r.lhs)
    (scope : ∀ r ∈ rules, head r.lhs = .ac f → ∀ v, r.rhs.Occurs v → r.lhs.Occurs v)
    (a b : Term s) (typed : HasSort a (s.acSort f))
    (z : Equation s → Variable) (sort : ∀ r ∈ rules, (z r).sort = s.acSort f)
    (fresh : ∀ r ∈ rules, ¬r.lhs.Occurs (z r))
    (answers : Equation s → Bool → List (Substitution s))
    (hits : ∀ r ∈ rules, head r.lhs = .ac f → ∀ ext,
      RuleMatches (pattern f (z r) r ext) a (answers r ext)) :
    Occurrence (ruleRoot rules) f a b ↔ ∃ r ∈ rules, head r.lhs = .ac f ∧ ∃ ext,
      ∃ θ ∈ answers r ext, EquivB (θ.apply (pattern f (z r) r ext).rhs) b := by
  have output (r) (hr : r ∈ rules) (hd : head r.lhs = .ac f) (ext : Bool) :=
    (hits r hr hd ext).outputs (by
      cases ext with
      | false => exact scope r hr hd
      | true => exact fun v hv => hv.imp (scope r hr hd v) id) b
  rw [occurrence_iff_instances f rules apps scope a b typed z sort fresh]
  constructor
  · rintro ⟨r,hr,hd,ext,σ,l,right⟩
    exact ⟨r,hr,hd,ext,(output r hr hd ext).mp ⟨σ,l.symm,right⟩⟩
  · rintro ⟨r,hr,hd,ext,hit⟩
    obtain ⟨θ,l,right⟩ := (output r hr hd ext).mpr hit
    exact ⟨r,hr,hd,ext,θ,l.symm,right⟩

/-- A finite completed search has one observable answer if every terminal
agrees and the returned terminal has a replay. Cycles need no semantic
special case. An implementation may defer on any unfinished branch. -/
theorem unique_endpoint (states : List (Term s)) (start result : Term s)
    (seed : start ∈ states)
    (next : Term s → List (Term s))
    (edges : ∀ a ∈ states, ∀ b, StepModulo R a b ↔ ∃ v ∈ next a, EquivB v b)
    (closed : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states)
    (ends : ∀ a ∈ states, next a = [] → EquivB a result)
    (replay : NormalForm R start result) :
    NormalForm R start result ∧ ∀ u, NormalForm R start u → EquivB u result := by
  refine ⟨replay,?_⟩
  intro u form
  let P (t : Term s) := ∃ a ∈ states, EquivB a t
  obtain ⟨a,ha,e⟩ := RootNarrowing.reduction_invariant P
    (fun ⟨a,ha,eq⟩ out => ⟨a,ha,eq.trans out⟩)
    (fun ⟨a,ha,eq⟩ ⟨p,q,l,step,r⟩ => by
      obtain ⟨b,mem,h⟩ := (edges a ha _).mp ⟨p,q,eq.trans l,step,r⟩
      exact ⟨b,closed a ha b mem,h⟩)
    form.1 ⟨start,seed,.refl _⟩
  apply e.symm.trans (ends a ha _)
  cases hn : next a with
  | nil => rfl
  | cons b bs =>
    have st := (edges a ha b).mpr ⟨b,by simp [hn],.refl _⟩
    exact False.elim (((normal_equiv R e).mpr form.2.1) b st)

/-- A path in the stored graph supplies the replay of a returned leaf.
Branches outside this path must still satisfy the closure and endpoint checks. -/
inductive Visited (next : Term s → List (Term s)) (start : Term s) : Term s → Prop where
  | seed : Visited next start start
  | follow {a b} : Visited next start a → b ∈ next a → Visited next start b

theorem completed (states : List (Term s)) (next : Term s → List (Term s)) (start result : Term s)
    (seed : start ∈ states)
    (edges : ∀ a ∈ states, ∀ b, StepModulo R a b ↔ ∃ v ∈ next a, EquivB v b)
    (closed : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states)
    (ends : ∀ a ∈ states, next a = [] → EquivB a result)
    (visited : Visited next start result) (leaf : next result = [])
    (sorts : ∀ k, HasSort start k → HasSort result k) :
    NormalForm R start result ∧ ∀ u, NormalForm R start u → EquivB u result := by
  have reach {t} (path : Visited next start t) : t ∈ states ∧ Reduces R start t := by
    induction path with
    | seed => exact ⟨seed,.basis (.refl _)⟩
    | follow _ h ih =>
      exact ⟨closed _ ih.1 _ h,ih.2.trans (.step ((edges _ ih.1 _).mpr ⟨_,h,.refl _⟩))⟩
  obtain ⟨hr,red⟩ := reach visited
  apply unique_endpoint states start result seed next edges closed ends ⟨red,?_,sorts⟩
  intro b st
  obtain ⟨_,hm,_⟩ := (edges result hr b).mp st
  simp [leaf] at hm

end Tamarin.Rewriting.ACSubproductReduction
