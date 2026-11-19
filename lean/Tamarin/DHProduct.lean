import Tamarin.ACRepresentation
import Tamarin.Cancellation
import Tamarin.RulePattern
import Tamarin.ConstructorVariants

/-! Appending one factor to a signed exponent. A cancellation consumes one
occurrence in the inverse; the unmatched positive and negative operands
determine which of the four nonempty-product cases applies. -/
namespace Tamarin.Rewriting.DHProduct
open ACRepresentation
variable {s : Signature}

structure Ops (s : Signature) where
  mult : s.ACSym
  inv : Term s → Term s
  one : Term s

def Ops.mul (a : Ops s) (u v : Term s) := Term.ac a.mult u v

structure Laws (a : Ops s) (R : Root s) : Prop where
  cancel (r : Term s) : HasSort r .msg → Reduces R (a.mul (a.inv r) r) a.one
  cancelWith (u r : Term s) : HasSort u .msg → HasSort r .msg →
    Reduces R (a.mul (a.mul u (a.inv r)) r) u
  cancelInside (v r : Term s) : HasSort v .msg → HasSort r .msg →
    Reduces R (a.mul (a.inv (a.mul v r)) r) (a.inv v)
  cancelBoth (u v r : Term s) : HasSort u .msg → HasSort v .msg → HasSort r .msg →
    Reduces R (a.mul (a.mul u (a.inv (a.mul v r))) r) (a.mul u (a.inv v))

/-- Exactly four oriented rules from the DH table suffice. The operand layouts
here are the layouts of those rules prior to reassociation/commutation. -/
structure CancellationRoots (a : Ops s) (R : Root s) : Prop where
  direct (r : Term s) : HasSort r .msg → R (a.mul r (a.inv r)) a.one
  extra (r u : Term s) : HasSort r .msg → HasSort u .msg → R (a.mul r (a.mul (a.inv r) u)) u
  inside (v r : Term s) : HasSort v .msg → HasSort r .msg → R (a.mul (a.inv (a.mul v r)) r) (a.inv v)
  both (v r u : Term s) : HasSort v .msg → HasSort r .msg → HasSort u .msg →
    R (a.mul (a.inv (a.mul v r)) (a.mul r u)) (a.mul (a.inv v) u)

theorem CancellationRoots.laws {a : Ops s} {R : Root s} (roots : CancellationRoots a R) : Laws a R where
  cancel r h := .step ⟨_, _, .ac_swap _ _ _, .root (roots.direct r h), .refl _⟩
  cancelWith u r hu hr := .step ⟨_,_, (EquivB.ac_swap _ _ _).trans (EquivB.ac_congr _ (.refl _) (EquivB.ac_swap _ _ _)),
    .root (roots.extra r u hr hu), .refl _⟩
  cancelInside v r hv hr := .step ⟨_,_,.refl _, .root (roots.inside v r hv hr), .refl _⟩
  cancelBoth u v r hu hv hr := .step ⟨_,_,
    (EquivB.ac_congr _ (EquivB.ac_swap _ _ _) (.refl _)).trans
      ((EquivB.ac_assoc _ _ _ _).trans (EquivB.ac_congr _ (.refl _) (EquivB.ac_swap _ _ _))),
    .root (roots.both v r u hv hr hu), .ac_swap _ _ _⟩

/-- A possible redex consumes a submultiset of the whole product. All
equivalent presentations of its AC factors count as the same occurrence. -/
def Subbag (f : s.ACSym) (part whole : Term s) : Prop :=
  ∃ residual, (Cancellation.flatten f whole).Perm (Cancellation.flatten f part ++ residual)

private theorem subbag_left (f : s.ACSym) {a b whole : Term s} (h : Subbag f (.ac f a b) whole) :
    Subbag f a whole := by
  obtain ⟨rs,perm⟩ := h
  exact ⟨Cancellation.flatten f b ++ rs, by simpa [Cancellation.flatten_ac,List.append_assoc] using perm⟩

private theorem subbag_right (f : s.ACSym) {a b whole : Term s} (h : Subbag f (.ac f a b) whole) :
    Subbag f b whole := by
  obtain ⟨rs,perm⟩ := h
  exact subbag_left (a := b) (b := a) f ⟨rs, perm.trans
    ((Cancellation.flatten_equiv f (EquivB.ac_swap f a b)).append_right _)⟩

private theorem noStep [DecidableEq s.ACSym] {R : Root s} (f : s.ACSym) (whole : Term s)
    (blocked : ∀ p q, ConstructorVariants.head p = .ac f → Subbag f p whole → ¬R p q)
    {p q : Term s} (step : Step R p q) (sub : Subbag f p whole)
    (children : ∀ t ∈ flatten f p, Normal R t) : False := by
  have alien (p : Term s) (hd : ConstructorVariants.head p ≠ .ac f) : flatten f p = [p] := by
    cases p with
    | ac g a b =>
      have ne : f ≠ g := fun e => hd (e ▸ rfl)
      simp [flatten,ne]
    | var | atom | free | comm => rfl
  induction step with
  | @root a b fire =>
    by_cases h : ConstructorVariants.head a = .ac f
    · exact blocked a b h sub fire
    · exact children a (by simp [alien a h]) b ⟨_,_,.refl _,.root fire,.refl _⟩
  | @ac_left g a b c hs ih =>
    by_cases eq : f = g
    · subst g
      exact ih (subbag_left f sub) (fun t ht => children t (by simp [flatten,ht]))
    · exact children (.ac g a c) (by simp [flatten,eq]) _ ⟨_,_,.refl _,.ac_left _ _ hs,.refl _⟩
  | @ac_right g a b c hs ih =>
    by_cases eq : f = g
    · subst g
      exact ih (subbag_right f sub) (fun t ht => children t (by simp [flatten,ht]))
    · exact children (.ac g a b) (by simp [flatten,eq]) _ ⟨_,_,.refl _,.ac_right _ _ hs,.refl _⟩
  | free f xs i step _ => exact children _ (by simp [flatten]) _ ⟨_,_,.refl _,.free _ _ _ step,.refl _⟩
  | @comm_left f a b c step _ => exact children (.comm f a c) (by simp [flatten]) _ ⟨_,_,.refl _,.comm_left _ _ step,.refl _⟩
  | @comm_right f c a b step _ => exact children (.comm f c a) (by simp [flatten]) _ ⟨_,_,.refl _,.comm_right _ _ step,.refl _⟩

theorem classes [DecidableEq s.ACSym] (f : s.ACSym) (t : Term s) :
    Cancellation.flatten f t = (flatten f t).map Cancellation.classOf := by
  induction t with
  | ac g a b ia ib =>
    by_cases eq : f = g
    · subst g; simp [Cancellation.flatten_ac,flatten,ia,ib]
    · simp [Cancellation.flatten,flatten,eq]
  | _ => rfl

theorem subgroup_normal [DecidableEq s.ACSym] {R : Root s} (f : s.ACSym) (whole : Term s)
    (children : ∀ t ∈ flatten f whole, Normal R t)
    (blocked : ∀ p q, ConstructorVariants.head p = .ac f → Subbag f p whole → ¬R p q) :
    Normal R whole := by
  intro q ⟨p,b,e,step,_⟩
  have perm := Cancellation.flatten_equiv f e
  apply noStep f whole blocked step ⟨[], by simpa using perm⟩
  rw [classes,classes] at perm
  intro t ht
  obtain ⟨u,hu,h⟩ := List.mem_map.mp (perm.mem_iff.mpr (List.mem_map_of_mem ht))
  exact (normal_equiv R (Quotient.exact h)).mp (children u hu)

theorem atom_factors [DecidableEq s.ACSym] (f : s.ACSym) (t : Term s) :
    ∀ k ∈ flatten f t, Cancellation.flatten f k = [Cancellation.classOf k] := by
  induction t with
  | ac g a b ia ib =>
    by_cases e : f = g
    · subst g; intro k hk
      rcases List.mem_append.mp (by simpa [flatten] using hk) with ha | hb
      · exact ia _ ha
      · exact ib _ hb
    · simp [flatten,Cancellation.flatten,e]
  | var | atom | free | comm => simp [flatten,Cancellation.flatten]

/-- A residual class list really can be interpreted as a nonempty term.
It only contains full classes of individual factors drawn from the input. -/
private theorem realize (f : s.ACSym) (k : Cancellation.Class s) (ks : List (Cancellation.Class s))
    (reps : ∀ c ∈ k::ks, ∃ u, Cancellation.flatten f u = [c]) :
    ∃ rest, Cancellation.flatten f rest = k :: ks := by
  induction ks generalizing k with
  | nil => exact reps k List.mem_cons_self
  | cons x xs ih =>
    obtain ⟨t,et⟩ := reps k List.mem_cons_self
    obtain ⟨u,eu⟩ := ih x (fun c hc => reps c (List.mem_cons_of_mem _ hc))
    exact ⟨.ac f t u,by simp [Cancellation.flatten_ac,et,eu]⟩

theorem Subbag.context [DecidableEq s.ACSym] {f : s.ACSym} {p whole : Term s}
    (sub : Subbag f p whole) : EquivB whole p ∨ ∃ rest, EquivB whole (.ac f p rest) := by
  obtain ⟨tail,perm⟩ := sub
  cases tail with
  | nil => exact Or.inl (Cancellation.equiv_of_flatten_perm f (by simpa using perm))
  | cons k ks =>
    obtain ⟨u,e⟩ := realize f k ks (fun c hc => by
      have mem := perm.mem_iff.mpr (List.mem_append_right _ hc)
      rw [classes] at mem
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp mem
      exact ⟨t, atom_factors f whole t ht⟩)
    exact Or.inr ⟨u,Cancellation.equiv_of_flatten_perm f (by simpa [Cancellation.flatten_ac,e] using perm)⟩

/-- Checking all root matches in all subgroups is also necessary. Thus
a matcher may prove a negative result by any complete submultiset search. -/
theorem subgroup_normal_iff [DecidableEq s.ACSym] {R : Root s} (f : s.ACSym) (whole : Term s) :
    Normal R whole ↔ (∀ t ∈ flatten f whole, Normal R t) ∧
      (∀ p q, ConstructorVariants.head p = .ac f → Subbag f p whole → ¬R p q) := by
  constructor
  · intro hn
    constructor
    · intro t ht
      have sub : Subbag f t whole := by
        have mem : Cancellation.classOf t ∈ Cancellation.flatten f whole := by rw [classes]; exact List.mem_map_of_mem ht
        classical
        exact ⟨(Cancellation.flatten f whole).erase (Cancellation.classOf t),
          by rw [atom_factors f whole t ht]; exact List.perm_cons_erase mem⟩
      rcases sub.context with e|⟨_,e⟩
      · exact (normal_equiv R e).mp hn
      · exact (normal_ac_children f ((normal_equiv R e).mp hn)).1
    · intro p q _ sub fire
      rcases sub.context with e|⟨_,e⟩
      · exact hn _ ⟨_,_,e,.root fire,.refl _⟩
      · exact hn _ ⟨_,_,e,.ac_left _ _ (.root fire),.refl _⟩
  · rintro ⟨hc,hr⟩; exact subgroup_normal f whole hc hr

/-- The inverse occurrence contains the appended factor, possibly after
permutation or reassociation at either multiplication. -/
def Opposite [DecidableEq s.ACSym] (a : Ops s) (e r : Term s) : Prop :=
  ∃ f ∈ flatten a.mult e, ∃ n, EquivB f (a.inv n) ∧
    ∃ v ∈ flatten a.mult n, EquivB v r

/-- Splitting an occurrence does not fabricate an identity for the empty
remainder. A nonempty complement is both well sorted and normal. -/
theorem extract [DecidableEq s.ACSym] (f : s.ACSym) (hs : s.acSort f = .msg)
    (p k : Term s) {R : Root s} (typed : HasSort p .msg) (hn : Normal R p)
    (mem : k ∈ flatten f p) : EquivB p k ∨
      ∃ rem, EquivB p (.ac f rem k) ∧ HasSort rem .msg ∧ Normal R rem := by
  obtain ⟨pre, post, layout⟩ := List.mem_iff_append.mp mem
  obtain ⟨t,ht,eq⟩ := flatten_correct f p
  have perm : (flatten f p).Perm (k :: (pre ++ post)) := by rw [layout]; exact List.perm_middle
  cases htail : pre ++ post with
  | nil =>
    rw [htail] at perm
    exact Or.inl (eq.symm.trans (decode_perm f perm t k ht rfl))
  | cons b rest =>
    rw [htail] at perm
    let rem := fold f b rest
    have rearranged := (eq.symm.trans (decode_perm f perm t (.ac f k rem) ht rfl)).trans (.ac_swap f k rem)
    have each (v) (hv : v ∈ b :: rest) : HasSort v (s.acSort f) :=
      flatten_hasSort f p (hs ▸ typed) v (perm.mem_iff.mpr (List.mem_cons_of_mem k hv))
    exact Or.inr ⟨rem,rearranged,hs ▸ fold_hasSort f b rest (each b List.mem_cons_self)
      (fun v hv => each v (List.mem_cons_of_mem _ hv)),
      (normal_ac_children f ((normal_equiv R rearranged).mp hn)).1⟩

/-- Shared operands in each shape are real, nonempty, normalized terms. -/
inductive Shape [DecidableEq s.ACSym] (a : Ops s) (R : Root s) (e r : Term s) : Term s → Prop where
  | extend (clear : ¬ Opposite a e r) : Shape a R e r (a.mul e r)
  | cancel (input : EquivB e (a.inv r)) : Shape a R e r a.one
  | cancelWith (u) (hu : HasSort u .msg) (nu : Normal R u)
      (input : EquivB e (a.mul u (a.inv r))) : Shape a R e r u
  | cancelInside (v) (hv : HasSort v .msg) (nv : Normal R v)
      (input : EquivB e (a.inv (a.mul v r))) : Shape a R e r (a.inv v)
  | cancelBoth (u v) (hu : HasSort u .msg) (hv : HasSort v .msg) (nu : Normal R u) (nv : Normal R v)
      (input : EquivB e (a.mul u (a.inv (a.mul v r)))) : Shape a R e r (a.mul u (a.inv v))

theorem classify [DecidableEq s.ACSym] (a : Ops s) (R : Root s)
    (sort : s.acSort a.mult = .msg) (congrInv : ∀ {x y}, EquivB x y → EquivB (a.inv x) (a.inv y))
    (invChild : ∀ {n t}, EquivB t (a.inv n) → HasSort t .msg → Normal R t → HasSort n .msg ∧ Normal R n)
    (e r : Term s) (he : HasSort e .msg) (hn : Normal R e) : ∃ out, Shape a R e r out := by
  classical
  by_cases opposed : Opposite a e r
  · obtain ⟨f, hf, n, ei, k, hk, ek⟩ := opposed
    have hfSort : HasSort f .msg := sort ▸ flatten_hasSort a.mult e (sort ▸ he) f hf
    have outer := extract a.mult sort e f he hn hf
    have hfNormal : Normal R f := by
      rcases outer with same | ⟨rem,pair,_,_⟩
      · exact (normal_equiv R same).mp hn
      · exact (normal_ac_children _ ((normal_equiv R pair).mp hn)).2
    obtain ⟨nt,nn⟩ := invChild ei hfSort hfNormal
    have inner := extract a.mult sort n k nt nn hk
    rcases outer with same | ⟨u,top,hu,nu⟩ <;> rcases inner with single | ⟨v,part,hv,nv⟩
    · exact ⟨_,.cancel (same.trans (ei.trans (congrInv (single.trans ek))))⟩
    · exact ⟨_,.cancelInside v hv nv (same.trans (ei.trans (congrInv (part.trans (.ac_congr _ (.refl _) ek)))))⟩
    · exact ⟨_,.cancelWith u hu nu (top.trans (.ac_congr _ (.refl _) (ei.trans (congrInv (single.trans ek)))))⟩
    · exact ⟨_,.cancelBoth u v hu hv nu nv (top.trans (.ac_congr _ (.refl _)
          (ei.trans (congrInv (part.trans (.ac_congr _ (.refl _) ek))))))⟩
  · exact ⟨_, .extend opposed⟩

theorem Shape.reduces [DecidableEq s.ACSym] {a : Ops s} {R : Root s} (laws : Laws a R)
    {e r out : Term s} (hr : HasSort r .msg) (h : Shape a R e r out) :
    Reduces R (a.mul e r) out := by
  cases h with
  | extend => exact .basis (.refl _)
  | cancel input => exact .trans (.basis (.ac_congr _ input (.refl _))) (laws.cancel _ hr)
  | cancelWith u hu nu input => exact .trans (.basis (.ac_congr _ input (.refl _))) (laws.cancelWith _ _ hu hr)
  | cancelInside v hv nv input => exact .trans (.basis (.ac_congr _ input (.refl _))) (laws.cancelInside v _ hv hr)
  | cancelBoth u v hu hv nu nv input => exact .trans (.basis (.ac_congr _ input (.refl _))) (laws.cancelBoth u v _ hu hv hr)

end Tamarin.Rewriting.DHProduct
