import Tamarin.VariantJoinRenaming

/-! A local call observes only one term. Reopen all its images and its value
together before adding identity images for variables observed by other leaves. -/
namespace Tamarin.Rewriting.VariantJoin
variable {sig : Signature} {I : Type}

abbrev LocalKey (t : Term sig) := {v : Variable // t.Occurs v}

def leafRow (t : Term sig) (a : Variant sig) (value : Term sig) : Row sig (LocalKey t) Unit :=
  ⟨fun i => a.subst.image i.val, fun _ => value⟩

/-- Rebuilding through smart constructors may change representatives modulo B.
Local witnesses may occur only in the value. Those witnesses must also avoid
the untouched keys, because the key images are filled with their identities. -/
structure Pads (t : Term sig) (ids : I → Variable) (l : Row sig (LocalKey t) Unit)
    (out : Row sig I Unit) : Prop where
  input : ∀ i (h : t.Occurs (ids i)), EquivB (out.input i) (l.input ⟨ids i,h⟩)
  outside : ∀ i, ¬t.Occurs (ids i) → EquivB (out.input i) (.var (ids i))
  value : EquivB (out.value ()) (l.value ())
  apart : ∀ i, ¬t.Occurs (ids i) → ¬l.Uses (ids i)

theorem Pads.denotes {t : Term sig} {ids : I → Variable} {l out} (pad : Pads t ids l out)
    (scope : ∀ v, t.Occurs v → ∃ i, ids i = v) {R : Root sig}
    (ρ : Substitution sig) (hρ : Normalized R ρ) (y : Unit → Term sig) :
    Denotes R l (fun i => ρ.image i.val) y ↔ Denotes R out (fun i => ρ.image (ids i)) y := by
  classical
  constructor
  · rintro ⟨δ,nd,fit⟩
    let η := choose l.Uses δ ρ
    have onImage (i : LocalKey t) : η.apply (l.input i) = δ.apply (l.input i) :=
      (choose_apply l.Uses δ ρ _).1 (fun _ h => .inl ⟨i,h⟩)
    have onValue : η.apply (l.value ()) = δ.apply (l.value ()) :=
      (choose_apply l.Uses δ ρ _).1 (fun _ h => .inr ⟨(),h⟩)
    refine ⟨η,?_,?_,?_⟩
    · intro v; change Normal R (if l.Uses v then _ else _); split
      · exact nd v
      · exact hρ v
    · intro i
      by_cases hi : t.Occurs (ids i)
      · exact (fit.inputs ⟨ids i,hi⟩).trans ((onImage _).symm ▸ ((pad.input i hi).subst η.image).symm)
      · have h := ((pad.outside i hi).subst η.image).symm
        have idAt : η.image (ids i) = ρ.image (ids i) := by simp [η,choose,pad.apart i hi]
        exact idAt ▸ h
    · rintro ⟨⟩
      exact (fit.values ()).trans (onValue.symm ▸ (pad.value.subst η.image).symm)
  · rintro ⟨δ,nd,fit⟩
    refine ⟨δ,nd,?_,?_⟩
    · rintro ⟨v,hv⟩
      obtain ⟨i,rfl⟩ := scope v hv
      exact (fit.inputs i).trans ((pad.input i hv).subst δ.image)
    · rintro ⟨⟩; exact (fit.values ()).trans (pad.value.subst δ.image)

/-- A decoder reconstructs the value under the same substitution as the
local images, then renames their entire range in one operation. -/
def DecodesLeaf (R : Root sig) (t : Term sig) (ids : I → Variable) (a : Variant sig)
    (out : Row sig I Unit) : Prop :=
  ∃ u, NormalForm R (a.subst.apply t) u ∧
    ∃ opened, (leafRow t a u).Relabels opened ∧ Pads t ids opened out

/-- Thus the local family also meets the typing and normality obligations
when it is the first row family, before any join has run. -/
theorem DecodesLeaf.valid {rules : List (Equation sig)} {t : Term sig} {ids : I → Variable}
    {a : Variant sig} {out : Row sig I Unit} (decoded : DecodesLeaf (ruleRoot rules) t ids a out)
    (sound : a.Sound (ruleRoot rules) [t]) (vars : Normalized (ruleRoot rules) Substitution.identity) :
    (∀ i, HasSort (out.input i) (ids i).sort) ∧ out.IsNormal (ruleRoot rules) := by
  obtain ⟨u,nf,opened,ren,pad⟩ := decoded
  have norm := ren.normal.mp (show (leafRow t a u).IsNormal (ruleRoot rules) from
    ⟨fun i => sound.1 i.val,fun _ => nf.2.1⟩)
  obtain ⟨π,images,_⟩ := ren
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases h : t.Occurs (ids i)
    · have eq := (pad.input i h).trans (images ⟨ids i,h⟩).symm
      exact Term.checkSort_sound _ _ ((SortClash.check_equiv eq _).symm ▸
        Term.checkSort_complete ((a.subst.sorted (ids i)).subst (π.subst sig).image (π.subst sig).sorted))
    · exact Term.checkSort_sound _ _ ((SortClash.check_equiv (pad.outside i h) _).symm ▸
        Term.checkSort_complete (.var (ids i)))
  · intro i
    by_cases h : t.Occurs (ids i)
    · exact (normal_equiv _ (pad.input i h)).mpr (norm.1 _)
    · exact (normal_equiv _ (pad.outside i h)).mpr (vars _)
  · rintro ⟨⟩; exact (normal_equiv _ pad.value).mpr (norm.2 ())

/-- A bare leaf can use any complete local variant family and any validated
normalizer for reconstructing the value of an arm. The membership conditions
allow different choices of names and ordering, and duplicate removal. -/
def LeafSemantic : Prop :=
  ∀ {s : Signature} {J : Type} (rules : List (Equation s)) (t : Term s), HasSort t t.rootSort →
    ∀ (ids : J → Variable), (∀ v, t.Occurs v → ∃ i, ids i = v) →
    ∀ (variants : List (Variant s)), CompleteVariants (ruleRoot rules) [t] variants →
    (∀ a ∈ variants, a.Reconstructible (ruleRoot rules) [t]) →
    ∀ rows : List (Row s J Unit),
      (∀ a ∈ variants, ∃ out ∈ rows, DecodesLeaf (ruleRoot rules) t ids a out) →
      (∀ out ∈ rows, ∃ a ∈ variants, DecodesLeaf (ruleRoot rules) t ids a out) →
      Exact (ruleRoot rules) ids (fun _ => t) rows ∧
      (Normalized (ruleRoot rules) Substitution.identity → ∀ out ∈ rows,
        (∀ i, HasSort (out.input i) (ids i).sort) ∧ out.IsNormal (ruleRoot rules))

theorem leafSemantic : LeafSemantic := by
  intro s J rules t typed ids scope vs complete reconstruct rows all only
  constructor
  case right =>
    intro vars out mem
    obtain ⟨a,hm,decoded⟩ := only out mem
    exact decoded.valid (complete.1 a hm) vars
  intro ρ hρ y normal
  constructor
  · intro forms
    obtain ⟨a,mem,δ,nd,agree,values⟩ := complete.2 ρ hρ [y ()] ⟨forms (),trivial⟩
    obtain ⟨out,hm,u,nf,opened,ren,pad⟩ := all a mem
    refine ⟨out,hm,(pad.denotes scope ρ hρ y).mp ((ren.denotes _ y).mp ⟨δ,nd,?_,?_⟩)⟩
    · intro i; exact agree _ ⟨_,List.mem_singleton_self _,i.property⟩
    · rintro ⟨⟩
      have hu := reconstruct a mem [u] ⟨nf,trivial⟩
      cases av : a.values with
      | nil => rw [av] at values; contradiction
      | cons b bs =>
        rw [av] at values hu
        exact values.1.trans ((hu.1.subst δ.image).symm)
  · rintro ⟨out,hm,hit⟩ ⟨⟩
    obtain ⟨a,mem,u,nf,opened,ren,pad⟩ := only out hm
    obtain ⟨δ,_,fit⟩ := (ren.denotes _ y).mpr ((pad.denotes scope ρ hρ y).mpr hit)
    apply form_of_instance hρ typed (σ := a.subst) (δ := δ) _ nf (fit.values ()) (normal ())
    exact fun v occ => fit.inputs ⟨v,occ⟩

end Tamarin.Rewriting.VariantJoin
