import Tamarin.ACSystem
import Tamarin.VariablePermutation

/-! Identifying flat AC answers modulo a single renaming of all range
variables. Each column includes the witness sort and the input position of
every occurrence. Columns with identical descriptors remain distinct. -/
namespace Tamarin.FlatAnswerIncidence
variable {sig : Signature}

inductive Image (sig : Signature) where
  | single (v : Variable)
  | product (f : sig.ACSym) (a b : Variable) (rest : List Variable)

def Image.head : Image sig → Option sig.ACSym
  | .single _ => none
  | .product f .. => some f

def Image.vars : Image sig → List Variable
  | .single v => [v]
  | .product _ a b rest => a :: b :: rest

def Image.term : Image sig → Term sig
  | .single v => .var v
  | .product f a b rest => ACRepresentation.fold f (.var a) ((b :: rest).map Term.var)

private theorem Image.occurs_mem (im : Image sig) (w : Variable) : im.term.Occurs w → w ∈ im.vars := by
  cases im with
  | single x => simp [Image.term,Image.vars,Term.Occurs]
  | product f x y xs =>
    change (ACSystem.Side.term ⟨x,y::xs⟩ f).Occurs w → _
    have inventory (u : Variable) (us : List Variable) :
        (ACSystem.Side.term ⟨u,us⟩ f).Occurs w → w ∈ u :: us := by
      induction us generalizing u with
      | nil => simp [ACSystem.Side.term,ACRepresentation.fold,Term.Occurs]
      | cons j js ih =>
        change (w = u ∨ (ACSystem.Side.term ⟨j,js⟩ f).Occurs w) → _
        rintro (rfl | h)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih j h)
    exact inventory x (y::xs)

/-- The fixed input positions also include identity images when present. -/
structure View (inputs : List Variable) (σ : Substitution sig) where
  image : Nat → Image sig
  represents : ∀ i (hi : i < inputs.length), EquivB (σ.image inputs[i]) (image i).term
  witnesses : List Variable
  distinct : witnesses.Nodup
  includes : ∀ i < inputs.length, ∀ v ∈ (image i).vars, v ∈ witnesses

/-- Sparse column as transmitted by the adapter. Multiple occurrences in one
image repeat the same position; one witness can occur in many images. -/
def column (n : Nat) (im : Nat → Image sig) (v : Variable) : SortId × List Nat :=
  (v.sort,(List.range n).flatMap fun i => List.replicate ((im i).vars.count v) i)

def SameKey {inputs : List Variable} {σ τ : Substitution sig} (a : View inputs σ) (b : View inputs τ) : Prop :=
  (List.range inputs.length).map (fun i => (a.image i).head) =
    (List.range inputs.length).map (fun i => (b.image i).head) ∧
  (a.witnesses.map (column inputs.length a.image)).Perm (b.witnesses.map (column inputs.length b.image))

private theorem countPositions (f : Nat → Nat) (i : Nat) (is : List Nat) (nd : is.Nodup) :
    ((is.flatMap fun j => List.replicate (f j) j).count i) = if i ∈ is then f i else 0 := by
  induction is with
  | nil => simp
  | cons j js ih =>
    rw [List.flatMap_cons,List.count_append,ih nd.tail,List.count_replicate]
    by_cases h : j = i
    · subst j
      simp [(List.nodup_cons.mp nd).1]
    · simp [h,Ne.symm h]

private theorem matchColumns {xs ys : List Variable} {α : Type}
    (f g : Variable → α) (distinct : xs.Nodup) (h : (xs.map f).Perm (ys.map g)) :
    ∃ rename : Variable → Variable, (xs.map rename).Perm ys ∧ ∀ v ∈ xs, f v = g (rename v) := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := by simpa using h.length_eq.symm
    subst ys
    exact ⟨id,.nil,by simp⟩
  | cons x xs ih =>
    obtain ⟨y,hy,eq⟩ := List.mem_map.mp (h.mem_iff.mp List.mem_cons_self)
    have split := List.perm_cons_erase hy
    have rest := h.trans (split.map g)
    rw [List.map_cons,List.map_cons,eq] at rest
    obtain ⟨r,perm,matched⟩ := ih distinct.tail rest.cons_inv
    let rename (v : Variable) := if v = x then y else r v
    have unchanged (v : Variable) (hv : v ∈ xs) : rename v = r v :=
      ite_eq_right fun (he : v = x) => (List.nodup_cons.mp distinct).1 (he ▸ hv)
    refine ⟨rename,?_,?_⟩
    · rw [List.map_cons,List.map_congr_left unchanged]
      simpa [rename] using (perm.cons y).trans split.symm
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | h'
      · simpa [rename] using eq.symm
      · rw [unchanged v h']; exact matched v h'

private theorem countRenamed (r : Variable → Variable) (xs : List Variable) (v : Variable)
    (unique : ∀ x ∈ xs, r x = r v → x = v) :
    (xs.map r).count (r v) = xs.count v := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun y hy => unique y (List.mem_cons_of_mem _ hy))
    by_cases h : x = v
    · subst x; simp [tail]
    · have ne : r x ≠ r v := fun eq => h (unique x List.mem_cons_self eq)
      simp [List.count_cons_of_ne ne,List.count_cons_of_ne h,tail]

private theorem foldRename (f : sig.ACSym) (a : Variable) (as : List Variable) (r : Variable → Variable) :
    (ACRepresentation.fold f (.var a) (as.map Term.var)).subst (fun v => .var (r v)) =
      ACRepresentation.fold f (.var (r a)) ((as.map r).map Term.var) := by
  induction as generalizing a with
  | nil => rfl
  | cons x xs ih =>
    change Term.ac f _ ((ACRepresentation.fold f (.var x) (xs.map Term.var)).subst _) = _
    rw [ih]; rfl

private theorem imageRename (a b : Image sig) (r : Variable → Variable)
    (head : a.head = b.head) (perm : (a.vars.map r).Perm b.vars) :
    EquivB (a.term.subst (fun v => .var (r v))) b.term := by
  cases a with
  | single x =>
    cases b with
    | single y =>
      have : r x = y := by simpa [Image.vars] using perm
      simpa only [Image.term,Term.subst,this] using EquivB.refl (Term.var (sig := sig) y)
    | product => contradiction
  | product f x y xs =>
    cases b with
    | single => contradiction
    | product g u v us =>
      cases Option.some.inj head
      rw [Image.term,foldRename]
      exact ACRepresentation.decode_perm f (perm.map Term.var) _ _ rfl rfl

private theorem instanceOfKey {inputs : List Variable} {σ τ : Substitution sig}
    (a : View inputs σ) (b : View inputs τ) (key : SameKey a b) :
    Substitution.InstanceOn (· ∈ inputs) τ σ := by
  obtain ⟨r,perm,matched⟩ := matchColumns _ _ a.distinct key.2
  have sorted (v) (hv : v ∈ a.witnesses) : (r v).sort = v.sort :=
    (congrArg Prod.fst (matched v hv)).symm
  let δ : Substitution sig := {
    image := fun v => if v ∈ a.witnesses then .var (r v) else .var v
    support := a.witnesses
    outside := fun _ hv => ite_eq_right hv
    sorted := by
      intro v; split
      · next hv => rw [← sorted v hv]; exact .var _
      · exact .var _ }
  have inj (v u) (hv : v ∈ a.witnesses) (hu : u ∈ a.witnesses) (eq : r v = r u) : v = u := by
    obtain ⟨i,hi,ei⟩ := List.getElem_of_mem hv
    obtain ⟨j,hj,ej⟩ := List.getElem_of_mem hu
    have same := (perm.nodup_iff.mpr b.distinct).eq_of_getElem_eq
      (by simpa using hi : i < (a.witnesses.map r).length)
      (by simpa using hj : j < (a.witnesses.map r).length)
      (by simpa [ei,ej] using eq)
    subst j; exact ei.symm.trans ej
  refine ⟨δ,?_⟩
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  have heads : (a.image i).head = (b.image i).head := by
    have eq := congrArg (fun (xs : List (Option sig.ACSym)) => xs[i]?) key.1
    simpa [hi] using eq
  have row : ((a.image i).vars.map r).Perm (b.image i).vars := by
    apply List.perm_iff_count.mpr
    intro y
    by_cases hy : y ∈ b.witnesses
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (perm.mem_iff.mpr hy)
      rw [countRenamed _ _ _ (fun u hu => inj u x (a.includes i hi u hu) hx)]
      have eq := congrArg (fun (c : SortId × List Nat) => c.2.count i) (matched x hx)
      simpa [column,countPositions,List.nodup_range,hi] using eq
    · have noA : y ∉ (a.image i).vars.map r := by
        rintro hm
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
        exact hy (perm.mem_iff.mp (List.mem_map_of_mem (a.includes i hi x hx)))
      rw [List.count_eq_zero.mpr noA,List.count_eq_zero.mpr (fun h => hy (b.includes i hi y h))]
  have image := imageRename _ _ r heads row
  have agree := (a.image i).term.subst_eq_of_agree δ.image (fun w => .var (r w))
    fun w hw => ite_eq_left (a.includes i hi w ((a.image i).occurs_mem _ hw))
  exact (b.represents i hi).trans (image.symm.trans (agree ▸ ((a.represents i hi).subst δ.image).symm))

/-- Equality of the complete incidence key yields mutual instantiation
using one finite, sort-preserving substitution per direction. -/
theorem equivalent {inputs : List Variable} {σ τ : Substitution sig}
    (a : View inputs σ) (b : View inputs τ) (key : SameKey a b) :
    Substitution.InstanceOn (· ∈ inputs) τ σ ∧ Substitution.InstanceOn (· ∈ inputs) σ τ :=
  ⟨instanceOfKey a b key,instanceOfKey b a ⟨key.1.symm,key.2.symm⟩⟩

/-- Projecting onto a list that includes all input variables also covers the
problem's observation predicate, regardless of the caller's input order. -/
theorem covers {inputs : List Variable} {σ τ : Substitution sig} (p : Problem sig)
    (domain : ∀ v, p.Occurs v → v ∈ inputs)
    (a : View inputs σ) (b : View inputs τ) (key : SameKey a b) :
    Substitution.InstanceOn p.Occurs σ τ ∧ Substitution.InstanceOn p.Occurs τ σ := by
  obtain ⟨⟨δ,back⟩,⟨ε,fwd⟩⟩ := equivalent a b key
  exact ⟨⟨ε,fun v hv => fwd v (domain v hv)⟩,⟨δ,fun v hv => back v (domain v hv)⟩⟩

end Tamarin.FlatAnswerIncidence
