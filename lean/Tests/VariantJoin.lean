import Tamarin.VariantJoinLeaf
import Tamarin.VariantJoinPacked
import Tamarin.VariantJoinAmbient
import Tamarin.Reflexive
import Tamarin.VariableElimination
import Tamarin.RootNormalForms

/-! A real rewrite at a unary free head distinguishes equality of input
images from irreducibility of specialized output terms. -/
namespace Tamarin.VariantJoinTests
open Rewriting Rewriting.VariantJoin Rewriting.ConstructorVariants
private abbrev sig : Signature where
  FreeSym := Unit
  CSym := Empty
  ACSym := Empty
  Atom := Bool
  arity _ := 1
  inputSort _ _ := .msg
  outputSort _ := .msg
  cSort _ := .msg
  acSort _ := .msg
  atomSort _ := .msg

private abbrev T := Term sig
private abbrev row := Row sig Unit Unit
private def lit (b : Bool) : T := .atom b
private def unary (t : T) : T := .free () fun _ => t
private def rules : List (Equation sig) := [⟨unary (lit false),lit true⟩]
private abbrev R := ruleRoot rules
private def v (i : Nat) : Variable := ⟨i,.msg⟩
private def frame (x y : T) : row := ⟨fun _ => x,fun _ => y⟩
private theorem apps : ∀ eq ∈ rules, Application eq.lhs := by
  intro eq mem; obtain rfl := List.mem_singleton.mp mem; trivial
private theorem vars : Normalized R Substitution.identity := (constructor_normal rules apps).1
private theorem atomN (b) : Normal R (lit b) :=
  constructor_node_normal rules apps _ (by intro h; obtain h := List.mem_singleton.mp h; cases h) trivial
private theorem different : ¬EquivB (lit true) (lit false) := fun eq => by cases eq.head_eq
private def bind (i : Nat) (b : Bool) : Substitution sig := .binding (v i) (lit b) (HasSort.atom (sig := sig) b)
private theorem bindN (i b) : Normalized R (bind i b) := by
  intro w; change Normal _ (if w = v i then lit b else .var w)
  split <;> first | exact atomN _ | exact vars _
private theorem bindHit (i b) : (bind i b).apply (.var (v i)) = lit b := Substitution.binding_image_self ..

private theorem inputs_incompatible :
    CompleteSet (problem (frame (lit true) (lit true)) (frame (lit false) (lit true)) [()] []) [] := by
  apply (complete_empty_iff _).mpr; rintro ⟨σ,sol⟩
  exact different (sol ⟨lit true,lit false⟩ List.mem_cons_self)

-- The result stays empty even when the two local values are identical.
example (x : T) (hx : Normal R x) :
    ¬(Denotes R (frame (lit true) (lit true)) (fun _ => x) (fun _ => lit true) ∧
      Denotes R (frame (lit false) (lit true)) (fun _ => x) (fun _ => lit true)) := by
  intro h
  have unused (b c : Bool) (w) : ¬ (frame (lit b) (lit c)).Uses w := by
    rintro (⟨_,h⟩|⟨_,h⟩) <;> exact h
  have law := exact_join vars _ _ (fun w hw => False.elim (unused _ _ w hw)) [()] (by simp) []
    (fun w h => h.elim (fun hw => False.elim (unused _ _ w hw)) (fun hw => False.elim (unused _ _ w hw)))
    [] inputs_incompatible _ _ _ (fun _ => hx) (fun _ => atomN true) (fun _ => atomN true)
  obtain ⟨_,mem,_⟩ := law.mp h
  exact List.not_mem_nil mem

private def capture (i : Nat) := frame (lit false) (.var (v i))
private theorem captureUses (i : Nat) (w) : (capture i).Uses w ↔ w = v i := by
  constructor
  · rintro (⟨_,h⟩|⟨_,h⟩)
    · exact False.elim h
    · exact h
  · intro eq; exact .inr ⟨(),eq⟩
private theorem captureDenotes (i b) : Denotes R (capture i) (fun _ => lit false) (fun _ => lit b) :=
  ⟨bind i b,bindN i b,fun _ => .refl _,fun _ => by change EquivB _ ((bind i b).apply (.var (v i))); rw [bindHit]; exact .refl _⟩

-- Both witnesses occur only in returned values. Reflexive anchors give
-- the CSU a factorization obligation for each of them. One instantiating
-- substitution must simultaneously choose distinct outputs in the joined row.
example :
    let q := capture 0
    let r := capture 1
    (join q r Substitution.identity).IsNormal R ∧
      Denotes R (join q r Substitution.identity) (fun _ => lit false)
        (Sum.elim (fun _ => lit false) (fun _ => lit true)) := by
  let anchors : List T := [.var (v 0),.var (v 1)]
  let p := problem (capture 0) (capture 1) [()] anchors
  have ids : CompleteSet p [.identity] := Reflexive.identity_complete p (by
    intro e h; rcases List.mem_cons.mp h with rfl|h
    · rfl
    · rcases List.mem_cons.mp h with rfl|h
      · rfl
      · obtain rfl := List.mem_singleton.mp h; rfl)
  have apart (w) (h : (capture 0).Uses w) : ¬(capture 1).Uses w := by
    intro h'; have eq := ((captureUses _ _).mp h).symm.trans ((captureUses _ _).mp h'); cases eq
  have tracked (w) (h : (capture 0).Uses w ∨ (capture 1).Uses w) : p.Occurs w := by
    rcases h with h|h
    · obtain rfl := (captureUses _ _).mp h
      exact ⟨⟨.var _,.var _⟩,by right; exact List.mem_cons_self,.inl rfl⟩
    · obtain rfl := (captureUses _ _).mp h
      exact ⟨⟨.var _,.var _⟩,by right; right; exact List.mem_cons_self,.inl rfl⟩
  have iff := exact_join vars _ _ apart [()] (by simp) anchors tracked _ ids _ _ _
    (fun _ => atomN false) (fun _ => atomN false) (fun _ => atomN true)
  obtain ⟨μ,mem,both⟩ := iff.mp ⟨captureDenotes 0 false,captureDenotes 1 true⟩
  obtain rfl := List.mem_singleton.mp mem
  exact both

-- Without an output-only anchor, even a complete input CSU can bind that
-- witness to a single literal and silently lose another possible value.
example :
    let q := capture 0
    let r := frame (lit false) (lit false)
    let μ := bind 0 false
    CompleteSet (problem q r [()] []) [μ] ∧
    Denotes R q (fun _ => lit false) (fun _ => lit true) ∧
    Denotes R r (fun _ => lit false) (fun _ => lit false) ∧
    ¬Denotes R (join q r μ) (fun _ => lit false) (Sum.elim (fun _ => lit true) (fun _ => lit false)) := by
  refine ⟨?_,captureDenotes 0 true,⟨.identity,vars,fun _ => .refl _,fun _ => .refl _⟩,?_⟩
  · constructor
    · intro σ _ e mem; obtain rfl := List.mem_singleton.mp mem; exact .refl _
    · intro ρ _
      refine ⟨_,List.mem_cons_self,.identity,?_⟩
      rintro w ⟨e,mem,occurs⟩
      obtain rfl := List.mem_singleton.mp mem
      exact False.elim (occurs.elim id id)
  · rintro ⟨_,_,fits⟩
    exact different (fits.values (.inl ()))

-- The input call contains only X = false. Reserving the hidden output
-- witness W permits an arbitrary W in the answer, even though the unifier
-- never received either f(W) = f(W) or a reflexive equation for W.
example :
    let q := frame (.var (v 0)) (.var (v 1))
    let r := frame (lit false) (lit false)
    let anchors := [unary (.var (v 1)),.var (v 0)]
    CompleteSet (problem q r [()] anchors) [bind 0 false] ∧
      Denotes R (join q r (bind 0 false)) (fun _ => lit false)
        (Sum.elim (fun _ => lit true) (fun _ => lit false)) := by
  let q := frame (.var (v 0)) (.var (v 1))
  let r := frame (lit false) (lit false)
  let p := problem q r [()] []
  let anchors := [unary (.var (v 1)),.var (v 0)]
  have live (w) : p.Occurs w ↔ w = v 0 := by
    constructor
    · rintro ⟨eq,mem,h⟩; obtain rfl := List.mem_singleton.mp mem; exact h.elim id False.elim
    · intro h; exact ⟨_,List.mem_cons_self,.inl h⟩
  have reserve : Reserves p anchors (bind 0 false) := by
    apply Reserves.of_scoped (avoid := [v 1])
    · intro w hw; exact Substitution.binding_image_other _ _ _ _ (fun h => hw ((live w).mpr h))
    · intro y hy w hw
      obtain rfl := (live y).mp hy
      rw [show (bind 0 false).image (v 0) = lit false from bindHit ..] at hw
      exact False.elim hw
    · rintro w ⟨⟨t,mem,occ⟩,outside⟩
      rcases List.mem_cons.mp mem with rfl|h
      · obtain ⟨_,eq⟩ := occ; exact List.mem_singleton.mpr eq
      · obtain rfl := List.mem_singleton.mp h; exact False.elim (outside ((live w).mpr occ))
  have inputs : CompleteSet p [bind 0 false] :=
    VariableElimination.binding_complete _ _ (HasSort.atom (sig := sig) false) (fun h => h)
  refine ⟨join_csu inputs anchors (fun μ mem => (List.mem_singleton.mp mem) ▸ reserve),?_⟩
  exact ⟨bind 1 true,bindN 1 true,fun _ => .refl _,fun a => by cases a <;> exact .refl _⟩

-- Merely leaving W unbound is insufficient. An input-only CSU for X = X
-- may use W as its parameter; forcing that same W to occur in the output
-- prevents simultaneous assignments X = true and W = false.
example :
    let x := v 0
    let w := v 1
    let p : Problem sig := [⟨.var x,.var x⟩]
    let μ := Substitution.binding x (Term.var (sig := sig) w) (HasSort.var w)
    CompleteSet p [μ] ∧ μ.image w = .var w ∧
      ¬CompleteSet (p ++ [⟨.var w,.var w⟩]) [μ] := by
  let μ := Substitution.binding (v 0) (Term.var (sig := sig) (v 1)) (HasSort.var (v 1))
  have image : μ.image (v 0) = .var (v 1) := Substitution.binding_image_self ..
  have fixed : μ.image (v 1) = .var (v 1) := Substitution.binding_image_other _ _ _ _ (by decide)
  refine ⟨⟨?_,?_⟩,fixed,?_⟩
  · intro σ hm e mem; obtain rfl := List.mem_singleton.mp mem; exact .refl _
  · intro ρ _
    let δ := Substitution.binding (v 1) (ρ.image (v 0)) (ρ.sorted (v 0))
    refine ⟨μ,List.mem_cons_self,δ,?_⟩
    rintro z ⟨e,hm,occ⟩
    obtain rfl := List.mem_singleton.mp hm
    obtain rfl : z = v 0 := occ.elim id id
    change EquivB _ (δ.apply (μ.image (v 0)))
    rw [image,show δ.apply (.var (v 1)) = ρ.image (v 0) from Substitution.binding_image_self ..]
    exact .refl _
  · intro complete
    let ρ := (bind 0 true).compose (bind 1 false)
    obtain ⟨σ,mem,δ,agree⟩ := complete.covers ρ (by
      intro e h; rcases List.mem_cons.mp h with rfl|h
      · exact .refl _
      · obtain rfl := List.mem_singleton.mp h; exact .refl _)
    obtain rfl := List.mem_singleton.mp mem
    have ex := agree (v 0) ⟨_,List.mem_cons_self,.inl rfl⟩
    have ew := agree (v 1) ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,.inl rfl⟩
    change EquivB (lit true) (δ.apply (μ.image (v 0))) at ex
    change EquivB (lit false) (δ.apply (μ.image (v 1))) at ew
    rw [image] at ex; rw [fixed] at ew
    exact different (ex.trans ew.symm)

-- Without opening scopes, independent local specializations can falsely
-- identify the two output-only witnesses. No unifier, even outside the
-- usual CSU, can realize both concrete outputs in the incorrectly joined row.
example :
    Denotes R (capture 0) (fun _ => lit false) (fun _ => lit false) ∧
    Denotes R (capture 0) (fun _ => lit false) (fun _ => lit true) ∧
    ∀ μ, ¬Denotes R (join (capture 0) (capture 0) μ) (fun _ => lit false)
      (Sum.elim (fun _ => lit false) (fun _ => lit true)) := by
  refine ⟨captureDenotes 0 false,captureDenotes 0 true,?_⟩
  rintro μ ⟨δ,_,fits⟩
  exact different ((fits.values (.inr ())).trans (fits.values (.inl ())).symm)

-- The local pattern f(X) is irreducible, but matching the other row's
-- input forces X = false, exposing the active rule f(false) -> true.
private def left := frame (.var (v 0)) (unary (.var (v 0)))
private def right := frame (lit false) (lit true)
private theorem localNormal : left.IsNormal R := by
  refine ⟨fun _ => vars _,fun _ => normal_free_no_root (fun _ => vars _) ?_⟩
  rintro ys h out ⟨eq,mem,σ,root,_⟩
  obtain rfl := List.mem_singleton.mp mem
  have eq : ys 0 = lit false := by cases root; rfl
  have bad := h 0; rw [eq] at bad; cases bad.head_eq

private theorem redex : ¬Normal R (unary (lit false)) := by
  intro n
  exact n _ ⟨_,_,.refl _,.root ⟨_,List.mem_cons_self,.identity,(Substitution.apply_identity _).symm,
    (Substitution.apply_identity _).symm⟩,.refl _⟩

example : left.IsNormal R ∧ right.IsNormal R ∧
    (problem left right [()] []).Solves (bind 0 false) ∧
    ¬(join left right (bind 0 false)).IsNormal R := by
  refine ⟨localNormal,⟨fun _ => atomN _,fun _ => atomN _⟩,?_,?_⟩
  · intro eq h; obtain rfl := List.mem_singleton.mp h
    change EquivB ((bind 0 false).apply (.var _)) (lit false)
    rw [bindHit]; exact .refl _
  · intro h; exact redex (h.2 (.inl ()))

-- Two rows insist that their common input and its observed output coincide.
-- Different requested outputs contradict the shared input even with two
-- different witness variables and arbitrary choices of unifier.
example (μ : Substitution sig)
    (sol : (problem (frame (.var (v 0)) (.var (v 0))) (frame (.var (v 1)) (.var (v 1))) [()] []).Solves μ)
    (x : T) : ¬Denotes R (join (frame (.var (v 0)) (.var (v 0))) (frame (.var (v 1)) (.var (v 1))) μ)
      (fun _ => x) (Sum.elim (fun _ => lit false) (fun _ => lit true)) := by
  rintro ⟨δ,_,fits⟩
  have eq := sol ⟨.var (v 0),.var (v 1)⟩ List.mem_cons_self
  exact different ((fits.values (.inr ())).trans (((eq.subst δ.image).symm).trans (fits.values (.inl ())).symm))


-- Renaming 0 → 1 and 1 → 2 overlaps the old range. Both changes apply
-- simultaneously, including the occurrence of the second name in a value.
private def overlap : CallerFreshening.Allocation [v 0,v 1] where
  assign w := if w = v 0 then v 1 else v 2
  sorted := by intro w hw; simp at hw; rcases hw with rfl|rfl <;> rfl
  injective := by
    intro u hu w hw same
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu hw
    rcases hu with rfl|rfl <;> rcases hw with rfl|rfl <;> first | rfl | contradiction

example (x y : T) :
    Denotes R (frame (.var (v 0)) (unary (.var (v 1)))) (fun _ => x) (fun _ => y) ↔
      Denotes R (frame (.var (v 1)) (unary (.var (v 2)))) (fun _ => x) (fun _ => y) := by
  apply Row.Relabels.denotes
  apply Row.Relabels.of_allocation _ overlap
  · rintro w (⟨_,occ⟩|⟨_,i,occ⟩)
    · exact List.mem_cons.mpr (.inl occ)
    · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr occ)
  · intro _; exact .refl _
  · intro _; exact .refl _

-- An empty key set and an empty list of operations are valid. Repeated
-- stable slots still need positional correspondence and reconstruction.
private def ground : Row sig (Key []) Empty := ⟨fun i => False.elim (List.not_mem_nil i.property),Empty.elim⟩
private theorem groundExact : Exact R Subtype.val Empty.elim [ground] := by
  intro _ _ _ _
  constructor
  · intro _
    exact ⟨ground,List.mem_cons_self,.identity,vars,
      fun i => False.elim (List.not_mem_nil i.property),fun i => Empty.elim i⟩
  · exact fun _ i => Empty.elim i

example :
    let slots : List (Sum Empty T) := [.inr (lit true),.inr (lit false),.inr (lit true)]
    let typed : ∀ r ∈ [ground], r.Sorted := fun _ _ i => False.elim (List.not_mem_nil i.property)
    let query := slots.map (packedInput Empty.elim)
    let answers := packRows [ground] typed slots
    CompleteVariants R query answers ∧ ∀ a ∈ answers, a.Reconstructible R query := by
  dsimp only
  apply groundExact.packed vars _ (fun _ _ => ⟨fun i => False.elim (List.not_mem_nil i.property),fun a => Empty.elim a⟩)
    _ (fun a => Empty.elim a)
  · rintro v ⟨_,ht,occ⟩
    simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> exact False.elim occ
  · intro t ht
    simp at ht
    rcases ht with rfl|rfl|rfl <;> exact fun _ _ => atomN _
  · exact fun _ _ i => Empty.elim i

-- A local answer for the single variable X may use Y as its parameter.
-- Another leaf also observes Y. Padding with Y's identity before reopening
-- the parameter would falsely require X and Y to have the same image.
private def localTerm : T := .var (v 0)
private def ids : Bool → Variable := fun b => if b then v 1 else v 0
private def localLeaf (w : Variable) : Row sig (LocalKey localTerm) Unit :=
  ⟨fun _ => .var w, fun _ => .var w⟩
private def lifted (w : Variable) : Row sig Bool Unit :=
  ⟨fun b => if b then .var (v 1) else .var w, fun _ => .var w⟩

private theorem ids_cover : ∀ z, localTerm.Occurs z → ∃ b, ids b = z :=
  fun _ occ => ⟨false,occ.symm⟩

example : ¬ Pads localTerm ids (localLeaf (v 1)) (lifted (v 1)) := by
  intro bad
  exact bad.apart true (by intro h; cases h) (.inr ⟨(),rfl⟩)

example :
    Denotes R (localLeaf (v 1)) (fun _ => lit true) (fun _ => lit true) ∧
    ¬ Denotes R (lifted (v 1)) (fun b => if b then lit false else lit true) (fun _ => lit true) := by
  constructor
  · have hit : EquivB (lit true) ((bind 1 true).apply (.var (v 1))) := by
      rw [bindHit]; exact .refl _
    exact ⟨bind 1 true,bindN 1 true,fun _ => hit,fun _ => hit⟩
  · rintro ⟨_,_,fit⟩
    exact different ((fit.inputs false).trans (fit.inputs true).symm)

example (ρ : Substitution sig) (hn : Normalized R ρ) (out : Unit → T) :
    Denotes R (localLeaf (v 2)) (fun i => ρ.image i.val) out ↔
      Denotes R (lifted (v 2)) (fun i => ρ.image (ids i)) out := by
  apply Pads.denotes _ ids_cover ρ hn
  constructor
  · intro i h; cases i
    · exact .refl _
    · cases h
  · intro i h; cases i
    · exact False.elim (h rfl)
    · exact .refl _
  · exact .refl _
  · intro i h used; cases i
    · exact h rfl
    · rcases used with ⟨_,occ⟩|⟨_,occ⟩ <;> cases occ

end Tamarin.VariantJoinTests
