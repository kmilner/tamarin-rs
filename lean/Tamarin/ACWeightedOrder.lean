import Tamarin.ACWeightedComposition
import Tamarin.ACSparsePlane
import Tamarin.ACRationalCone

namespace Tamarin.ACBasis.WeightedComposition
variable {n : Nat}

theorem draw_zero (tag : Fin 0 → Side) (q : Quota) : draw 0 tag q =
    (if q .pos = 0 ∧ q .neg = 0 ∧ q .neutral = 0 then [Fin.elim0] else []) := rfl

theorem draw_succ (tag : Fin (n+1) → Side) (q : Quota) : draw (n+1) tag q =
    (heads (fun i => tag i.succ) (tag 0) (q (tag 0))).flatMap fun h =>
      (draw n (fun i => tag i.succ) (spend q (tag 0) h)).map (prepend h) := by
  simp [draw,plan,Plan.draw,heads]

private theorem mass_cons (tag : Fin (n+1) → Side) (v : Vec (n+1)) (t : Side) :
    mass tag t v = (if tag 0 = t then v 0 else 0) + mass (fun i => tag i.succ) t (fun i => v i.succ) := by
  simp [mass,mask,total,List.ofFn_succ]; rfl

private theorem mass_absent (tag : Fin n → Side) (t : Side) (absent : ¬ ∃ i, tag i = t) (v : Vec n) :
    mass tag t v = 0 := by
  have z i : tag i ≠ t := fun h => absent ⟨i,h⟩
  simp [mass,mask,z,total,List.sum_eq_zero_iff_forall_eq_nat]

theorem mem_draw (tag : Fin n → Side) (q : Quota) (v : Vec n) :
    v ∈ draw n tag q ↔ Meets tag q v := by
  induction n generalizing q with
  | zero =>
    have z : v = Fin.elim0 := funext fun i => Fin.elim0 i
    simp only [draw_zero,Meets,mass,total,List.ofFn_zero,List.sum_nil]
    split
    · rename_i h; simp [z]; intro s; cases s <;> simp_all
    · rename_i h; simp only [List.not_mem_nil,false_iff]; intro all; exact h ⟨(all .pos).symm,(all .neg).symm,(all .neutral).symm⟩
  | succ n ih =>
    let s := tag 0
    let tail i := tag (Fin.succ i)
    let w i := v (Fin.succ i)
    have split (t) : mass tag t v = (if s = t then v 0 else 0) + mass tail t w := mass_cons tag v t
    simp only [draw_succ,List.mem_flatMap,List.mem_map]
    constructor
    · rintro ⟨h,hm,u,hu,hv⟩
      have head : h = v 0 := congrFun hv 0
      have cut : u = w := funext fun i => congrFun hv i.succ
      have left : h ≤ q s := by
        change h ∈ heads tail s (q s) at hm
        unfold heads at hm; split at hm <;> simp_all <;> omega
      have matchTail := (ih _ _ _).mp hu
      intro t
      change Meets tail (spend q s h) u at matchTail
      rw [split,←cut,matchTail,←head]
      by_cases e : s = t
      · subst t; simp [spend]; omega
      · simp [e,spend]
    · intro hit
      have hs := hit s; rw [split] at hs; simp at hs
      refine ⟨v 0,?_,w,(ih ..).mpr ?_,funext fun i => Fin.cases rfl (fun _ => rfl) i⟩
      · change v 0 ∈ heads tail s (q s)
        unfold heads; split
        · simp; omega
        · rename_i h; rw [mass_absent _ _ h] at hs; simp_all
      · intro t
        change mass tail t w = spend q s (v 0) t
        have ht := hit t; rw [split] at ht
        by_cases e : s = t <;> simp [spend,e] at ht ⊢ <;> omega

private abbrev Before (v w : Vec n) := List.ofFn v < List.ofFn w
private abbrev Ordered (v w : Vec n) := decide (List.ofFn v ≤ List.ofFn w) = true

private theorem sorted_draw (tag : Fin n → Side) (q : Quota) : (draw n tag q).Pairwise Before := by
  induction n generalizing q with
  | zero => simp [draw_zero]; split <;> simp
  | succ n ih =>
    rw [draw_succ,List.pairwise_flatMap]
    constructor
    · intro h _; apply List.pairwise_map.mpr
      exact (ih _ _).imp (fun b => by simpa [Before,List.ofFn_succ] using b)
    · have sorted (xs : Fin n → Side) (s) (k) : (heads xs s k).Pairwise (· < ·) := by
        unfold heads; split; exact List.pairwise_lt_range; simp
      apply (sorted ..).imp
      rintro a b lt u hu v hv
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hu; obtain ⟨_,_,rfl⟩ := List.mem_map.mp hv
      simp only [Before,List.ofFn_succ,Fin.cases_zero,Fin.cases_succ]
      exact List.Lex.rel lt

private theorem member (r : Row n) {a b} (u : Uniform r a b) {v} (p : Primitive r a b v) :
    v ∈ r.generators := by
  have basis : BasisCorrect [r] r.generators := by
    intro x
    constructor
    · intro h; exact r.complete x (h _ List.mem_cons_self)
    · rintro ⟨c,rfl⟩
      simpa [SystemHolds] using Cone.mix_holds r r.generators.get
        (fun i => ((r.mem_generators _).mp (List.get_mem _ i)).2.1) c
  have mem := (minimize_iff_irreducible [r] r.generators basis v).mpr ((primitive_iff r u v).mp p)
  exact ((mem_minimize ..).mp mem).1

private noncomputable def keep (r : Row n) (a b : Nat) (v : Vec n) : Bool := by
  classical exact decide (Primitive r a b v)

theorem ordered (r : Row n) {a b} (u : Uniform r a b) :
    enumerate r a b = r.generators.filter (keep r a b) := by
  let L := draw n (side r) (active a b)
  let R := draw n (side r) singleton
  have sl := sorted_draw (side r) (active a b)
  have sr := sorted_draw (side r) singleton
  have st : (r.generators.filter (keep r a b)).Pairwise Before :=
    ((SparsePlane.box_sorted _ _).sublist List.filter_sublist).sublist List.filter_sublist
  have nd {xs : List (Vec n)} (s : xs.Pairwise Before) : xs.Nodup :=
    s.imp fun {x y} h e => by subst y; exact (List.lt_irrefl _) h
  have lr : (L ++ R).Nodup := by
    apply List.nodup_append.mpr; refine ⟨nd sl,nd sr,?_⟩
    intro x hx y hy e; subst y
    have left := (mem_draw ..).mp hx .neutral
    have right := (mem_draw ..).mp hy .neutral
    change _ = 0 at left; change _ = 1 at right; omega
  have perm : (L ++ R).Perm (r.generators.filter (keep r a b)) := by
    apply (List.perm_ext_iff_of_nodup lr (nd st)).mpr
    intro v; simp only [L,R,List.mem_append,mem_draw,List.mem_filter,keep,decide_eq_true_eq]
    exact ⟨fun h => ⟨member r u h,h⟩,And.right⟩
  have weak {xs : List (Vec n)} (s : xs.Pairwise Before) : xs.Pairwise Ordered :=
    s.imp fun h => decide_eq_true (List.le_of_lt h)
  apply List.Perm.eq_of_pairwise (le := Ordered)
  · intro v w _ _ h h'
    have eq := List.le_antisymm (of_decide_eq_true h) (of_decide_eq_true h')
    funext i
    simpa [List.getElem?_ofFn,i.isLt] using congrArg (fun xs => xs[i.val]?) eq
  · apply List.pairwise_merge _ _ _ _ (weak sl) (weak sr)
    · intro v w u h h'; exact decide_eq_true (List.le_trans (of_decide_eq_true h) (of_decide_eq_true h'))
    · intro v w; simpa using List.le_total (List.ofFn v) (List.ofFn w)
  · exact weak st
  · exact (List.merge_perm_append ..).trans perm

theorem minimize_lift {k} (r : Row k) {a b} (u : Uniform r a b) (g : Fin k → Vec n)
    (live : ∀ i, ∃ j, 0 < g i j) :
    minimize (lift g (enumerate r a b)) = minimize (lift g r.generators) := by
  rw [ordered r u]; apply minimize_lift_filter _ _ _ live
  intro c hc drop
  obtain ⟨_,hs,nz⟩ := (r.mem_generators c).mp hc
  obtain ⟨y,p,le⟩ := dominated r u hs nz
  exact ⟨y,member r u p,by simp [keep,p], ((primitive_iff r u y).mp p).2.1,le,
    fun eq => by subst c; simp [keep,p] at drop⟩

end Tamarin.ACBasis.WeightedComposition
