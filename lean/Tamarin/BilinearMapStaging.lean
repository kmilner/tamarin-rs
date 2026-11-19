import Tamarin.BilinearPointStaging

/-! Staging signed operands of a bilinear map. Either point can expose a
scalar before the other finishes normalizing. The extracted state carries
the resulting outer power through every competing reduction. -/
namespace Tamarin.Rewriting.Bilinear.MapStaging
open ConstructorVariants DHPeer Cancellation DHTower
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {T : Table s} {E : ExtraTable T}
variable {R : Root sig}

private structure Pending (s : Symbols sig) (R : Root sig) (v t : Term sig) : Prop where
  typed : HasSort t .msg
  signed : Staging.Signed s R t
  value : ∀ {u}, Reduces R t u → Normal R u → EquivB v u

private theorem Pending.start [DecidableEq sig.ACSym] (g : Balance.Inventory E) {v t : Term sig}
    (st : HasSort t .msg) (rd : Staging.Signed s (ruleRoot T.rules) t) (nf : NormalForm (ruleRoot T.rules) t v) :
    Pending s (ruleRoot T.rules) v t :=
  ⟨st,rd,fun red norm => Balance.normal_unique g E.presentation (fun _ => Balance.plain_of_inverse E) rd
    (nf.2.2 _ st) (g.reduces_sorted st (rd _) red) nf.2.1 norm nf.1 red⟩

private theorem Pending.step (g : Balance.Inventory E) {v t u : Term sig}
    (p : Pending s (ruleRoot T.rules) v t) (st : StepModulo (ruleRoot T.rules) t u) :
    Pending s (ruleRoot T.rules) v u :=
  ⟨g.reduces_sorted p.typed (p.signed _) (.step st),
   fun k => let ⟨z,rd⟩ := p.signed k; ⟨z,g.reduces k (.step st) z rd⟩,
   fun r n => p.value ((Reduces.step st).trans r) n⟩

private theorem Pending.done {v t : Term sig} (p : Pending s R v t) (n : Normal R t) : EquivB v t :=
  p.value (.basis (.refl _)) n

private theorem pow_eq {x y u v : Term sig} (a : EquivB x y) (b : EquivB u v) :
    EquivB (s.power x u) (s.power y v) := by apply EquivB.free; intro i; split <;> assumption

private theorem step_rebase {a b c : Term sig} (e : EquivB a b) (st : StepModulo R b c) : StepModulo R a c := by
  obtain ⟨x,y,l,h,r⟩ := st; exact ⟨x,y,e.trans l,h,r⟩

private def powOp (β : Operators sig) (s : Symbols sig) : Operators sig :=
  { β with pmult := s.pow, arity := s.powArity, inputs := s.powInput, pointSort := s.powSort }

private inductive State (s : Symbols sig) (β : Operators sig) (R : Root sig) (x y : Term sig) : Term sig → Prop where
  | both {a b t} (l : Pending s R x a) (r : Pending s R y b) (e : EquivB (β.map a b) t) : State s β R x y t
  | extracted {a v k q t} (p : Pending s R v a) (sk : Normal R k) (sq : Normal R q)
      (nonunit : head k ≠ .free s.one) (plain : head q ≠ .free β.pmult)
      (start : Reduces R (β.map x y) (s.power (β.map v q) k)) (e : EquivB (s.power (β.map a q) k) t) :
      State s β R x y t
  | staged {t} (red : Reduces R (β.map x y) t) : State s β R x y t

private theorem State.rebase {x y t u : Term sig} (st : State s β R x y t) (eq : EquivB t u) : State s β R x y u := by
  cases st with
  | both l r e => exact .both l r (e.trans eq)
  | extracted p k q u v start e => exact .extracted p k q u v start (e.trans eq)
  | staged red => exact .staged (red.trans (.basis eq))

private theorem Pending.expose (I : Inventory s β T.rules) {v t k q : Term sig}
    (p : Pending s (ruleRoot T.rules) v t) (hit : EquivB t (β.point k q)) :
    EquivB v (β.point k q) ∧ HasSort k .msg ∧ HasSort q .msg ∧
    Normal (ruleRoot T.rules) k ∧ Normal (ruleRoot T.rules) q ∧ head k ≠ .free s.one ∧ head q ≠ .free β.pmult := by
  have n := signed_point_normal β p.signed hit.head_eq
  obtain ⟨sk,sq⟩ := β.point_types (Term.checkSort_sound _ _ ((SortClash.check_equiv hit _) ▸ Term.checkSort_complete p.typed))
  exact ⟨(p.done n).trans hit,sk,sq,(I.point_normal_iff sk sq).mp ((normal_equiv _ hit).mp n)⟩

private theorem State.step (I : Inventory s β T.rules) (pow : PowerBucket T) (g : Balance.Inventory E)
    {x y t u : Term sig} (sx : HasSort x .msg) (sy : HasSort y .msg)
    (st : State s β (ruleRoot T.rules) x y t) (step : StepModulo (ruleRoot T.rules) t u) :
    State s β (ruleRoot T.rules) x y u := by
  cases st with
  | both l r e =>
    rcases (ContextualReduction.comm_iff ..).mp (step_rebase e step) with ⟨_,_,pre,hit,post⟩|⟨_,h,eq⟩|⟨_,h,eq⟩
    · cases I.map_root pre hit with
      | left point result =>
        obtain ⟨eq,sk,sq,nk,nq,nu,plain⟩ := l.expose I point
        have red := Reduces.step (root := ruleRoot T.rules) (by
          exact ⟨_,_,(EquivB.comm_swap ..).trans (.comm_congr _ (.refl y) eq),.root (I.extract sy sk sq),.refl _⟩ :
            StepModulo _ (β.map x y) _)
        exact .extracted r nk nq nu plain red ((pow_eq (.comm_swap ..) (.refl _)).trans (result.symm.trans post))
      | right point result =>
        obtain ⟨eq,sk,sq,nk,nq,nu,plain⟩ := r.expose I point
        have red : StepModulo (ruleRoot T.rules) (β.map x y) _ :=
          ⟨_,_,.comm_congr _ (.refl x) eq,.root (I.extract sx sk sq),.refl _⟩
        exact .extracted l nk nq nu plain (.step red) (result.symm.trans post)
    · exact .both (l.step g h) r eq
    · exact .both l (r.step g h) eq
  | @extracted a v k q _ p nk nq nu plain start e =>
    rcases (powOp β s).steps (step_rebase e step) with ⟨_,_,pre,hit,_⟩|⟨b,h,eq⟩|⟨b,h,_⟩
    · cases pow.root _ _ pre hit with
      | one unit => exact (nu unit).elim
      | neutral hd => cases hd
      | tower prev => cases prev.head_eq
    · rcases (ContextualReduction.comm_iff ..).mp h with ⟨u,w,pre,hit,post⟩|⟨_,h,f⟩|⟨_,h,_⟩
      · cases I.map_root pre hit with
        | right point => exact (plain point.head_eq).elim
        | left point =>
          have fixed := p.done (signed_point_normal β p.signed point.head_eq)
          have replay : StepModulo (ruleRoot T.rules) (β.map v q) b :=
            ⟨u,w,(EquivB.comm_congr _ fixed (.refl _)).trans pre,.root hit,post⟩
          have rr : Reduces (ruleRoot T.rules) (s.power (β.map v q) k) (s.power b k) := by
            apply Reduces.free; intro i; split <;> first | exact .step replay | exact .basis (.refl _)
          exact .staged ((start.trans rr).trans (.basis eq))
      · exact .extracted (p.step g h) nk nq nu plain start ((pow_eq f (.refl _)).trans eq)
      · exact (nq _ h).elim
    · exact (nk _ h).elim
  | staged r => exact .staged (r.trans (.step step))

/-- The full bilinear map has exactly the same normal outputs after any two
signed arguments are normalized, including simultaneous extraction races. -/
theorem map_stage [DecidableEq sig.ACSym] (I : Inventory s β T.rules) (pow : PowerBucket T) (g : Balance.Inventory E)
    {a b x y out : Term sig} (sa : HasSort a .msg) (sb : HasSort b .msg)
    (da : Staging.Signed s (ruleRoot T.rules) a) (db : Staging.Signed s (ruleRoot T.rules) b)
    (l : NormalForm (ruleRoot T.rules) a x) (r : NormalForm (ruleRoot T.rules) b y) :
    NormalForm (ruleRoot T.rules) (β.map a b) out ↔ NormalForm (ruleRoot T.rules) (β.map x y) out := by
  have sx := l.2.2 _ sa
  have sy := r.2.2 _ sb
  constructor
  · intro nf
    have h := RootNarrowing.reduction_invariant (State s β (ruleRoot T.rules) x y)
      State.rebase (State.step I pow g sx sy) nf.1 (.both (.start g sa da l) (.start g sb db r) (.refl _))
    refine ⟨?_,nf.2.1,fun _ hs => .widen (nf.2.2 _ (β.map_sorted sa sb)) (β.mapSort ▸ Term.rootSort_le hs)⟩
    cases h with
    | both l r e =>
      obtain ⟨nx,ny⟩ := normal_comm_children _ ((normal_equiv _ e).mpr nf.2.1)
      exact .basis ((EquivB.comm_congr _ (l.done nx) (r.done ny)).trans e)
    | @extracted a v k q _ p _ _ _ _ start e =>
      let i : Fin (sig.arity s.pow) := ⟨0,by have := s.powArity; omega⟩
      have nm : Normal (ruleRoot T.rules) (β.map a q) := by simpa [i] using normal_free_child _ _ ((normal_equiv _ e).mpr nf.2.1) i
      have f := p.done (normal_comm_children _ nm).1
      exact start.trans (.basis ((pow_eq (.comm_congr _ f (.refl _)) (.refl _)).trans e))
    | staged red => exact red
  · intro nf
    exact ⟨(Reduces.comm _ l.1 r.1).trans nf.1,nf.2.1,
      fun _ hs => .widen (nf.2.2 _ (β.map_sorted sx sy)) (β.mapSort ▸ Term.rootSort_le hs)⟩

end Tamarin.Rewriting.Bilinear.MapStaging
