import Tamarin.MixedComponentSearch

/-! The homogeneous solver works in one sort. Purified slots represent raw
terms, including kind-level subterms of a sorted unification query. Run the
component search in a copy of the signature with one common sort and restore
the source sorts only after projecting the shared slot valuation. -/
namespace Tamarin.MixedUnification.ComponentEncoding
variable {s : Signature}

abbrev uniform (s : Signature) : Signature := { s with
  inputSort := fun _ _ => .msg, outputSort := fun _ => .msg, cSort := fun _ => .msg,
  acSort := fun _ => .msg, atomSort := fun _ => .msg }

private def number : SortId → Nat
  | .pub => 0 | .fresh => 1 | .msg => 2 | .node => 3 | .nat => 4

private def original (v : Variable) : Variable :=
  ⟨v.id / 5,match v.id % 5 with | 0 => .pub | 1 => .fresh | 2 => .msg | 3 => .node | _ => .nat⟩

private def name (v : Variable) : Variable := ⟨v.id * 5 + number v.sort,.msg⟩

private theorem original_name (v : Variable) : original (name v) = v := by
  obtain ⟨i,k⟩ := v
  cases k <;> simp [original,name,number,Nat.add_mod] <;> omega

private def encode : Term s → Term (uniform s)
  | .var v => .var (name v)
  | .atom a => .atom a
  | .free f args => .free f fun i => encode (args i)
  | .comm f a b => .comm f (encode a) (encode b)
  | .ac f a b => .ac f (encode a) (encode b)

private theorem encode_sorted (t : Term s) : HasSort (encode t) .msg := by
  induction t with
  | var => exact .var _
  | atom => exact .atom _
  | free f xs ih => exact .free _ _ ih
  | comm f a b ha hb => exact .comm _ _ _ ha hb
  | ac f a b ha hb => exact .ac _ _ _ ha hb

private theorem encode_equiv {a b : Term s} (h : EquivB a b) : EquivB (encode a) (encode b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih hj => exact ih.trans hj
  | free _ _ _ _ ih => exact .free _ _ _ ih
  | comm_congr _ _ _ ih hj => exact .comm_congr _ ih hj
  | ac_congr _ _ _ ih hj => exact .ac_congr _ ih hj
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

private def read (vars : Variable → Term s) : Term (uniform s) → Term s
  | .var v => vars v
  | .atom a => .atom a
  | .free f args => .free f fun i => read vars (args i)
  | .comm f a b => .comm f (read vars a) (read vars b)
  | .ac f a b => .ac f (read vars a) (read vars b)

private theorem read_equiv (vars : Variable → Term s) {a b} (h : EquivB a b) :
    EquivB (read vars a) (read vars b) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih hj => exact ih.trans hj
  | free _ _ _ _ ih => exact .free _ _ _ ih
  | comm_congr _ _ _ ih hj => exact .comm_congr _ ih hj
  | ac_congr _ _ _ ih hj => exact .ac_congr _ ih hj
  | comm_swap => exact .comm_swap _ _ _
  | ac_swap => exact .ac_swap _ _ _
  | ac_assoc => exact .ac_assoc _ _ _ _

private theorem read_encode (t : Term s) : read (.var ∘ original) (encode t) = t := by
  induction t with
  | var v => simp [encode,read,original_name]
  | atom => rfl
  | free f xs ih => exact congrArg (Term.free f) (funext ih)
  | ac _ _ _ ih hj | comm _ _ _ ih hj => simp [encode,read,ih,hj]

private theorem read_subst (vars : Variable → Term s) (δ : Substitution (uniform s)) (t) :
    read vars (δ.apply t) = (read Term.var t).subst (fun w => read vars (δ.image w)) := by
  induction t with
  | var | atom => rfl
  | free f xs ih => apply congrArg (Term.free (sig := s) f); funext i; exact ih i
  | ac f a b ih hj | comm f a b ih hj =>
    simp only [Substitution.apply,Term.subst,read] at *; rw [ih,hj]

private def slot (i : Nat) : Variable := ⟨i,.msg⟩
private def equation (c : Constraint s) : Equation (uniform s) :=
  ⟨.var (slot c.out),match c with
    | .atom _ a => .atom a
    | .free _ f args => .free f fun j => .var (slot (args j))
    | .comm _ f i j => .comm f (.var (slot i)) (.var (slot j))
    | .ac _ f i j => .ac f (.var (slot i)) (.var (slot j))⟩

private def reserve (obs : List Variable) (V : Nat → Term s) : Substitution (uniform s) where
  support := obs
  image v := if v ∈ obs ∧ v.sort = .msg then encode (V v.id) else .var v
  outside := by intro v hv; simp [hv]
  sorted := by intro v; split <;> rename_i h; exact h.2 ▸ encode_sorted _; exact .var _

private theorem reserve_solves (q : System s) {V} (model : q.Model V) (obs : List Variable)
    (includes : ∀ v, Problem.Occurs (q.constraints.map equation) v → v ∈ obs) :
    Problem.Solves (q.constraints.map equation) (reserve obs V) := by
  intro e he
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
  let full := fun (v : Variable) => encode (V v.id)
  have same (t : Term (uniform s)) (side : t = (equation c).lhs ∨ t = (equation c).rhs)
      (msg : ∀ v, t.Occurs v → v.sort = .msg) :
      (reserve obs V).apply t = t.subst full := by
    apply Term.subst_eq_of_agree
    intro v hv
    have live := includes v ⟨equation c,List.mem_map_of_mem hc,by rcases side with rfl|rfl <;> simp_all⟩
    simp [reserve,full,live,msg v hv]
  have typed (v : Variable) (h : (equation c).rhs.Occurs v) : v.sort = .msg := by
    cases c with
    | atom => exact False.elim h
    | free _ _ _ => obtain ⟨_,rfl⟩ := h; rfl
    | comm | ac => rcases h with rfl|rfl <;> rfl
  rw [same _ (.inl rfl) (fun v hv => (show v = slot c.out from hv) ▸ rfl),
      same _ (.inr rfl) typed]
  have h := encode_equiv (model c hc)
  cases c <;> exact h

private theorem read_model (q : System s) {σ : Substitution (uniform s)}
    (h : Problem.Solves (q.constraints.map equation) σ) :
    q.Model (fun i => read Term.var (σ.image (slot i))) := by
  intro c hc
  have eq := read_equiv (s := s) Term.var (h (equation c) (List.mem_map_of_mem hc))
  cases c <;> exact eq

private def heads (q : System s) [DecidableEq s.ACSym] : List s.ACSym :=
  (q.constraints.filterMap fun c => match c with | .ac _ f .. => some f | _ => none).eraseDups

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def compiledProblem (q : System s) : Problem (uniform s) := q.constraints.map equation

private def observations (p : Problem s) : List Variable :=
  let q := purify p
  ((compiledProblem q).variables ++ (inventory p).map (fun t => slot (q.slot t))).eraseDups

/-- An input-side sufficient condition. It inspects the constraints in the
complete joint AC frontier and does not require a successful unifier result. -/
def ConstructorFrontier (p : Problem s) : Prop :=
  let q := purify p
  let obs := observations p
  ∀ c ∈ (ComponentSearch.frontier (s := uniform s) (heads (s := s) q) (compiledProblem q) obs).val,
    ComponentSearch.ConstructorDecided c obs

abbrev SlotPair (s : Signature) := Term s × Term s

structure Stage (p : Problem s) (candidates : List (SlotPair s)) where
  rows : List (UnifierSorts.Template s)
  reopen : List (SlotPair s)
  subset : reopen ⊆ candidates
  sound : ∀ θ ∈ rows, RigidBranches.Solves p θ
  covers : ∀ ρ : Substitution s, p.Solves ρ →
    (∃ θ ∈ rows, ∃ μ, ∀ v, p.Occurs v → EquivB (ρ.image v) ((θ v).subst μ)) ∨
    ∃ z ∈ reopen, EquivB (ρ.apply z.1) (ρ.apply z.2)

/-- A completed branch projects its shared slot valuation back to the input.
A blocked branch may instead prove a new equality between original subterms.
Only those original terms cross into the next pass. -/
def branch (p : Problem s) (candidates : List (SlotPair s)) : Option (Stage p candidates) := by
  let q := purify p
  let compiled := compiledProblem q
  let key (z : SlotPair s) := (slot (q.slot z.1),slot (q.slot z.2))
  let terms := inventory p
  let eligible := candidates.filter fun z => z.1 ∈ terms && z.2 ∈ terms
  let obs := observations p
  let result := ComponentSearch.analyze (s := uniform s) key eligible (heads (s := s) q) compiled obs
  let image := fun (σ : Substitution (uniform s)) => project q (fun i => read Term.var (σ.image (slot i)))
  have live (v) (h : compiled.Occurs v) : v ∈ obs :=
    List.mem_eraseDups.mpr (List.mem_append_left _ ((Problem.mem_variables ..).mpr h))
  have observed (t : Term s) (h : t ∈ terms) : slot (q.slot t) ∈ obs :=
    List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_map_of_mem h))
  match hr : result.val with
  | none => exact none
  | some ans =>
    let rows := ans.filterMap Sum.getLeft?
    let again := (ans.filterMap Sum.getRight?).eraseDups
    obtain ⟨allowed,valid,cover⟩ := result.property ans hr
    have memL {σ} : σ ∈ rows ↔ Sum.inl σ ∈ ans := by
      simp [rows,List.mem_filterMap,Sum.getLeft?_eq_some_iff]
    have memR {z} : z ∈ again ↔ Sum.inr z ∈ ans := by
      simp [again,List.mem_filterMap,Sum.getRight?_eq_some_iff]
    refine some ⟨rows.map image,again,fun z hz => (List.mem_filter.mp (allowed z (memR.mp hz))).1,?_,?_⟩
    · intro θ hθ
      obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hθ
      have solves := (Residual.start (· ∈ obs) compiled live σ).mp (valid σ (memL.mp hσ))
      exact project_solves _ (read_model q solves)
    · intro ρ sol
      obtain ⟨V,model,values⟩ := extend_inventory p ρ.image sol
      have start := (Residual.start (· ∈ obs) compiled live _).mpr (reserve_solves q model obs live)
      have hs (i) (h : slot i ∈ obs) : (reserve obs V).image (slot i) = encode (V i) :=
        ite_eq_left ⟨h,rfl⟩
      rcases cover _ start with ⟨σ,hσ,δ,hδ⟩ | ⟨z,hz,linked⟩
      · refine .inl ⟨_,List.mem_map_of_mem (memL.mpr hσ),fun w => read (.var ∘ original) (δ.image w),?_⟩
        intro v hv
        apply (values _ (var_in_inventory hv)).trans
        let i := q.slot (.var v)
        have eq := read_equiv (s := s) (.var ∘ original) (hδ _ (observed _ (var_in_inventory hv)))
        change EquivB (read _ ((reserve obs V).image (slot i))) (read _ (δ.apply (σ.image (slot i)))) at eq
        rw [hs _ (observed _ (var_in_inventory hv)),read_encode,read_subst] at eq
        exact eq
      · have member := allowed z hz
        have both := (List.mem_filter.mp member).2
        simp only [Bool.and_eq_true,decide_eq_true_eq] at both
        have eq := read_equiv (s := s) (.var ∘ original) linked
        change EquivB (read _ ((reserve obs V).image (slot (q.slot z.1))))
          (read _ ((reserve obs V).image (slot (q.slot z.2)))) at eq
        rw [hs _ (observed _ both.1),hs _ (observed _ both.2),read_encode,read_encode] at eq
        exact .inr ⟨z,memR.mpr hz,(values _ both.1).trans (eq.trans (values _ both.2).symm)⟩

theorem branch_closed (p : Problem s) (candidates : List (SlotPair s)) (closed : ConstructorFrontier p) :
    ∃ stage, branch p candidates = some stage ∧ stage.reopen = [] := by
  let q := purify p
  let key (z : SlotPair s) := (slot (q.slot z.1),slot (q.slot z.2))
  let es := candidates.filter fun z => z.1 ∈ inventory p && z.2 ∈ inventory p
  obtain ⟨ans,hr,clean⟩ := ComponentSearch.analyze_closed (s := uniform s) key es
    (heads (s := s) q) (compiledProblem q) (observations p) closed
  have empty : (ans.filterMap Sum.getRight?).eraseDups = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    simpa [List.mem_filterMap,Sum.getRight?_eq_some_iff] using clean
  unfold branch
  dsimp only
  split
  next none =>
    change (ComponentSearch.analyze key es _ (compiledProblem q) _).val = _ at none
    rw [hr] at none; contradiction
  next as same =>
    change (ComponentSearch.analyze key es _ (compiledProblem q) _).val = _ at same
    rw [hr] at same; cases same
    exact ⟨_,rfl,empty⟩

end Tamarin.MixedUnification.ComponentEncoding
