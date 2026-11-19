import Tamarin.DHSignedVariantFamily
import Tamarin.HomogeneousContract

/-! Public complete answers may use any order, parameter numbering or
generator algorithm. Decode the response and compare its relation directly
with the live signed DH normalization graph. -/
namespace Tamarin.SignedGraph
open Rewriting Rewriting.DHPeer Rewriting.DHPeer.SignedMatrix ACBasis
variable {n : Nat} {sig : Signature}
local instance : DecidableEq (Fin n → Bool) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext,congrFun⟩

abbrev Image := List Nat × List Nat
abbrev Arm (n : Nat) := Fin n → Image

def imageWords (a : Image) := a.1.length :: a.1 ++ a.2.length :: a.2

def represents (rows : List (Arm n)) (packet : Array UInt64) : Prop :=
  packet.toList.map UInt64.toNat =
    1 :: rows.length :: rows.flatMap (fun arm => (List.finRange n).flatMap fun i => imageWords (arm i))

def imageTerm (s : Symbols sig) (a : Image) : Term sig :=
  let var (j : Nat) : Variable := ⟨j,.msg⟩
  Balance.assemble s (side s.mul (a.1.map var)) (side s.mul (a.2.map var))

def spelling : SignedMatrix.Expr n → List Nat
  | .input i => [3+i.val]
  | .unit => [0]
  | .inv a => spelling a ++ [1]
  | .mul a b => spelling a ++ spelling b ++ [2]

inductive Aligned {α β : Type} (rel : α → β → Prop) : List α → List β → Prop where
  | nil : Aligned rel [] []
  | cons {a : α} {b : β} {xs ys} : rel a b → Aligned rel xs ys → Aligned rel (a::xs) (b::ys)

/-- Re-encode the syntax independently and check that each output has its
own coordinate, in caller order. An input opcode can never read an output. -/
def Source (m : Nat) (obs : Array (Array UInt64)) (qs : List (SignedMatrix.Expr (m+obs.size) × Fin (m+obs.size))) :=
  Aligned (fun (i : Fin obs.size) (p : SignedMatrix.Expr (m+obs.size) × Fin (m+obs.size)) =>
    p.2.val = m+i.val ∧ spelling p.1 = obs[i].toList.map UInt64.toNat ∧
      ∀ w ∈ spelling p.1, w < 3+m) (List.finRange obs.size) qs

private theorem decode_spelling (m k) (ws : Array UInt64) {e} (h : decode m k ws = some e) :
    spelling e = ws.toList.map UInt64.toNat ∧ ∀ w ∈ spelling e, w < 3+m := by
  let code (xs : List (SignedMatrix.Expr (m+k))) := xs.reverse.flatMap spelling
  have one (xs ys) (w : UInt64) (stepH : step m k xs w = some ys) :
      code ys = code xs ++ [w.toNat] ∧ w.toNat < 3+m := by
    unfold step at stepH
    split at stepH
    all_goals first | contradiction | skip
    all_goals try split at stepH
    all_goals first | contradiction | skip
    all_goals cases stepH
    all_goals constructor
    all_goals first | omega | (simp_all [code,spelling,List.flatMap_append,List.append_assoc,Nat.add_comm] <;> omega)
  have many (words : List UInt64) (xs ys) (h : words.foldlM (step m k) xs = some ys) :
      code ys = code xs ++ words.map UInt64.toNat ∧ ∀ w ∈ words, w.toNat < 3+m := by
    induction words generalizing xs with
    | nil => cases h; simp
    | cons w ws ih =>
      simp only [List.foldlM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨next,hs,ht⟩ := h
      obtain ⟨c,b⟩ := ih next ht
      obtain ⟨a,small⟩ := one _ _ _ hs
      exact ⟨by simp [c,a,List.append_assoc],fun v hv => (List.mem_cons.mp hv).elim (fun e => e ▸ small) (b v)⟩
  unfold decode at h
  simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨stack,hs,endH⟩ := h
  split at endH <;> try contradiction
  cases endH
  have ⟨eq,small⟩ := many _ _ _ hs
  simp [code] at eq
  refine ⟨eq,?_⟩
  rw [eq]
  rintro _ hit
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hit
  exact small w hw

private theorem graph_source (m : Nat) (obs : Array (Array UInt64)) {qs} (h : graph m obs = some qs) : Source m obs qs := by
  let read (i : Fin obs.size) := do
    let e ← decode m obs.size obs[i]
    return (e,(⟨m+i.val,by omega⟩ : Fin (m+obs.size)))
  have go (is : List (Fin obs.size)) {ps} (h : is.mapM read = some ps) :
      Aligned (fun (i : Fin obs.size) (p : SignedMatrix.Expr (m+obs.size) × Fin (m+obs.size)) =>
        p.2.val = m+i.val ∧ spelling p.1 = obs[i].toList.map UInt64.toNat ∧
        ∀ w ∈ spelling p.1, w < 3+m) is ps := by
    induction is generalizing ps with
    | nil => cases h; exact .nil
    | cons i is ih =>
      simp only [read,List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
      obtain ⟨_,⟨e,he,rfl⟩,tail,ht,rfl⟩ := h
      exact .cons ⟨rfl,decode_spelling m obs.size _ he⟩ (ih ht)
  exact go _ h

private theorem fold_spelling (m k : Nat) (e : SignedMatrix.Expr (m+k))
    (small : 3+m ≤ UInt64.size) (live : ∀ w ∈ spelling e, w < 3+m)
    (stack : List (SignedMatrix.Expr (m+k))) :
    ((spelling e).map Nat.toUInt64).foldlM (step m k) stack = some (e :: stack) := by
  induction e generalizing stack with
  | input i =>
    have h := live (3+i.val) List.mem_cons_self
    have ix : i.val < m := by omega
    have fit := UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le h small)
    have read : step m k stack (3+i.val).toUInt64 = some (.input i :: stack) := by
      unfold step
      rw [show (3+i.val).toUInt64.toNat = 3+i.val from fit,Nat.add_comm 3 i.val]
      simp [ix]
    simp only [spelling,List.map_cons,List.map_nil,List.foldlM_cons,read,Option.bind_eq_bind,Option.bind_some,List.foldlM_nil,Option.pure_def]
  | unit => rfl
  | inv a ih =>
    have ha := ih (fun w hw => live w (by simp [spelling,hw])) stack
    simp only [spelling,List.map_append,List.foldlM_append,ha]
    rfl
  | mul a b left right =>
    have ha := left (fun w hw => live w (by simp [spelling,hw])) stack
    have hb := right (fun w hw => live w (by simp [spelling,hw])) (a :: stack)
    simp only [spelling,List.map_append,List.foldlM_append,ha,Option.bind_eq_bind,Option.bind_some,hb]
    rfl

private theorem source_graph (m : Nat) (obs : Array (Array UInt64)) {qs} (small : 3+m ≤ UInt64.size)
    (h : Source m obs qs) : graph m obs = some qs := by
  unfold Source at h
  unfold graph
  generalize List.finRange obs.size = is at h ⊢
  induction h with
  | nil => rfl
  | @cons i p _ _ head _ ih =>
    obtain ⟨slot,code,live⟩ := head
    obtain ⟨e,j⟩ := p
    have he := fold_spelling m obs.size e small live []
    rw [code,List.map_map] at he
    simp only [Function.comp_def,Nat.toUInt64,UInt64.ofNat_toNat] at he
    change (obs[i].toList.map id).foldlM _ _ = _ at he
    rw [List.map_id] at he
    have parse : decode m obs.size obs[i] = some e := by unfold decode; rw [he]; rfl
    simp only [Option.bind_eq_bind,Option.pure_def] at ih
    simp only [List.mapM_cons,Option.bind_eq_bind,parse,Option.bind_some,Option.pure_def,ih]
    have eq : (⟨m+i.val,by omega⟩ : Fin (m+obs.size)) = j := Fin.ext slot.symm
    rw [eq]

def Correct (solve : UInt64 → Array (Array UInt64) → Array UInt64) : Prop :=
  ∀ inputs obs, solve inputs obs = #[0] ∨
    ∃ qs, Source inputs.toNat obs qs ∧ ∃ rows, represents rows (solve inputs obs) ∧
      ∀ {sig : Signature} [DecidableEq sig.ACSym] {s : Symbols sig} {T : Table s} {E : ExtraTable T},
      Balance.Inventory E → MulBucket E → InverseBucket E → Normal (ruleRoot T.rules) s.product.one →
      (∀ r ∈ rows, ∀ i, HasSort (imageTerm s (r i)) .msg ∧ Normal (ruleRoot T.rules) (imageTerm s (r i))) ∧
      ∀ env, (∀ i, HasSort (env i) .msg) → (∀ i, Normal (ruleRoot T.rules) (env i)) →
        ((∀ p ∈ qs, NormalForm (ruleRoot T.rules) (p.1.term s env) (env p.2)) ↔
          ∃ r ∈ rows, ∃ δ : Substitution sig, Normalized (ruleRoot T.rules) δ ∧
            ∀ i, EquivB (env i) (δ.apply (imageTerm s (r i))))

private theorem table_correct {qs : List (SignedMatrix.Expr n × Fin n)} {bs} (h : table qs = some bs) (d) :
    (bs.lookup d).getD [] = graphBasis qs d := by
  let f (d : Fin n → Bool) := do
    let gs ← Homogeneous.boundedBasis (qs.map fun (p : SignedMatrix.Expr n × Fin n) => row d (p.1,.input p.2))
    return (d,gs)
  have same (ds : List (Fin n → Bool)) {ls} (hd : ds.mapM f = some ls) :
      ls = ds.map (fun d => (d,graphBasis qs d)) := by
    induction ds generalizing ls with
    | nil => simpa using hd.symm
    | cons a ds ih =>
      simp only [List.mapM_cons,f,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
        Option.some.injEq] at hd
      obtain ⟨u,⟨gs,hg,rfl⟩,ts,ht,rfl⟩ := hd
      rw [ih ht]
      simp [graphBasis,(Homogeneous.bounded_spec _).1 _ hg]
  have lookup (ds : List (Fin n → Bool)) (mem : d ∈ ds) :
      ((ds.map (fun d => (d,graphBasis qs d))).lookup d).getD [] = graphBasis qs d := by
    induction ds with
    | nil => contradiction
    | cons a ds ih =>
      by_cases ha : a = d
      · subst a; simp
      · have miss : (d == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm ha)
        simp [List.lookup_cons,miss,ih ((List.mem_cons.mp mem).resolve_left (Ne.symm ha))]
  rw [same _ h]
  exact lookup _ (mem_profiles d)

private def layout (basis : (Fin n → Bool) → List (Vec n)) (active : List (Column basis)) : Arm n :=
  fun i => ((slots basis active i false).map (columns basis).idxOf,
            (slots basis active i true).map (columns basis).idxOf)

private theorem term_layout (s : Symbols sig) (basis : (Fin n → Bool) → List (Vec n))
    (active) (i : Fin n) :
    imageTerm s (layout basis active i) = template s basis active (param basis) i := by
  simp only [imageTerm,layout,template,List.map_map,Function.comp_def]
  rfl

private theorem encode_eq (basis : (Fin n → Bool) → List (Vec n)) (arm : List (Column basis)) :
    encode basis (columns basis) arm = (List.finRange n).flatMap fun i => imageWords (layout basis arm i) := by
  unfold encode imageWords layout
  simp only [List.length_map]

private theorem packet_correct {basis : (Fin n → Bool) → List (Vec n)} {out} (h : packet basis = some out) :
    represents ((FlatMatchSearch.sublists (columns basis)).map (layout basis)) out := by
  simp only [packet, Option.bind_eq_bind,Option.bind_eq_some_iff,guard,Option.pure_def,Option.some.injEq] at h
  obtain ⟨_,_,_,_,_,fits,rfl⟩ := h
  let arms := FlatMatchSearch.sublists (columns basis)
  let words := 1 :: arms.length :: arms.flatMap (encode basis (columns basis))
  have fit : ∀ w ∈ words, w < UInt64.size := by
    split at fits
    · next h => exact fun w hw => of_decide_eq_true (List.all_eq_true.mp h w hw)
    · contradiction
  have round : (words.map Nat.toUInt64).map UInt64.toNat = words := by
    rw [List.map_map]
    calc
      _ = words.map id := List.map_congr_left fun w hw => UInt64.toNat_ofNat_of_lt' (fit w hw)
      _ = words := List.map_id _
  unfold represents
  simp only [List.length_map,List.flatMap_map]
  have eq := funext (encode_eq basis)
  exact round.trans (by unfold words; rw [eq])

theorem run_correct : Correct run := by
  intro inputs obs
  cases h : candidate inputs obs with
  | none => exact .inl (by simp [run,h])
  | some out =>
    apply Or.inr
    simp only [candidate,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨_,size,qs,hq,bs,hb,hp⟩ := h
    let basis := fun d => (bs.lookup d).getD []
    let arms := FlatMatchSearch.sublists (columns basis)
    refine ⟨qs,graph_source _ _ hq,arms.map (layout basis),?_,?_⟩
    · have hh : candidate inputs obs = some out := by
        simp only [candidate,Option.bind_eq_bind,Option.bind_eq_some_iff]
        exact ⟨_,size,qs,hq,bs,hb,hp⟩
      simpa [run,hh] using packet_correct hp
    · intro sig _ s T E inventory mul inv unit
      have ok d : BasisCorrect (qs.map fun p => row d (p.1,.input p.2)) (basis d) := by
        rw [show basis d = graphBasis qs d from table_correct hb d]
        exact generate_correct _
      constructor
      · intro r hr i
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hr
        rw [term_layout]
        exact template_normal mul inv unit basis a (param basis) (param_injective _) (fun _ => rfl) i
      · intro env typed norm
        rw [exact_graph inventory mul inv unit qs basis ok (param basis) (param_injective _) (fun _ => rfl) env typed norm]
        constructor
        · rintro ⟨a,ha,δ,hn,fit⟩
          exact ⟨_,List.mem_map_of_mem (f := layout basis) ha,δ,hn,fun i => term_layout s basis a i ▸ fit i⟩
        · rintro ⟨r,hr,δ,hn,fit⟩
          obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
          exact ⟨a,ha,δ,hn,fun i => (term_layout s basis a i) ▸ fit i⟩

/-- A candidate must finish every parsed request within the bounded matrix
and packet envelopes. The dimensions are properties of the reference bases;
candidates may also support larger matrices and other compact encodings of
the same family of answers within the response format. -/
def Within (inputs : UInt64) (obs : Array (Array UInt64)) : Prop :=
  inputs.toNat + obs.size ≤ 8 ∧ obs.size > 0 ∧ (∀ p ∈ obs, p.size ≤ 256) ∧
  ∃ qs, Source inputs.toNat obs qs ∧
    (∀ d, Homogeneous.Within (qs.map fun p => row d (p.1,.input p.2))) ∧
    let basis := graphBasis qs
    let cs := columns basis
    let selections := FlatMatchSearch.sublists cs
    cs.length ≤ 12 ∧ 2 + 2 ^ cs.length * (2 * (inputs.toNat + obs.size) +
        (cs.map fun g => total ((basis g.1).get g.2)).sum) ≤ 65536 ∧
      ∀ w ∈ (1 :: selections.length :: selections.flatMap fun a =>
        (List.finRange _).flatMap fun i => imageWords (layout basis a i)), w < UInt64.size

def Total (solve : UInt64 → Array (Array UInt64) → Array UInt64) : Prop :=
  ∀ m obs, Within m obs → solve m obs ≠ #[0]

theorem run_total : Total run := by
  rintro m obs ⟨width,nonempty,codeSize,qs,src,bases,columnsCap,wordsCap,fit⟩
  have hq := source_graph _ _ (by change 3+m.toNat ≤ 2^64; omega) src
  rw [← funext (encode_eq (graphBasis qs))] at fit
  let basis := graphBasis qs
  let store := (profiles (m.toNat + obs.size)).map fun d => (d,basis d)
  have ht : table qs = some store := by
    unfold table store
    generalize profiles (m.toNat + obs.size) = ds
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq]
      exact ⟨_,⟨_,(Homogeneous.bounded_spec _).2 (bases d),rfl⟩,_,ih,rfl⟩
  have lookup : (fun d => (store.lookup d).getD []) = basis := funext (table_correct ht)
  have result : candidate m obs = some ((1 :: (FlatMatchSearch.sublists (columns basis)).length ::
      (FlatMatchSearch.sublists (columns basis)).flatMap (encode basis (columns basis))).map Nat.toUInt64).toArray := by
    have programs : (obs.all fun p => p.size ≤ 256) = true := Array.all_eq_true.mpr fun p h => decide_eq_true (codeSize obs[p] (Array.getElem_mem h))
    simp only [candidate,Option.bind_eq_bind,Option.bind_eq_some_iff]
    refine ⟨(),by simp [guard,width,nonempty,programs],qs,hq,store,ht,?_⟩
    rw [lookup]
    have fits := List.all_eq_true.mpr (fun w hw => decide_eq_true (fit w hw))
    simp only [packet,Option.bind_eq_bind,Option.bind_eq_some_iff]
    exact ⟨(),by simp [guard,basis,columnsCap],(),by simp only [basis,guard,ite_eq_left wordsCap,Option.pure_def],
      (),by simp only [guard,basis,fits,ite_true,Option.pure_def],rfl⟩
  rw [run,result]
  intro eq
  have first := congrArg (fun a : Array UInt64 => a[0]?) eq
  simp at first

end Tamarin.SignedGraph
