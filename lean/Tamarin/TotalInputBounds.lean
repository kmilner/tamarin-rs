import Tamarin.TotalUnifyPacket
import Tamarin.TableWire

/-! The shared graph contains only machine-word variable IDs and arities. -/
namespace Tamarin.TotalUnifyWire
open Whole Packet

private theorem decl_widths (xs : List UInt64) {ds : List Decl} (h : declarations xs = some ds) :
    ∀ a ∈ ds, a.inputs.length < UInt64.size := by
  induction xs using declarations.induct generalizing ds with
  | case1 => simp [declarations] at h; subst ds; simp
  | case2 k id ar out rest ih =>
    simp only [declarations,guard,Bind.bind,Option.bind] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    cases ht : declarations (rest.drop ar.toNat) with
    | none => simp [ht] at h
    | some tail =>
      simp only [ht] at h
      split at h <;> try contradiction
      cases h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Nat.lt_of_le_of_lt (List.length_take_le ..) ar.toNat_lt_size
      · exact ih ht a ha
  | case3 xs empty short =>
    cases xs with
    | nil => contradiction
    | cons a xs =>
      cases xs with
      | nil => simp [declarations] at h
      | cons b xs =>
        cases xs with
        | nil => simp [declarations] at h
        | cons c xs =>
          cases xs with
          | nil => simp [declarations] at h
          | cons d xs => exact (short a b c d xs rfl).elim

private theorem fold_fits {d : Dictionary} (f : d.sig.ACSym) (t : Term d.sig) (ts : List (Term d.sig))
    (h : FieldsFit t) (hs : ∀ a ∈ ts, FieldsFit a) : FieldsFit (ACRepresentation.fold f t ts) := by
  induction ts generalizing t with
  | nil => exact h
  | cons a as ih => exact ⟨h,ih a (hs _ List.mem_cons_self) (fun b hb => hs b (.tail _ hb))⟩

private theorem app_fits (d : Dictionary) (width : ∀ f, d.sig.arity f < UInt64.size)
    (k id) (children : List (Term d.sig)) (t) (ok : app d k id children = some t)
    (bounded : ∀ a ∈ children, FieldsFit a) : FieldsFit t := by
  unfold app at ok
  split at ok
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
    obtain ⟨f,_,h⟩ := ok
    split at h <;> try contradiction
    cases h
    exact ⟨width f,fun i => bounded _ (List.get_mem ..)⟩
  · split at ok
    · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
      obtain ⟨_,_,h⟩ := ok
      split at h <;> try contradiction
      cases h
      exact ⟨bounded _ (by simp),bounded _ (by simp)⟩
    · split at ok
      · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at ok
        obtain ⟨_,_,h⟩ := ok
        split at h <;> try contradiction
        cases h
        exact ⟨bounded _ (by simp),fold_fits _ _ _ (bounded _ (by simp)) (fun a ha => bounded a (by simp [ha]))⟩
      · contradiction

theorem children_fits {α β : Type} (P : β → Prop) (f : α → Option β)
    (each : ∀ a b, f a = some b → P b) (xs : List α) (ys : List β) (h : xs.mapM f = some ys) :
    ∀ b ∈ ys, P b := by
  induction xs generalizing ys with
  | nil => cases h; simp
  | cons x xs ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨y,hy,tail,ht,rfl⟩ := h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact each _ _ hy
    · exact ih _ ht b hb

private theorem node_fits (d : Dictionary) (width : ∀ f, d.sig.arity f < UInt64.size)
    (prior : Array (Term d.sig)) (row) (t) (h : node d prior row = some t)
    (bounded : ∀ a ∈ prior, FieldsFit a) : FieldsFit t := by
  unfold node at h
  split at h <;> try contradiction
  split at h
  · split at h <;> try contradiction
    unfold leaf at h
    simp only [guard,Bind.bind,Option.bind] at h
    split at h <;> try contradiction
    split at h
    · cases h; exact UInt64.toNat_lt_size _
    · split at h <;> try contradiction
      split at h <;> try contradiction
      cases h
      trivial
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨cs,hc,ht⟩ := h
    exact app_fits _ width _ _ _ _ ht (children_fits _ _ (fun _ _ h => bounded _ (Array.mem_of_getElem? h)) _ _ hc)

private theorem graph_fits (d : Dictionary) (width : ∀ f, d.sig.arity f < UInt64.size)
    (rows : Array (Array UInt64)) (init result : Array (Term d.sig)) (hi : ∀ a ∈ init, FieldsFit a)
    (h : rows.foldlM (fun acc r => do return acc.push (← node d acc r)) init = some result) :
    ∀ a ∈ result, FieldsFit a := by
  rw [← Array.foldlM_toList] at h
  generalize rows.toList = xs at h
  induction xs generalizing init with
  | nil => cases h; exact hi
  | cons r rs ih =>
    simp only [List.foldlM_cons,Option.bind_eq_bind,Option.bind_assoc,Option.bind_eq_some_iff] at h
    obtain ⟨t,ht,a,ha,tail⟩ := h
    cases ha
    apply ih _ (h := tail)
    intro a ha
    rcases Array.mem_push.mp ha with old | rfl
    · exact hi a old
    · exact node_fits _ width _ _ _ ht hi

private theorem roots_fit {d : Dictionary} (terms : Array (Term d.sig)) (h : ∀ a ∈ terms, FieldsFit a)
    (xs : List UInt64) (p) (hp : equations terms xs = some p) :
    ∀ e ∈ p, FieldsFit e.lhs ∧ FieldsFit e.rhs := by
  induction xs using equations.induct generalizing p with
  | case1 => cases hp; simp
  | case3 => contradiction
  | case2 a b xs ih =>
    simp only [equations,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at hp
    obtain ⟨l,hl,r,hr,rest,ht,rfl⟩ := hp
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨h _ (Array.mem_of_getElem? hl),h _ (Array.mem_of_getElem? hr)⟩
    · exact ih _ ht e he

theorem Packet.var_fits {d : Dictionary} (t : Term d.sig) (v : Variable) (h : t.Occurs v) (bounded : FieldsFit t) :
    v.id < UInt64.size := by
  induction t with
  | var w => exact h ▸ bounded
  | atom => contradiction
  | free _ _ ih => obtain ⟨i,hi⟩ := h; exact ih i hi (bounded.2 i)
  | ac _ _ _ ih ik | comm _ _ _ ih ik =>
    exact h.elim (fun hl => ih hl bounded.1) (fun hr => ik hr bounded.2)

theorem graph_widths {ds ns d ts} (decoded : graph ds ns = some ⟨d,ts⟩) :
    ∀ f, d.sig.arity f < UInt64.size := by
  simp only [graph,Option.bind_eq_bind,Option.bind_eq_some_iff] at decoded
  obtain ⟨decls,hd,terms,_,eq⟩ := decoded
  cases eq
  intro f
  apply decl_widths _ hd (info f)
  exact List.mem_of_find?_eq_some (Option.some_get f.property).symm

theorem graph_fieldsFit {ds ns d ts} (decoded : graph ds ns = some ⟨d,ts⟩) :
    ∀ t ∈ ts, FieldsFit t := by
  have widths := graph_widths decoded
  simp only [graph,Option.bind_eq_bind,Option.bind_eq_some_iff] at decoded
  obtain ⟨_,_,_,ht,eq⟩ := decoded
  cases eq
  exact graph_fits _ widths _ _ _ (by simp) ht

theorem input_fieldsFit {ds ns es d p} (decoded : input ds ns es = some ⟨d,p⟩) :
    ∀ e ∈ p, FieldsFit e.lhs ∧ FieldsFit e.rhs := by
  simp only [input,Option.bind_eq_bind,Option.bind_eq_some_iff] at decoded
  obtain ⟨⟨_,terms⟩,hd,problem,hp,eq⟩ := decoded
  cases eq
  exact roots_fit terms (graph_fieldsFit hd) _ _ hp

end Tamarin.TotalUnifyWire

namespace Tamarin.TableWire
open TotalUnifyWire TotalUnifyWire.Packet

/-- Every selected root comes from the graph's bounded dictionary and IDs. -/
theorem input_fits {ds ns es roots d rs q}
    (decoded : input ds ns es roots = some ⟨d,rs,q⟩) :
    (∀ f, d.sig.arity f < UInt64.size) ∧ ∀ t ∈ q, FieldsFit t := by
  simp only [input,Option.bind_eq_bind,Option.bind_eq_some_iff] at decoded
  obtain ⟨⟨_,ts⟩,dg,_,_,_,ho,eq⟩ := decoded
  cases eq
  exact ⟨graph_widths dg,children_fits _ _ (fun _ _ h =>
    graph_fieldsFit dg _ (Array.mem_of_getElem? h)) _ _ ho⟩

end Tamarin.TableWire
