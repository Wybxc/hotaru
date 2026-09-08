import HotaruKernel.Check
import HotaruKernel.Semantics

namespace HotaruKernel

theorem HolType.instArgs_eq_map (s : TypeSubst) (args : List HolType) :
    HolType.instArgs s args = args.map (HolType.inst s) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [instArgs, List.map_cons, ih]

def TypeSubst.compose (s t : TypeSubst) : TypeSubst :=
  s.map (fun (n, a) => (n, a.inst t)) ++ t

theorem TypeSubst.var_compose (s t : TypeSubst) (n : String) :
    ((HolType.var n).inst s).inst t = (HolType.var n).inst (s.compose t) := by
  induction s with
  | nil => rfl
  | cons entry s ih =>
    obtain ⟨k, a⟩ := entry
    by_cases h : n = k
    · subst k
      simp [HolType.inst, compose]
    · have hn : (n == k) = false := beq_eq_false_iff_ne.mpr h
      simpa [HolType.inst, compose, List.lookup_cons, hn] using ih

theorem HolType.inst_compose (a : HolType) (s t : TypeSubst) :
    (a.inst s).inst t = a.inst (s.compose t) := by
  induction a using HolType.rec
    (motive_2 := fun args => HolType.instArgs t (HolType.instArgs s args) =
      HolType.instArgs (s.compose t) args) with
  | var n => exact s.var_compose t n
  | bool => rfl
  | fn a b ha hb => simp only [inst, ha, hb]
  | op n args ih => simp only [inst, ih]
  | nil => rfl
  | cons a args ha ih => simp only [instArgs, ha, ih]

theorem HolType.inst_nil (a : HolType) : a.inst [] = a := by
  induction a using HolType.rec
    (motive_2 := fun args => HolType.instArgs [] args = args) with
  | var n => rfl
  | bool => rfl
  | fn a b ha hb => simp only [inst, ha, hb]
  | op n args ih => simp only [inst, ih]
  | nil => rfl
  | cons a args ha ih => simp only [instArgs, ha, ih]

def TypeSubst.Valid (s : TypeSubst) (sig : Signature) : Prop :=
  ∀ entry ∈ s, sig.validType entry.2 = true

instance {sig : Signature} : Decidable (TypeSubst.Valid s sig) :=
  inferInstanceAs (Decidable (∀ entry ∈ s, sig.validType entry.2 = true))

theorem TypeSubst.valid_var (s : TypeSubst) (sig : Signature) (h : s.Valid sig) (n : String) :
    sig.validType ((HolType.var n).inst s) = true := by
  induction s with
  | nil => simp [HolType.inst, Signature.validType]
  | cons entry s ih =>
    obtain ⟨k, a⟩ := entry
    have ha := h (k, a) (List.mem_cons_self ..)
    have hs := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    by_cases hn : n = k
    · subst k
      simpa [HolType.inst, List.lookup_cons] using ha
    · have he : (n == k) = false := beq_eq_false_iff_ne.mpr hn
      simpa [HolType.inst, List.lookup_cons, he] using hs

theorem Signature.validType_op_iff (s : Signature) (n : QName) (args : List HolType) :
    s.validType (.op n args) = true ↔
      s.typeOps.lookup n = some args.length ∧ ∀ a ∈ args, s.validType a = true := by
  simp [Signature.validType]

theorem Signature.validType_inst (sig : Signature) (s : TypeSubst) (hs : s.Valid sig)
    (a : HolType) : sig.validType a = true → sig.validType (a.inst s) = true := by
  induction a using HolType.rec
    (motive_2 := fun args => ∀ a ∈ args, sig.validType a = true →
      sig.validType (a.inst s) = true) with
  | var n => exact fun _ => s.valid_var sig hs n
  | bool => exact fun h => h
  | fn a b ha hb =>
    simp only [HolType.inst, Signature.validType, Bool.and_eq_true]
    exact fun ⟨h₁, h₂⟩ => ⟨ha h₁, hb h₂⟩
  | op n args ih =>
    intro h
    rw [validType_op_iff] at h
    rw [HolType.inst, HolType.instArgs_eq_map, validType_op_iff]
    refine ⟨by simpa using h.1, ?_⟩
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ih b hb (h.2 b hb)
  | nil a h => cases h
  | cons a args ha ih b hb hv =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha hv
    · exact ih b hb hv

noncomputable def TypeModel.instantiate (m : TypeModel) (s : TypeSubst) : TypeModel where
  typeVar n := m.interp ((HolType.var n).inst s)
  typeOp := m.typeOp
  var_nonempty _ := m.interp_nonempty _
  op_nonempty := m.op_nonempty

theorem TypeModel.interp_instantiate (m : TypeModel) (s : TypeSubst) (a : HolType) :
    (m.instantiate s).interp a = m.interp (a.inst s) := by
  induction a using HolType.rec
    (motive_2 := fun args => args.map (m.instantiate s).interp =
      args.map (fun a => m.interp (a.inst s))) with
  | var n => rfl
  | bool => rfl
  | fn a b ha hb =>
    change ((m.instantiate s).interp a → (m.instantiate s).interp b) =
      (m.interp (a.inst s) → m.interp (b.inst s))
    rw [ha, hb]
  | op n args ih =>
    rw [interp_op, HolType.inst, interp_op, HolType.instArgs_eq_map, List.map_map]
    exact congrArg (m.typeOp n) ih
  | nil => rfl
  | cons a args ha ih => simp only [List.map_cons, ha, ih]

def BVar.instType {ctx : List HolType} (s : TypeSubst) :
    BVar ctx a → BVar (ctx.map (HolType.inst s)) (a.inst s)
  | .zero => .zero
  | .succ v => .succ (v.instType s)

theorem BVar.index_instType {ctx : List HolType} (s : TypeSubst) (v : BVar ctx a) :
    (v.instType s).index = v.index := by
  induction v with
  | zero => rfl
  | succ v ih => simp [instType, index, ih]

def RawTerm.instType (s : TypeSubst) : RawTerm → RawTerm
  | .fvar n a => .fvar n (a.inst s)
  | .bvar i => .bvar i
  | .const n i => .const n (i.compose s)
  | .app f x => .app (f.instType s) (x.instType s)
  | .lam a b => .lam (a.inst s) (b.instType s)
  | .equal l r => .equal (l.instType s) (r.instType s)
  | .imp p q => .imp (p.instType s) (q.instType s)

def Term.instType {ctx : List HolType} (i : TypeSubst) (hi : i.Valid s) :
    Term s ctx a → Term s (ctx.map (HolType.inst i)) (a.inst i)
  | .fvar n a h => .fvar n (a.inst i) (s.validType_inst i hi a h)
  | .bvar v => .bvar (v.instType i)
  | .const n scheme j hd hv =>
      have valid : s.validType (scheme.inst (j.compose i)) = true := by
        rw [← HolType.inst_compose]
        exact s.validType_inst i hi _ hv
      cast (congrArg (Term s (ctx.map (HolType.inst i)))
        (HolType.inst_compose scheme j i).symm) (.const n scheme (j.compose i) hd valid)
  | .app f x => .app (f.instType i hi) (x.instType i hi)
  | .lam h b => .lam (s.validType_inst i hi _ h) (b.instType i hi)
  | .equal l r => .equal (l.instType i hi) (r.instType i hi)
  | .imp p q => .imp (p.instType i hi) (q.instType i hi)

theorem Term.raw_cast {ctx : List HolType} (h : a = b) (t : Term s ctx a) :
    (cast (congrArg (Term s ctx) h) t).raw = t.raw := by cases h; rfl

theorem Term.raw_instType {ctx : List HolType} (t : Term s ctx a)
    (i : TypeSubst) (hi : i.Valid s) : (t.instType i hi).raw = t.raw.instType i := by
  induction t with
  | fvar => rfl
  | bvar v => simp [instType, raw, RawTerm.instType, BVar.index_instType]
  | const n scheme j hd hv => exact raw_cast (HolType.inst_compose scheme j i).symm _
  | app f x hf hx => exact congrArg₂ RawTerm.app hf hx
  | lam h b hb => exact congrArg (RawTerm.lam _) hb
  | equal l r hl hr => exact congrArg₂ RawTerm.equal hl hr
  | imp p q hp hq => exact congrArg₂ RawTerm.imp hp hq

theorem instType_preserves_type {ctx : List HolType} (t : Term s ctx a)
    (i : TypeSubst) (hi : i.Valid s) :
    HasType s (ctx.map (HolType.inst i)) (t.raw.instType i) (a.inst i) := by
  rw [← t.raw_instType i hi]
  exact (t.instType i hi).hasType

def instantiateTermChecked (s : Signature) (i : TypeSubst) (r : RawTerm) :
    Except KernelError (Checked s [] (r.instType i)) := do
  if hi : i.Valid s then
    let c ← check s [] r
    return ⟨c.type.inst i, c.term.instType i hi,
      (c.term.raw_instType i hi).trans (congrArg (RawTerm.instType i) c.erases)⟩
  else .error .invalidType

end HotaruKernel
