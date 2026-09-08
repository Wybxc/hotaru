import HotaruKernel.TypeSupport
import HotaruKernel.SignatureExtension

namespace HotaruKernel

structure TypeModel.Agrees (s : Signature) (m n : TypeModel) : Prop where
  vars : ∀ k, m.typeVar k = n.typeVar k
  operators : ∀ name arity, s.typeOps.lookup name = some arity →
    ∀ args : List Type, args.length = arity → m.typeOp name args = n.typeOp name args

theorem TypeModel.Agrees.refl (s : Signature) (m : TypeModel) : Agrees s m m :=
  ⟨fun _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem TypeModel.Agrees.symm (h : Agrees s m n) : Agrees s n m :=
  ⟨fun k => (h.vars k).symm, fun name arity hd args ha =>
    (h.operators name arity hd args ha).symm⟩

theorem TypeModel.Agrees.trans (h : Agrees s m n) (k : Agrees s n o) : Agrees s m o :=
  ⟨fun x => (h.vars x).trans (k.vars x), fun name arity hd args ha =>
    (h.operators name arity hd args ha).trans (k.operators name arity hd args ha)⟩

theorem TypeModel.Agrees.interp (h : Agrees s m n) (a : HolType) :
    s.validType a = true → m.interp a = n.interp a := by
  induction a using HolType.rec
    (motive_2 := fun args => (∀ a ∈ args, s.validType a = true) →
      args.map m.interp = args.map n.interp) with
  | var k => exact fun _ => h.vars k
  | bool => exact fun _ => rfl
  | fn a b ha hb =>
    intro hv
    simp only [Signature.validType, Bool.and_eq_true] at hv
    obtain ⟨va, vb⟩ := hv
    change (m.interp a → m.interp b) = (n.interp a → n.interp b)
    rw [ha va, hb vb]
  | op name args ih =>
    intro hv
    obtain ⟨hd, hv⟩ := (Signature.validType_op_iff s name args).mp hv
    rw [TypeModel.interp_op, TypeModel.interp_op, ih hv]
    exact h.operators name args.length hd _ (List.length_map ..)
  | nil h => rfl
  | cons a args ha ih h =>
    exact congrArg₂ List.cons (ha (h a (List.mem_cons_self ..)))
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem TypeModel.Agrees.instantiate (h : Agrees s m n) (i : TypeSubst) (hi : i.Valid s) :
    Agrees s (m.instantiate i) (n.instantiate i) := by
  refine ⟨?_, h.operators⟩
  intro k
  exact h.interp _ (TypeSubst.valid_var i s hi k)

theorem HolType.valid_inst_variable (a : HolType) (i : TypeSubst) (s : Signature) :
    s.validType (a.inst i) = true →
      ∀ k ∈ a.vars, s.validType ((HolType.var k).inst i) = true := by
  induction a using HolType.rec
    (motive_2 := fun args => (∀ a ∈ args, s.validType (a.inst i) = true) →
      ∀ k ∈ HolType.varsArgs args, s.validType ((HolType.var k).inst i) = true) with
  | var k =>
    intro hv n hn
    have hn : n = k := List.mem_singleton.mp hn
    subst n
    exact hv
  | bool => intro _ k hk; cases hk
  | fn a b ha hb =>
    intro hv k hk
    simp only [HolType.inst, Signature.validType, Bool.and_eq_true] at hv
    rcases List.mem_append.mp hk with hk | hk
    · exact ha hv.1 k hk
    · exact hb hv.2 k hk
  | op name args ih =>
    intro hv
    have hv' := ((Signature.validType_op_iff s name (HolType.instArgs i args)).mp hv).2
    apply ih
    intro a ha
    apply hv'
    rw [HolType.instArgs_eq_map]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  | nil _ k hk => cases hk
  | cons a args ha ih hv k hk =>
    rcases List.mem_append.mp hk with hk | hk
    · exact ha (hv a (List.mem_cons_self ..)) k hk
    · exact ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) k hk

structure Model.Agrees (s : Signature) (m : Model s) (n : Model u) : Prop where
  types : TypeModel.Agrees s m.toTypeModel n.toTypeModel
  constants : ∀ name a (_hv : s.validType a = true)
    (hm : ∃ scheme i, s.constants.lookup name = some scheme ∧ scheme.inst i = a)
    (hn : ∃ scheme i, u.constants.lookup name = some scheme ∧ scheme.inst i = a),
    HEq (m.constant name a hm) (n.constant name a hn)

theorem Term.freeVar_valid {ctx : List HolType} (t : Term s ctx a)
    (name : String) (b : HolType) (hb : (name, b) ∈ t.freeVars) : s.validType b = true := by
  induction t with
  | fvar n a hv =>
    have he := List.mem_singleton.mp hb
    cases he
    exact hv
  | bvar => cases hb
  | const => cases hb
  | app _ _ ihf ihx | equal _ _ ihf ihx | imp _ _ ihf ihx =>
    rcases List.mem_append.mp hb with hb | hb
    · exact ihf hb
    · exact ihx hb
  | lam _ _ ih => exact ih hb

noncomputable def Model.Agrees.pullFree (h : Model.Agrees s m n) (g : FreeEnv n) : FreeEnv m :=
  fun a name => if hv : s.validType a = true then cast (h.types.interp a hv).symm (g a name)
    else Classical.choice (m.toTypeModel.interp_nonempty a)

theorem Model.Agrees.pullFree_heq (h : Model.Agrees s m n) (g : FreeEnv n)
    (a : HolType) (name : String) (hv : s.validType a = true) :
    HEq (h.pullFree g a name) (g a name) := by
  simp only [pullFree, hv, ↓reduceDIte]
  exact cast_heq _ _

theorem Term.eval_agrees {ctx : List HolType} (t : Term s ctx a)
    (h : s.Extends u) (m : Model s) (n : Model u) (hm : Model.Agrees s m n)
    (f : FreeEnv m) (g : FreeEnv n) (d : BoundEnv m ctx) (e : BoundEnv n ctx)
    (hc : ∀ a ∈ ctx, s.validType a = true)
    (hf : ∀ name a, (name, a) ∈ t.freeVars → HEq (f a name) (g a name))
    (he : ∀ a (v : BVar ctx a), HEq (d v) (e v)) :
    HEq (t.eval m f d) ((t.rebase h).eval n g e) := by
  induction t with
  | fvar name a valid => exact hf name a (List.mem_cons_self ..)
  | bvar v => exact he _ v
  | const name scheme i hd valid => exact hm.constants name _ valid _ _
  | @app a b ctx fn x ihf ihx =>
    apply ValueEquality.apply (hm.types.interp a (x.validType hc))
      (hm.types.interp b ((Term.app fn x).validType hc))
    · exact ihf d e hc (fun name a hn => hf name a (List.mem_append_left _ hn)) he
    · exact ihx d e hc (fun name a hn => hf name a (List.mem_append_right _ hn)) he
  | @lam a b ctx valid body ih =>
    have hctx : ∀ a' ∈ a :: ctx, s.validType a' = true := by
      intro a' h'
      rcases List.mem_cons.mp h' with rfl | h'
      · exact valid
      · exact hc a' h'
    apply ValueEquality.funext (hm.types.interp a valid)
      (hm.types.interp b (body.validType hctx))
    intro x y hxy
    apply ih (d.cons x) (e.cons y) hctx hf
    intro a v
    cases v with
    | zero => exact hxy
    | succ v => exact he _ v
  | @equal a ctx l r ihl ihr =>
    apply ValueEquality.decideEqual (hm.types.interp a (l.validType hc))
    · exact ihl d e hc (fun name a hn => hf name a (List.mem_append_left _ hn)) he
    · exact ihr d e hc (fun name a hn => hf name a (List.mem_append_right _ hn)) he
  | imp l r ihl ihr =>
    apply heq_of_eq
    apply congrArg₂ (fun a b : Bool => !a || b)
    · exact eq_of_heq (ihl d e hc (fun name a hn => hf name a (List.mem_append_left _ hn)) he)
    · exact eq_of_heq (ihr d e hc (fun name a hn => hf name a (List.mem_append_right _ hn)) he)

end HotaruKernel
