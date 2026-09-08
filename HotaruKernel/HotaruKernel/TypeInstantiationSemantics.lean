import HotaruKernel.PolymorphicModel

namespace HotaruKernel

private theorem apply_heq {A B C D : Type} (ha : A = C) (hb : B = D)
    {f : A → B} {g : C → D} {x : A} {y : C}
    (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  cases ha
  cases hb
  cases eq_of_heq hf
  cases eq_of_heq hx
  rfl

private theorem funext_heq {A B C D : Type} (ha : A = C) (hb : B = D)
    {f : A → B} {g : C → D}
    (h : ∀ x y, HEq x y → HEq (f x) (g y)) : HEq f g := by
  cases ha
  cases hb
  apply heq_of_eq
  funext x
  exact eq_of_heq (h x x HEq.rfl)

private theorem decide_equal_heq {A B : Type} (ha : A = B)
    {l r : A} {u v : B} (hl : HEq l u) (hr : HEq r v) :
    HEq (@decide (l = r) (Classical.propDecidable _))
      (@decide (u = v) (Classical.propDecidable _)) := by
  cases ha
  cases eq_of_heq hl
  cases eq_of_heq hr
  rfl

theorem Term.eval_cast {ctx : List HolType} (h : a = b) (t : Term s ctx a)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    HEq ((cast (congrArg (Term s ctx) h) t).eval m f e) (t.eval m f e) := by
  cases h
  rfl

theorem Term.eval_instType {ctx : List HolType} (t : Term s ctx a)
    (i : TypeSubst) (hi : i.Valid s) (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m hm)) (g : FreeEnv (p.atTypes (m.instantiate i) hm))
    (d : BoundEnv (p.atTypes m hm) (ctx.map (HolType.inst i)))
    (e : BoundEnv (p.atTypes (m.instantiate i) hm) ctx)
    (hf : ∀ a n, HEq (f (a.inst i) n) (g a n))
    (he : ∀ a (v : BVar ctx a), HEq (d (v.instType i)) (e v)) :
    HEq ((t.instType i hi).eval (p.atTypes m hm) f d)
      (t.eval (p.atTypes (m.instantiate i) hm) g e) := by
  induction t with
  | fvar n a _ => exact hf a n
  | bvar v => exact he _ v
  | const n scheme j hd hv =>
    apply (Term.eval_cast (HolType.inst_compose scheme j i).symm _ _ _ _).trans
    change HEq ((p.atTypes m hm).constant n (scheme.inst (j.compose i)) _)
      ((p.atTypes (m.instantiate i) hm).constant n (scheme.inst j) _)
    rw [p.atTypes_constant, p.atTypes_constant]
    exact p.instanceValue_instantiate m hm n scheme hd j i
  | @app a b ctx f' x ihf ihx =>
    exact apply_heq (m.interp_instantiate i a).symm (m.interp_instantiate i b).symm
      (ihf d e he) (ihx d e he)
  | @lam a b ctx valid body ih =>
    apply funext_heq (m.interp_instantiate i a).symm (m.interp_instantiate i b).symm
    intro x y hxy
    apply ih (d.cons x) (e.cons y)
    intro a v
    cases v with
    | zero => exact hxy
    | succ v => exact he _ v
  | @equal a ctx l r ihl ihr =>
    exact decide_equal_heq (m.interp_instantiate i a).symm (ihl d e he) (ihr d e he)
  | imp l r ihl ihr =>
    apply heq_of_eq
    exact congrArg₂ (fun a b : Bool => !a || b) (eq_of_heq (ihl d e he))
      (eq_of_heq (ihr d e he))

noncomputable def FreeEnv.instType (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) (i : TypeSubst)
    (f : FreeEnv (p.atTypes m hm)) : FreeEnv (p.atTypes (m.instantiate i) hm) :=
  fun a n => cast (m.interp_instantiate i a).symm (f (a.inst i) n)

theorem Formula.eval_instType (t : Formula s) (i : TypeSubst) (hi : i.Valid s)
    (p : PolymorphicModel s) (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m hm)) :
    (t.instType i hi).eval (p.atTypes m hm) f BoundEnv.nil =
      t.eval (p.atTypes (m.instantiate i) hm) (f.instType p m hm i) BoundEnv.nil := by
  apply eq_of_heq
  apply Term.eval_instType t i hi p m hm f (f.instType p m hm i) BoundEnv.nil BoundEnv.nil
  · intro a n
    exact (cast_heq _ _).symm
  · intro a v
    cases v

end HotaruKernel
