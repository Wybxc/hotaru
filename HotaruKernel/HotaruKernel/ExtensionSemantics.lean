import HotaruKernel.SignatureExtension
import HotaruKernel.PolymorphicModel

namespace HotaruKernel

variable {s u : Signature}

def Model.restrict (m : Model u) (h : s.Extends u) : Model s where
  toTypeModel := m.toTypeModel
  constant n a ha := m.constant n a (by
    obtain ⟨scheme, i, hd, hi⟩ := ha
    exact ⟨scheme, i, h.constants n scheme hd, hi⟩)

theorem Term.eval_rebase {ctx : List HolType} (t : Term s ctx a) (h : s.Extends u)
    (m : Model u) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (t.rebase h).eval m f e = t.eval (m.restrict h) f e := by
  induction t with
  | fvar => rfl
  | bvar => rfl
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ (fun f x => f x) (ihf e) (ihx e)
  | lam hv b ih => funext x; exact ih (e.cons x)
  | equal l r ihl ihr =>
    change @decide _ (Classical.propDecidable _) = @decide _ (Classical.propDecidable _)
    rw [ihl e, ihr e]
    rfl
  | imp p q ihp ihq => exact congrArg₂ (fun p q : Bool => !p || q) (ihp e) (ihq e)

def PolymorphicModel.restrict (p : PolymorphicModel u) (h : s.Extends u) :
    PolymorphicModel s where
  typeOp := p.typeOp
  op_nonempty := p.op_nonempty
  constant n a ha m hm := p.constant n a (h.constants n a ha) m hm
  constant_support n a ha m₁ m₂ h₁ h₂ hv :=
    p.constant_support n a (h.constants n a ha) m₁ m₂ h₁ h₂ hv

theorem PolymorphicModel.restrict_instanceValue (p : PolymorphicModel u)
    (h : s.Extends u) (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (n : QName) (scheme : HolType) (hd : s.constants.lookup n = some scheme)
    (i : TypeSubst) :
    (p.restrict h).instanceValue m hm n scheme hd i =
      p.instanceValue m hm n scheme (h.constants n scheme hd) i := rfl

theorem PolymorphicModel.restrict_atTypes (p : PolymorphicModel u) (h : s.Extends u)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) :
    (p.restrict h).atTypes m hm = (p.atTypes m hm).restrict h := by
  have hc : ∀ n a ha,
      ((p.restrict h).atTypes m hm).constant n a ha =
        ((p.atTypes m hm).restrict h).constant n a ha := by
    intro n a ha
    obtain ⟨scheme, i, hd, rfl⟩ := ha
    change ((p.restrict h).atTypes m hm).constant n (scheme.inst i) _ =
      (p.atTypes m hm).constant n (scheme.inst i) _
    rw [(p.restrict h).atTypes_constant m hm n scheme hd i,
      p.atTypes_constant m hm n scheme (h.constants n scheme hd) i]
    rfl
  unfold atTypes Model.restrict
  congr 1
  funext n a ha
  exact hc n a ha

theorem Term.eval_rebase_polymorphic {ctx : List HolType} (t : Term s ctx a) (h : s.Extends u)
    (p : PolymorphicModel u) (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m hm)) (e : BoundEnv (p.atTypes m hm) ctx) :
    (t.rebase h).eval (p.atTypes m hm) f e =
      t.eval ((p.restrict h).atTypes m hm) f e := by
  rw [Term.eval_rebase]
  let evaluate (constant : (n : QName) → (a : HolType) →
      (∃ scheme i, s.constants.lookup n = some scheme ∧ scheme.inst i = a) → m.interp a) :
      m.interp a := t.eval (Model.mk m constant) f e
  change evaluate _ = evaluate _
  apply congrArg evaluate
  funext n a ha
  obtain ⟨scheme, i, hd, rfl⟩ := ha
  change (p.atTypes m hm).constant n (scheme.inst i) _ =
    ((p.restrict h).atTypes m hm).constant n (scheme.inst i) _
  rw [p.atTypes_constant m hm n scheme (h.constants n scheme hd) i,
    (p.restrict h).atTypes_constant m hm n scheme hd i]
  rfl

theorem Formula.eval_rebase_polymorphic (t : Formula s) (h : s.Extends u)
    (p : PolymorphicModel u) (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m hm)) :
    (t.rebase h).eval (p.atTypes m hm) f BoundEnv.nil =
      t.eval ((p.restrict h).atTypes m hm) f BoundEnv.nil :=
  Term.eval_rebase_polymorphic t h p m hm f BoundEnv.nil

end HotaruKernel
