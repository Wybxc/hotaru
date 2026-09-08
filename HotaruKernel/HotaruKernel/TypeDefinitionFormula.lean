import HotaruKernel.Quantifiers

namespace HotaruKernel

variable {ctx : List HolType}

def Term.typeDefinitionT (p : Term s ctx (.fn b .bool)) (a : HolType)
    (ha : s.validType a = true) (hb : s.validType b = true) : Term s ctx .bool :=
  let hf : s.validType (.fn a b) = true := by simp [Signature.validType, ha, hb]
  Term.existsT (.lam hf (p.weaken.representsT (.bvar .zero) ha hb)) hf

theorem Term.eval_typeDefinitionT (p : Term s ctx (.fn b .bool)) (a : HolType)
    (ha : s.validType a = true) (hb : s.validType b = true)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (p.typeDefinitionT a ha hb).eval m f e = true ↔
      ∃ r : m.Val a → m.Val b, Function.Injective r ∧
        ∀ y, p.eval m f e y = true ↔ ∃ x, y = r x := by
  unfold typeDefinitionT
  refine (eval_existsT _ _ m f e).trans ?_
  apply exists_congr
  intro r
  refine (eval_representsT _ _ ha hb m f (BoundEnv.cons (a := .fn a b) r e)).trans ?_
  simp only [eval_weaken, eval, BoundEnv.cons]
  rfl

theorem subtype_representation (p : B → Bool) :
    ∃ r : {y : B // p y = true} → B, Function.Injective r ∧
      ∀ y, p y = true ↔ ∃ x, y = r x := by
  refine ⟨Subtype.val, Subtype.val_injective, fun y => ?_⟩
  constructor
  · intro h
    exact ⟨⟨y, h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

theorem subtype_nonempty_iff (p : B → Bool) :
    Nonempty {y : B // p y = true} ↔ ∃ y, p y = true := by
  constructor
  · rintro ⟨⟨y, hy⟩⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, hy⟩⟩

theorem representation_nonempty [Nonempty A] (p : B → Bool) (r : A → B)
    (hr : ∀ y, p y = true ↔ ∃ x, y = r x) : ∃ y, p y = true := by
  obtain ⟨x⟩ := ‹Nonempty A›
  exact ⟨r x, (hr (r x)).mpr ⟨x, rfl⟩⟩

theorem Term.typeDefinition_nonempty (p : Term s ctx (.fn b .bool)) (a : HolType)
    (ha : s.validType a = true) (hb : s.validType b = true)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx)
    (h : (p.typeDefinitionT a ha hb).eval m f e = true) :
    (p.existsT hb).eval m f e = true := by
  obtain ⟨r, _, hr⟩ := (eval_typeDefinitionT p a ha hb m f e).mp h
  letI : Nonempty (m.Val a) := m.toTypeModel.interp_nonempty a
  exact (eval_existsT p hb m f e).mpr (representation_nonempty _ r hr)

end HotaruKernel
