import HotaruKernel.Quantifiers

namespace HotaruKernel

variable {ctx : List HolType}

def Term.surjectiveT (r : Term s ctx (.fn a b)) (ha : s.validType a = true)
    (hb : s.validType b = true) : Term s ctx .bool :=
  (r.rangeT ha hb).forallT hb

theorem Term.eval_surjectiveT (r : Term s ctx (.fn a b)) (ha : s.validType a = true)
    (hb : s.validType b = true) (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (r.surjectiveT ha hb).eval m f e = true ↔ Function.Surjective (r.eval m f e) := by
  refine (eval_forallT _ hb m f e).trans ?_
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := (eval_rangeT r ha hb m f e y).mp (h y)
    exact ⟨x, hx.symm⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact (eval_rangeT r ha hb m f e y).mpr ⟨x, hx.symm⟩

def Term.infiniteT (s : Signature) (ctx : List HolType) (a : HolType)
    (ha : s.validType a = true) : Term s ctx .bool :=
  let hf : s.validType (.fn a a) = true := by simp [Signature.validType, ha]
  let r : Term s (a.fn a :: ctx) (a.fn a) := .bvar .zero
  Term.existsT (.lam hf ((r.injectiveT ha).andT (r.surjectiveT ha ha).notT)) hf

theorem Term.eval_infiniteT (s : Signature) (ctx : List HolType) (a : HolType)
    (ha : s.validType a = true) (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (Term.infiniteT s ctx a ha).eval m f e = true ↔
      ∃ r : m.Val a → m.Val a, Function.Injective r ∧ ¬ Function.Surjective r := by
  unfold infiniteT
  refine (eval_existsT _ _ m f e).trans ?_
  apply exists_congr
  intro r
  have hn (b : Bool) : Bool.not b = true ↔ ¬ b = true := by cases b <;> decide
  change (Term.andT _ _).eval m f (BoundEnv.cons (a := .fn a a) r e) = true ↔ _
  rw [eval_andT]
  change Bool.and _ _ = true ↔ _
  refine (Iff.of_eq (Bool.and_eq_true _ _)).trans ?_
  apply and_congr
  · exact eval_injectiveT _ ha m f (BoundEnv.cons (a := .fn a a) r e)
  · rw [eval_notT]
    exact (hn _).trans (not_congr (eval_surjectiveT _ ha ha m f
      (BoundEnv.cons (a := .fn a a) r e)))

theorem nat_infinity :
    ∃ r : Nat → Nat, Function.Injective r ∧ ¬ Function.Surjective r := by
  refine ⟨Nat.succ, Nat.succ_injective, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := h 0
  exact Nat.noConfusion hx

end HotaruKernel
