import HotaruKernel.Inference

namespace HotaruKernel

variable {ctx : List HolType}

def Term.trueT : Term s ctx .bool :=
  let id : Term s ctx (.fn .bool .bool) :=
    .lam (by simp [Signature.validType]) (.bvar .zero)
  .equal id id

def Term.falseT : Term s ctx .bool :=
  .equal (.lam (by simp [Signature.validType]) (.bvar .zero))
    (.lam (by simp [Signature.validType]) (Term.trueT (s := s)))

def Term.notT (p : Term s ctx .bool) : Term s ctx .bool := .imp p .falseT

def Term.andT (p q : Term s ctx .bool) : Term s ctx .bool :=
  (Term.imp p q.notT).notT

def Term.forallT (p : Term s ctx (.fn a .bool)) (hv : s.validType a = true) :
    Term s ctx .bool := .equal p (.lam hv .trueT)

def Term.existsT (p : Term s ctx (.fn a .bool)) (hv : s.validType a = true) :
    Term s ctx .bool := (Term.equal p (.lam hv .falseT)).notT

theorem Term.eval_trueT (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (Term.trueT (s := s)).eval m f e = true :=
  (eval_equal_true _ _ _ _ _).mpr rfl

theorem Term.eval_falseT (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (Term.falseT (s := s)).eval m f e = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := (eval_equal_true _ _ _ _ _).mp h
  have hx := congrFun he false
  change false = Term.trueT.eval m f (BoundEnv.cons (a := .bool) false e) at hx
  rw [eval_trueT] at hx
  cases hx

theorem Term.eval_notT (p : Term s ctx .bool) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) : p.notT.eval m f e = !(p.eval m f e) := by
  change (!(p.eval m f e) || Term.falseT.eval m f e) = _
  rw [eval_falseT, Bool.or_false]

theorem Term.eval_andT (p q : Term s ctx .bool) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) : (p.andT q).eval m f e = (p.eval m f e && q.eval m f e) := by
  rw [andT, eval_notT]
  change (!(!(p.eval m f e) || q.notT.eval m f e)) = _
  rw [eval_notT]
  cases p.eval m f e <;> cases q.eval m f e <;> rfl

theorem Term.eval_forallT (p : Term s ctx (.fn a .bool)) (hv : s.validType a = true)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (p.forallT hv).eval m f e = true ↔ ∀ x, p.eval m f e x = true := by
  rw [forallT, eval_equal_true]
  constructor
  · intro h x
    exact (congrFun h x).trans (eval_trueT m f (e.cons x))
  · intro h
    funext x
    exact (h x).trans (eval_trueT m f (e.cons x)).symm

theorem Term.eval_existsT (p : Term s ctx (.fn a .bool)) (hv : s.validType a = true)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (p.existsT hv).eval m f e = true ↔ ∃ x, p.eval m f e x = true := by
  classical
  have hn (b : Bool) : ((!b) = true) ↔ b ≠ true := by cases b <;> decide
  rw [existsT, eval_notT]
  change Bool.not ((Term.equal p (.lam hv .falseT)).eval m f e) = true ↔ _
  refine (hn _).trans ((not_congr (eval_equal_true p (.lam hv .falseT) m f e)).trans ?_)
  constructor
  · intro h
    by_contra hn
    apply h
    funext x
    have hx : p.eval m f e x ≠ true := fun hx => hn ⟨x, hx⟩
    exact (Bool.eq_false_iff.mpr hx).trans (eval_falseT m f (e.cons x)).symm
  · rintro ⟨x, hx⟩ he
    have hf : true = false := hx.symm.trans ((congrFun he x).trans (eval_falseT m f (e.cons x)))
    cases hf

theorem Term.freeVars_existsT (p : Term s ctx (.fn a .bool)) (hv : s.validType a = true) :
    (p.existsT hv).freeVars = p.freeVars := by
  simp [existsT, notT, falseT, trueT, freeVars]

def Term.injectiveT (r : Term s ctx (.fn a b)) (ha : s.validType a = true) :
    Term s ctx .bool :=
  Term.forallT (.lam ha (Term.forallT (.lam ha
    (.imp (.equal (.app r.weaken.weaken (.bvar (.succ .zero)))
                  (.app r.weaken.weaken (.bvar .zero)))
           (.equal (.bvar (.succ .zero)) (.bvar .zero)))) ha)) ha

def Term.rangeT (r : Term s ctx (.fn a b)) (ha : s.validType a = true)
    (hb : s.validType b = true) : Term s ctx (.fn b .bool) :=
  .lam hb (Term.existsT (.lam ha
    (.equal (.bvar (.succ .zero)) (.app r.weaken.weaken (.bvar .zero)))) ha)

def Term.representsT (p : Term s ctx (.fn b .bool)) (r : Term s ctx (.fn a b))
    (ha : s.validType a = true) (hb : s.validType b = true) : Term s ctx .bool :=
  (r.injectiveT ha).andT (.equal p (r.rangeT ha hb))

theorem Term.eval_injectiveT (r : Term s ctx (.fn a b)) (ha : s.validType a = true)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (r.injectiveT ha).eval m f e = true ↔ Function.Injective (r.eval m f e) := by
  classical
  have himp (p q : Bool) : ((!p || q) = true) ↔ (p = true → q = true) := by
    cases p <;> cases q <;> decide
  unfold injectiveT
  refine (eval_forallT _ ha m f e).trans ?_
  have inner (x : m.Val a) :
      (Term.forallT (.lam ha
        (.imp (.equal (.app r.weaken.weaken (.bvar (.succ .zero)))
          (.app r.weaken.weaken (.bvar .zero)))
          (.equal (.bvar (.succ .zero)) (.bvar .zero)))) ha).eval m f (e.cons x) = true ↔
      ∀ y, r.eval m f e x = r.eval m f e y → x = y := by
    refine (eval_forallT _ ha m f (e.cons x)).trans ?_
    apply forall_congr'
    intro y
    change ((!decide (r.weaken.weaken.eval m f (BoundEnv.cons y (BoundEnv.cons x e)) x =
      r.weaken.weaken.eval m f (BoundEnv.cons y (BoundEnv.cons x e)) y) ||
      decide (x = y)) = true) ↔ _
    simp only [eval_weaken, himp, decide_eq_true_eq]
  constructor
  · intro h x y he
    exact (inner x).mp (h x) y he
  · intro h x
    exact (inner x).mpr (fun _ he => h he)

theorem Term.eval_rangeT (r : Term s ctx (.fn a b)) (ha : s.validType a = true)
    (hb : s.validType b = true) (m : Model s) (f : FreeEnv m)
    (e : BoundEnv m ctx) (y : m.Val b) :
    (r.rangeT ha hb).eval m f e y = true ↔ ∃ x, y = r.eval m f e x := by
  change (Term.existsT _ ha).eval m f (e.cons y) = true ↔ _
  rw [eval_existsT]
  simp only [eval, eval_weaken, BoundEnv.cons, decide_eq_true_eq]

theorem Term.eval_representsT (p : Term s ctx (.fn b .bool))
    (r : Term s ctx (.fn a b)) (ha : s.validType a = true) (hb : s.validType b = true)
    (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    (p.representsT r ha hb).eval m f e = true ↔
      Function.Injective (r.eval m f e) ∧
        ∀ y, p.eval m f e y = true ↔ ∃ x, y = r.eval m f e x := by
  rw [representsT, eval_andT]
  change Bool.and ((r.injectiveT ha).eval m f e)
    ((Term.equal p (r.rangeT ha hb)).eval m f e) = true ↔ _
  refine (Iff.of_eq (Bool.and_eq_true _ _)).trans ((and_congr (eval_injectiveT r ha m f e)
    (eval_equal_true p (r.rangeT ha hb) m f e)).trans ?_)
  constructor
  · rintro ⟨hi, he⟩
    exact ⟨hi, fun y => by rw [congrFun he y]; exact eval_rangeT r ha hb m f e y⟩
  · rintro ⟨hi, he⟩
    refine ⟨hi, funext fun y => ?_⟩
    have h := (he y).trans (eval_rangeT r ha hb m f e y).symm
    exact Bool.eq_iff_iff.mpr h

end HotaruKernel
