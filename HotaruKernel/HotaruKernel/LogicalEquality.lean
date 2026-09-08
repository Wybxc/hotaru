import HotaruKernel.Equality
import HotaruKernel.Semantics

namespace HotaruKernel

inductive LogicalTerm where
  | fvar : String → HolType → LogicalTerm
  | bvar : Nat → LogicalTerm
  | const : QName → HolType → LogicalTerm
  | app : LogicalTerm → LogicalTerm → LogicalTerm
  | lam : HolType → LogicalTerm → LogicalTerm
  | equal : LogicalTerm → LogicalTerm → LogicalTerm
  | imp : LogicalTerm → LogicalTerm → LogicalTerm
  deriving DecidableEq, Repr

def Term.logical {ctx : List HolType} : Term s ctx a → LogicalTerm
  | .fvar n a _ => .fvar n a
  | .bvar v => .bvar v.index
  | .const n scheme i _ _ => .const n (scheme.inst i)
  | .app f x => .app f.logical x.logical
  | @Term.lam _ a _ _ _ b => .lam a b.logical
  | .equal l r => .equal l.logical r.logical
  | .imp p q => .imp p.logical q.logical

def LogicalTerm.freeVars : LogicalTerm → List FVar
  | .fvar n a => [(n, a)]
  | .bvar _ | .const .. => []
  | .app f x | .equal f x | .imp f x => f.freeVars ++ x.freeVars
  | .lam _ b => b.freeVars

theorem Term.logical_freeVars {ctx : List HolType} (t : Term s ctx a) :
    t.logical.freeVars = t.freeVars := by
  induction t <;> simp_all [logical, LogicalTerm.freeVars, freeVars]

theorem Term.logical_type {ctx : List HolType} (t : Term s ctx a) (u : Term s ctx b)
    (h : t.logical = u.logical) : a = b := by
  induction t generalizing b with
  | fvar n a hv =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.fvar.injEq] at h
    exact h.2
  | bvar v =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.bvar.injEq] at h
    exact (v.index_heq _ h).1
  | const n scheme i hd hv =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.const.injEq] at h
    exact h.2
  | app f x ihf ihx =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.app.injEq] at h
    exact (HolType.fn.inj (ihf _ h.1)).2
  | lam hv body ih =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.lam.injEq] at h
    obtain ⟨rfl, hb⟩ := h
    exact congrArg (HolType.fn _) (ih _ hb)
  | equal l r ihl ihr =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.equal.injEq] at h
    rfl
  | imp p q ihp ihq =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.imp.injEq] at h
    rfl

theorem Model.constant_heq (m : Model s) (n : QName) (a b : HolType)
    (ha : ∃ scheme i, s.constants.lookup n = some scheme ∧ scheme.inst i = a)
    (hb : ∃ scheme i, s.constants.lookup n = some scheme ∧ scheme.inst i = b)
    (h : a = b) : HEq (m.constant n a ha) (m.constant n b hb) := by
  cases h
  rfl

theorem Term.eval_logical {ctx : List HolType} (t : Term s ctx a) (u : Term s ctx b)
    (h : t.logical = u.logical) (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    HEq (t.eval m f e) (u.eval m f e) := by
  classical
  induction t generalizing b with
  | fvar n a hv =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.fvar.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | bvar v =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.bvar.injEq] at h
    obtain ⟨rfl, hw⟩ := v.index_heq _ h
    cases eq_of_heq hw
    rfl
  | const n scheme i hd hv =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.const.injEq] at h
    obtain ⟨rfl, ht⟩ := h
    exact m.constant_heq _ _ _ _ _ ht
  | app f' x ihf ihx =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.app.injEq] at h
    rename_i x' f''
    obtain ⟨ha, hb⟩ := HolType.fn.inj (f'.logical_type f'' h.1)
    cases ha
    cases hb
    exact heq_of_eq (congrArg₂ (fun g x => g x)
      (eq_of_heq (ihf f'' h.1 e)) (eq_of_heq (ihx x' h.2 e)))
  | lam hv body ih =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.lam.injEq] at h
    rename_i body'
    obtain ⟨rfl, hb⟩ := h
    have ht := body.logical_type body' hb
    cases ht
    apply heq_of_eq
    funext x
    exact eq_of_heq (ih body' hb (e.cons x))
  | equal l r ihl ihr =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.equal.injEq] at h
    rename_i l' r'
    have ht := l.logical_type l' h.1
    cases ht
    have hl := eq_of_heq (ihl l' h.1 e)
    have hr := eq_of_heq (ihr r' h.2 e)
    apply heq_of_eq
    change decide _ = decide _
    rw [hl, hr]
  | imp p q ihp ihq =>
    cases u <;> simp only [logical, reduceCtorEq, LogicalTerm.imp.injEq] at h
    rename_i p' q'
    exact heq_of_eq (congrArg₂ (fun x y : Bool => !x || y)
      (eq_of_heq (ihp p' h.1 e)) (eq_of_heq (ihq q' h.2 e)))

def Term.Equivalent {ctx : List HolType} (t u : Term s ctx a) : Prop :=
  t.logical = u.logical

instance {ctx : List HolType} (t u : Term s ctx a) : Decidable (t.Equivalent u) :=
  inferInstanceAs (Decidable (t.logical = u.logical))

theorem Term.Equivalent.eval {ctx : List HolType} {t u : Term s ctx a}
    (h : t.Equivalent u) (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    t.eval m f e = u.eval m f e := eq_of_heq (t.eval_logical u h m f e)

theorem Term.Equivalent.freeVars {ctx : List HolType} {t u : Term s ctx a}
    (h : t.Equivalent u) : t.freeVars = u.freeVars :=
  t.logical_freeVars.symm.trans ((congrArg LogicalTerm.freeVars h).trans u.logical_freeVars)

end HotaruKernel
