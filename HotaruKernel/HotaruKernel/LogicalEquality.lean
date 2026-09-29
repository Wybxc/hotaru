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

def Term.logicalEq {ctx dst : List HolType} {a b : HolType}
    (t : Term s ctx a) (u : Term s dst b) : Bool :=
  match t with
  | .fvar n a _ =>
      match u with
      | .fvar m b _ => n == m && a == b
      | _ => false
  | .bvar v =>
      match u with
      | .bvar w => v.index == w.index
      | _ => false
  | .const n scheme i _ _ =>
      match u with
      | .const m other j _ _ =>
          n == m && (i == j || scheme.inst i == other.inst j)
      | _ => false
  | .app f x =>
      match u with
      | .app g y => f.logicalEq g && x.logicalEq y
      | _ => false
  | @Term.lam _ a _ _ _ body =>
      match u with
      | @Term.lam _ b _ _ _ other => a == b && body.logicalEq other
      | _ => false
  | .equal l r =>
      match u with
      | .equal l' r' => l.logicalEq l' && r.logicalEq r'
      | _ => false
  | .imp p q =>
      match u with
      | .imp p' q' => p.logicalEq p' && q.logicalEq q'
      | _ => false

theorem Term.logicalEq_correct {ctx dst : List HolType} {a b : HolType}
    (t : Term s ctx a) (u : Term s dst b) :
    t.logicalEq u = true ↔ t.logical = u.logical := by
  induction t generalizing dst b with
  | fvar n a _ => cases u <;> simp [logicalEq, logical]
  | bvar v => cases u <;> simp [logicalEq, logical]
  | const n scheme i _ _ =>
      cases u <;> simp [logicalEq, logical] <;> aesop
  | app f x ihf ihx => cases u <;> simp [logicalEq, logical, ihf, ihx]
  | lam _ body ih => cases u <;> simp [logicalEq, logical, ih]
  | equal l r ihl ihr => cases u <;> simp [logicalEq, logical, ihl, ihr]
  | imp p q ihp ihq => cases u <;> simp [logicalEq, logical, ihp, ihq]

theorem Term.rawEq_logical {ctx : List HolType} {a : HolType}
    (t u : Term s ctx a) (h : t.rawEq u = true) : t.logical = u.logical := by
  exact congrArg Term.logical (eq_of_heq (t.raw_heq u ((t.rawEq_correct u).mp h)).2)

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

def Term.closedLogicalEq {a b : HolType} (t : Closed s a) (u : Closed s b) : Bool :=
  if h : a = b then
    let u' : Closed s a := h ▸ u
    withPtrEq t u' (fun _ => t.logicalEq u') (fun htu => by
      change t.logicalEq u' = true
      rw [htu]
      exact (u'.logicalEq_correct u').2 rfl)
  else false

theorem Term.closedLogicalEq_correct {a b : HolType} (t : Closed s a) (u : Closed s b) :
    t.closedLogicalEq u = true ↔ t.logical = u.logical := by
  unfold closedLogicalEq
  split
  · rename_i h
    subst b
    simp only [withPtrEq]
    exact t.logicalEq_correct u
  · rename_i h
    constructor
    · simp
    · intro heq
      exact False.elim (h (t.logical_type u heq))

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
  decidable_of_iff (t.logicalEq u = true) (t.logicalEq_correct u)

theorem Term.Equivalent.eval {ctx : List HolType} {t u : Term s ctx a}
    (h : t.Equivalent u) (m : Model s) (f : FreeEnv m) (e : BoundEnv m ctx) :
    t.eval m f e = u.eval m f e := eq_of_heq (t.eval_logical u h m f e)

theorem Term.Equivalent.freeVars {ctx : List HolType} {t u : Term s ctx a}
    (h : t.Equivalent u) : t.freeVars = u.freeVars :=
  t.logical_freeVars.symm.trans ((congrArg LogicalTerm.freeVars h).trans u.logical_freeVars)

def Term.holEquality {s : Signature} (a : HolType)
    (ha : s.validType a = true) (l r : Closed s a) : Formula s :=
  let body : Term s [a] (.fn a .bool) :=
    .lam ha (.equal (.bvar (.succ .zero)) (.bvar .zero))
  let connective : Closed s (.fn a (.fn a .bool)) := .lam ha body
  .app (.app connective l) r

theorem Term.eval_holEquality {s : Signature} (a : HolType)
    (ha : s.validType a = true) (l r : Closed s a)
    (m : Model s) (f : FreeEnv m) :
    (Term.holEquality a ha l r).eval m f BoundEnv.nil =
      (Term.equal l r).eval m f BoundEnv.nil := by
  simp only [Term.holEquality, Term.eval]
  rfl

end HotaruKernel
