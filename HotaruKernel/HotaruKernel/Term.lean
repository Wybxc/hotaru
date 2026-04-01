import HotaruKernel.Type
import Aesop

/-- HOL terms. -/
inductive Term
| var : String -> HOLType -> Term
| const : String -> HOLType -> Term
| app : Term -> Term -> Term
| abs : Term -> Term -> Term
deriving Repr, DecidableEq

instance : Inhabited Term where
  default := .var "x" HOLType.bool

/-- Type checking predicate for terms. -/
inductive HasType : Term -> HOLType -> Prop
| var : ∀ (x : String) (T : HOLType), HasType (.var x T) T
| const : ∀ (c : String) (T : HOLType), HasType (.const c T) T
| app : ∀ (s t : Term) (dT rT : HOLType),
          HasType s (.fun dT rT) → HasType t dT → HasType (.app s t) rT
| abs : ∀ (n : String) (dT rT : HOLType) (t : Term),
          HasType t rT → HasType (.abs (.var n dT) t) (.fun dT rT)

/-- Predicate for well-typed terms. -/
abbrev WellTyped (t : Term) : Prop := ∃ T, HasType t T

/-- Type inference function for terms. -/
def typeof (t : Term) : Option HOLType :=
  match t with
  | .var _ T => some T
  | .const _ T => some T
  | .app s t =>
      match typeof s, typeof t with
      | some (.fun dT rT), some tT =>
          if dT = tT then some rT else none
      | _, _ => none
  | .abs (.var _ dT) t =>
      match typeof t with
      | some rT => some (.fun dT rT)
      | none => none
  | _ => none

theorem welltyped_typeof : ∀ (t : Term) (T : HOLType), HasType t T → typeof t = some T
    := by
  intros t T ht
  induction ht with simp [typeof] <;> aesop

theorem typeof_welltyped : ∀ (t : Term) (T : HOLType), typeof t = some T → HasType t T
    := by
  intros t T h
  induction t generalizing T with try simp [typeof] at h; subst h
  | var x T' => apply HasType.var
  | const c T' => apply HasType.const
  | app s t ih_s ih_t =>
      unfold typeof at h
      split at h
      · rename_i dT rT tT heq_s heq_t
        split at h <;> simp at h
        subst h
        apply HasType.app
        · exact ih_s (.fun dT rT) heq_s
        · have : typeof t = some dT := by
            rw [heq_t]; aesop
          exact ih_t dT this
      · simp at h
  | abs n t ih_n ih_t =>
      cases n with simp [typeof] at h
      | var var_name dT =>
          split at h <;> simp at h
          subst h
          apply HasType.abs
          aesop

/-- Theorem: `HasType t T` if and only if `typeof t = some T`. -/
theorem welltyped_typeof_iff : ∀ (t : Term) (T : HOLType), HasType t T ↔ typeof t = some T
    := by
  intros t T
  constructor
  · apply welltyped_typeof
  · apply typeof_welltyped

/-- Alpha-equivalence for variables under a list of renamings. -/
@[simp] def IsAlphaVars (bv : List (Term × Term)) (v1 v2 : Term) : Prop :=
  match bv with
  | [] => v1 = v2
  | (b1, b2) :: bvs =>
      (v1 = b1 ∧ v2 = b2) ∨ (v1 ≠ b1 ∧ v2 ≠ b2 ∧ IsAlphaVars bvs v1 v2)

/-- Alpha-equivalence for terms under a list of renamings. -/
inductive IsAlphaTerms : List (Term × Term) -> Term -> Term -> Prop
| var : ∀ (bv : List (Term × Term)) (x1 x2 : String) (T1 T2 : HOLType),
          IsAlphaVars bv (.var x1 T1) (.var x2 T2) → IsAlphaTerms bv (.var x1 T1) (.var x2 T2)
| const : ∀ (bv : List (Term × Term)) (c1 c2 : String) (T1 T2 : HOLType),
          IsAlphaVars bv (.const c1 T1) (.const c2 T2) → IsAlphaTerms bv (.const c1 T1) (.const c2 T2)
| app : ∀ (bv : List (Term × Term)) (s1 s2 t1 t2 : Term),
          IsAlphaTerms bv s1 s2 → IsAlphaTerms bv t1 t2 → IsAlphaTerms bv (.app s1 t1) (.app s2 t2)
| abs : ∀ (bv : List (Term × Term)) (n1 n2 : Term) (t1 t2 : Term),
          IsAlphaTerms ((n1, n2) :: bv) t1 t2 → IsAlphaTerms bv (.abs n1 t1) (.abs n2 t2)

/-- Predicate for alpha-equivalence of terms. -/
def IsAlpha (t1 t2 : Term) : Prop := IsAlphaTerms [] t1 t2

def IsTrivialRenaming (bv : List (Term × Term)) : Prop :=
  match bv with
  | [] => true
  | (b1, b2) :: bvs => b1 = b2 ∧ IsTrivialRenaming bvs

@[aesop safe]
theorem IsAlphaVars_refl : ∀ (bv : List (Term × Term)) (v : Term), IsTrivialRenaming bv → IsAlphaVars bv v v
    := by
  intros bv v h
  induction bv with
  | nil => simp [IsAlphaVars]
  | cons bv bvs ih =>
      rcases bv with ⟨b1, b2⟩
      simp [IsTrivialRenaming] at h
      by_cases hv : v = b1 <;> aesop

@[aesop safe]
theorem IsAlphaTerms_refl : ∀ (bv : List (Term × Term)) (t : Term), IsTrivialRenaming bv → IsAlphaTerms bv t t
    := by
  intro bv t
  induction t generalizing bv with intro h
  | var x T =>
      apply IsAlphaTerms.var
      exact IsAlphaVars_refl bv (.var x T) h
  | const c T =>
      apply IsAlphaTerms.const
      exact IsAlphaVars_refl bv (.const c T) h
  | app s t ih_s ih_t =>
      apply IsAlphaTerms.app <;> aesop
  | abs n t ih_n ih_t =>
      apply IsAlphaTerms.abs
      have h' : IsTrivialRenaming ((n, n) :: bv) := by
        simp [IsTrivialRenaming, h]
      exact ih_t ((n, n) :: bv) h'

def swap_renaming : List (Term × Term) -> List (Term × Term)
| [] => []
| (a, b) :: bvs => (b, a) :: swap_renaming bvs

@[aesop safe]
theorem IsAlphaVars_symm :
  ∀ (bv : List (Term × Term)) (v1 v2 : Term),
    IsAlphaVars bv v1 v2 → IsAlphaVars (swap_renaming bv) v2 v1 := by
  intro bv v1 v2 h
  induction bv generalizing v1 v2 with
  | nil =>
      simpa [IsAlphaVars, swap_renaming] using h.symm
  | cons b bvs ih =>
      simp [IsAlphaVars, swap_renaming] at h ⊢
      aesop

@[aesop safe]
theorem IsAlphaTerms_symm :
  ∀ (bv : List (Term × Term)) (t1 t2 : Term),
    IsAlphaTerms bv t1 t2 → IsAlphaTerms (swap_renaming bv) t2 t1 := by
  intro bv t1 t2 h
  induction h with
  | var bv x1 x2 T1 T2 hv => apply IsAlphaTerms.var; aesop
  | const bv c1 c2 T1 T2 hv => apply IsAlphaTerms.const; aesop
  | app bv s1 s2 t1 t2 hs ht ihs iht => apply IsAlphaTerms.app <;> aesop
  | abs bv n1 n2 t1 t2 hbody ih =>
      simpa [swap_renaming] using (IsAlphaTerms.abs (swap_renaming bv) n2 n1 t2 t1 ih)

inductive RenamingChain :
  List (Term × Term) -> List (Term × Term) -> List (Term × Term) -> Prop
| nil : RenamingChain [] [] []
| cons :
  ∀ (n1 n2 n3 : Term)
    (bv12 bv23 bv13 : List (Term × Term)),
    RenamingChain bv12 bv23 bv13 ->
    RenamingChain ((n1, n2) :: bv12) ((n2, n3) :: bv23) ((n1, n3) :: bv13)

@[aesop unsafe]
theorem IsAlphaVars_trans :
  ∀ (bv12 bv23 bv13 : List (Term × Term)) (v1 v2 v3 : Term),
    RenamingChain bv12 bv23 bv13 ->
    IsAlphaVars bv12 v1 v2 ->
    IsAlphaVars bv23 v2 v3 ->
    IsAlphaVars bv13 v1 v3 := by
  intro bv12 bv23 bv13 v1 v2 v3 hchain h12 h23
  induction hchain generalizing v1 v2 v3 with
  | nil => simpa [IsAlphaVars] using Eq.trans h12 h23
  | cons n1 n2 n3 bv12 bv23 bv13 hchain ih =>
      simp [IsAlphaVars] at h12 h23 ⊢
      aesop

@[aesop safe]
theorem IsAlphaTerms_trans :
  ∀ (bv12 bv23 bv13 : List (Term × Term)) (t1 t2 t3 : Term),
    RenamingChain bv12 bv23 bv13 ->
    IsAlphaTerms bv12 t1 t2 ->
    IsAlphaTerms bv23 t2 t3 ->
    IsAlphaTerms bv13 t1 t3 := by
  intro bv12 bv23 bv13 t1 t2 t3 hchain h12
  induction h12 generalizing bv23 bv13 t3 with intro h23
  | var bv x1 x2 T1 T2 hv12 =>
    cases h23 with
    | var => apply IsAlphaTerms.var; aesop
  | const bv c1 c2 T1 T2 hv12 =>
    cases h23 with
    | const => apply IsAlphaTerms.const; aesop
  | app bv s1 s2 t1 t2 hs12 ht12 ihs iht =>
    cases h23 with
    | app => apply IsAlphaTerms.app <;> aesop
  | abs bv n1 n2 t1 t2 hbody12 ih =>
    cases h23 with
    | abs =>
      apply IsAlphaTerms.abs
      apply ih <;> try aesop
      apply RenamingChain.cons; simpa

theorem IsAlpha.refl : ∀ (t : Term), IsAlpha t t
    := by
  intro t
  unfold IsAlpha
  simpa using IsAlphaTerms_refl [] t (by simp [IsTrivialRenaming])

theorem IsAlpha.symm : ∀ {t1 t2 : Term}, IsAlpha t1 t2 → IsAlpha t2 t1
    := by
  intro t1 t2 h
  unfold IsAlpha at h ⊢
  simpa [swap_renaming] using IsAlphaTerms_symm [] t1 t2 h

theorem IsAlpha.trans : ∀ {t1 t2 t3 : Term}, IsAlpha t1 t2 → IsAlpha t2 t3 → IsAlpha t1 t3
    := by
  intro t1 t2 t3 h12 h23
  unfold IsAlpha at h12 h23 ⊢
  exact IsAlphaTerms_trans [] [] [] t1 t2 t3 RenamingChain.nil h12 h23

instance : Equivalence IsAlpha where
  refl := IsAlpha.refl
  symm := IsAlpha.symm
  trans := IsAlpha.trans

noncomputable instance : DecidableRel IsAlpha := by
  intro t1 t2
  classical
  infer_instance

instance : Setoid Term where
  r := IsAlpha
  iseqv :=
    ⟨IsAlpha.refl, @IsAlpha.symm, @IsAlpha.trans⟩
