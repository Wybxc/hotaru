import HotaruKernel.Type

/-- HOL terms. -/
inductive Term
| var : String -> HOLType -> Term
| const : String -> HOLType -> Term
| app : Term -> Term -> Term
| abs : Term -> Term -> Term

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
  induction ht with
  | var x T => simp [typeof]
  | const c T => simp [typeof]
  | app s t dT rT ht_s ht_t ih_s ih_t =>
      simp [typeof]
      rw [ih_s, ih_t]
      simp [HOLType.fun, HOLTypeList.fromList]
  | abs n dT rT t ht_t ih_t =>
      simp [typeof]
      rw [ih_t]

theorem typeof_welltyped : ∀ (t : Term) (T : HOLType), typeof t = some T → HasType t T
    := by
  intros t T h
  induction t generalizing T with
  | var x T' =>
      simp [typeof] at h
      rw [h]
      apply HasType.var
  | const c T' =>
      simp [typeof] at h
      rw [h]
      apply HasType.const
  | app s t ih_s ih_t =>
      -- Key idea: unfold typeof and analyze the match
      unfold typeof at h
      split at h
      · -- typeof s = some (.fun dT rT), typeof t = some tT
        rename_i dT rT tT heq_s heq_t
        split at h
        · -- dT = tT, h : some rT = some T
          rename_i eq_dt
          simp at h
          subst h
          -- now we need to show HasType (s.app t) rT
          -- apply HasType.app: need HasType s (.fun dT rT) and HasType t dT
          apply HasType.app
          · -- show HasType s (.fun dT rT)
            have : typeof s = some (.fun dT rT) := heq_s
            exact ih_s (.fun dT rT) this
          · -- show HasType t dT
            have : typeof t = some dT := by
              rw [eq_dt]; exact heq_t
            exact ih_t dT this
        · -- contradiction: dT ≠ tT and h : none = some T
          simp at h
      · -- typeof s and typeof t don't match the pattern, h : none = some T
        -- contradiction
        simp at h
  | abs n t =>
      rename_i ih_n ih_t
      -- Pattern match on n at the tactic level
      cases n with
      | var var_name dT =>
          -- Now typeof (.abs (.var var_name dT) t) = match typeof t with ...
          simp [typeof] at h
          split at h
          · -- typeof t = some rT and T = .fun dT rT
            rename_i rT heq_t
            simp at h
            subst h
            -- Show HasType (.abs (.var var_name dT) t) (.fun dT rT)
            apply HasType.abs
            exact ih_t rT heq_t
          · -- none = some T, contradiction
            simp at h
      | const _ _ =>
          -- typeof (.abs (.const _ _) t) = none (doesn't match the .var pattern)
          simp [typeof] at h
      | app _ _ =>
          simp [typeof] at h
      | abs _ _ =>
          simp [typeof] at h

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

def IsTrivialRenaming (bv : List (Term × Term)) : Prop :=
  match bv with
  | [] => true
  | (b1, b2) :: bvs => b1 = b2 ∧ IsTrivialRenaming bvs

theorem IsAlphaVars.refl : ∀ (bv : List (Term × Term)) (v : Term), IsTrivialRenaming bv → IsAlphaVars bv v v
    := by
  intros bv v h
  induction bv with
  | nil => simp [IsAlphaVars]
  | cons bv bvs ih =>
      rcases bv with ⟨b1, b2⟩
      simp [IsTrivialRenaming] at h
      rcases h with ⟨hb, htail⟩
      by_cases hv : v = b1
      · left
        exact ⟨hv, by simpa [hb] using hv⟩
      · right
        refine ⟨hv, ?_, ih htail⟩
        intro hv2
        apply hv
        simpa [hb] using hv2

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

theorem IsAlphaTerms.refl : ∀ (bv : List (Term × Term)) (t : Term), IsTrivialRenaming bv → IsAlphaTerms bv t t
    := by
  intro bv t
  induction t generalizing bv with
  | var x T =>
      intro h
      apply IsAlphaTerms.var
      exact IsAlphaVars.refl bv (.var x T) h
  | const c T =>
      intro h
      apply IsAlphaTerms.const
      exact IsAlphaVars.refl bv (.const c T) h
  | app s t ih_s ih_t =>
      intro h
      apply IsAlphaTerms.app
      · exact ih_s bv h
      · exact ih_t bv h
  | abs n t ih_n ih_t =>
      intro h
      apply IsAlphaTerms.abs
      have h' : IsTrivialRenaming ((n, n) :: bv) := by
        simp [IsTrivialRenaming, h]
      exact ih_t ((n, n) :: bv) h'

/-- Predicate for alpha-equivalence of terms. -/
def IsAlpha (t1 t2 : Term) : Prop := IsAlphaTerms [] t1 t2

theorem IsAlpha.refl : ∀ (t : Term), IsAlpha t t
    := by
  intro t
  unfold IsAlpha
  exact IsAlphaTerms.refl [] t (by simp [IsTrivialRenaming])

theorem IsAlpha.symm : ∀ (t1 t2 : Term), IsAlpha t1 t2 → IsAlpha t2 t1
    := by
  sorry

theorem IsAlpha.trans : ∀ (t1 t2 t3 : Term), IsAlpha t1 t2 → IsAlpha t2 t3 → IsAlpha t1 t3
    := by
  sorry

instance : Equivalence IsAlpha where
  refl := IsAlpha.refl
  symm := by sorry
  trans := by sorry
