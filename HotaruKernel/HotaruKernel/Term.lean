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

theorem IsAlphaVars_refl : ∀ (bv : List (Term × Term)) (v : Term), IsTrivialRenaming bv → IsAlphaVars bv v v
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

theorem IsAlphaTerms_refl : ∀ (bv : List (Term × Term)) (t : Term), IsTrivialRenaming bv → IsAlphaTerms bv t t
    := by
  intro bv t
  induction t generalizing bv with
  | var x T =>
      intro h
      apply IsAlphaTerms.var
      exact IsAlphaVars_refl bv (.var x T) h
  | const c T =>
      intro h
      apply IsAlphaTerms.const
      exact IsAlphaVars_refl bv (.const c T) h
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

def swap_renaming : List (Term × Term) -> List (Term × Term)
| [] => []
| (a, b) :: bvs => (b, a) :: swap_renaming bvs

theorem IsAlphaVars_symm :
  ∀ (bv : List (Term × Term)) (v1 v2 : Term),
    IsAlphaVars bv v1 v2 → IsAlphaVars (swap_renaming bv) v2 v1 := by
  intro bv v1 v2 h
  induction bv generalizing v1 v2 with
  | nil =>
    simpa [IsAlphaVars, swap_renaming] using h.symm
  | cons b bvs ih =>
    rcases b with ⟨b1, b2⟩
    simp [IsAlphaVars, swap_renaming] at h ⊢
    rcases h with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2.1, h.1, ih _ _ h.2.2⟩

theorem IsAlphaTerms_symm :
  ∀ (bv : List (Term × Term)) (t1 t2 : Term),
    IsAlphaTerms bv t1 t2 → IsAlphaTerms (swap_renaming bv) t2 t1 := by
  intro bv t1 t2 h
  induction h with
  | var bv x1 x2 T1 T2 hv =>
    exact IsAlphaTerms.var _ _ _ _ _ (IsAlphaVars_symm bv _ _ hv)
  | const bv c1 c2 T1 T2 hv =>
    exact IsAlphaTerms.const _ _ _ _ _ (IsAlphaVars_symm bv _ _ hv)
  | app bv s1 s2 t1 t2 hs ht ihs iht =>
    exact IsAlphaTerms.app _ _ _ _ _ ihs iht
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

theorem IsAlphaVars_trans :
  ∀ (bv12 bv23 bv13 : List (Term × Term)) (v1 v2 v3 : Term),
    RenamingChain bv12 bv23 bv13 ->
    IsAlphaVars bv12 v1 v2 ->
    IsAlphaVars bv23 v2 v3 ->
    IsAlphaVars bv13 v1 v3 := by
  intro bv12 bv23 bv13 v1 v2 v3 hchain h12 h23
  induction hchain generalizing v1 v2 v3 with
  | nil =>
    simpa [IsAlphaVars] using Eq.trans h12 h23
  | cons n1 n2 n3 bv12 bv23 bv13 hchain ih =>
    simp [IsAlphaVars] at h12 h23 ⊢
    rcases h12 with h12 | h12
    · rcases h23 with h23 | h23
      · exact Or.inl ⟨h12.1, h23.2⟩
      · exfalso
        exact h23.1 h12.2
    · rcases h23 with h23 | h23
      · exfalso
        exact h12.2.1 h23.1
      · exact Or.inr ⟨h12.1, h23.2.1, ih _ _ _ h12.2.2 h23.2.2⟩

theorem IsAlphaTerms_trans :
  ∀ (bv12 bv23 bv13 : List (Term × Term)) (t1 t2 t3 : Term),
    RenamingChain bv12 bv23 bv13 ->
    IsAlphaTerms bv12 t1 t2 ->
    IsAlphaTerms bv23 t2 t3 ->
    IsAlphaTerms bv13 t1 t3 := by
  intro bv12 bv23 bv13 t1 t2 t3 hchain h12
  induction h12 generalizing bv23 bv13 t3 with
  | var bv x1 x2 T1 T2 hv12 =>
    intro h23
    cases h23 with
    | var _ _ x3 _ T3 hv23 =>
      exact IsAlphaTerms.var _ _ _ _ _ (IsAlphaVars_trans _ _ _ _ _ _ hchain hv12 hv23)
  | const bv c1 c2 T1 T2 hv12 =>
    intro h23
    cases h23 with
    | const _ _ c3 _ T3 hv23 =>
      exact IsAlphaTerms.const _ _ _ _ _ (IsAlphaVars_trans _ _ _ _ _ _ hchain hv12 hv23)
  | app bv s1 s2 t1 t2 hs12 ht12 ihs iht =>
    intro h23
    cases h23 with
    | app _ _ s3 _ t3 hs23 ht23 =>
      exact IsAlphaTerms.app _ _ _ _ _ (ihs _ _ _ hchain hs23) (iht _ _ _ hchain ht23)
  | abs bv n1 n2 t1 t2 hbody12 ih =>
    intro h23
    cases h23 with
    | abs _ _ n3 _ t3 hbody23 =>
      apply IsAlphaTerms.abs
      exact ih _ _ _
        (RenamingChain.cons n1 n2 n3 bv bv23 bv13 hchain)
        hbody23

theorem IsAlpha.refl : ∀ (t : Term), IsAlpha t t
    := by
  intro t
  unfold IsAlpha
  exact IsAlphaTerms_refl [] t (by simp [IsTrivialRenaming])

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
