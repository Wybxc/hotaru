import HotaruKernel.Type

inductive Term
| var : String -> HOLType -> Term
| const : String -> HOLType -> Term
| app : Term -> Term -> Term
| abs : Term -> Term -> Term

inductive HasType : Term -> HOLType -> Prop
| var : ∀ (x : String) (T : HOLType), HasType (.var x T) T
| const : ∀ (c : String) (T : HOLType), HasType (.const c T) T
| app : ∀ (s t : Term) (dT rT : HOLType),
          HasType s (.fun dT rT) → HasType t dT → HasType (.app s t) rT
| abs : ∀ (n : String) (dT rT : HOLType) (t : Term),
          HasType t rT → HasType (.abs (.var n dT) t) (.fun dT rT)

abbrev WellTyped (t : Term) : Prop := ∃ T, HasType t T

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
            have : typeof s = some (.app "fun" (.cons dT (.cons rT .nil))) := heq_s
            exact ih_s (.app "fun" (.cons dT (.cons rT .nil))) this
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
