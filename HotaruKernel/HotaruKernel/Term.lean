import HotaruKernel.Type
import Mathlib.Data.String.Basic
import Aesop

/-- HOL terms. -/
inductive Term
| var : String -> HOLType -> Term
| const : String -> HOLType -> Term
| app : Term -> Term -> Term
| abs : String -> HOLType -> Term -> Term
deriving Repr, DecidableEq

instance : Inhabited Term where
  default := .var "x" HOLType.bool

/-- Type checking predicate for terms. -/
inductive Term.HasType : Term -> HOLType -> Prop
| var : ∀ (x : String) (T : HOLType), Term.HasType (.var x T) T
| const : ∀ (c : String) (T : HOLType), Term.HasType (.const c T) T
| app : ∀ (s t : Term) (dT rT : HOLType),
          Term.HasType s (.fun dT rT) → Term.HasType t dT → Term.HasType (.app s t) rT
| abs : ∀ (n : String) (dT rT : HOLType) (t : Term),
          Term.HasType t rT → Term.HasType (.abs n dT t) (.fun dT rT)

/-- Predicate for well-typed terms. -/
abbrev WellTyped (t : Term) : Prop := ∃ T, t.HasType T

abbrev WellTypedTerm := { t : Term // WellTyped t }

/-- Type inference function for terms. -/
def typeof? (t : Term) : Option HOLType :=
  match t with
  | .var _ T => some T
  | .const _ T => some T
  | .app s t =>
      match typeof? s, typeof? t with
      | some (.fun dT rT), some tT =>
          if dT = tT then some rT else none
      | _, _ => none
  | .abs _ dT t =>
      match typeof? t with
      | some rT => some (.fun dT rT)
      | none => none

theorem welltyped_typeof? : ∀ (t : Term) (T : HOLType), Term.HasType t T → typeof? t = some T
    := by
  intros t T ht
  induction ht with simp [typeof?] <;> aesop

theorem typeof?_welltyped : ∀ (t : Term) (T : HOLType), typeof? t = some T → t.HasType T
    := by
  intros t T h
  induction t generalizing T with try simp [typeof?] at h; subst h
  | var x T' => apply Term.HasType.var
  | const c T' => apply Term.HasType.const
  | app s t ih_s ih_t =>
      unfold typeof? at h
      split at h
      · rename_i dT rT tT heq_s heq_t
        split at h <;> simp at h
        subst h
        apply Term.HasType.app
        · exact ih_s (.fun dT rT) heq_s
        · have : typeof? t = some dT := by
            rw [heq_t]; aesop
          exact ih_t dT this
      · simp at h
  | abs n dT t ih_t =>
      unfold typeof? at h
      split at h
      · rename_i rT hBody
        simp at h
        subst h
        exact Term.HasType.abs n dT rT t (ih_t rT hBody)
      · simp at h

def typeof (t : WellTypedTerm) : HOLType :=
  Option.get (typeof? t.1) <| by
    rcases t.2 with ⟨T, hHasType⟩
    have hSome : typeof? t.1 = some T := welltyped_typeof? t.1 T hHasType
    simp [hSome]

theorem typeof_welltyped : ∀ (t : WellTypedTerm) {T : HOLType}, typeof t = T → t.1.HasType T := by
  intro wt T hT
  rcases wt with ⟨t, hwt⟩
  rcases hwt with ⟨U, hHasType⟩
  have hTy : typeof? t = some U := welltyped_typeof? t U hHasType
  have hTypeof : typeof ⟨t, ⟨U, hHasType⟩⟩ = U := by
    unfold typeof
    simp [hTy]
  aesop

theorem welltyped_typeof : ∀ (t : WellTypedTerm) {T : HOLType}, t.1.HasType T → typeof t = T := by
  intro wt T hHasType
  rcases wt with ⟨t, hwt⟩
  have hTy : typeof? t = some T := welltyped_typeof? t T hHasType
  unfold typeof
  simp [hTy]

theorem welltyped_fun : ∀ (s t : Term), WellTyped (Term.app s t) → WellTyped s := by
  intros s t h
  rcases h with ⟨T, hT⟩
  cases hT with
  | app _ _ dT rT hs _ =>
  exact ⟨_, hs⟩

theorem welltyped_arg : ∀ (s t : Term), WellTyped (Term.app s t) → WellTyped t := by
  intros s t h
  rcases h with ⟨_, hT⟩
  cases hT with
  | app _ _ dT _ _ ht =>
      exact ⟨dT, ht⟩

theorem welltyped_bind : ∀ (n : String) (dT : HOLType) (t : Term),
    WellTyped (Term.abs n dT t) → ∃ n' T, n = n' ∧ dT = T := by
  intros n dT t _
  exact ⟨n, dT, rfl, rfl⟩

theorem welltyped_body : ∀ (n : String) (dT : HOLType) (t : Term),
    WellTyped (Term.abs n dT t) → WellTyped t := by
  intros n dT t h
  rcases h with ⟨_, hT⟩
  cases hT with
  | abs _ _ rT _ ht =>
      exact ⟨rT, ht⟩
