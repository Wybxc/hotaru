import HotaruKernel.Type
import HotaruKernel.Term

/-- De Bruijn representation used to reason about alpha-equivalence. -/
inductive DBTerm
| bvar : Nat -> DBTerm
| fvar : String -> HOLType -> DBTerm
| const : String -> HOLType -> DBTerm
| app : DBTerm -> DBTerm -> DBTerm
| abs : DBTerm -> DBTerm
deriving Repr, DecidableEq

/-- Convert a named term to de Bruijn form under a context. -/
@[simp]
private def toDBAux (env : List (String × HOLType)) : Term -> DBTerm
| .var x T =>
    match env.findIdx? (fun (y, yT) => x = y ∧ T = yT) with
    | some n => DBTerm.bvar n
    | none => DBTerm.fvar x T
| .const c T => DBTerm.const c T
| .app s t => DBTerm.app (toDBAux env s) (toDBAux env t)
| .abs (.var x T) t => DBTerm.abs (toDBAux ((x, T) :: env) t)
| .abs _ t => DBTerm.abs (toDBAux env t)

/-- Convert a named term to de Bruijn form. -/
def Term.toDB (t : Term) : DBTerm := toDBAux [] t

theorem debrujin_alpha :
  ∀ t1 t2 : Term,
    AlphaEqv t1 t2 ↔ t1.toDB = t2.toDB := by
  intros t1 t2
  constructor <;> sorry

theorem debrujin_alpha_counterexample :
  ∃ t1 t2 : Term, AlphaEqv t1 t2 ∧ t1.toDB ≠ t2.toDB := by
  refine ⟨.abs (.const "k1" HOLType.bool) (.const "k1" HOLType.bool),
          .abs (.const "k2" HOLType.bool) (.const "k2" HOLType.bool), ?_⟩
  constructor
  · unfold AlphaEqv
    apply IsAlphaTerms.abs
    · constructor <;> intro h <;> rcases h with ⟨T, hT⟩ <;> cases hT
    · apply IsAlphaTerms.const
      simp [IsAlphaVars]
  · simp [Term.toDB]

theorem not_debrujin_alpha :
  ¬ (∀ t1 t2 : Term, AlphaEqv t1 t2 ↔ t1.toDB = t2.toDB) := by
  intro hAll
  rcases debrujin_alpha_counterexample with ⟨t1, t2, hAlpha, hNe⟩
  exact hNe ((hAll t1 t2).1 hAlpha)
