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

theorem alpha_debrujin :
  ∀ t1 t2 : Term,
    AlphaEqv t1 t2 → t1.toDB = t2.toDB := by
  intros t1 t2 h
  sorry

theorem debrujin_alpha :
  ∀ t1 t2 : Term,
    t1.toDB = t2.toDB → WellTyped t1 → WellTyped t2 → AlphaEqv t1 t2 := by
  intros t1 t2
  sorry
