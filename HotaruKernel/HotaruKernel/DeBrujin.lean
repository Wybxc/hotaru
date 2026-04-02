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
private def toDBAux (env : List (String × HOLType)) : Term -> Option DBTerm
| .var x T =>
    match env.findIdx? (fun (y, yT) => x = y ∧ T = yT) with
    | some n => some (DBTerm.bvar n)
    | none => some (DBTerm.fvar x T)
| .const c T => some (DBTerm.const c T)
| .app s t => do
    let s' ← toDBAux env s
    let t' ← toDBAux env t
    some (DBTerm.app s' t')
| .abs (.var x T) t => do
    let t' ← toDBAux ((x, T) :: env) t
    some (DBTerm.abs t')
| .abs _ _ => none

/-- Convert a named term to de Bruijn form. -/
def Term.toDB (t : Term) : Option DBTerm := toDBAux [] t

theorem alpha_debrujin :
  ∀ t1 t2 : Term,
    AlphaEqv t1 t2 → ∃ dt, t1.toDB = some dt ∧ t2.toDB = some dt := by
  intros t1 t2 h
  sorry

theorem debrujin_alpha :
  ∀ (t1 t2 : Term) (dt : DBTerm),
    t1.toDB = some dt → t2.toDB = some dt → AlphaEqv t1 t2 := by
  intros t1 t2 dt h1 h2
  sorry
