import HotaruKernel.Type
import HotaruKernel.Term
import HotaruKernel.Alpha

/-- Term variable substitution: applies a list of term substitutions to a term -/
private def captureRisk (bvar body : Term) (i : List (Term × Term)) : Bool :=
  i.any (fun p => decide (bvar.IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body))

def subst (i : List (Term × Term)) : Term → Option Term
| .var x ty =>
    match i.find? (fun (y, _) => y = Term.var x ty) with
    | some (_, t) => some t
    | none => some (.var x ty)
| .const c ty => some (.const c ty)
| .app s t => do
    let s' ← subst i s
    let t' ← subst i t
    some (.app s' t')
| .abs bvar t => do
    let i' := i.filter (fun p => !decide (p.fst = bvar))
    let t' ← subst i' t
    if captureRisk bvar t i' then
      match bvar with
      | .var x ty => do
          let freshName := generateVariant t' x ty
          let z := Term.var freshName ty
          let i'' := (bvar, z) :: i'
          let t'' ← subst i'' t
          some (.abs z t'')
      | _ => none
    else
      some (.abs bvar t')

/-- Substitute free variables in de Bruijn terms according to a named substitution list. -/
def dbSubst (i : List (Term × Term)) : DBTerm -> Option DBTerm
| .bvar n => some (.bvar n)
| .fvar x T =>
    match i.find? (fun p => p.fst = Term.var x T) with
    | some (_, t) => t.toDB
    | none => some (.fvar x T)
| .const c T => some (.const c T)
| .app s t => do
    let s' ← dbSubst i s
    let t' ← dbSubst i t
    some (.app s' t')
| .abs T t => do
    let t' ← dbSubst i t
    some (.abs T t')
