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

/-!
Proof roadmap: `subst` and `dbSubst` are consistent through `toDB`.

The target commutation statement is written directly in monadic form:
- left pipeline: `do let t' ← subst i t; t'.toDB`
- right pipeline: `do let dt ← t.toDB; dbSubst i dt`

The final theorem `subst_dbSubst_toDB_consistent` is intended to be proved by structural
induction on `t`, with abstraction split into no-capture and capture-avoidance branches.
-/

/-- Useful bridge: alpha-equivalent terms have identical de Bruijn encodings. -/
theorem toDB_eq_of_alpha {t1 t2 : Term} (h : AlphaEqv t1 t2) : t1.toDB = t2.toDB := by
    rcases alpha_debrujin t1 t2 h with ⟨dt, h1, h2⟩
    exact h1.trans h2.symm

/-- Lemma 1 (variable case): commutation on free-variable leaves. -/
theorem subst_dbSubst_var_comm :
        ∀ (i : List (Term × Term)) (x : String) (T : HOLType),
            (do
                let t' ← subst i (.var x T)
                t'.toDB) = dbSubst i (.fvar x T) := by
    intro i x T
    -- `subst` and `dbSubst` both consult the same lookup list; replacement terms are related by `toDB`.
    sorry

/-- Lemma 2 (application case): commutation distributes over application. -/
theorem subst_dbSubst_app_comm :
        ∀ (i : List (Term × Term)) (s t : Term),
            (do
                let t' ← subst i (Term.app s t)
                t'.toDB) =
            (do
                let dt ← (Term.app s t).toDB
                dbSubst i dt) := by
    intro i s t
    -- Reduce to IH on `s` and `t` and reassemble with monadic congruence.
    sorry

/-- Lemma 3 (abstraction, no capture): filtered substitution commutes under binders. -/
theorem subst_dbSubst_abs_no_capture :
        ∀ (i : List (Term × Term)) (bvar body : Term),
            captureRisk bvar body (i.filter (fun p => !decide (p.fst = bvar))) = false ->
            (do
                let t' ← subst i (Term.abs bvar body)
                t'.toDB) =
            (do
                let dt ← (Term.abs bvar body).toDB
                dbSubst i dt) := by
    intro i bvar body hNoCap
    -- After dropping shadowed substitution entries, the binder case is an IH application on `body`.
    sorry

/-- Turn an existential common `some` witness into option equality. -/
theorem option_eq_of_exists_common :
                ∀ {a b : Option DBTerm},
                        (∃ dt, a = some dt ∧ b = some dt) -> a = b := by
        intro a b h
        rcases h with ⟨dt, ha, hb⟩
        simpa [ha, hb]

/-- Lemma 4 (abstraction, capture branch): produce a common DB witness directly. -/
theorem subst_dbSubst_abs_capture_exists :
                ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
                        captureRisk (Term.var x T) body
                            (i.filter (fun p => !decide (p.fst = Term.var x T))) = true ->
                        ∃ dt,
                            (do
                                let t' ← subst i (Term.abs (Term.var x T) body)
                                t'.toDB) = some dt ∧
                            (do
                                let dta ← (Term.abs (Term.var x T) body).toDB
                                dbSubst i dta) = some dt := by
        intro i x T body hCap
        -- Key idea: avoid the invalid alpha-bridge. Prove both pipelines compute the same DB term
        -- in capture mode, then conclude by `option_eq_of_exists_common` in the main theorem.
        sorry

/-- Main theorem: `subst` and `dbSubst` are consistent under `toDB`. -/
theorem subst_dbSubst_toDB_consistent :
        ∀ (i : List (Term × Term)) (t : Term),
            (do
                let t' ← subst i t
                t'.toDB) =
            (do
                let dt ← t.toDB
                dbSubst i dt) := by
    intro i t
    induction t generalizing i with
    | var x T =>
            simpa using subst_dbSubst_var_comm i x T
    | const c T =>
          sorry
    | app s t ihS ihT =>
            -- Use `subst_dbSubst_app_comm` (or directly IH + simp) to combine both subterms.
            simpa using subst_dbSubst_app_comm i s t
    | abs bvar body ih =>
            -- Split on capture risk:
            -- 1) no-capture: apply `subst_dbSubst_abs_no_capture`;
            -- 2) capture and binder `.var x T`: use `subst_dbSubst_abs_capture_exists`
            --    then close with `option_eq_of_exists_common`.
            -- 3) capture and non-variable binder: both sides evaluate to `none`.
            sorry
