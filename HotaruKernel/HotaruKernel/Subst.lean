import HotaruKernel.Type
import HotaruKernel.Term
import HotaruKernel.Alpha
import HotaruKernel.DBTerm
import Aesop

@[simp] def Term.isFreeVarIn : Term -> Term -> Bool
| v, .var x T => decide (v = .var x T)
| _, .const _ _ => false
| v, .app s u => v.isFreeVarIn s || v.isFreeVarIn u
| v, .abs x T body => decide (v ≠ .var x T) && v.isFreeVarIn body

@[simp] def Term.IsFreeVarIn (v t : Term) : Prop :=
  v.isFreeVarIn t = true

instance (v t : Term) : Decidable (v.IsFreeVarIn t) := by
  unfold Term.IsFreeVarIn
  infer_instance

/-- Maximum variable-name length appearing in a term. -/
def Term.maxVarNameLen : Term → Nat
| .var x _ => String.length x
| .const _ _ => 0
| .app s t => Nat.max s.maxVarNameLen t.maxVarNameLen
| .abs n _ t => Nat.max (String.length n) t.maxVarNameLen

theorem varNotFreeOfNameLengthGt :
  ∀ (t : Term) (x : String) (T : HOLType),
    t.maxVarNameLen < String.length x → ¬(Term.var x T).IsFreeVarIn t := by
  have freeVarNameLen_le :
      ∀ (t : Term) (x : String) (T : HOLType),
        (Term.var x T).IsFreeVarIn t -> String.length x ≤ t.maxVarNameLen := by
    intro t
    induction t with
    | var y Ty =>
        intro x T hfree
        simp [Term.IsFreeVarIn, Term.isFreeVarIn] at hfree
        rcases hfree with ⟨hx, hT⟩
        subst hx hT
        simp [Term.maxVarNameLen]
    | const c Ty =>
        intro x T hfree
        simp [Term.IsFreeVarIn, Term.isFreeVarIn] at hfree
    | app s t ihs iht =>
        intro x T hfree
        simp [Term.IsFreeVarIn, Term.isFreeVarIn] at hfree
        rcases hfree with hs | ht
        · exact Nat.le_trans (ihs x T hs) (Nat.le_max_left s.maxVarNameLen t.maxVarNameLen)
        · exact Nat.le_trans (iht x T ht) (Nat.le_max_right s.maxVarNameLen t.maxVarNameLen)
    | abs n Ty t ih =>
        intro x T hfree
        simp [Term.IsFreeVarIn, Term.isFreeVarIn] at hfree
        rcases hfree with ⟨_, ht⟩
        exact Nat.le_trans (ih x T ht) (Nat.le_max_right (String.length n) t.maxVarNameLen)
  intro t
  intro x T hlen hfree
  have hle : String.length x ≤ t.maxVarNameLen := freeVarNameLen_le t x T hfree
  exact (Nat.not_lt_of_ge hle) hlen

/-- Generate a variable variant with primes appended to avoid name collisions -/
private def variantCandidate (baseName : String) (k : Nat) : String :=
  baseName ++ String.ofList (List.replicate k '\'')

/-- Freshness predicate for a suffix length. -/
private def variantFreshAt (term : Term) (baseName : String) (ty : HOLType) (k : Nat) : Prop :=
  ¬(Term.var (variantCandidate baseName k) ty).IsFreeVarIn term

instance (term : Term) (baseName : String) (ty : HOLType) (k : Nat) :
    Decidable (variantFreshAt term baseName ty k) := by
  unfold variantFreshAt
  infer_instance

/-- Scan suffix lengths from `k` down to `0`, keeping the smallest fresh one found. -/
private def chooseMinFreshSuffix (term : Term) (baseName : String) (ty : HOLType) :
    (k best : Nat) → variantFreshAt term baseName ty best → {n : Nat // variantFreshAt term baseName ty n}
| 0, best, hbest =>
    if h0 : variantFreshAt term baseName ty 0 then ⟨0, h0⟩ else ⟨best, hbest⟩
| k + 1, best, hbest =>
    let next : {n : Nat // variantFreshAt term baseName ty n} :=
      if hk1 : variantFreshAt term baseName ty (k + 1) then
        ⟨k + 1, hk1⟩
      else
        ⟨best, hbest⟩
    chooseMinFreshSuffix term baseName ty k next.1 next.2

/-- Generate a variable variant with the shortest suffix that avoids capture. -/
def generateVariant (term : Term) (baseName : String) (ty : HOLType) : String :=
  let bound := term.maxVarNameLen + 1
  let hbound : variantFreshAt term baseName ty bound := by
    apply varNotFreeOfNameLengthGt
    have h1 : term.maxVarNameLen < term.maxVarNameLen + 1 := Nat.lt_succ_self _
    have h2 : term.maxVarNameLen + 1 ≤ String.length (variantCandidate baseName bound) := by
      simp [bound, variantCandidate, Nat.le_add_left (term.maxVarNameLen + 1) (String.length baseName)]
    exact Nat.lt_of_lt_of_le h1 h2
  let best := chooseMinFreshSuffix term baseName ty bound bound hbound
  variantCandidate baseName best.1

theorem VariantFresh : ∀ t x T, ¬(Term.var (generateVariant t x T) T).IsFreeVarIn t
    := by
  intros t x T
  unfold generateVariant
  have hbound : variantFreshAt t x T (t.maxVarNameLen + 1) := by
    apply varNotFreeOfNameLengthGt
    have h1 : t.maxVarNameLen < t.maxVarNameLen + 1 := Nat.lt_succ_self _
    have h2 : t.maxVarNameLen + 1 ≤ String.length (variantCandidate x (t.maxVarNameLen + 1)) := by
      simp [variantCandidate, Nat.le_add_left (t.maxVarNameLen + 1) (String.length x)]
    exact Nat.lt_of_lt_of_le h1 h2
  let best := chooseMinFreshSuffix t x T (t.maxVarNameLen + 1) (t.maxVarNameLen + 1) hbound
  simpa [variantFreshAt] using best.2

/-- Term variable substitution: applies a list of term substitutions to a term -/
private def captureRisk (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)) : Bool :=
  let bvar := Term.var x T
  i.any (fun p => decide (bvar.IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body))

def subst (i : List (Term × Term)) : Term → Term
| .var x ty =>
    match i.find? (fun (y, _) => y = Term.var x ty) with
    | some (_, t) => t
    | none => .var x ty
| .const c ty => .const c ty
| .app s t =>
    let s' := subst i s
    let t' := subst i t
    .app s' t'
| .abs x T t =>
    let bvar := Term.var x T
    let i' := i.filter (fun p => !decide (p.fst = bvar))
    let t' := subst i' t
    if captureRisk x T t i' then
      let freshName := generateVariant t' x T
      let z := Term.var freshName T
      let i'' := (bvar, z) :: i'
      let t'' := subst i'' t
      .abs freshName T t''
    else
      .abs x T t'

/-- Substitute free variables in de Bruijn terms according to a named substitution list. -/
def dbSubst (i : List (Term × Term)) : DBTerm -> DBTerm
| .bvar n => .bvar n
| .fvar x T =>
    match i.find? (fun p => p.fst = Term.var x T) with
    | some (_, t) => t.toDB
    | none => .fvar x T
| .const c T => .const c T
| .app s t => .app (dbSubst i s) (dbSubst i t)
| .abs T t => .abs T (dbSubst i t)

def SubstOk (i : List (Term × Term)) : Prop :=
  ∀ v t, (v, t) ∈ i → ∃ x T, v = Term.var x T ∧ t.HasType T

theorem SubstOk.filter : ∀ (i : List (Term × Term)) (bvar : Term),
    SubstOk i -> SubstOk (i.filter (fun p => !decide (p.fst = bvar))) := by
  intro i bvar hOk
  intro v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

theorem subst_toDB_comm :
  ∀ (i : List (Term × Term)) (t : Term),
    SubstOk i → (subst i t).toDB = dbSubst i t.toDB := by
  intro i t hOk
  induction t generalizing i with
  | var x T =>
      cases hfind : i.find? (fun p => p.fst = Term.var x T) with
      | none =>
        simp [subst, dbSubst, Term.toDB, hfind]
      | some p =>
        rcases p with ⟨v, u⟩
        simp [subst, dbSubst, Term.toDB, hfind]
  | const c T =>
      simp [subst, dbSubst, Term.toDB]
  | app s t ihs iht =>
      have hSubstApp : (subst i (Term.app s t)).toDB = DBTerm.app (subst i s).toDB (subst i t).toDB := by
        rfl
      have hToDBApp : (Term.app s t).toDB = DBTerm.app s.toDB t.toDB := by
        rfl
      calc
        (subst i (Term.app s t)).toDB
        = DBTerm.app (subst i s).toDB (subst i t).toDB := by
                exact hSubstApp
      _ = DBTerm.app (dbSubst i s.toDB) (dbSubst i t.toDB) := by
          simp [ihs i hOk, iht i hOk]
        _ = dbSubst i (Term.app s t).toDB := by
              rw [hToDBApp]
              rfl
  | abs x T body ih =>
        sorry

-- /-!
-- Proof roadmap: `subst` and `dbSubst` are consistent through `toDB`.

-- The target commutation statement is written directly in monadic form:
-- - left pipeline: `do let t' ← subst i t; t'.toDB`
-- - right pipeline: `do let dt ← t.toDB; dbSubst i dt`

-- The final theorem `subst_dbSubst_toDB_consistent` is intended to be proved by structural
-- induction on `t`, with abstraction split into no-capture and capture-avoidance branches.
-- -/

-- /-- Useful bridge: alpha-equivalent terms have identical de Bruijn encodings. -/
-- theorem toDB_eq_of_alpha {t1 t2 : Term} (h : AlphaEqv t1 t2) : t1.toDB = t2.toDB := by
--     rcases alpha_debrujin t1 t2 h with ⟨dt, h1, h2⟩
--     exact h1.trans h2.symm

-- /-- Lemma 1 (variable case): commutation on free-variable leaves. -/
-- theorem subst_dbSubst_var_comm :
--         ∀ (i : List (Term × Term)) (x : String) (T : HOLType),
--             (do
--                 let t' ← subst? i (.var x T)
--                 t'.toDB) = dbSubst i (.fvar x T) := by
--     intro i x T
--     -- `subst` and `dbSubst` both consult the same lookup list; replacement terms are related by `toDB`.
--     sorry

-- /-- Lemma 2 (application case): commutation distributes over application. -/
-- theorem subst_dbSubst_app_comm :
--         ∀ (i : List (Term × Term)) (s t : Term),
--             (do
--                 let t' ← subst? i (Term.app s t)
--                 t'.toDB) =
--             (do
--                 let dt ← (Term.app s t).toDB
--                 dbSubst i dt) := by
--     intro i s t
--     -- Reduce to IH on `s` and `t` and reassemble with monadic congruence.
--     sorry

-- /-- Lemma 3 (abstraction, no capture): filtered substitution commutes under binders. -/
-- theorem subst_dbSubst_abs_no_capture :
--         ∀ (i : List (Term × Term)) (bvar body : Term),
--             captureRisk bvar body (i.filter (fun p => !decide (p.fst = bvar))) = false ->
--             (do
--                 let t' ← subst? i (Term.abs bvar body)
--                 t'.toDB) =
--             (do
--                 let dt ← (Term.abs bvar body).toDB
--                 dbSubst i dt) := by
--     intro i bvar body hNoCap
--     -- After dropping shadowed substitution entries, the binder case is an IH application on `body`.
--     sorry

-- /-- Turn an existential common `some` witness into option equality. -/
-- theorem option_eq_of_exists_common :
--                 ∀ {a b : Option DBTerm},
--                         (∃ dt, a = some dt ∧ b = some dt) -> a = b := by
--         intro a b h
--         rcases h with ⟨dt, ha, hb⟩
--         simpa [ha, hb]

-- /-- Lemma 4 (abstraction, capture branch): produce a common DB witness directly. -/
-- theorem subst_dbSubst_abs_capture_exists :
--                 ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
--                         captureRisk (Term.var x T) body
--                             (i.filter (fun p => !decide (p.fst = Term.var x T))) = true ->
--                         ∃ dt,
--                             (do
--                                 let t' ← subst? i (Term.abs (Term.var x T) body)
--                                 t'.toDB) = some dt ∧
--                             (do
--                                 let dta ← (Term.abs (Term.var x T) body).toDB
--                                 dbSubst i dta) = some dt := by
--         intro i x T body hCap
--         -- Key idea: avoid the invalid alpha-bridge. Prove both pipelines compute the same DB term
--         -- in capture mode, then conclude by `option_eq_of_exists_common` in the main theorem.
--         sorry

-- /-- Main theorem: `subst` and `dbSubst` are consistent under `toDB`. -/
-- theorem subst_dbSubst_toDB_consistent :
--         ∀ (i : List (Term × Term)) (t : Term),
--             (do
--                 let t' ← subst? i t
--                 t'.toDB) =
--             (do
--                 let dt ← t.toDB
--                 dbSubst i dt) := by
--     intro i t
--     induction t generalizing i with
--     | var x T =>
--             simpa using subst_dbSubst_var_comm i x T
--     | const c T =>
--           sorry
--     | app s t ihS ihT =>
--             -- Use `subst_dbSubst_app_comm` (or directly IH + simp) to combine both subterms.
--             simpa using subst_dbSubst_app_comm i s t
--     | abs bvar body ih =>
--             -- Split on capture risk:
--             -- 1) no-capture: apply `subst_dbSubst_abs_no_capture`;
--             -- 2) capture and binder `.var x T`: use `subst_dbSubst_abs_capture_exists`
--             --    then close with `option_eq_of_exists_common`.
--             -- 3) capture and non-variable binder: both sides evaluate to `none`.
--             sorry
