import HotaruKernel.Type
import HotaruKernel.Term
import HotaruKernel.Alpha
import HotaruKernel.DBTerm
import Mathlib.Data.List.Defs
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
        have ⟨hx, hT⟩ : x = y ∧ T = Ty := by
          unfold Term.IsFreeVarIn Term.isFreeVarIn at hfree
          aesop
        subst hx hT
        simp [Term.maxVarNameLen]
    | const c Ty =>
        intro x T hfree
        simp [Term.IsFreeVarIn, Term.isFreeVarIn] at hfree
    | app s t ihs iht =>
        intro x T hfree
        unfold Term.IsFreeVarIn Term.isFreeVarIn at hfree
        simp only [Bool.or_eq_true] at hfree
        rcases hfree with hs | ht
        · exact Nat.le_trans (ihs x T hs) (Nat.le_max_left s.maxVarNameLen t.maxVarNameLen)
        · exact Nat.le_trans (iht x T ht) (Nat.le_max_right s.maxVarNameLen t.maxVarNameLen)
    | abs n Ty t ih =>
        intro x T hfree
        have ht : (Term.var x T).isFreeVarIn t = true := by
          unfold Term.IsFreeVarIn Term.isFreeVarIn at hfree
          aesop
        exact Nat.le_trans (ih x T ht) (Nat.le_max_right (String.length n) t.maxVarNameLen)
  intro t x T hlen hfree
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
    (k best : Nat) → variantFreshAt term baseName ty best →
      {n : Nat // variantFreshAt term baseName ty n}
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
def generateVariant (t : Term) (baseName : String) (ty : HOLType) : String :=
  let bound := t.maxVarNameLen + 1
  let hbound : variantFreshAt t baseName ty bound := by
    apply varNotFreeOfNameLengthGt
    have h1 : t.maxVarNameLen < t.maxVarNameLen + 1 := Nat.lt_succ_self _
    have h2 : t.maxVarNameLen + 1 ≤ String.length (variantCandidate baseName bound) := by
      simp [bound, variantCandidate, Nat.le_add_left (t.maxVarNameLen + 1) (String.length baseName)]
    exact Nat.lt_of_lt_of_le h1 h2
  let best := chooseMinFreshSuffix t baseName ty bound bound hbound
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

private theorem captureRisk_eq_true_iff_exists :
  ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)),
    captureRisk x T body i = true ↔
      ∃ p ∈ i, (Term.var x T).IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body := by
  intro x T body i
  induction i with
  | nil =>
      simp [captureRisk]
  | cons p ps ih =>
      simp [captureRisk]

private theorem captureRisk_eq_false_iff_forall_not :
  ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)),
    captureRisk x T body i = false ↔
      ∀ p ∈ i, ¬((Term.var x T).IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body) := by
  intro x T body i
  constructor
  · intro hFalse p hp hPair
    have hTrue : captureRisk x T body i = true :=
      (captureRisk_eq_true_iff_exists x T body i).2 ⟨p, hp, hPair⟩
    simp [hFalse] at hTrue
  · intro hNoPair
    by_cases hTrue : captureRisk x T body i = true
    · rcases (captureRisk_eq_true_iff_exists x T body i).1 hTrue with ⟨p, hp, hPair⟩
      exact False.elim ((hNoPair p hp) hPair)
    · cases hVal : captureRisk x T body i with
      | false => rfl
      | true =>
          exfalso
          exact hTrue hVal

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
  intro i bvar hOk v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

private theorem dbSubst_filter_shadowed_predEq :
  ∀ (x y : String) (T U : HOLType) (a : Term × Term),
    Term.var y U ≠ Term.var x T ->
    (!decide (a.fst = Term.var x T) && decide (a.fst = Term.var y U)) = decide (a.fst = Term.var y U)
    := by
  intro x y T U a hneq
  by_cases hy : a.fst = Term.var y U
  · have hxFalse : decide (a.fst = Term.var x T) = false := by
      apply (decide_eq_false_iff_not).2
      intro hx
      have hEq : Term.var y U = Term.var x T := by aesop
      exact hneq hEq
    have hdy : decide (a.fst = Term.var y U) = true := (decide_eq_true_iff).2 hy
    simp [hdy, hxFalse]
  · simp [hy]

private theorem dbSubst_filter_shadowed_findEq :
  ∀ (l : List (Term × Term)) (x y : String) (T U : HOLType),
    Term.var y U ≠ Term.var x T ->
    List.find? (fun p => decide (p.fst = Term.var y U)) l =
      List.find? (fun a => !decide (a.fst = Term.var x T) && decide (a.fst = Term.var y U)) l := by
  intro l x y T U hneq
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.find?, dbSubst_filter_shadowed_predEq x y T U a hneq, ih]

private theorem dbSubst_filter_shadowed_lookup :
  ∀ (l : List (Term × Term)) (x y : String) (T U : HOLType),
    Term.var y U ≠ Term.var x T ->
    dbSubst l (DBTerm.fvar y U) =
      dbSubst (l.filter (fun p => !decide (p.fst = Term.var x T))) (DBTerm.fvar y U) := by
  intro l x y T U hneq
  simp [dbSubst, List.find?_filter, dbSubst_filter_shadowed_predEq x y T U _ hneq]

private theorem dbSubst_filter_shadowed_ctx :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType)
    (ctx : List (String × HOLType)) (t : Term),
    (x, T) ∈ ctx ->
    dbSubst i (toDBAux ctx t) =
      dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) (toDBAux ctx t) := by
  intro i x T ctx t hmem
  induction t generalizing ctx with
  | var y U =>
      cases hidx : ctx.idxOf? (y, U) with
      | some n =>
          simp [toDBAux, dbSubst, hidx]
      | none =>
          have hNotMem : (y, U) ∉ ctx :=
            (List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).1 hidx
          have hneq : Term.var y U ≠ Term.var x T := by aesop
          simpa [toDBAux, dbSubst, hidx] using dbSubst_filter_shadowed_lookup i x y T U hneq
  | const c U =>
      simp [toDBAux, dbSubst]
  | app s t ihs iht =>
      have hs := ihs ctx hmem
      have ht := iht ctx hmem
      simp [toDBAux, dbSubst, hs, ht]
  | abs y U t ih =>
      have hmem' : (x, T) ∈ ((y, U) :: ctx) := List.mem_cons_of_mem _ hmem
      have ht := ih ((y, U) :: ctx) hmem'
      simpa [toDBAux, dbSubst] using ht

/-- removing substitutions for the bound variable does not change dbSubst on a bound body. -/
private theorem dbSubst_filter_shadowed_on_abs :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    dbSubst i (Term.abs x T body).toDB =
      dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) (Term.abs x T body).toDB := by
  intro i x T body
  have hBody :
      dbSubst i (toDBAux [(x, T)] body) =
        dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) (toDBAux [(x, T)] body) :=
    dbSubst_filter_shadowed_ctx i x T [(x, T)] body (by simp)
  simpa [Term.toDB, dbSubst] using congrArg (DBTerm.abs T) hBody

/-- abstraction branch when no capture risk. -/
private theorem subst_toDB_comm_abs_no_capture :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    SubstOk i ->
    captureRisk x T body (i.filter (fun p => !decide (p.fst = Term.var x T))) = false ->
    (subst i (Term.abs x T body)).toDB = dbSubst i (Term.abs x T body).toDB := by
  intro i x T body hOk hNoCap
  sorry

/-- capture branch gives alpha-equivalent abstractions after renaming. -/
private theorem subst_abs_capture_alpha :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    SubstOk i ->
    captureRisk x T body (i.filter (fun p => !decide (p.fst = Term.var x T))) = true ->
    AlphaEqv
      (subst i (Term.abs x T body))
      (Term.abs
        (generateVariant (subst (i.filter (fun p => !decide (p.fst = Term.var x T))) body) x T)
        T
        (subst
          ((Term.var x T,
            Term.var (generateVariant (subst (i.filter (fun p => !decide (p.fst = Term.var x T))) body) x T) T)
            :: i.filter (fun p => !decide (p.fst = Term.var x T)))
          body)) := by
  sorry

/-- use alpha_debrujin to close the capture branch. -/
private theorem subst_toDB_comm_abs_capture :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    SubstOk i ->
    captureRisk x T body (i.filter (fun p => !decide (p.fst = Term.var x T))) = true ->
    (subst i (Term.abs x T body)).toDB = dbSubst i (Term.abs x T body).toDB := by
  intro i x T body hOk hCap
  let fresh := generateVariant (subst (i.filter (fun p => !decide (p.fst = Term.var x T))) body) x T
  have hCore :
      (Term.abs fresh T
        (subst
          ((Term.var x T, Term.var fresh T) :: i.filter (fun p => !decide (p.fst = Term.var x T)))
          body)).toDB
        = dbSubst i (Term.abs x T body).toDB := by
    sorry
  simpa [subst, hCap, fresh] using hCore

/-- split abstraction branch by captureRisk. -/
private theorem subst_toDB_comm_abs_split :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    SubstOk i ->
    (subst i (Term.abs x T body)).toDB = dbSubst i (Term.abs x T body).toDB := by
  intro i x T body hOk
  by_cases hCap : captureRisk x T body (i.filter (fun p => !decide (p.fst = Term.var x T))) = true
  · exact subst_toDB_comm_abs_capture i x T body hOk hCap
  · have hNoCap : captureRisk x T body (i.filter (fun p => !decide (p.fst = Term.var x T))) = false
        := by
      cases hVal : captureRisk x T body (i.filter (fun p => !decide (p.fst = Term.var x T))) <;>
        simp [hVal] at hCap ⊢
    exact subst_toDB_comm_abs_no_capture i x T body hOk hNoCap

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
      have hSubstApp : (subst i (Term.app s t)).toDB = DBTerm.app (subst i s).toDB (subst i t).toDB
        := by rfl
      have hToDBApp : (Term.app s t).toDB = DBTerm.app s.toDB t.toDB := by rfl
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
      apply subst_toDB_comm_abs_split
      trivial
