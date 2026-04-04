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

private theorem captureRisk_app_left_of_false :
  ∀ (x : String) (T : HOLType) (s t : Term) (i : List (Term × Term)),
    captureRisk x T (.app s t) i = false ->
    captureRisk x T s i = false := by
  intro x T s t i hApp
  apply (captureRisk_eq_false_iff_forall_not x T s i).2
  intro p hp hPair
  have hAll := (captureRisk_eq_false_iff_forall_not x T (.app s t) i).1 hApp
  have hNot := hAll p hp
  apply hNot
  constructor
  · exact hPair.1
  · have hOr : p.fst.IsFreeVarIn s ∨ p.fst.IsFreeVarIn t := Or.inl hPair.2
    simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr

private theorem captureRisk_app_right_of_false :
  ∀ (x : String) (T : HOLType) (s t : Term) (i : List (Term × Term)),
    captureRisk x T (.app s t) i = false ->
    captureRisk x T t i = false := by
  intro x T s t i hApp
  apply (captureRisk_eq_false_iff_forall_not x T t i).2
  intro p hp hPair
  have hAll := (captureRisk_eq_false_iff_forall_not x T (.app s t) i).1 hApp
  have hNot := hAll p hp
  apply hNot
  constructor
  · exact hPair.1
  · have hOr : p.fst.IsFreeVarIn s ∨ p.fst.IsFreeVarIn t := Or.inr hPair.2
    simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr

private theorem captureRisk_abs_body_of_false_filtered :
  ∀ (y : String) (U : HOLType) (x : String) (T : HOLType) (t : Term) (i : List (Term × Term)),
    captureRisk y U (.abs x T t) i = false ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    captureRisk y U t i' = false := by
  intro y U x T t i hAbs i'
  apply (captureRisk_eq_false_iff_forall_not y U t i').2
  intro p hp hPair
  have hpMem : p ∈ i := (List.mem_filter.mp hp).1
  have hpNe : p.fst ≠ Term.var x T := by
    have hPred : (!decide (p.fst = Term.var x T)) = true := (List.mem_filter.mp hp).2
    by_contra hEq
    simp [hEq] at hPred
  have hAll := (captureRisk_eq_false_iff_forall_not y U (.abs x T t) i).1 hAbs
  have hNot := hAll p hpMem
  apply hNot
  have hFreeAbs : p.fst.IsFreeVarIn (.abs x T t) := by
    unfold Term.IsFreeVarIn Term.isFreeVarIn
    have hDec : decide (p.fst ≠ Term.var x T) = true := (decide_eq_true_iff).2 hpNe
    rw [hDec]
    simpa using hPair.2
  constructor
  · exact hPair.1
  · exact hFreeAbs

private theorem toDBAux_eq_of_ctxIdxEq_on_free :
  ∀ (t : Term) (ctx1 ctx2 : List (String × HOLType)),
    (∀ (x : String) (T : HOLType), (Term.var x T).IsFreeVarIn t →
      ctx1.idxOf? (x, T) = ctx2.idxOf? (x, T)) ->
    toDBAux ctx1 t = toDBAux ctx2 t := by
  intro t
  induction t with
  | var y U =>
      intro ctx1 ctx2 hIdx
      have hFree : (Term.var y U).IsFreeVarIn (Term.var y U) := by
        simp [Term.IsFreeVarIn, Term.isFreeVarIn]
      have hEq := hIdx y U hFree
      simp [toDBAux, hEq]
  | const c U =>
      intro ctx1 ctx2 _
      simp [toDBAux]
  | app s u ihs ihu =>
      intro ctx1 ctx2 hIdx
      have hIdxS :
          ∀ (x : String) (T : HOLType), (Term.var x T).IsFreeVarIn s ->
            ctx1.idxOf? (x, T) = ctx2.idxOf? (x, T) := by
        intro x T hFreeS
        apply hIdx x T
        have hOr : (Term.var x T).IsFreeVarIn s ∨ (Term.var x T).IsFreeVarIn u := Or.inl hFreeS
        simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr
      have hIdxU :
          ∀ (x : String) (T : HOLType), (Term.var x T).IsFreeVarIn u ->
            ctx1.idxOf? (x, T) = ctx2.idxOf? (x, T) := by
        intro x T hFreeU
        apply hIdx x T
        have hOr : (Term.var x T).IsFreeVarIn s ∨ (Term.var x T).IsFreeVarIn u := Or.inr hFreeU
        simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr
      simp [toDBAux, ihs ctx1 ctx2 hIdxS, ihu ctx1 ctx2 hIdxU]
  | abs n U b ih =>
      intro ctx1 ctx2 hIdx
      have hIdxBody :
          ∀ (x : String) (T : HOLType), (Term.var x T).IsFreeVarIn b ->
            ((n, U) :: ctx1).idxOf? (x, T) = ((n, U) :: ctx2).idxOf? (x, T) := by
        intro x T hFreeBody
        by_cases hEqVar : Term.var x T = Term.var n U
        · have hEqPair : (x, T) = (n, U) := by aesop
          cases hEqPair
          simp [List.idxOf?_cons]
        · have hFreeAbs : (Term.var x T).IsFreeVarIn (.abs n U b) := by
            unfold Term.IsFreeVarIn Term.isFreeVarIn
            have hDec : decide (Term.var x T ≠ Term.var n U) = true :=
              (decide_eq_true_iff).2 hEqVar
            rw [hDec]
            simpa using hFreeBody
          have hTail := hIdx x T hFreeAbs
          have hbeq : ((n, U) == (x, T)) = false := (beq_eq_false_iff_ne).2 (by aesop)
          simpa [List.idxOf?_cons, hbeq] using congrArg (Option.map Nat.succ) hTail
      simp [toDBAux, ih ((n, U) :: ctx1) ((n, U) :: ctx2) hIdxBody]

private theorem toDBAux_eq_toDB_of_no_free_ctx :
  ∀ (ctx : List (String × HOLType)) (t : Term),
    (∀ (x : String) (T : HOLType), (x, T) ∈ ctx -> ¬(Term.var x T).IsFreeVarIn t) ->
    toDBAux ctx t = t.toDB := by
  intro ctx t hNoFree
  have hEqIdx :
      ∀ (x : String) (T : HOLType), (Term.var x T).IsFreeVarIn t ->
        ctx.idxOf? (x, T) = ([] : List (String × HOLType)).idxOf? (x, T) := by
    intro x T hFree
    have hNotMem : (x, T) ∉ ctx := by
      intro hMem
      exact (hNoFree x T hMem) hFree
    have hNone : ctx.idxOf? (x, T) = none :=
      (List.idxOf?_eq_none_iff (l := ctx) (a := (x, T))).2 hNotMem
    simp [hNone]
  simpa [Term.toDB] using toDBAux_eq_of_ctxIdxEq_on_free t ctx [] hEqIdx

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

theorem SubstOk.filter : ∀ (i : List (Term × Term)) (f : Term × Term → Bool),
  SubstOk i → SubstOk (i.filter f)
    := by
  intro i f hOk v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

private theorem dbSubst_filter_shadowed_lookup :
  ∀ (i : List (Term × Term)) (x y : String) (T U : HOLType),
    Term.var y U ≠ Term.var x T ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    dbSubst i (DBTerm.fvar y U) = dbSubst i' (DBTerm.fvar y U) := by
  intro l x y T U hneq
  have hPredEq :
    ∀ t, (!decide (t = Term.var x T) && decide (t = Term.var y U)) = decide (t = Term.var y U) := by
    intro t
    by_cases hy : t = Term.var y U
    · have hxFalse : decide (t = Term.var x T) = false := by
        apply (decide_eq_false_iff_not).2
        intro hx
        have hEq : Term.var y U = Term.var x T := by aesop
        exact hneq hEq
      have hdy : decide (t = Term.var y U) = true := (decide_eq_true_iff).2 hy
      simp [hdy, hxFalse]
    · simp [hy]
  simp [dbSubst, List.find?_filter, hPredEq]

private theorem dbSubst_filter_shadowed_ctx :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType)
    (ctx : List (String × HOLType)) (t : Term),
    (x, T) ∈ ctx ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    dbSubst i (toDBAux ctx t) = dbSubst i' (toDBAux ctx t) := by
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

private theorem subst_toDBAux_comm_abs_capture_bridge :
  ∀ (ctx : List (String × HOLType)) (i : List (Term × Term))
    (x : String) (T : HOLType) (t : Term),
    SubstOk i ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    captureRisk x T t i' = true ->
    let fresh := generateVariant (subst i' t) x T
    toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') t)
      = dbSubst i (toDBAux ((x, T) :: ctx) t) := by
  intro ctx i x T t hOk i' hCap fresh
  sorry

private theorem subst_toDBAux_comm :
  ∀ (ctx : List (String × HOLType)) (i : List (Term × Term)) (body : Term),
    SubstOk i ->
    (∀ (x : String) (T : HOLType), (x, T) ∈ ctx →
      captureRisk x T body i = false ∧ i.find? (fun p => p.fst = Term.var x T) = none) →
    toDBAux ctx (subst i body) = dbSubst i (toDBAux ctx body) := by
  intro ctx i body hOk hNoCap
  induction body generalizing ctx i with
  | var y U =>
      cases hidx : ctx.idxOf? (y, U) with
      | some n =>
          have hMem : (y, U) ∈ ctx := by
            rcases (List.idxOf?_eq_some_iff (l := ctx) (a := (y, U)) (i := n)).1 hidx with
              ⟨hn, hget, _⟩
            simpa [hget] using (List.getElem_mem (l := ctx) (n := n) hn)
          have hNoFind : i.find? (fun p => p.fst = Term.var y U) = none := (hNoCap y U hMem).2
          simp [subst, dbSubst, toDBAux, hidx, hNoFind]
      | none =>
          cases hfind : i.find? (fun p => p.fst = Term.var y U) with
          | none => simp [subst, dbSubst, toDBAux, hidx, hfind]
          | some p =>
              rcases p with ⟨v, t⟩
              have hClosedRhs : toDBAux ctx t = t.toDB := by
                have hMem : (v, t) ∈ i := List.mem_of_find?_eq_some hfind
                have hPred : decide (v = Term.var y U) = true :=
                  (List.find?_eq_some_iff_getElem.mp hfind).1
                have hv : v = Term.var y U := (decide_eq_true_iff).1 hPred
                subst hv
                apply toDBAux_eq_toDB_of_no_free_ctx
                intro x T hctx hFree
                have hRiskFalse : captureRisk x T (Term.var y U) i = false := (hNoCap x T hctx).1
                have hAll := (captureRisk_eq_false_iff_forall_not x T (Term.var y U) i).1 hRiskFalse
                have hNot := hAll (Term.var y U, t) hMem
                apply hNot
                constructor
                · exact hFree
                · simp [Term.IsFreeVarIn, Term.isFreeVarIn]
              simp [subst, dbSubst, toDBAux, hidx, hfind, hClosedRhs]
  | const c U => simp [subst, dbSubst, toDBAux]
  | app s t ihs iht =>
      have hCtxS :
          ∀ (x : String) (T : HOLType), (x, T) ∈ ctx →
            captureRisk x T s i = false ∧ i.find? (fun p => p.fst = Term.var x T) = none := by
        intro x T hmem
        have hAll := hNoCap x T hmem
        refine ⟨?_, hAll.2⟩
        exact captureRisk_app_left_of_false x T s t i hAll.1
      have hCtxT :
          ∀ (x : String) (T : HOLType), (x, T) ∈ ctx →
            captureRisk x T t i = false ∧ i.find? (fun p => p.fst = Term.var x T) = none := by
        intro x T hmem
        have hAll := hNoCap x T hmem
        refine ⟨?_, hAll.2⟩
        exact captureRisk_app_right_of_false x T s t i hAll.1
      have hs := ihs ctx i hOk hCtxS
      have ht := iht ctx i hOk hCtxT
      simp [subst, toDBAux, dbSubst, hs, ht]
  | abs x T t ih =>
      set i' := i.filter (fun p => !decide (p.fst = Term.var x T))
      have hOk' : SubstOk i' := SubstOk.filter i (fun p => !decide (p.fst = Term.var x T)) hOk
      by_cases hCap : captureRisk x T t i' = true
      · -- TODO: capture branch requires alpha/renaming bridge under extended context.
        simp only [subst, hCap, ↓reduceIte, toDBAux, dbSubst, DBTerm.abs.injEq, true_and, i']
        set fresh := generateVariant (subst i' t) x T
        simpa [fresh] using subst_toDBAux_comm_abs_capture_bridge ctx i x T t hOk (by simpa [i'] using hCap)
      · have hShadow :
            dbSubst i (toDBAux ((x, T) :: ctx) t) = dbSubst i' (toDBAux ((x, T) :: ctx) t) := by
          simpa [i'] using dbSubst_filter_shadowed_ctx i x T ((x, T) :: ctx) t (by simp)
        simp only [subst, hCap, Bool.false_eq_true, ↓reduceIte, toDBAux, dbSubst, DBTerm.abs.injEq,
          true_and, i']
        calc
            toDBAux ((x, T) :: ctx) (subst i' t)
          = dbSubst i' (toDBAux ((x, T) :: ctx) t) := by
              apply ih
              · exact hOk'
              · intro y U hmem
                cases hmem with
                | head => constructor <;> aesop
                | tail _ hmemTail =>
                  have hOrig := hNoCap y U hmemTail
                  constructor
                  · simpa [i'] using
                      captureRisk_abs_body_of_false_filtered y U x T t i hOrig.1
                  · aesop
        _ = dbSubst i (toDBAux ((x, T) :: ctx) t) := by
              simpa using hShadow.symm

/-- abstraction branch when no capture risk. -/
private theorem subst_toDB_comm_abs_no_capture :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    SubstOk i ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    captureRisk x T body i' = false ->
    toDBAux [(x, T)] (subst i' body) = dbSubst i (toDBAux [(x, T)] body) := by
  intro i x T body hOk i' hNoCap
  have hShadow : dbSubst i (toDBAux [(x, T)] body) = dbSubst i' (toDBAux [(x, T)] body) :=
    dbSubst_filter_shadowed_ctx i x T [(x, T)] body (by simp)
  calc
      toDBAux [(x, T)] (subst i' body)
    = dbSubst i' (toDBAux [(x, T)] body) := by
        apply subst_toDBAux_comm
        · apply SubstOk.filter
          exact hOk
        · aesop
  _ = dbSubst i (toDBAux [(x, T)] body) := by aesop

/-- use alpha_debrujin to close the capture branch. -/
private theorem subst_toDB_comm_abs_capture :
  ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
    SubstOk i ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    captureRisk x T body i' = true ->
    let fresh := generateVariant (subst i' body) x T
    toDBAux [(fresh, T)] (subst ((Term.var x T, Term.var fresh T) :: i') body)
      = dbSubst i (toDBAux [(x, T)] body) := by
  intro i x T body hOk i' hCap
  let fresh := generateVariant (subst i' body) x T
  simpa [fresh] using
    subst_toDBAux_comm_abs_capture_bridge [] i x T body hOk (by simpa [i'] using hCap)

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
        = DBTerm.app (subst i s).toDB (subst i t).toDB := by exact hSubstApp
      _ = DBTerm.app (dbSubst i s.toDB) (dbSubst i t.toDB) := by aesop
      _ = dbSubst i (Term.app s t).toDB := by aesop
  | abs x T body ih =>
      simp only [Term.toDB, subst, toDBAux, dbSubst]
      set i' := i.filter (fun p ↦ !decide (p.fst = Term.var x T))
      set fresh := generateVariant (subst i' body) x T
      by_cases hCap : captureRisk x T body i' = true
      · simp only [hCap, ↓reduceIte, toDBAux, DBTerm.abs.injEq, true_and]
        apply subst_toDB_comm_abs_capture
        · exact hOk
        · simpa [i'] using hCap
      · simp only [hCap, Bool.false_eq_true, ↓reduceIte, toDBAux, DBTerm.abs.injEq, true_and]
        apply subst_toDB_comm_abs_no_capture
        · exact hOk
        · simpa [i'] using hCap
