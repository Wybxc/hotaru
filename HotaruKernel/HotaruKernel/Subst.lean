import HotaruKernel.Type
import HotaruKernel.Term
import HotaruKernel.Alpha
import HotaruKernel.DBTerm
import Mathlib.Data.List.Defs
import Aesop

set_option linter.style.longLine false

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

@[simp] def Term.hasName : String -> Term -> Bool
| x, .var y _ => decide (x = y)
| _, .const _ _ => false
| x, .app s u => s.hasName x || u.hasName x
| x, .abs y _ body => decide (x = y) || body.hasName x

@[simp] def Term.HasName (x : String) (t : Term) : Prop :=
  t.hasName x = true

instance (x : String) (t : Term) : Decidable (Term.HasName x t) := by
  unfold Term.HasName
  infer_instance

/-- Maximum variable-name length appearing in a term. -/
def Term.maxVarNameLen : Term → Nat
| .var x _ => String.length x
| .const _ _ => 0
| .app s t => Nat.max s.maxVarNameLen t.maxVarNameLen
| .abs n _ t => Nat.max (String.length n) t.maxVarNameLen

theorem nameNotInOfNameLengthGt :
  ∀ (t : Term) (x : String),
    t.maxVarNameLen < String.length x → ¬Term.HasName x t := by
  have hasNameLen_le :
      ∀ (t : Term) (x : String),
        Term.HasName x t -> String.length x ≤ t.maxVarNameLen := by
    intro t
    induction t with
    | var y Ty =>
        intro x hHas
        have hx : x = y := by
          unfold Term.HasName Term.hasName at hHas
          exact (decide_eq_true_iff).1 hHas
        subst hx
        simp [Term.maxVarNameLen]
    | const c Ty =>
        intro x hHas
        simp [Term.HasName, Term.hasName] at hHas
    | app s t ihs iht =>
        intro x hHas
        unfold Term.HasName Term.hasName at hHas
        have hOr : s.hasName x = true ∨ t.hasName x = true := by
          simpa [Bool.or_eq_true] using hHas
        rcases hOr with hs | ht
        · exact Nat.le_trans (ihs x hs) (Nat.le_max_left s.maxVarNameLen t.maxVarNameLen)
        · exact Nat.le_trans (iht x ht) (Nat.le_max_right s.maxVarNameLen t.maxVarNameLen)
    | abs n Ty t ih =>
        intro x hHas
        unfold Term.HasName Term.hasName at hHas
        have hOr : decide (x = n) = true ∨ t.hasName x = true := by
          simpa [Bool.or_eq_true] using hHas
        rcases hOr with hx | ht
        · have hEq : x = n := (decide_eq_true_iff).1 hx
          subst hEq
          exact Nat.le_max_left (String.length x) t.maxVarNameLen
        · exact Nat.le_trans (ih x ht) (Nat.le_max_right (String.length n) t.maxVarNameLen)
  intro t x hlen hHas
  have hle : String.length x ≤ t.maxVarNameLen := hasNameLen_le t x hHas
  exact (Nat.not_lt_of_ge hle) hlen

private theorem hasName_of_isFreeVarIn :
  ∀ (x : String) (T : HOLType) (t : Term),
    (Term.var x T).IsFreeVarIn t -> Term.HasName x t := by
  intro x T t hFree
  induction t with
  | var y U =>
      have hEq : Term.var x T = Term.var y U := by
        unfold Term.IsFreeVarIn Term.isFreeVarIn at hFree
        exact (decide_eq_true_iff).1 hFree
      have hx : x = y := by aesop
      subst hx
      simp [Term.HasName, Term.hasName]
  | const c U =>
      simp [Term.IsFreeVarIn, Term.isFreeVarIn] at hFree
  | app s u ihs ihu =>
      unfold Term.IsFreeVarIn Term.isFreeVarIn at hFree
      have hOr : (Term.var x T).isFreeVarIn s = true ∨ (Term.var x T).isFreeVarIn u = true := by
        simpa [Bool.or_eq_true] using hFree
      rcases hOr with hs | hu
      · have hsName : Term.HasName x s := ihs hs
        unfold Term.HasName Term.hasName
        have hOrName : Term.hasName x s = true ∨ Term.hasName x u = true := Or.inl hsName
        simpa [Bool.or_eq_true] using hOrName
      · have huName : Term.HasName x u := ihu hu
        unfold Term.HasName Term.hasName
        have hOrName : Term.hasName x s = true ∨ Term.hasName x u = true := Or.inr huName
        simpa [Bool.or_eq_true] using hOrName
  | abs y U body ih =>
      have hBody : (Term.var x T).IsFreeVarIn body := by
        unfold Term.IsFreeVarIn Term.isFreeVarIn at hFree
        aesop
      have hBodyName : Term.HasName x body := ih hBody
      unfold Term.HasName Term.hasName
      have hOrName : decide (x = y) = true ∨ Term.hasName x body = true := Or.inr hBodyName
      simpa [Bool.or_eq_true] using hOrName

private theorem not_isFreeVarIn_of_noName :
  ∀ (x : String) (T : HOLType) (t : Term),
    ¬Term.HasName x t -> ¬(Term.var x T).IsFreeVarIn t := by
  intro x T t hNoName hFree
  exact hNoName (hasName_of_isFreeVarIn x T t hFree)

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
private def variantFreshAt (term : Term) (baseName : String) (_ty : HOLType) (k : Nat) : Prop :=
  ¬Term.HasName (variantCandidate baseName k) term

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
    apply nameNotInOfNameLengthGt
    have h1 : t.maxVarNameLen < t.maxVarNameLen + 1 := Nat.lt_succ_self _
    have h2 : t.maxVarNameLen + 1 ≤ String.length (variantCandidate baseName bound) := by
      simp [bound, variantCandidate, Nat.le_add_left (t.maxVarNameLen + 1) (String.length baseName)]
    exact Nat.lt_of_lt_of_le h1 h2
  let best := chooseMinFreshSuffix t baseName ty bound bound hbound
  variantCandidate baseName best.1

theorem VariantNoName : ∀ t x T, ¬Term.HasName (generateVariant t x T) t := by
  intros t x T
  unfold generateVariant
  have hbound : variantFreshAt t x T (t.maxVarNameLen + 1) := by
    apply nameNotInOfNameLengthGt
    have h1 : t.maxVarNameLen < t.maxVarNameLen + 1 := Nat.lt_succ_self _
    have h2 : t.maxVarNameLen + 1 ≤ String.length (variantCandidate x (t.maxVarNameLen + 1)) := by
      simp [variantCandidate, Nat.le_add_left (t.maxVarNameLen + 1) (String.length x)]
    exact Nat.lt_of_lt_of_le h1 h2
  let best := chooseMinFreshSuffix t x T (t.maxVarNameLen + 1) (t.maxVarNameLen + 1) hbound
  simpa [variantFreshAt] using best.2

theorem VariantFresh : ∀ t x T, ¬(Term.var (generateVariant t x T) T).IsFreeVarIn t
    := by
  intros t x T
  exact not_isFreeVarIn_of_noName (generateVariant t x T) T t (VariantNoName t x T)

/-- Term variable substitution: applies a list of term substitutions to a term -/
private def captureRisk (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)) : Bool :=
  i.any (fun (t, t') => decide ((Term.var x T).IsFreeVarIn t' ∧ t.IsFreeVarIn body))

private theorem captureRisk_true :
  ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)),
    captureRisk x T body i = true ↔
      ∃ p ∈ i, (Term.var x T).IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body := by
  intro x T body i
  induction i <;> simp [captureRisk]

private theorem captureRisk_false :
  ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)),
    captureRisk x T body i = false ↔
      ∀ p ∈ i, ¬((Term.var x T).IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body) := by
  intro x T body i
  constructor
  · intro hFalse p hp hPair
    have hTrue : captureRisk x T body i = true :=
      (captureRisk_true x T body i).2 ⟨p, hp, hPair⟩
    simp [hFalse] at hTrue
  · intro hNoPair
    by_cases hTrue : captureRisk x T body i = true
    · rcases (captureRisk_true x T body i).1 hTrue with ⟨p, hp, hPair⟩
      exact False.elim ((hNoPair p hp) hPair)
    · cases hVal : captureRisk x T body i with
      | false => rfl
      | true =>
          exfalso
          exact hTrue hVal

private theorem captureRisk_false_filter :
  ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term))
    (f : Term × Term → Bool),
    captureRisk x T body i = false ->
    captureRisk x T body (i.filter f) = false := by
  intro x T body i f hFalse
  apply (captureRisk_false x T body (i.filter f)).2
  intro p hp hPair
  have hpMem : p ∈ i := (List.mem_filter.mp hp).1
  have hAll := (captureRisk_false x T body i).1 hFalse
  exact (hAll p hpMem) hPair

private theorem captureRisk_false_fun :
  ∀ (x : String) (T : HOLType) (s t : Term) (i : List (Term × Term)),
    captureRisk x T (.app s t) i = false ->
    captureRisk x T s i = false := by
  intro x T s t i hApp
  apply (captureRisk_false x T s i).2
  intro p hp hPair
  have hAll := (captureRisk_false x T (.app s t) i).1 hApp
  have hNot := hAll p hp
  apply hNot
  constructor
  · exact hPair.1
  · have hOr : p.fst.IsFreeVarIn s ∨ p.fst.IsFreeVarIn t := Or.inl hPair.2
    simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr

private theorem captureRisk_false_arg :
  ∀ (x : String) (T : HOLType) (s t : Term) (i : List (Term × Term)),
    captureRisk x T (.app s t) i = false ->
    captureRisk x T t i = false := by
  intro x T s t i hApp
  apply (captureRisk_false x T t i).2
  intro p hp hPair
  have hAll := (captureRisk_false x T (.app s t) i).1 hApp
  have hNot := hAll p hp
  apply hNot
  constructor
  · exact hPair.1
  · have hOr : p.fst.IsFreeVarIn s ∨ p.fst.IsFreeVarIn t := Or.inr hPair.2
    simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr

private theorem captureRisk_true_fun_or_arg :
  ∀ (x : String) (T : HOLType) (s t : Term) (i : List (Term × Term)),
    captureRisk x T (.app s t) i = true ->
    captureRisk x T s i = true ∨ captureRisk x T t i = true := by
  intro x T s t i hApp
  rcases (captureRisk_true x T (.app s t) i).1 hApp with ⟨p, hp, hPair⟩
  have hSplit : p.1.IsFreeVarIn s ∨ p.1.IsFreeVarIn t := by
    unfold Term.IsFreeVarIn Term.isFreeVarIn at hPair
    simpa [Bool.or_eq_true] using hPair.2
  cases hSplit with
  | inl hs =>
      left
      exact (captureRisk_true x T s i).2 ⟨p, hp, ⟨hPair.1, hs⟩⟩
  | inr ht =>
      right
      exact (captureRisk_true x T t i).2 ⟨p, hp, ⟨hPair.1, ht⟩⟩

private theorem captureRisk_true_abs_body :
  ∀ (x y : String) (T U : HOLType) (t : Term) (i : List (Term × Term)),
    captureRisk x T (.abs y U t) i = true ->
    captureRisk x T t i = true := by
  intro x y T U t i hAbs
  rcases (captureRisk_true x T (.abs y U t) i).1 hAbs with ⟨p, hp, hPair⟩
  have hFreeBody : p.1.IsFreeVarIn t := by
    unfold Term.IsFreeVarIn Term.isFreeVarIn at hPair
    have hAnd : decide (p.1 ≠ Term.var y U) = true ∧ p.1.isFreeVarIn t = true := by
      simpa [Bool.and_eq_true] using hPair.2
    exact hAnd.2
  exact (captureRisk_true x T t i).2 ⟨p, hp, ⟨hPair.1, hFreeBody⟩⟩

private theorem captureRisk_false_body_abs :
  ∀ (x y : String) (T U : HOLType) (t : Term) (i : List (Term × Term)),
    captureRisk x T t i = false ->
    captureRisk x T (.abs y U t) i = false := by
  intro x y T U t i hBody
  apply (captureRisk_false x T (.abs y U t) i).2
  intro p hp hPair
  have hBodyAll := (captureRisk_false x T t i).1 hBody
  have hNot := hBodyAll p hp
  have hFreeBody : p.1.IsFreeVarIn t := by
    unfold Term.IsFreeVarIn Term.isFreeVarIn at hPair
    have hAnd : decide (p.1 ≠ Term.var y U) = true ∧ p.1.isFreeVarIn t = true := by
      simpa [Bool.and_eq_true] using hPair.2
    exact hAnd.2
  exact hNot ⟨hPair.1, hFreeBody⟩

private theorem not_free_in_app_fun :
  ∀ (v s t : Term), ¬v.IsFreeVarIn (.app s t) -> ¬v.IsFreeVarIn s := by
  intro v s t hNot hS
  apply hNot
  have hOr : v.IsFreeVarIn s ∨ v.IsFreeVarIn t := Or.inl hS
  simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr

private theorem not_free_in_app_arg :
  ∀ (v s t : Term), ¬v.IsFreeVarIn (.app s t) -> ¬v.IsFreeVarIn t := by
  intro v s t hNot hT
  apply hNot
  have hOr : v.IsFreeVarIn s ∨ v.IsFreeVarIn t := Or.inr hT
  simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hOr

private theorem not_hasName_in_app_fun :
  ∀ (x : String) (s t : Term), ¬Term.HasName x (Term.app s t) -> ¬Term.HasName x s := by
  intro x s t hNot hS
  apply hNot
  unfold Term.HasName Term.hasName
  have hOrName : Term.hasName x s = true ∨ Term.hasName x t = true := Or.inl hS
  simpa [Bool.or_eq_true] using hOrName

private theorem not_hasName_in_app_arg :
  ∀ (x : String) (s t : Term), ¬Term.HasName x (Term.app s t) -> ¬Term.HasName x t := by
  intro x s t hNot hT
  apply hNot
  unfold Term.HasName Term.hasName
  have hOrName : Term.hasName x s = true ∨ Term.hasName x t = true := Or.inr hT
  simpa [Bool.or_eq_true] using hOrName

private theorem not_hasName_in_abs :
  ∀ (x y : String) (U : HOLType) (t : Term),
    ¬Term.HasName x (Term.abs y U t) -> x ≠ y ∧ ¬Term.HasName x t := by
  intro x y U t hNot
  constructor
  · intro hEq
    apply hNot
    unfold Term.HasName Term.hasName
    simp [hEq]
  · intro hHas
    apply hNot
    unfold Term.HasName Term.hasName
    have hOrName : decide (x = y) = true ∨ Term.hasName x t = true := Or.inr hHas
    simpa [Bool.or_eq_true] using hOrName

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

private theorem subst_toDBAux_comm_capture_no_capture_child :
  ∀ (ctx : List (String × HOLType)) (i : List (Term × Term))
    (x : String) (T : HOLType) (child : Term) (fresh : String),
    SubstOk i ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    (∀ (y : String) (U : HOLType), (y, U) ∈ ctx →
      captureRisk y U child i' = false ∧ i'.find? (fun p => p.fst = Term.var y U) = none) ->
    captureRisk x T child i' = false ->
    ¬Term.HasName fresh (subst i' child) ->
    toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') child)
      = dbSubst i (toDBAux ((x, T) :: ctx) child) := by
  intro ctx i x T child fresh hOk i' hCtxNoCap hNoCap hFreshNoName
  induction child generalizing ctx i with
  | var y U =>
      cases hFind : i'.find? (fun p => p.fst = Term.var y U) with
      | none =>
          by_cases hEqXY : Term.var x T = Term.var y U
          · have hSubstHead :
              subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U) = Term.var fresh T := by
              simp [subst, hEqXY]
            have hEqPair : (y, U) = (x, T) := by aesop
            cases hEqPair
            simp [hSubstHead, toDBAux, dbSubst, List.idxOf?_cons]
          · have hneqYX : Term.var y U ≠ Term.var x T := by
              intro hEq
              exact hEqXY hEq.symm
            have hSubstHead :
              subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U) = Term.var y U := by
              simp [subst, hEqXY, hFind]
            have hSubstI' : subst i' (Term.var y U) = Term.var y U := by
              simp [subst, hFind]
            have hNoNameVar : ¬Term.HasName fresh (Term.var y U) := by
              simpa [hSubstI'] using hFreshNoName
            have hneqFY : fresh ≠ y := by
              intro hEq
              apply hNoNameVar
              unfold Term.HasName Term.hasName
              simpa [hEq]
            by_cases hyInCtx : (y, U) ∈ ctx
            · have hHeadBeqFresh : ((fresh, T) == (y, U)) = false :=
                (beq_eq_false_iff_ne).2 (by aesop)
              have hHeadBeqX : ((x, T) == (y, U)) = false :=
                (beq_eq_false_iff_ne).2 (by aesop)
              cases hIdx : ctx.idxOf? (y, U) with
              | none =>
                  exfalso
                  exact ((List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).1 hIdx) hyInCtx
              | some n =>
                  simp [hSubstHead, toDBAux, dbSubst, List.idxOf?_cons, hHeadBeqFresh, hHeadBeqX, hIdx]
            · have hTailNone : ctx.idxOf? (y, U) = none :=
                (List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).2 hyInCtx
              have hHeadBeqFresh : ((fresh, T) == (y, U)) = false :=
                (beq_eq_false_iff_ne).2 (by aesop)
              have hHeadBeqX : ((x, T) == (y, U)) = false :=
                (beq_eq_false_iff_ne).2 (by aesop)
              have hShadow : dbSubst i (DBTerm.fvar y U) = dbSubst i' (DBTerm.fvar y U) := by
                simpa [i'] using dbSubst_filter_shadowed_lookup i x y T U hneqYX
              have hDbI' : dbSubst i' (DBTerm.fvar y U) = DBTerm.fvar y U := by
                simp [dbSubst, hFind]
              calc
                  toDBAux ((fresh, T) :: ctx)
                      (subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U))
                = DBTerm.fvar y U := by
                    simp [hSubstHead, toDBAux, List.idxOf?_cons, hHeadBeqFresh, hTailNone]
              _ = dbSubst i' (DBTerm.fvar y U) := by simp [hDbI']
              _ = dbSubst i (DBTerm.fvar y U) := by simp [hShadow]
              _ = dbSubst i (toDBAux ((x, T) :: ctx) (Term.var y U)) := by
                    simp [toDBAux, List.idxOf?_cons, hHeadBeqX, hTailNone]
      | some p =>
          rcases p with ⟨v, rhs⟩
          have hMem : (v, rhs) ∈ i' := List.mem_of_find?_eq_some hFind
          have hPred : decide (v = Term.var y U) = true :=
            (List.find?_eq_some_iff_getElem.mp hFind).1
          have hv : v = Term.var y U := (decide_eq_true_iff).1 hPred
          subst hv
          by_cases hyInCtx : (y, U) ∈ ctx
          · have hNoFind : i'.find? (fun q => q.fst = Term.var y U) = none :=
              (hCtxNoCap y U hyInCtx).2
            rw [hNoFind] at hFind
            contradiction
          · have hKeep : (!decide ((Term.var y U) = Term.var x T)) = true :=
              (List.mem_filter.mp hMem).2
            have hneqYX : Term.var y U ≠ Term.var x T := by
              by_contra hEq
              simp [hEq] at hKeep
            have hneqXY : Term.var x T ≠ Term.var y U := by
              intro hEq
              exact hneqYX hEq.symm
            have hSubstI' : subst i' (Term.var y U) = rhs := by
              simp [subst, hFind]
            have hFreshNoFreeSubst : ¬(Term.var fresh T).IsFreeVarIn (subst i' (Term.var y U)) := by
              exact not_isFreeVarIn_of_noName fresh T (subst i' (Term.var y U)) hFreshNoName
            have hFreshNoFreeRhs : ¬(Term.var fresh T).IsFreeVarIn rhs := by
              simpa [hSubstI'] using hFreshNoFreeSubst
            have hCtxNoFreeRhs :
                ∀ (z : String) (V : HOLType), (z, V) ∈ ctx → ¬(Term.var z V).IsFreeVarIn rhs := by
              intro z V hz
              have hNoCapZ : captureRisk z V (Term.var y U) i' = false := (hCtxNoCap z V hz).1
              have hAll := (captureRisk_false z V (Term.var y U) i').1 hNoCapZ
              have hNot := hAll (Term.var y U, rhs) hMem
              intro hFree
              have hSelf : (Term.var y U).IsFreeVarIn (Term.var y U) := by
                simp [Term.IsFreeVarIn, Term.isFreeVarIn]
              exact hNot ⟨hFree, hSelf⟩
            have hLeftToDB :
                toDBAux ((fresh, T) :: ctx)
                    (subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U))
                  = rhs.toDB := by
              have hHeadNo : decide (Term.var x T = Term.var y U) = false :=
                (decide_eq_false_iff_not).2 hneqXY
              have hSubstHead :
                  subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U) = rhs := by
                have hHeadPredFalse :
                    ((fun q : Term × Term => q.fst = Term.var y U) (Term.var x T, Term.var fresh T)) = false := by
                  simpa using hHeadNo
                unfold subst
                rw [List.find?_cons]
                simp [hHeadPredFalse, hFind]
              have hClosed : toDBAux ((fresh, T) :: ctx) rhs = rhs.toDB := by
                apply toDBAux_eq_toDB_of_no_free_ctx
                intro z V hz
                cases hz with
                | head =>
                    simpa using hFreshNoFreeRhs
                | tail _ hzTail =>
                    exact hCtxNoFreeRhs z V hzTail
              simpa [hSubstHead] using hClosed
            have hToDBVar : toDBAux ((x, T) :: ctx) (Term.var y U) = DBTerm.fvar y U := by
              have hPairNe : (x, T) ≠ (y, U) := by
                intro hEq
                exact hneqYX (by aesop)
              have hHeadBeq : ((x, T) == (y, U)) = false := (beq_eq_false_iff_ne).2 hPairNe
              have hTailNone : ctx.idxOf? (y, U) = none :=
                (List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).2 hyInCtx
              have hIdxNone : ((x, T) :: ctx).idxOf? (y, U) = none := by
                simp [List.idxOf?_cons, hHeadBeq, hTailNone]
              simp [toDBAux, hIdxNone]
            have hShadow : dbSubst i (DBTerm.fvar y U) = dbSubst i' (DBTerm.fvar y U) := by
              simpa [i'] using dbSubst_filter_shadowed_lookup i x y T U hneqYX
            have hDbI' : dbSubst i' (DBTerm.fvar y U) = rhs.toDB := by
              simp [dbSubst, hFind]
            calc
                toDBAux ((fresh, T) :: ctx)
                    (subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U))
              = rhs.toDB := hLeftToDB
            _ = dbSubst i' (DBTerm.fvar y U) := by simp [hDbI']
            _ = dbSubst i (DBTerm.fvar y U) := by simp [hShadow]
            _ = dbSubst i (toDBAux ((x, T) :: ctx) (Term.var y U)) := by
              rw [hToDBVar]
  | const c U =>
      simp [subst, toDBAux, dbSubst]
  | app s u ihs ihu =>
      have hCtxNoCapS :
          ∀ (z : String) (V : HOLType), (z, V) ∈ ctx →
            captureRisk z V s i' = false ∧ i'.find? (fun p => p.fst = Term.var z V) = none := by
        intro z V hz
        have hAll := hCtxNoCap z V hz
        exact ⟨captureRisk_false_fun z V s u i' hAll.1, hAll.2⟩
      have hCtxNoCapU :
          ∀ (z : String) (V : HOLType), (z, V) ∈ ctx →
            captureRisk z V u i' = false ∧ i'.find? (fun p => p.fst = Term.var z V) = none := by
        intro z V hz
        have hAll := hCtxNoCap z V hz
        exact ⟨captureRisk_false_arg z V s u i' hAll.1, hAll.2⟩
      have hNoCapS : captureRisk x T s i' = false := captureRisk_false_fun x T s u i' hNoCap
      have hNoCapU : captureRisk x T u i' = false := captureRisk_false_arg x T s u i' hNoCap
      have hFreshNoNameS : ¬Term.HasName fresh (subst i' s) := by
        apply not_hasName_in_app_fun fresh (subst i' s) (subst i' u)
        simpa [subst] using hFreshNoName
      have hFreshNoNameU : ¬Term.HasName fresh (subst i' u) := by
        apply not_hasName_in_app_arg fresh (subst i' s) (subst i' u)
        simpa [subst] using hFreshNoName
      have hs := ihs ctx i hOk (by simpa [i'] using hCtxNoCapS) (by simpa [i'] using hNoCapS) hFreshNoNameS
      have hu := ihu ctx i hOk (by simpa [i'] using hCtxNoCapU) (by simpa [i'] using hNoCapU) hFreshNoNameU
      calc
          toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') (Term.app s u))
        = DBTerm.app
            (toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') s))
            (toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') u)) := by
              simp [subst, toDBAux]
      _ = DBTerm.app
            (dbSubst i (toDBAux ((x, T) :: ctx) s))
            (dbSubst i (toDBAux ((x, T) :: ctx) u)) := by
              simp [i', hs, hu]
      _ = dbSubst i (toDBAux ((x, T) :: ctx) (Term.app s u)) := by
              simp [toDBAux, dbSubst]
  | abs y U t ih =>
      sorry

private theorem subst_toDBAux_comm_capture :
  ∀ (ctx : List (String × HOLType)) (i : List (Term × Term))
    (x : String) (T : HOLType) (t : Term) (fresh : String),
    SubstOk i ->
    let i' := i.filter (fun p => !decide (p.fst = Term.var x T))
    (∀ (y : String) (U : HOLType), (y, U) ∈ ctx →
      captureRisk y U t i' = false ∧ i'.find? (fun p => p.fst = Term.var y U) = none) ->
    captureRisk x T t i' = true ->
    ¬Term.HasName fresh (subst i' t) ->
    toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') t)
      = dbSubst i (toDBAux ((x, T) :: ctx) t) := by
  intro ctx i x T t fresh hOk i' hCtxNoCap hCap hFreshNoName
  induction t generalizing ctx i with
  | var y U =>
      cases hFind : i'.find? (fun p => p.fst = Term.var y U) with
      | none =>
          have hRisk : captureRisk x T (Term.var y U) i' = true := hCap
          have hContra : False := by
            rcases (captureRisk_true x T (Term.var y U) i').1 hRisk with ⟨p, hp, hPair⟩
            have hFindNone := (List.find?_eq_none).1 hFind
            have hp1Eq : p.1 = Term.var y U := by
              unfold Term.IsFreeVarIn Term.isFreeVarIn at hPair
              exact (decide_eq_true_iff).1 hPair.2
            have hPredTrue : (fun q => decide (q.fst = Term.var y U)) p = true := by
              simp [hp1Eq]
            exact (hFindNone p hp) hPredTrue
          exact False.elim hContra
      | some p =>
          rcases p with ⟨v, rhs⟩
          have hMem : (v, rhs) ∈ i' := List.mem_of_find?_eq_some hFind
          have hPred : decide (v = Term.var y U) = true :=
            (List.find?_eq_some_iff_getElem.mp hFind).1
          have hv : v = Term.var y U := (decide_eq_true_iff).1 hPred
          subst hv
          have hRisk : captureRisk x T (Term.var y U) i' = true := hCap
          by_cases hyInCtx : (y, U) ∈ ctx
          · have hNoFind : i'.find? (fun q => q.fst = Term.var y U) = none :=
              (hCtxNoCap y U hyInCtx).2
            rw [hNoFind] at hFind
            contradiction
          · have hKeep : (!decide ((Term.var y U) = Term.var x T)) = true :=
              (List.mem_filter.mp hMem).2
            have hneqYX : Term.var y U ≠ Term.var x T := by
              by_contra hEq
              simp [hEq] at hKeep
            have hneqXY : Term.var x T ≠ Term.var y U := by
              intro hEq
              exact hneqYX hEq.symm
            have hSubstI' : subst i' (Term.var y U) = rhs := by
              simp [subst, hFind]
            have hFreshNoFreeSubst : ¬(Term.var fresh T).IsFreeVarIn (subst i' (Term.var y U)) := by
              exact not_isFreeVarIn_of_noName fresh T (subst i' (Term.var y U)) hFreshNoName
            have hFreshNoFreeRhs : ¬(Term.var fresh T).IsFreeVarIn rhs := by
              simpa [hSubstI'] using hFreshNoFreeSubst
            have hCtxNoFreeRhs :
                ∀ (z : String) (V : HOLType), (z, V) ∈ ctx → ¬(Term.var z V).IsFreeVarIn rhs := by
              intro z V hz
              have hNoCapZ : captureRisk z V (Term.var y U) i' = false := (hCtxNoCap z V hz).1
              have hAll := (captureRisk_false z V (Term.var y U) i').1 hNoCapZ
              have hNot := hAll (Term.var y U, rhs) hMem
              intro hFree
              have hSelf : (Term.var y U).IsFreeVarIn (Term.var y U) := by
                simp [Term.IsFreeVarIn, Term.isFreeVarIn]
              exact hNot ⟨hFree, hSelf⟩
            have hLeftToDB :
                toDBAux ((fresh, T) :: ctx)
                    (subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U))
                  = rhs.toDB := by
              have hHeadNo : decide (Term.var x T = Term.var y U) = false :=
                (decide_eq_false_iff_not).2 hneqXY
              have hSubstHead :
                  subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U) = rhs := by
                have hHeadPredFalse :
                    ((fun q : Term × Term => q.fst = Term.var y U) (Term.var x T, Term.var fresh T)) = false := by
                  simpa using hHeadNo
                unfold subst
                rw [List.find?_cons]
                simp [hHeadPredFalse, hFind]
              have hClosed : toDBAux ((fresh, T) :: ctx) rhs = rhs.toDB := by
                apply toDBAux_eq_toDB_of_no_free_ctx
                intro z V hz
                cases hz with
                | head =>
                    simpa using hFreshNoFreeRhs
                | tail _ hzTail =>
                    exact hCtxNoFreeRhs z V hzTail
              simpa [hSubstHead] using hClosed
            have hToDBVar : toDBAux ((x, T) :: ctx) (Term.var y U) = DBTerm.fvar y U := by
              have hPairNe : (x, T) ≠ (y, U) := by
                intro hEq
                exact hneqYX (by aesop)
              have hHeadBeq : ((x, T) == (y, U)) = false := (beq_eq_false_iff_ne).2 hPairNe
              have hTailNone : ctx.idxOf? (y, U) = none :=
                (List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).2 hyInCtx
              have hIdxNone : ((x, T) :: ctx).idxOf? (y, U) = none := by
                simp [List.idxOf?_cons, hHeadBeq, hTailNone]
              simp [toDBAux, hIdxNone]
            have hShadow : dbSubst i (DBTerm.fvar y U) = dbSubst i' (DBTerm.fvar y U) := by
              simpa [i'] using dbSubst_filter_shadowed_lookup i x y T U hneqYX
            have hDbI' : dbSubst i' (DBTerm.fvar y U) = rhs.toDB := by
              simp [dbSubst, hFind]
            calc
                toDBAux ((fresh, T) :: ctx)
                    (subst ((Term.var x T, Term.var fresh T) :: i') (Term.var y U))
              = rhs.toDB := hLeftToDB
            _ = dbSubst i' (DBTerm.fvar y U) := by simp [hDbI']
            _ = dbSubst i (DBTerm.fvar y U) := by simp [hShadow]
            _ = dbSubst i (toDBAux ((x, T) :: ctx) (Term.var y U)) := by
              rw [hToDBVar]
  | const c U =>
      have hFalse : captureRisk x T (Term.const c U) i' = false := by
        simp [captureRisk]
      simp [hFalse] at hCap
  | app s u ihs ihu =>
      have hCtxNoCapS :
          ∀ (z : String) (V : HOLType), (z, V) ∈ ctx →
            captureRisk z V s i' = false ∧ i'.find? (fun p => p.fst = Term.var z V) = none := by
        intro z V hz
        have hAll := hCtxNoCap z V hz
        exact ⟨captureRisk_false_fun z V s u i' hAll.1, hAll.2⟩
      have hCtxNoCapU :
          ∀ (z : String) (V : HOLType), (z, V) ∈ ctx →
            captureRisk z V u i' = false ∧ i'.find? (fun p => p.fst = Term.var z V) = none := by
        intro z V hz
        have hAll := hCtxNoCap z V hz
        exact ⟨captureRisk_false_arg z V s u i' hAll.1, hAll.2⟩
      have hCapSplit : captureRisk x T s i' = true ∨ captureRisk x T u i' = true :=
        captureRisk_true_fun_or_arg x T s u i' hCap
      have hFreshNoNameS : ¬Term.HasName fresh (subst i' s) := by
        apply not_hasName_in_app_fun fresh (subst i' s) (subst i' u)
        simpa [subst] using hFreshNoName
      have hFreshNoNameU : ¬Term.HasName fresh (subst i' u) := by
        apply not_hasName_in_app_arg fresh (subst i' s) (subst i' u)
        simpa [subst] using hFreshNoName
      have hsEq :
          captureRisk x T s i' = true ->
            toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') s)
              = dbSubst i (toDBAux ((x, T) :: ctx) s) := by
        intro hCapS
        exact ihs ctx i hOk (by simpa [i'] using hCtxNoCapS) (by simpa [i'] using hCapS) hFreshNoNameS
      have huEq :
          captureRisk x T u i' = true ->
            toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') u)
              = dbSubst i (toDBAux ((x, T) :: ctx) u) := by
        intro hCapU
        exact ihu ctx i hOk (by simpa [i'] using hCtxNoCapU) (by simpa [i'] using hCapU) hFreshNoNameU
      cases hCapSplit with
      | inl hCapS =>
          have hs :
              toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') s)
                = dbSubst i (toDBAux ((x, T) :: ctx) s) := hsEq hCapS
          have hu :
              toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') u)
                = dbSubst i (toDBAux ((x, T) :: ctx) u) := by
            by_cases hCapU : captureRisk x T u i' = true
            · exact huEq hCapU
            · have hNoCapU : captureRisk x T u i' = false := by
                cases hVal : captureRisk x T u i' with
                | false => rfl
                | true => exfalso; exact hCapU hVal
              exact subst_toDBAux_comm_capture_no_capture_child ctx i x T u fresh hOk
                (by simpa [i'] using hCtxNoCapU) hNoCapU hFreshNoNameU
          simp [subst, toDBAux, dbSubst, hs, hu]
      | inr hCapU =>
          have hs :
              toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') s)
                = dbSubst i (toDBAux ((x, T) :: ctx) s) := by
            by_cases hCapS : captureRisk x T s i' = true
            · exact hsEq hCapS
            · have hNoCapS : captureRisk x T s i' = false := by
                cases hVal : captureRisk x T s i' with
                | false => rfl
                | true => exfalso; exact hCapS hVal
              exact subst_toDBAux_comm_capture_no_capture_child ctx i x T s fresh hOk
                (by simpa [i'] using hCtxNoCapS) hNoCapS hFreshNoNameS
          have hu :
              toDBAux ((fresh, T) :: ctx) (subst ((Term.var x T, Term.var fresh T) :: i') u)
                = dbSubst i (toDBAux ((x, T) :: ctx) u) := huEq hCapU
          simp [subst, toDBAux, dbSubst, hs, hu]
  | abs y U t ih =>
      have hCapXBody : captureRisk x T t i' = true :=
        captureRisk_true_abs_body x y T U t i' hCap
      by_cases hCapBody : captureRisk y U t i' = true
      · -- nested capture branch
        sorry
      · -- nested no-capture branch
        have hNoCapBody : captureRisk y U t i' = false := by
          cases hVal : captureRisk y U t i' with
          | false => rfl
          | true =>
              exfalso
              exact hCapBody hVal
        have hNoCapBodyFiltered :
            captureRisk y U t (i'.filter (fun p => !decide (p.fst = Term.var y U))) = false := by
          exact captureRisk_false_filter y U t i' (fun p => !decide (p.fst = Term.var y U)) hNoCapBody
        let iY := i'.filter (fun p => !decide (p.fst = Term.var y U))
        have hSubstI'Abs :
            subst i' (Term.abs y U t) = Term.abs y U (subst iY t) := by
          simp [subst, iY, hNoCapBodyFiltered]
        have hFreshSplit : fresh ≠ y ∧ ¬Term.HasName fresh (subst iY t) := by
          have hNoNameAbs : ¬Term.HasName fresh (Term.abs y U (subst iY t)) := by
            simpa [hSubstI'Abs] using hFreshNoName
          exact not_hasName_in_abs fresh y U (subst iY t) hNoNameAbs
        have hFreshNeY : fresh ≠ y := hFreshSplit.1
        have hFreshNoNameBody : ¬Term.HasName fresh (subst iY t) := hFreshSplit.2
        let iHead := (Term.var x T, Term.var fresh T) :: i'
        let iHeadY := iHead.filter (fun p => !decide (p.fst = Term.var y U))
        have hNoCapBodyHeadY : captureRisk y U t iHeadY = false := by
          by_cases hEqXY : Term.var x T = Term.var y U
          · have hEqFilter : iHeadY = iY := by
              simp [iHead, iHeadY, iY, hEqXY]
            simpa [hEqFilter] using hNoCapBodyFiltered
          · have hEqFilter : iHeadY = (Term.var x T, Term.var fresh T) :: iY := by
              simp [iHead, iHeadY, iY, hEqXY]
            apply (captureRisk_false y U t iHeadY).2
            intro p hp hPair
            rw [hEqFilter] at hp
            cases hp with
            | head =>
                have hVarNe : Term.var y U ≠ Term.var fresh T := by
                  intro hEq
                  exact hFreshNeY (by aesop)
                have hNotFreeFresh : ¬(Term.var y U).IsFreeVarIn (Term.var fresh T) := by
                  simpa [Term.IsFreeVarIn, Term.isFreeVarIn] using hVarNe
                simpa using hNotFreeFresh hPair.1
            | tail _ hpTail =>
                have hAll := (captureRisk_false y U t iY).1 hNoCapBodyFiltered
                exact (hAll p hpTail) hPair
        have hSubstHeadAbs :
            subst ((Term.var x T, Term.var fresh T) :: i') (Term.abs y U t)
              = Term.abs y U (subst iHeadY t) := by
          simp [subst, iHead, iHeadY, hNoCapBodyHeadY]
        have hRhsShadowX :
            dbSubst i (toDBAux ((y, U) :: (x, T) :: ctx) t)
              = dbSubst i' (toDBAux ((y, U) :: (x, T) :: ctx) t) := by
          simpa [i'] using
            dbSubst_filter_shadowed_ctx i x T ((y, U) :: (x, T) :: ctx) t (by simp)
        have hRhsShadowY :
            dbSubst i' (toDBAux ((y, U) :: (x, T) :: ctx) t)
              = dbSubst iY (toDBAux ((y, U) :: (x, T) :: ctx) t) := by
          simpa [iY] using
            dbSubst_filter_shadowed_ctx i' y U ((y, U) :: (x, T) :: ctx) t (by simp)
        have hRhsToIY :
            dbSubst i (toDBAux ((y, U) :: (x, T) :: ctx) t)
              = dbSubst iY (toDBAux ((y, U) :: (x, T) :: ctx) t) :=
          hRhsShadowX.trans hRhsShadowY
        have hneqXYVar : Term.var x T ≠ Term.var y U := by
          intro hEq
          have hNoCapXBody : captureRisk x T t i' = false := by
            cases hEq
            simpa using hNoCapBody
          rw [hNoCapXBody] at hCapXBody
          simp at hCapXBody
        have hIHeadYCons : iHeadY = (Term.var x T, Term.var fresh T) :: iY := by
          simp [iHead, iHeadY, iY, hneqXYVar]
        have hBodyGoal :
            toDBAux ((y, U) :: (fresh, T) :: ctx) (subst iHeadY t)
              = dbSubst iY (toDBAux ((y, U) :: (x, T) :: ctx) t) := by
          rw [hIHeadYCons]
          sorry
        clear hFreshNoNameBody
        calc
            toDBAux ((fresh, T) :: ctx)
                (subst ((Term.var x T, Term.var fresh T) :: i') (Term.abs y U t))
          = DBTerm.abs U (toDBAux ((y, U) :: (fresh, T) :: ctx) (subst iHeadY t)) := by
              simp [hSubstHeadAbs, toDBAux]
        _ = DBTerm.abs U (dbSubst iY (toDBAux ((y, U) :: (x, T) :: ctx) t)) := by
              simp [hBodyGoal]
        _ = DBTerm.abs U (dbSubst i (toDBAux ((y, U) :: (x, T) :: ctx) t)) := by
              simp [hRhsToIY, congrArg (DBTerm.abs U) hRhsToIY.symm]
        _ = dbSubst i (toDBAux ((x, T) :: ctx) (Term.abs y U t)) := by
              simp [toDBAux, dbSubst]

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
                have hAll := (captureRisk_false x T (Term.var y U) i).1 hRiskFalse
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
        exact captureRisk_false_fun x T s t i hAll.1
      have hCtxT :
          ∀ (x : String) (T : HOLType), (x, T) ∈ ctx →
            captureRisk x T t i = false ∧ i.find? (fun p => p.fst = Term.var x T) = none := by
        intro x T hmem
        have hAll := hNoCap x T hmem
        refine ⟨?_, hAll.2⟩
        exact captureRisk_false_arg x T s t i hAll.1
      have hs := ihs ctx i hOk hCtxS
      have ht := iht ctx i hOk hCtxT
      simp [subst, toDBAux, dbSubst, hs, ht]
  | abs x T t ih =>
      set i' := i.filter (fun p => !decide (p.fst = Term.var x T))
      have hOk' : SubstOk i' := SubstOk.filter i (fun p => !decide (p.fst = Term.var x T)) hOk
      by_cases hCap : captureRisk x T t i' = true
      · simp only [subst, hCap, ↓reduceIte, toDBAux, dbSubst, DBTerm.abs.injEq, true_and, i']
        set fresh := generateVariant (subst i' t) x T
        have hFreshNoName : ¬Term.HasName fresh (subst i' t) := by
          simpa [fresh] using (VariantNoName (subst i' t) x T)
        have hCtxNoCap :
            ∀ (y : String) (U : HOLType), (y, U) ∈ ctx →
              captureRisk y U t i' = false ∧ i'.find? (fun p => p.fst = Term.var y U) = none := by
          intro y U hmem
          have hOrig := hNoCap y U hmem
          constructor
          · apply (captureRisk_false y U t i').2
            intro p hp hPair
            have hpMem : p ∈ i := (List.mem_filter.mp hp).1
            have hpNe : p.fst ≠ Term.var x T := by
              have hPred : (!decide (p.fst = Term.var x T)) = true := (List.mem_filter.mp hp).2
              by_contra hEq
              simp [hEq] at hPred
            apply (captureRisk_false y U (.abs x T t) i).mp hOrig.1 p hpMem
            have hFreeAbs : p.fst.IsFreeVarIn (.abs x T t) := by
              unfold Term.IsFreeVarIn Term.isFreeVarIn
              rw [decide_eq_true_iff.mpr hpNe]
              simpa using hPair.2
            exact ⟨hPair.1, hFreeAbs⟩
          · apply (List.find?_eq_none).2
            intro p hp
            have hpMem : p ∈ i := (List.mem_filter.mp hp).1
            exact (List.find?_eq_none).1 hOrig.2 p hpMem
        simpa [fresh] using
          subst_toDBAux_comm_capture ctx i x T t fresh hOk (by simpa [i'] using hCtxNoCap) (by simpa [i'] using hCap) (by simpa [fresh] using hFreshNoName)
      · have hShadow :
            dbSubst i (toDBAux ((x, T) :: ctx) t) = dbSubst i' (toDBAux ((x, T) :: ctx) t) := by
          simpa [i'] using dbSubst_filter_shadowed_ctx i x T ((x, T) :: ctx) t (by simp)
        simp only [subst, hCap, Bool.false_eq_true, ↓reduceIte, toDBAux, dbSubst, DBTerm.abs.injEq,
          true_and, i']
        calc
            toDBAux ((x, T) :: ctx) (subst i' t)
          = dbSubst i' (toDBAux ((x, T) :: ctx) t) := by
              apply ih <;> try trivial
              intro y U hmem
              cases hmem with
              | head => constructor <;> aesop
              | tail _ hmemTail =>
                have hOrig := hNoCap y U hmemTail
                constructor
                · apply (captureRisk_false y U t i').2
                  intro p hp hPair
                  have hpMem : p ∈ i := (List.mem_filter.mp hp).1
                  have hpNe : p.fst ≠ Term.var x T := by
                    have hPred : (!decide (p.fst = Term.var x T)) = true
                      := (List.mem_filter.mp hp).right
                    by_contra hEq
                    simp [hEq] at hPred
                  apply (captureRisk_false y U (.abs x T t) i).mp hOrig.left p hpMem
                  have hFreeAbs : p.fst.IsFreeVarIn (.abs x T t) := by
                    unfold Term.IsFreeVarIn Term.isFreeVarIn
                    rw [decide_eq_true_iff.mpr hpNe]
                    simpa using hPair.right
                  constructor
                  · exact hPair.left
                  · exact hFreeAbs
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
  have hFreshNoName : ¬Term.HasName fresh (subst i' body) := by
    simpa [fresh] using (VariantNoName (subst i' body) x T)
  simpa [fresh] using
    subst_toDBAux_comm_capture [] i x T body fresh hOk (by intro y U hmem; cases hmem) (by simpa [i'] using hCap) (by simpa [fresh] using hFreshNoName)

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
