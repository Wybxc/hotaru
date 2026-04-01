import HotaruKernel.Type
import Aesop

/-- HOL terms. -/
inductive Term
| var : String -> HOLType -> Term
| const : String -> HOLType -> Term
| app : Term -> Term -> Term
| abs : Term -> Term -> Term
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
          Term.HasType t rT → Term.HasType (.abs (.var n dT) t) (.fun dT rT)

/-- Predicate for well-typed terms. -/
abbrev WellTyped (t : Term) : Prop := ∃ T, t.HasType T

/-- Type inference function for terms. -/
def typeof (t : Term) : Option HOLType :=
  match t with
  | .var _ T => some T
  | .const _ T => some T
  | .app s t =>
      match typeof s, typeof t with
      | some (.fun dT rT), some tT =>
          if dT = tT then some rT else none
      | _, _ => none
  | .abs (.var _ dT) t =>
      match typeof t with
      | some rT => some (.fun dT rT)
      | none => none
  | _ => none

theorem welltyped_typeof : ∀ (t : Term) (T : HOLType), Term.HasType t T → typeof t = some T
    := by
  intros t T ht
  induction ht with simp [typeof] <;> aesop

theorem typeof_welltyped : ∀ (t : Term) (T : HOLType), typeof t = some T → t.HasType T
    := by
  intros t T h
  induction t generalizing T with try simp [typeof] at h; subst h
  | var x T' => apply Term.HasType.var
  | const c T' => apply Term.HasType.const
  | app s t ih_s ih_t =>
      unfold typeof at h
      split at h
      · rename_i dT rT tT heq_s heq_t
        split at h <;> simp at h
        subst h
        apply Term.HasType.app
        · exact ih_s (.fun dT rT) heq_s
        · have : typeof t = some dT := by
            rw [heq_t]; aesop
          exact ih_t dT this
      · simp at h
  | abs n t ih_n ih_t =>
      cases n with simp [typeof] at h
      | var var_name dT =>
          split at h <;> simp at h
          subst h
          apply Term.HasType.abs
          aesop

/-- Theorem: `HasType t T` if and only if `typeof t = some T`. -/
theorem welltyped_typeof_iff : ∀ (t : Term) (T : HOLType), t.HasType T ↔ typeof t = some T
    := by
  intros t T
  constructor
  · apply welltyped_typeof
  · apply typeof_welltyped

/-- Alpha-equivalence for variables under a list of renamings. -/
@[simp] def IsAlphaVars (bv : List (Term × Term)) (v1 v2 : Term) : Prop :=
  match bv with
  | [] => v1 = v2
  | (b1, b2) :: bvs =>
      (v1 = b1 ∧ v2 = b2) ∨ (v1 ≠ b1 ∧ v2 ≠ b2 ∧ IsAlphaVars bvs v1 v2)

/-- Alpha-equivalence for terms under a list of renamings. -/
inductive IsAlphaTerms : List (Term × Term) -> Term -> Term -> Prop
| var : ∀ (bv : List (Term × Term)) (x1 x2 : String) (T1 T2 : HOLType),
          IsAlphaVars bv (.var x1 T1) (.var x2 T2) → IsAlphaTerms bv (.var x1 T1) (.var x2 T2)
| const : ∀ (bv : List (Term × Term)) (c1 c2 : String) (T1 T2 : HOLType),
          IsAlphaVars bv (.const c1 T1) (.const c2 T2) → IsAlphaTerms bv (.const c1 T1) (.const c2 T2)
| app : ∀ (bv : List (Term × Term)) (s1 s2 t1 t2 : Term),
          IsAlphaTerms bv s1 s2 → IsAlphaTerms bv t1 t2 → IsAlphaTerms bv (.app s1 t1) (.app s2 t2)
| abs : ∀ (bv : List (Term × Term)) (n1 n2 : Term) (t1 t2 : Term),
          IsAlphaTerms ((n1, n2) :: bv) t1 t2 → IsAlphaTerms bv (.abs n1 t1) (.abs n2 t2)

/-- Predicate for alpha-equivalence of terms. -/
def AlphaEqv (t1 t2 : Term) : Prop := IsAlphaTerms [] t1 t2

def IsTrivialRenaming (bv : List (Term × Term)) : Prop :=
  match bv with
  | [] => true
  | (b1, b2) :: bvs => b1 = b2 ∧ IsTrivialRenaming bvs

@[aesop safe]
theorem IsAlphaVars_refl : ∀ (bv : List (Term × Term)) (v : Term), IsTrivialRenaming bv → IsAlphaVars bv v v
    := by
  intros bv v h
  induction bv with
  | nil => simp [IsAlphaVars]
  | cons bv bvs ih =>
      rcases bv with ⟨b1, b2⟩
      simp [IsTrivialRenaming] at h
      by_cases hv : v = b1 <;> aesop

@[aesop safe]
theorem IsAlphaTerms_refl : ∀ (bv : List (Term × Term)) (t : Term), IsTrivialRenaming bv → IsAlphaTerms bv t t
    := by
  intro bv t
  induction t generalizing bv with intro h
  | var x T =>
      apply IsAlphaTerms.var
      exact IsAlphaVars_refl bv (.var x T) h
  | const c T =>
      apply IsAlphaTerms.const
      exact IsAlphaVars_refl bv (.const c T) h
  | app s t ih_s ih_t =>
      apply IsAlphaTerms.app <;> aesop
  | abs n t ih_n ih_t =>
      apply IsAlphaTerms.abs
      have h' : IsTrivialRenaming ((n, n) :: bv) := by
        simp [IsTrivialRenaming, h]
      exact ih_t ((n, n) :: bv) h'

def swap_renaming : List (Term × Term) -> List (Term × Term)
| [] => []
| (a, b) :: bvs => (b, a) :: swap_renaming bvs

@[aesop safe]
theorem IsAlphaVars_symm :
  ∀ (bv : List (Term × Term)) (v1 v2 : Term),
    IsAlphaVars bv v1 v2 → IsAlphaVars (swap_renaming bv) v2 v1 := by
  intro bv v1 v2 h
  induction bv generalizing v1 v2 with
  | nil =>
      simpa [IsAlphaVars, swap_renaming] using h.symm
  | cons b bvs ih =>
      simp [IsAlphaVars, swap_renaming] at h ⊢
      aesop

@[aesop safe]
theorem IsAlphaTerms_symm :
  ∀ (bv : List (Term × Term)) (t1 t2 : Term),
    IsAlphaTerms bv t1 t2 → IsAlphaTerms (swap_renaming bv) t2 t1 := by
  intro bv t1 t2 h
  induction h with
  | var bv x1 x2 T1 T2 hv => apply IsAlphaTerms.var; aesop
  | const bv c1 c2 T1 T2 hv => apply IsAlphaTerms.const; aesop
  | app bv s1 s2 t1 t2 hs ht ihs iht => apply IsAlphaTerms.app <;> simpa
  | abs bv n1 n2 t1 t2 hbody ih =>
      simpa [swap_renaming] using (IsAlphaTerms.abs (swap_renaming bv) n2 n1 t2 t1 ih)

inductive RenamingChain :
  List (Term × Term) -> List (Term × Term) -> List (Term × Term) -> Prop
| nil : RenamingChain [] [] []
| cons :
  ∀ (n1 n2 n3 : Term)
    (bv12 bv23 bv13 : List (Term × Term)),
    RenamingChain bv12 bv23 bv13 ->
    RenamingChain ((n1, n2) :: bv12) ((n2, n3) :: bv23) ((n1, n3) :: bv13)

@[aesop unsafe]
theorem IsAlphaVars_trans :
  ∀ (bv12 bv23 bv13 : List (Term × Term)) (v1 v2 v3 : Term),
    RenamingChain bv12 bv23 bv13 ->
    IsAlphaVars bv12 v1 v2 ->
    IsAlphaVars bv23 v2 v3 ->
    IsAlphaVars bv13 v1 v3 := by
  intro bv12 bv23 bv13 v1 v2 v3 hchain h12 h23
  induction hchain generalizing v1 v2 v3 with
  | nil => simpa [IsAlphaVars] using Eq.trans h12 h23
  | cons n1 n2 n3 bv12 bv23 bv13 hchain ih =>
      simp [IsAlphaVars] at h12 h23 ⊢
      aesop

@[aesop safe]
theorem IsAlphaTerms_trans :
  ∀ (bv12 bv23 bv13 : List (Term × Term)) (t1 t2 t3 : Term),
    RenamingChain bv12 bv23 bv13 ->
    IsAlphaTerms bv12 t1 t2 ->
    IsAlphaTerms bv23 t2 t3 ->
    IsAlphaTerms bv13 t1 t3 := by
  intro bv12 bv23 bv13 t1 t2 t3 hchain h12
  induction h12 generalizing bv23 bv13 t3 with intro h23
  | var bv x1 x2 T1 T2 hv12 =>
    cases h23 with
    | var => apply IsAlphaTerms.var; aesop
  | const bv c1 c2 T1 T2 hv12 =>
    cases h23 with
    | const => apply IsAlphaTerms.const; aesop
  | app bv s1 s2 t1 t2 hs12 ht12 ihs iht =>
    cases h23 with
    | app => apply IsAlphaTerms.app <;> aesop
  | abs bv n1 n2 t1 t2 hbody12 ih =>
    cases h23 with
    | abs =>
      apply IsAlphaTerms.abs
      apply ih <;> try simpa
      apply RenamingChain.cons; simpa

theorem AlphaEqv.refl : ∀ (t : Term), AlphaEqv t t
    := by
  intro t
  unfold AlphaEqv
  simpa using IsAlphaTerms_refl [] t (by simp [IsTrivialRenaming])

theorem AlphaEqv.symm : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → AlphaEqv t2 t1
    := by
  intro t1 t2 h
  unfold AlphaEqv at h ⊢
  simpa [swap_renaming] using IsAlphaTerms_symm [] t1 t2 h

theorem AlphaEqv.trans : ∀ {t1 t2 t3 : Term}, AlphaEqv t1 t2 → AlphaEqv t2 t3 → AlphaEqv t1 t3
    := by
  intro t1 t2 t3 h12 h23
  unfold AlphaEqv at h12 h23 ⊢
  apply IsAlphaTerms_trans <;> try simpa
  apply RenamingChain.nil

instance : Equivalence AlphaEqv where
  refl := AlphaEqv.refl
  symm := AlphaEqv.symm
  trans := AlphaEqv.trans

noncomputable instance : DecidableRel AlphaEqv := by
  intro t1 t2
  classical
  infer_instance

instance : Setoid Term where
  r := AlphaEqv
  iseqv := ⟨AlphaEqv.refl, AlphaEqv.symm, AlphaEqv.trans⟩

def Term.IsFreeVarIn (var : Term) : Term -> Prop
| .var x T => var = .var x T
| .const x T => var = .const x T
| .app s t => (var.IsFreeVarIn s) ∨ (var.IsFreeVarIn t)
| .abs n t => (var ≠ n) ∧ (var.IsFreeVarIn t)

def decIsFreeVarIn (var : Term) : (t : Term) → Decidable (var.IsFreeVarIn t)
| .var x T => by
  simpa [Term.IsFreeVarIn] using (by infer_instance)
| .const x T => by
  simpa [Term.IsFreeVarIn] using (by infer_instance)
| .app s t =>
  match decIsFreeVarIn var s, decIsFreeVarIn var t with
  | .isTrue hs, _ => .isTrue (Or.inl hs)
  | .isFalse hs, .isTrue ht => .isTrue (Or.inr ht)
  | .isFalse hs, .isFalse ht =>
    .isFalse (by
      intro h
      cases h with
      | inl h1 => exact hs h1
      | inr h2 => exact ht h2)
| .abs n t =>
  match (inferInstance : Decidable (var ≠ n)), decIsFreeVarIn var t with
  | .isTrue hne, .isTrue ht => .isTrue ⟨hne, ht⟩
  | .isFalse hne, _ => .isFalse (by intro h; exact hne h.1)
  | .isTrue _, .isFalse ht => .isFalse (by intro h; exact ht h.2)

instance {var t : Term} : Decidable (var.IsFreeVarIn t) := decIsFreeVarIn var t

def Closed (t : Term) : Prop := ∀ x T, (Term.var x T).IsFreeVarIn t → False

/-- Maximum variable-name length appearing in a term. -/
def Term.maxVarNameLen : Term → Nat
| .var x _ => String.length x
| .const _ _ => 0
| .app s t => Nat.max s.maxVarNameLen t.maxVarNameLen
| .abs n t => Nat.max n.maxVarNameLen t.maxVarNameLen

theorem varNotFreeOfNameLengthGt :
  ∀ (t : Term) (x : String) (T : HOLType),
    t.maxVarNameLen < String.length x → ¬(Term.var x T).IsFreeVarIn t := by
  intro t
  induction t with
  | var y Ty =>
      intro x T hlen
      intro hfree
      simp [Term.maxVarNameLen, Term.IsFreeVarIn] at hlen hfree
      rcases hfree with ⟨hxy, _⟩
      subst hxy
      exact (Nat.lt_irrefl _ hlen)
  | const c Ty =>
      intro x T _
      simp [Term.IsFreeVarIn]
  | app s t ihs iht =>
      intro x T hlen
      have hs : s.maxVarNameLen < String.length x :=
        Nat.lt_of_le_of_lt (Nat.le_max_left s.maxVarNameLen t.maxVarNameLen) hlen
      have ht : t.maxVarNameLen < String.length x :=
        Nat.lt_of_le_of_lt (Nat.le_max_right s.maxVarNameLen t.maxVarNameLen) hlen
      simp [Term.IsFreeVarIn, ihs x T hs, iht x T ht]
  | abs n t ihn iht =>
      intro x T hlen
      have ht : t.maxVarNameLen < String.length x :=
        Nat.lt_of_le_of_lt (Nat.le_max_right n.maxVarNameLen t.maxVarNameLen) hlen
      simp [Term.IsFreeVarIn, iht x T ht]

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
private def captureRisk (bvar body : Term) (i : List (Term × Term)) : Bool :=
  i.any (fun p => decide (bvar.IsFreeVarIn p.2 ∧ p.1.IsFreeVarIn body))

/-- Term variable substitution: applies a list of term substitutions to a term. -/
def subst (i : List (Term × Term)) : Term → Option Term
| .var x ty => match i.find? (fun (y, _) => y = .var x ty) with
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
    -- Check if any substitution introduces free variables that would be captured by bvar
    if captureRisk bvar t i' then
      -- Capture risk exists: generate a fresh variable
      match bvar with
      | .var x ty => do
          let freshName := generateVariant t' x ty
          let z := Term.var freshName ty
          -- Add the new binding to prevent capture
          let i'' := (z, bvar) :: i'
          let t'' ← subst i'' t
          some (.abs z t'')
      | _ => none
    else
      some (.abs bvar t')

theorem welltyped_subst : ∀ (t : Term) (i : List (Term × Term)),
    WellTyped t → ∃ t', subst i t = some t' := by
  intro t i hwt
  rcases hwt with ⟨T, ht⟩
  induction ht generalizing i with
  | var x T =>
      unfold subst
      split
      · rename_i t hfind
        exact ⟨t, rfl⟩
      · exact ⟨Term.var x T, rfl⟩
  | const c T =>
      exact ⟨Term.const c T, rfl⟩
  | app s t dT rT hs ht ihs iht =>
      rcases ihs i with ⟨s', hs'⟩
      rcases iht i with ⟨t', ht'⟩
      refine ⟨Term.app s' t', ?_⟩
      simp [subst, hs', ht']
  | abs n dT rT t ht iht =>
      let bvar := Term.var n dT
      let i' := i.filter (fun p => !decide (p.fst = bvar))
      rcases iht i' with ⟨t1, ht1⟩
      by_cases hcap : captureRisk bvar t i' = true
      · let z := Term.var (generateVariant t1 n dT) dT
        let i'' := (z, bvar) :: i'
        rcases iht i'' with ⟨t2, ht2⟩
        refine ⟨Term.abs z t2, ?_⟩
        simp [subst, i', bvar, ht1, hcap]
        have ht2' :
            subst
                ((Term.var (generateVariant t1 n dT) dT, Term.var n dT) ::
                  List.filter (fun p => !decide (p.fst = Term.var n dT)) i)
                t = some t2 := by
          simpa [i'', z, bvar] using ht2
        simp [z, Option.bind, ht2']
      · have hcap' : captureRisk bvar t i' = false := by
          cases hc : captureRisk bvar t i' <;> simp [hc] at hcap ⊢
        refine ⟨Term.abs bvar t1, ?_⟩
        simp [subst, i', bvar, ht1, hcap']

def SubstOk (i : List (Term × Term)) : Prop :=
  ∀ v t, (v, t) ∈ i → ∃ x T, v = Term.var x T ∧ t = Term.var x T

theorem SubstOk_filter : ∀ (i : List (Term × Term)) (bvar : Term),
    SubstOk i → SubstOk (i.filter (fun p => !decide (p.fst = bvar))) := by
  intro i bvar hOk
  intro v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

theorem captureRisk_false_of_SubstOk_filter :
    ∀ (bvar body : Term) (i : List (Term × Term)),
      SubstOk i →
      captureRisk bvar body (i.filter (fun p => !decide (p.fst = bvar))) = false := by
  intro bvar body i hOk
  unfold captureRisk
  rw [List.any_eq_false]
  intro p hp
  rcases p with ⟨v, t⟩
  have hpInI : (v, t) ∈ i := (List.mem_filter.mp hp).1
  have hpKeep : (!decide (v = bvar)) = true := (List.mem_filter.mp hp).2
  have hneq : v ≠ bvar := by
    by_cases hvb : v = bvar
    · simp [hvb] at hpKeep
    · exact hvb
  intro hcond
  have hcond' : bvar.IsFreeVarIn t ∧ v.IsFreeVarIn body := by
    simpa using hcond
  rcases hOk v t hpInI with ⟨x, T, hv, ht⟩
  have hbv : bvar = v := by
    have hbvt : bvar = Term.var x T := by
      simpa [ht, Term.IsFreeVarIn] using hcond'.1
    calc
      bvar = Term.var x T := hbvt
      _ = v := by simp [hv]
  exact hneq hbv.symm

theorem subst_self_of_SubstOk : ∀ (t : Term) (i : List (Term × Term)),
    SubstOk i → subst i t = some t := by
  intro t
  induction t with
  | var x ty =>
      intro i hOk
      unfold subst
      cases hfind : i.find? (fun (y, _) => y = Term.var x ty) with
      | none =>
          simp
      | some p =>
          rcases p with ⟨v, t⟩
          have hmem : (v, t) ∈ i := List.mem_of_find?_eq_some hfind
          have hpred : (fun q : Term × Term => decide (q.fst = Term.var x ty)) (v, t) = true := by
            exact (List.find?_some (p := fun q : Term × Term => decide (q.fst = Term.var x ty)) hfind)
          have hv : v = Term.var x ty := by
            simp at hpred
            exact hpred
          rcases hOk v t hmem with ⟨x', T', hv', ht'⟩
          have ht : t = Term.var x ty := by
            calc
              t = Term.var x' T' := ht'
              _ = v := by simp [hv']
              _ = Term.var x ty := hv
          simp [ht]
  | const c ty =>
      intro i hOk
      simp [subst]
  | app s t ihs iht =>
      intro i hOk
      have hs : subst i s = some s := ihs i hOk
      have ht : subst i t = some t := iht i hOk
      simp [subst, hs, ht]
  | abs n t ihn iht =>
      intro i hOk
      let i' := i.filter (fun p => !decide (p.fst = n))
      have hOk' : SubstOk i' := SubstOk_filter i n hOk
      have ht : subst i' t = some t := iht i' hOk'
      have hcap : captureRisk n t i' = false := by
        simpa [i'] using captureRisk_false_of_SubstOk_filter n t i hOk
      simp [subst, i', ht, hcap]

theorem subst_alpha : ∀ (t1 t2 : Term) (i : List (Term × Term)),
    WellTyped t1 → WellTyped t2 → SubstOk i → AlphaEqv t1 t2 →
    ∃ t1' t2', subst i t1 = some t1' ∧ subst i t2 = some t2' ∧ AlphaEqv t1' t2' := by
  intro t1 t2 i hwt1 hwt2 hOk hAlpha
  refine ⟨t1, t2, ?_, ?_, hAlpha⟩
  · exact subst_self_of_SubstOk t1 i hOk
  · exact subst_self_of_SubstOk t2 i hOk

/-- Structural size for fuel-based recursion in instantiation. -/
def Term.size : Term → Nat
| .var _ _ => 1
| .const _ _ => 1
| .app s t => 1 + s.size + t.size
| .abs _ t => 2 + t.size

-- theorem subst_size : ∀ (t t': Term) (i : List (Term × Term)),
--     (∀ s s', (s, s') ∈ i → ∃ x T, s' = Term.var x T) → subst i t = some t' → t'.size = t.size := by
--   intro t t' i hOk hsubst
--   induction t generalizing t' with
--   | var x T =>
--       simp [subst] at hsubst


private def instantiateCoreFuel : Nat → List (Term × Term) → List (String × HOLType) →
    Term → Except Term Term
| 0, _env, _tyin, tm => .error tm
| _ + 1, env, tyin, .var x ty =>
    let tm := Term.var x ty
    let tm' := Term.var x (typeSubst tyin ty)
    -- Check if tm' (the new instantiated variable) would cause a clash
    match env.find? (fun (old, _) => old = tm') with
    | some (_, orig) =>
        if orig = tm then
          .ok tm'
        else
          .error tm'
    | none => .ok tm'
| _ + 1, _env, tyin, .const x ty =>
    .ok (.const x (typeSubst tyin ty))
| fuel + 1, env, tyin, .app s t => do
    let s' ← instantiateCoreFuel fuel env tyin s
    let t' ← instantiateCoreFuel fuel env tyin t
    .ok (Term.app s' t')
| fuel + 1, env, tyin, .abs v t =>
    match v with
    | .var x ty =>
        let ty' := typeSubst tyin ty
        let v' := Term.var x ty'
        let env' := (v', v) :: env
        let tre : Except Term Term := instantiateCoreFuel fuel env' tyin t
        match tre with
        | .ok t' => .ok (Term.abs v' t')
        | .error w =>
            if w ≠ v' then
              .error w
            else do
              let t0 ← instantiateCoreFuel fuel [] tyin t
              let x' := generateVariant t0 x ty'
              let tSub? := subst [(Term.var x ty, Term.var x' ty)] t
              match tSub? with
              | none => .error w
              | some tSub => do
                  let env'' := (Term.var x' ty', Term.var x' ty) :: env
                  let t'' ← instantiateCoreFuel fuel env'' tyin tSub
                  .ok (Term.abs (Term.var x' ty') t'')
    | _ => .error v

/-- Instantiate type variables in a term according to a substitution.
    `env` tracks old/new binder correspondence to detect clashes. -/
def instantiateCore (env : List (Term × Term)) (tyin : List (String × HOLType))
    (tm : Term) : Except Term Term :=
  instantiateCoreFuel (2 * Term.size tm + 1) env tyin tm

/-- Instantiates type variables in a term according to a substitution.
    Returns `none` only when a clash cannot be resolved. -/
def instantiate (tyin : List (String × HOLType)) (tm : Term) : Option Term :=
  match instantiateCore [] tyin tm with
  | .ok t => some t
  | .error _ => none

-- theorem welltyped_instantiate_pre : ∀ (t : Term) (tyin : List (String × HOLType)),
--     WellTyped t → ∃ t', instantiate tyin t = some t'
--   := by
--   intro t tyin hwt
--   aesop

-- theorem instantiate_preserves_alpha : ∀ (t1 t2 t1' t2' : Term) (tyin : List (String × HOLType)),
--     AlphaEqv t1 t2 → instantiate tyin t1 = some t1' → instantiate tyin t2 = some t2' → AlphaEqv t1' t2'
--   := by
--   intro t1 t2 t1' t2' tyin hAlpha h1 h2
--   aesop

-- theorem instantiate_alpha : ∀ (t1 t2 : Term) (tyin : List (String × HOLType)),
--     WellTyped t1 → WellTyped t2 → AlphaEqv t1 t2 →
--     ∃ t1' t2', instantiate tyin t1 = some t1' ∧ instantiate tyin t2 = some t2' ∧ AlphaEqv t1' t2' := by
--   intro t1 t2 tyin hwt1 hwt2 hAlpha
--   rcases welltyped_instantiate_pre t1 tyin hwt1 with ⟨t1', ht1'⟩
--   rcases welltyped_instantiate_pre t2 tyin hwt2 with ⟨t2', ht2'⟩
--   have hAlpha' : AlphaEqv t1' t2' :=
--     instantiate_preserves_alpha t1 t2 t1' t2' tyin hAlpha ht1' ht2'
--   exact ⟨t1', t2', ht1', ht2', hAlpha'⟩
