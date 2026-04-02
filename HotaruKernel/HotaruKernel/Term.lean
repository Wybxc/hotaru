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
          (WellTyped (.app s1 t1) ↔ WellTyped (.app s2 t2)) →
          IsAlphaTerms bv s1 s2 → IsAlphaTerms bv t1 t2 → IsAlphaTerms bv (.app s1 t1) (.app s2 t2)
| abs : ∀ (bv : List (Term × Term)) (n1 n2 : Term) (t1 t2 : Term),
          (WellTyped (.abs n1 t1) ↔ WellTyped (.abs n2 t2)) →
          IsAlphaTerms ((n1, n2) :: bv) t1 t2 → IsAlphaTerms bv (.abs n1 t1) (.abs n2 t2)

/-- Predicate for alpha-equivalence of terms. -/
def AlphaEqv (t1 t2 : Term) : Prop :=
  IsAlphaTerms [] t1 t2

theorem AlphaEqv.isAlpha : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → IsAlphaTerms [] t1 t2 := by
  intro t1 t2 h
  exact h

theorem IsAlphaTerms_welltyped_iff :
    ∀ {bv : List (Term × Term)} {t1 t2 : Term}, IsAlphaTerms bv t1 t2 → (WellTyped t1 ↔ WellTyped t2) := by
  intro bv t1 t2 h
  induction h with
  | var bv x1 x2 T1 T2 hv =>
      constructor <;> intro _ <;> exact ⟨_, Term.HasType.var _ _⟩
  | const bv c1 c2 T1 T2 hv =>
      constructor <;> intro _ <;> exact ⟨_, Term.HasType.const _ _⟩
  | app bv s1 s2 t1 t2 hwt hs ht ihs iht =>
    exact hwt
  | abs bv n1 n2 t1 t2 hwt hbody ih =>
    exact hwt

theorem AlphaEqv.welltyped_iff : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → (WellTyped t1 ↔ WellTyped t2) := by
  intro t1 t2 h
  simpa [AlphaEqv] using IsAlphaTerms_welltyped_iff h

theorem AlphaEqv.welltyped_right : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → WellTyped t1 → WellTyped t2 := by
  intro t1 t2 h hwt1
  exact (AlphaEqv.welltyped_iff h).mp hwt1

theorem AlphaEqv.welltyped_left : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → WellTyped t2 → WellTyped t1 := by
  intro t1 t2 h hwt2
  exact (AlphaEqv.welltyped_iff h).mpr hwt2

theorem AlphaEqv.welltyped_both_of_either :
    ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → (WellTyped t1 ∨ WellTyped t2) → (WellTyped t1 ∧ WellTyped t2) := by
  intro t1 t2 hAlpha hEither
  cases hEither with
  | inl hwt1 => exact ⟨hwt1, AlphaEqv.welltyped_right hAlpha hwt1⟩
  | inr hwt2 => exact ⟨AlphaEqv.welltyped_left hAlpha hwt2, hwt2⟩

def IsTrivialRenaming (bv : List (Term × Term)) : Prop :=
  match bv with
  | [] => true
  | (b1, b2) :: bvs => b1 = b2 ∧ IsTrivialRenaming bvs

@[aesop safe]
theorem IsAlphaVars_refl : ∀ (bv : List (Term × Term)) (v : Term), IsTrivialRenaming bv → IsAlphaVars bv v v
    := by
  intro bv v h
  induction bv with
  | nil =>
      simp [IsAlphaVars]
  | cons b bvs ih =>
      rcases b with ⟨b1, b2⟩
      simp [IsTrivialRenaming] at h
      rcases h with ⟨hb, htriv⟩
      subst hb
      by_cases hv : v = b1
      · exact Or.inl ⟨hv, hv⟩
      · exact Or.inr ⟨hv, hv, ih htriv⟩

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
      apply IsAlphaTerms.app
      · exact Iff.rfl
      · aesop
      · aesop
  | abs n t ih_n ih_t =>
      apply IsAlphaTerms.abs
      · exact Iff.rfl
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
  | app bv s1 s2 t1 t2 hwt hs ht ihs iht =>
      apply IsAlphaTerms.app
      · exact hwt.symm
      · simpa using ihs
      · simpa using iht
  | abs bv n1 n2 t1 t2 hwt hbody ih =>
      simpa [swap_renaming] using (IsAlphaTerms.abs (swap_renaming bv) n2 n1 t2 t1 hwt.symm ih)

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
  | nil =>
      exact Eq.trans h12 h23
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
  | app bv s1 s2 t1 t2 hwt12 hs12 ht12 ihs iht =>
    cases h23 with
    | app bv s2 s3 t2 t3 hwt23 hs23 ht23 =>
      apply IsAlphaTerms.app
      · exact Iff.trans hwt12 hwt23
      · aesop
      · aesop
  | abs bv n1 n2 t1 t2 hwt12 hbody12 ih =>
    cases h23 with
    | abs bv n2 n3 t2 t3 hwt23 hbody23 =>
      apply IsAlphaTerms.abs
      · exact Iff.trans hwt12 hwt23
      apply ih <;> try simpa
      apply RenamingChain.cons; simpa

theorem AlphaEqv.refl : ∀ (t : Term), AlphaEqv t t
    := by
  intro t
  simpa [AlphaEqv] using IsAlphaTerms_refl [] t (by simp [IsTrivialRenaming])

theorem AlphaEqv.symm : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → AlphaEqv t2 t1
    := by
  intro t1 t2 h
  simpa [AlphaEqv, swap_renaming] using IsAlphaTerms_symm [] t1 t2 h

theorem AlphaEqv.trans : ∀ {t1 t2 t3 : Term}, AlphaEqv t1 t2 → AlphaEqv t2 t3 → AlphaEqv t1 t3
    := by
  intro t1 t2 t3 h12 h23
  exact IsAlphaTerms_trans [] [] [] t1 t2 t3 RenamingChain.nil h12 h23

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

theorem alphaeqv_not_preserve_welltyped_without_rhs_assumption :
    ¬ ∃ t1 t2, AlphaEqv t1 t2 ∧ WellTyped t1 ∧ ¬ WellTyped t2 := by
  intro h
  rcases h with ⟨t1, t2, hAlpha, hwt1, hnot2⟩
  exact hnot2 (AlphaEqv.welltyped_right hAlpha hwt1)

/-- De Bruijn representation used to reason about alpha-equivalence. -/
inductive DBTerm
| bvar : Nat -> DBTerm
| fvar : String -> HOLType -> DBTerm
| const : String -> HOLType -> DBTerm
| app : DBTerm -> DBTerm -> DBTerm
| abs : DBTerm -> DBTerm
deriving Repr, DecidableEq

/-- Lookup binder depth in a de Bruijn context. -/
def lookupBVar : List (String × HOLType) -> String -> HOLType -> Option Nat
| [], _, _ => none
| (y, Uy) :: ys, x, U =>
    if (x = y ∧ U = Uy) then
      some 0
    else
      Option.map Nat.succ (lookupBVar ys x U)

/-- Convert a named term to de Bruijn form under a context. -/
def toDBAux (ctx : List (String × HOLType)) : Term -> DBTerm
| .var x T =>
    match lookupBVar ctx x T with
  | some n => DBTerm.bvar n
    | none => DBTerm.fvar x T
| .const c T => DBTerm.const c T
| .app s t => DBTerm.app (toDBAux ctx s) (toDBAux ctx t)
| .abs (.var x T) t => DBTerm.abs (toDBAux ((x, T) :: ctx) t)
| .abs _ t => DBTerm.abs (toDBAux ctx t)

/-- Convert a named term to de Bruijn form. -/
def toDB (t : Term) : DBTerm := toDBAux [] t

/-- Substitute free variables in de Bruijn terms according to a named substitution list. -/
def dbSubst (i : List (Term × Term)) : DBTerm -> DBTerm
| .bvar n => .bvar n
| .fvar x T =>
    match i.find? (fun p => p.fst = Term.var x T) with
    | some (_, t) => toDB t
    | none => .fvar x T
| .const c T => .const c T
| .app s t => .app (dbSubst i s) (dbSubst i t)
| .abs t => .abs (dbSubst i t)

theorem dbSubst_refl : ∀ (t : DBTerm), dbSubst [] t = t := by
  intro t
  induction t with
  | bvar n => rfl
  | fvar x T => simp [dbSubst]
  | const c T => rfl
  | app s t ihs iht => simp [dbSubst, ihs, iht]
  | abs t iht => simp [dbSubst, iht]

theorem dbSubst_eq_of_eq : ∀ (i : List (Term × Term)) (t1 t2 : DBTerm),
    t1 = t2 -> dbSubst i t1 = dbSubst i t2 := by
  intro i t1 t2 h
  cases h
  rfl

theorem dbSubst_fvar_eq_of_find_some :
    ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (v s : Term),
      i.find? (fun p => p.fst = Term.var x T) = some (v, s) ->
      dbSubst i (DBTerm.fvar x T) = toDB s := by
  intro i x T v s hFind
  unfold dbSubst
  simp [hFind]

theorem dbSubst_fvar_eq_of_find_none :
    ∀ (i : List (Term × Term)) (x : String) (T : HOLType),
      i.find? (fun p => p.fst = Term.var x T) = none ->
      dbSubst i (DBTerm.fvar x T) = DBTerm.fvar x T := by
  intro i x T hFind
  unfold dbSubst
  simp [hFind]

theorem find?_filter_eq_find?_of_var_ne :
    ∀ (i : List (Term × Term)) (x y : String) (T U : HOLType),
      Term.var y U ≠ Term.var x T ->
      (i.filter (fun p => !decide (p.fst = Term.var x T))).find? (fun p => p.fst = Term.var y U)
        = i.find? (fun p => p.fst = Term.var y U) := by
  intro i x y T U hne
  induction i with
  | nil =>
      simp
  | cons p ps ih =>
      rcases p with ⟨v, t⟩
      by_cases hvx : v = Term.var x T
      · have hvy : v ≠ Term.var y U := by
          intro hvy
          apply hne
          calc
            Term.var y U = v := hvy.symm
            _ = Term.var x T := hvx
        have hxyu : ¬ (x = y ∧ T = U) := by
          intro h
          rcases h with ⟨hxy, hTU⟩
          apply hne
          subst hxy
          subst hTU
          rfl
        simp [List.find?, hvx, hxyu, ih]
      · by_cases hvy : v = Term.var y U
        · subst v
          simp [List.find?, hvx]
        · simp [List.find?, hvx, hvy, ih]

theorem lookupBVar_cons_hit :
    ∀ (ctx : List (String × HOLType)) (x : String) (T : HOLType),
      lookupBVar ((x, T) :: ctx) x T = some 0 := by
  intro ctx x T
  simp [lookupBVar]

theorem lookupBVar_cons_miss :
    ∀ (ctx : List (String × HOLType)) (x y : String) (T U : HOLType),
      (x ≠ y ∨ T ≠ U) ->
      lookupBVar ((y, U) :: ctx) x T = Option.map Nat.succ (lookupBVar ctx x T) := by
  intro ctx x y T U h
  have hxyu : ¬(x = y ∧ T = U) := by
    intro hxy
    rcases hxy with ⟨hx, hT⟩
    cases h with
    | inl hxy' => exact hxy' hx
    | inr hT' => exact hT' hT
  simp [lookupBVar, hxyu]

theorem lookupBVar_cons_eq_some_zero_iff :
    ∀ (ctx : List (String × HOLType)) (x y : String) (T U : HOLType),
      lookupBVar ((y, U) :: ctx) x T = some 0 ↔ x = y ∧ T = U := by
  intro ctx x y T U
  by_cases h : (x = y ∧ T = U)
  · simp [lookupBVar, h]
  · simp [lookupBVar, h]

theorem lookupBVar_cons_eq_some_succ_iff :
    ∀ (ctx : List (String × HOLType)) (x y : String) (T U : HOLType) (n : Nat),
      lookupBVar ((y, U) :: ctx) x T = some (Nat.succ n) ↔
      (x ≠ y ∨ T ≠ U) ∧ lookupBVar ctx x T = some n := by
  intro ctx x y T U n
  by_cases h : (x = y ∧ T = U)
  · have hFalse : (x ≠ y ∨ T ≠ U) = False := by
      apply propext
      constructor
      · intro h'
        rcases h with ⟨hx, hT⟩
        cases h' with
        | inl hxy => exact (hxy hx).elim
        | inr hTU => exact (hTU hT).elim
      · intro h'
        cases h'
    simp [lookupBVar, h]
  · have hTrue : (x ≠ y ∨ T ≠ U) = True := by
      apply propext
      constructor
      · intro _
        trivial
      · intro _
        by_cases hxy : x = y
        · right
          intro hTU
          apply h
          exact ⟨hxy, hTU⟩
        · exact Or.inl hxy
    simp [lookupBVar, h, hTrue]

/-- Relation between alpha-renaming environment and paired de Bruijn contexts. -/
inductive DBCtxRel : List (Term × Term) -> List (String × HOLType) -> List (String × HOLType) -> Prop
| nil : DBCtxRel [] [] []
| cons : ∀ (x y : String) (T1 T2 : HOLType)
    (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType)),
    DBCtxRel bv ctx1 ctx2 ->
  DBCtxRel ((Term.var x T1, Term.var y T2) :: bv) ((x, T1) :: ctx1) ((y, T2) :: ctx2)

theorem var_ne_disj :
    ∀ (x y : String) (T U : HOLType),
      Term.var x T ≠ Term.var y U -> (x ≠ y ∨ T ≠ U) := by
  intro x y T U h
  by_cases hxy : x = y
  · right
    intro hTU
    apply h
    subst hxy
    subst hTU
    rfl
  · exact Or.inl hxy

theorem lookupBVar_eq_of_IsAlphaVars_var :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
      lookupBVar ctx1 x1 T1 = lookupBVar ctx2 x2 T2 := by
  intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha
  induction hCtx generalizing x1 x2 T1 T2 with
  | nil =>
      dsimp [IsAlphaVars] at hAlpha
      cases hAlpha
      rfl
  | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
      dsimp [IsAlphaVars] at hAlpha
      rcases hAlpha with hHit | hMiss
      · rcases hHit with ⟨hx1, hx2⟩
        cases hx1
        cases hx2
        simp [lookupBVar]
      · rcases hMiss with ⟨hneq1, hneq2, hTail⟩
        have hdisj1 : x1 ≠ x ∨ T1 ≠ TL := var_ne_disj x1 x T1 TL hneq1
        have hdisj2 : x2 ≠ y ∨ T2 ≠ TR := var_ne_disj x2 y T2 TR hneq2
        rw [lookupBVar_cons_miss ctx1 x1 x T1 TL hdisj1]
        rw [lookupBVar_cons_miss ctx2 x2 y T2 TR hdisj2]
        have hrec : lookupBVar ctx1 x1 T1 = lookupBVar ctx2 x2 T2 :=
          ih x1 x2 T1 T2 hTail
        simpa using congrArg (Option.map Nat.succ) hrec

theorem free_eq_of_IsAlphaVars_var_lookup_none :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
      lookupBVar ctx1 x1 T1 = none ->
      x1 = x2 ∧ T1 = T2 := by
  intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha hNone
  induction hCtx generalizing x1 x2 T1 T2 with
  | nil =>
      dsimp [IsAlphaVars] at hAlpha
      cases hAlpha
      exact ⟨rfl, rfl⟩
  | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
      dsimp [IsAlphaVars] at hAlpha
      rcases hAlpha with hHit | hMiss
      · rcases hHit with ⟨hx1, _⟩
        cases hx1
        simp [lookupBVar] at hNone
      · rcases hMiss with ⟨hneq1, _, hTail⟩
        have hdisj1 : x1 ≠ x ∨ T1 ≠ TL := var_ne_disj x1 x T1 TL hneq1
        rw [lookupBVar_cons_miss ctx1 x1 x T1 TL hdisj1] at hNone
        cases htail : lookupBVar ctx1 x1 T1 with
        | none =>
            exact ih x1 x2 T1 T2 hTail htail
        | some n =>
            simp [htail] at hNone

theorem toDBAux_var_eq_of_IsAlphaVars :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
      toDBAux ctx1 (.var x1 T1) = toDBAux ctx2 (.var x2 T2) := by
  intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha
  have hLookup : lookupBVar ctx1 x1 T1 = lookupBVar ctx2 x2 T2 :=
    lookupBVar_eq_of_IsAlphaVars_var bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha
  cases hL : lookupBVar ctx1 x1 T1 with
  | none =>
      have hR : lookupBVar ctx2 x2 T2 = none := by simpa [hL] using hLookup.symm
      have hFree : x1 = x2 ∧ T1 = T2 :=
        free_eq_of_IsAlphaVars_var_lookup_none bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha hL
      rcases hFree with ⟨hx, hT⟩
      subst hx
      subst hT
      simp [toDBAux, hL, hR]
  | some n =>
      have hR : lookupBVar ctx2 x2 T2 = some n := by simpa [hL] using hLookup.symm
      simp [toDBAux, hL, hR]

theorem const_eq_of_IsAlphaVars :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (c1 c2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      IsAlphaVars bv (.const c1 T1) (.const c2 T2) ->
      c1 = c2 ∧ T1 = T2 := by
  intro bv ctx1 ctx2 c1 c2 T1 T2 hCtx hAlpha
  induction hCtx generalizing c1 c2 T1 T2 with
  | nil =>
      dsimp [IsAlphaVars] at hAlpha
      cases hAlpha
      exact ⟨rfl, rfl⟩
  | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
      dsimp [IsAlphaVars] at hAlpha
      rcases hAlpha with hHit | hMiss
      · rcases hHit with ⟨h1, _⟩
        cases h1
      · rcases hMiss with ⟨_, _, hTail⟩
        exact ih c1 c2 T1 T2 hTail

theorem toDBAux_const_eq_of_IsAlphaVars :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (c1 c2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      IsAlphaVars bv (.const c1 T1) (.const c2 T2) ->
      toDBAux ctx1 (.const c1 T1) = toDBAux ctx2 (.const c2 T2) := by
  intro bv ctx1 ctx2 c1 c2 T1 T2 hCtx hAlpha
  rcases const_eq_of_IsAlphaVars bv ctx1 ctx2 c1 c2 T1 T2 hCtx hAlpha with ⟨hc, hT⟩
  subst hc
  subst hT
  rfl

theorem IsAlphaVars_const_refl_of_DBCtxRel :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType)) (c : String) (T : HOLType),
      DBCtxRel bv ctx1 ctx2 -> IsAlphaVars bv (.const c T) (.const c T) := by
  intro bv ctx1 ctx2 c T hCtx
  induction hCtx with
  | nil => simp [IsAlphaVars]
  | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
      right
      constructor
      · intro hEq
        cases hEq
      constructor
      · intro hEq
        cases hEq
      · exact ih

theorem IsAlphaVars_of_toDBAux_const_eq :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (c1 c2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      toDBAux ctx1 (.const c1 T1) = toDBAux ctx2 (.const c2 T2) ->
      IsAlphaVars bv (.const c1 T1) (.const c2 T2) := by
  intro bv ctx1 ctx2 c1 c2 T1 T2 hCtx hEq
  simp [toDBAux] at hEq
  rcases hEq with ⟨hc, hT⟩
  subst hc
  subst hT
  exact IsAlphaVars_const_refl_of_DBCtxRel bv ctx1 ctx2 c1 T1 hCtx

theorem IsAlphaVars_of_lookup_eq_some :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType) (n : Nat),
      DBCtxRel bv ctx1 ctx2 ->
      lookupBVar ctx1 x1 T1 = some n ->
      lookupBVar ctx2 x2 T2 = some n ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) := by
  intro bv ctx1 ctx2 x1 x2 T1 T2 n hCtx hL1 hL2
  induction hCtx generalizing x1 x2 T1 T2 n with
  | nil =>
      simp [lookupBVar] at hL1
  | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
      cases n with
      | zero =>
          have h1 : x1 = x ∧ T1 = TL :=
            (lookupBVar_cons_eq_some_zero_iff ctx1 x1 x T1 TL).mp hL1
          have h2 : x2 = y ∧ T2 = TR :=
            (lookupBVar_cons_eq_some_zero_iff ctx2 x2 y T2 TR).mp hL2
          rcases h1 with ⟨hx1, hT1⟩
          rcases h2 with ⟨hx2, hT2⟩
          left
          constructor
          · cases hx1
            cases hT1
            rfl
          · cases hx2
            cases hT2
            rfl
      | succ n =>
          have h1 : (x1 ≠ x ∨ T1 ≠ TL) ∧ lookupBVar ctx1 x1 T1 = some n :=
            (lookupBVar_cons_eq_some_succ_iff ctx1 x1 x T1 TL n).mp hL1
          have h2 : (x2 ≠ y ∨ T2 ≠ TR) ∧ lookupBVar ctx2 x2 T2 = some n :=
            (lookupBVar_cons_eq_some_succ_iff ctx2 x2 y T2 TR n).mp hL2
          rcases h1 with ⟨hdisj1, hTail1⟩
          rcases h2 with ⟨hdisj2, hTail2⟩
          have hneq1 : Term.var x1 T1 ≠ Term.var x TL := by
            intro hEq
            cases hEq
            cases hdisj1 with
            | inl hxy => exact (hxy rfl).elim
            | inr hT => exact (hT rfl).elim
          have hneq2 : Term.var x2 T2 ≠ Term.var y TR := by
            intro hEq
            cases hEq
            cases hdisj2 with
            | inl hxy => exact (hxy rfl).elim
            | inr hT => exact (hT rfl).elim
          right
          exact ⟨hneq1, hneq2, ih x1 x2 T1 T2 n hTail1 hTail2⟩

theorem IsAlphaVars_of_lookup_none_eq :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (x : String) (T : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      lookupBVar ctx1 x T = none ->
      lookupBVar ctx2 x T = none ->
      IsAlphaVars bv (.var x T) (.var x T) := by
  intro bv ctx1 ctx2 x T hCtx hNone1 hNone2
  induction hCtx generalizing x T with
  | nil =>
      simp [IsAlphaVars]
  | cons xl xr TL TR bv ctx1 ctx2 hCtx ih =>
      have hdisj1 : x ≠ xl ∨ T ≠ TL := by
        by_cases h : x = xl ∧ T = TL
        · have : lookupBVar ((xl, TL) :: ctx1) x T = some 0 := by
            simp [lookupBVar, h]
          simp [hNone1] at this
        · by_cases hxy : x = xl
          · right
            intro hT
            exact h ⟨hxy, hT⟩
          · exact Or.inl hxy
      have hdisj2 : x ≠ xr ∨ T ≠ TR := by
        by_cases h : x = xr ∧ T = TR
        · have : lookupBVar ((xr, TR) :: ctx2) x T = some 0 := by
            simp [lookupBVar, h]
          simp [hNone2] at this
        · by_cases hxy : x = xr
          · right
            intro hT
            exact h ⟨hxy, hT⟩
          · exact Or.inl hxy
      have hTail1 : lookupBVar ctx1 x T = none := by
        rw [lookupBVar_cons_miss ctx1 x xl T TL hdisj1] at hNone1
        cases hlookup : lookupBVar ctx1 x T with
        | none => rfl
        | some n => simp [hlookup] at hNone1
      have hTail2 : lookupBVar ctx2 x T = none := by
        rw [lookupBVar_cons_miss ctx2 x xr T TR hdisj2] at hNone2
        cases hlookup : lookupBVar ctx2 x T with
        | none => rfl
        | some n => simp [hlookup] at hNone2
      have hneq1 : Term.var x T ≠ Term.var xl TL := by
        intro hEq
        cases hEq
        cases hdisj1 with
        | inl hxy => exact (hxy rfl).elim
        | inr hT => exact (hT rfl).elim
      have hneq2 : Term.var x T ≠ Term.var xr TR := by
        intro hEq
        cases hEq
        cases hdisj2 with
        | inl hxy => exact (hxy rfl).elim
        | inr hT => exact (hT rfl).elim
      right
      exact ⟨hneq1, hneq2, ih x T hTail1 hTail2⟩

theorem IsAlphaVars_of_toDBAux_var_eq :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType),
      DBCtxRel bv ctx1 ctx2 ->
      toDBAux ctx1 (.var x1 T1) = toDBAux ctx2 (.var x2 T2) ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) := by
  intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hEq
  dsimp [toDBAux] at hEq
  cases hL1 : lookupBVar ctx1 x1 T1 with
  | none =>
      cases hL2 : lookupBVar ctx2 x2 T2 with
      | none =>
          simp [hL1, hL2] at hEq
          rcases hEq with ⟨hx, hT⟩
          subst hx
          subst hT
          exact IsAlphaVars_of_lookup_none_eq bv ctx1 ctx2 x1 T1 hCtx hL1 hL2
      | some n =>
          simp [hL1, hL2] at hEq
  | some n =>
      cases hL2 : lookupBVar ctx2 x2 T2 with
      | none =>
          simp [hL1, hL2] at hEq
      | some m =>
          have hnm : n = m := by
            simp [hL1, hL2] at hEq
            exact hEq
          subst hnm
          exact IsAlphaVars_of_lookup_eq_some bv ctx1 ctx2 x1 x2 T1 T2 n hCtx hL1 hL2

  theorem toDBAux_eq_of_IsAlphaTerms_wt :
    ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
      (t1 t2 : Term),
      DBCtxRel bv ctx1 ctx2 ->
      WellTyped t1 -> WellTyped t2 ->
      IsAlphaTerms bv t1 t2 ->
      toDBAux ctx1 t1 = toDBAux ctx2 t2 := by
    intro bv ctx1 ctx2 t1 t2 hCtx hwt1 hwt2 hAlpha
    induction hAlpha generalizing ctx1 ctx2 with
    | var bv x1 x2 T1 T2 hv =>
      exact toDBAux_var_eq_of_IsAlphaVars bv ctx1 ctx2 x1 x2 T1 T2 hCtx hv
    | const bv c1 c2 T1 T2 hv =>
      exact toDBAux_const_eq_of_IsAlphaVars bv ctx1 ctx2 c1 c2 T1 T2 hCtx hv
    | app bv s1 s2 t1 t2 hwt hs ht ihs iht =>
      rcases hwt1 with ⟨_, hty1⟩
      rcases hwt2 with ⟨_, hty2⟩
      cases hty1 with
      | app _ _ _ _ hs1 ht1 =>
        cases hty2 with
        | app _ _ _ _ hs2 ht2 =>
          have hsEq : toDBAux ctx1 s1 = toDBAux ctx2 s2 :=
            ihs ctx1 ctx2 hCtx ⟨_, hs1⟩ ⟨_, hs2⟩
          have htEq : toDBAux ctx1 t1 = toDBAux ctx2 t2 :=
            iht ctx1 ctx2 hCtx ⟨_, ht1⟩ ⟨_, ht2⟩
          simp [toDBAux, hsEq, htEq]
    | abs bv n1 n2 t1 t2 hwt hbody ih =>
      rcases hwt1 with ⟨_, hty1⟩
      rcases hwt2 with ⟨_, hty2⟩
      cases hty1 with
      | abs x1 dT1 rT1 body1 hbody1 =>
        cases hty2 with
        | abs x2 dT2 rT2 body2 hbody2 =>
          have hCtx' :
            DBCtxRel
            ((Term.var x1 dT1, Term.var x2 dT2) :: bv)
            ((x1, dT1) :: ctx1)
            ((x2, dT2) :: ctx2) := by
            exact DBCtxRel.cons x1 x2 dT1 dT2 bv ctx1 ctx2 hCtx
          have hRec :
            toDBAux ((x1, dT1) :: ctx1) t1 =
            toDBAux ((x2, dT2) :: ctx2) t2 :=
            ih ((x1, dT1) :: ctx1) ((x2, dT2) :: ctx2) hCtx' ⟨rT1, hbody1⟩ ⟨rT2, hbody2⟩
          simpa [toDBAux] using hRec

  theorem IsAlphaTerms_of_toDBAux_eq_wt :
      ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
        (t1 t2 : Term),
        DBCtxRel bv ctx1 ctx2 ->
        WellTyped t1 -> WellTyped t2 ->
        toDBAux ctx1 t1 = toDBAux ctx2 t2 ->
        IsAlphaTerms bv t1 t2 := by
    intro bv ctx1 ctx2 t1 t2 hCtx hwt1 hwt2 hEq
    rcases hwt1 with ⟨T1, ht1⟩
    revert bv ctx1 ctx2 t2 hCtx hwt2 hEq
    induction ht1 with
    | var x1 T1 =>
        intro bv ctx1 ctx2 t2 hCtx hwt2 hEq
        rcases hwt2 with ⟨T2, ht2⟩
        cases ht2 with
        | var x2 T2 =>
            apply IsAlphaTerms.var
            exact IsAlphaVars_of_toDBAux_var_eq bv ctx1 ctx2 x1 x2 T1 T2 hCtx hEq
        | const c2 T2 =>
          cases hL : lookupBVar ctx1 x1 T1 <;> simp [toDBAux, hL] at hEq
        | app s2 t2 dT2 rT2 hs2 ht2 =>
          cases hL : lookupBVar ctx1 x1 T1 <;> simp [toDBAux, hL] at hEq
        | abs n2 dT2 rT2 body2 hbody2 =>
          cases hL : lookupBVar ctx1 x1 T1 <;> simp [toDBAux, hL] at hEq
    | const c1 T1 =>
        intro bv ctx1 ctx2 t2 hCtx hwt2 hEq
        rcases hwt2 with ⟨T2, ht2⟩
        cases ht2 with
        | var x2 T2 =>
          cases hL : lookupBVar ctx2 x2 T2 <;> simp [toDBAux, hL] at hEq
        | const c2 T2 =>
            apply IsAlphaTerms.const
            exact IsAlphaVars_of_toDBAux_const_eq bv ctx1 ctx2 c1 c2 T1 T2 hCtx hEq
        | app s2 t2 dT2 rT2 hs2 ht2 =>
          cases hEq
        | abs n2 dT2 rT2 body2 hbody2 =>
          cases hEq
    | app s1 t1 dT1 rT1 hs1 ht1 ihs iht =>
        intro bv ctx1 ctx2 u hCtx hwu hEq
        rcases hwu with ⟨U, hu⟩
        cases hu with
        | var x2 T2 =>
          cases hL : lookupBVar ctx2 x2 U <;> simp [toDBAux, hL] at hEq
        | const c2 T2 =>
            cases hEq
        | app s2 t2 dT2 rT2 hs2 ht2 =>
            have hEqApp :
                DBTerm.app (toDBAux ctx1 s1) (toDBAux ctx1 t1) =
                DBTerm.app (toDBAux ctx2 s2) (toDBAux ctx2 t2) := by
              simpa [toDBAux] using hEq
            have hInj : toDBAux ctx1 s1 = toDBAux ctx2 s2 ∧ toDBAux ctx1 t1 = toDBAux ctx2 t2 := by
              injection hEqApp with hsEq htEq
              exact ⟨hsEq, htEq⟩
            have hsEq : toDBAux ctx1 s1 = toDBAux ctx2 s2 := hInj.1
            have htEq : toDBAux ctx1 t1 = toDBAux ctx2 t2 := hInj.2
            have hAlphaS : IsAlphaTerms bv s1 s2 :=
              ihs bv ctx1 ctx2 s2 hCtx ⟨_, hs2⟩ hsEq
            have hAlphaT : IsAlphaTerms bv t1 t2 :=
              iht bv ctx1 ctx2 t2 hCtx ⟨dT2, ht2⟩ htEq
            have hwtApp1 : WellTyped (Term.app s1 t1) :=
              ⟨rT1, Term.HasType.app s1 t1 dT1 rT1 hs1 ht1⟩
            have hwtApp2 : WellTyped (Term.app s2 t2) :=
              ⟨_, Term.HasType.app s2 t2 dT2 _ hs2 ht2⟩
            refine IsAlphaTerms.app bv s1 s2 t1 t2 ?_ hAlphaS hAlphaT
            constructor <;> intro _
            · exact hwtApp2
            · exact hwtApp1
        | abs n2 dT2 rT2 body2 hbody2 =>
            cases hEq
    | abs n1 dT1 rT1 body1 hbody1 ihbody =>
        intro bv ctx1 ctx2 u hCtx hwu hEq
        rcases hwu with ⟨U, hu⟩
        cases hu with
        | var x2 T2 =>
          cases hL : lookupBVar ctx2 x2 U <;> simp [toDBAux, hL] at hEq
        | const c2 T2 =>
          cases hEq
        | app s2 t2 dT2 rT2 hs2 ht2 =>
          cases hEq
        | abs n2 dT2 rT2 body2 hbody2 =>
            have hEqBody :
                toDBAux ((n1, dT1) :: ctx1) body1 =
                toDBAux ((n2, dT2) :: ctx2) body2 := by
              simpa [toDBAux] using hEq
            have hCtx' :
                DBCtxRel ((Term.var n1 dT1, Term.var n2 dT2) :: bv)
                  ((n1, dT1) :: ctx1) ((n2, dT2) :: ctx2) := by
              exact DBCtxRel.cons n1 n2 dT1 dT2 bv ctx1 ctx2 hCtx
            have hAlphaBody :
                IsAlphaTerms ((Term.var n1 dT1, Term.var n2 dT2) :: bv) body1 body2 :=
              ihbody ((Term.var n1 dT1, Term.var n2 dT2) :: bv)
                ((n1, dT1) :: ctx1) ((n2, dT2) :: ctx2) body2 hCtx' ⟨_, hbody2⟩ hEqBody
            have hwtAbs1 : WellTyped (Term.abs (Term.var n1 dT1) body1) :=
              ⟨HOLType.fun dT1 rT1, Term.HasType.abs n1 dT1 rT1 body1 hbody1⟩
            have hwtAbs2 : WellTyped (Term.abs (Term.var n2 dT2) body2) :=
              ⟨_, Term.HasType.abs n2 dT2 _ body2 hbody2⟩
            refine IsAlphaTerms.abs bv (Term.var n1 dT1) (Term.var n2 dT2) body1 body2 ?_ hAlphaBody
            constructor <;> intro _
            · exact hwtAbs2
            · exact hwtAbs1

  theorem toDB_eq_of_AlphaEqv_wt :
    ∀ (t1 t2 : Term), WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 -> toDB t1 = toDB t2 := by
    intro t1 t2 hwt1 hwt2 hAlpha
    simpa [toDB] using toDBAux_eq_of_IsAlphaTerms_wt [] [] [] t1 t2 DBCtxRel.nil hwt1 hwt2 hAlpha

  theorem AlphaEqv_of_toDB_eq_wt :
      ∀ (t1 t2 : Term), WellTyped t1 -> WellTyped t2 -> toDB t1 = toDB t2 -> AlphaEqv t1 t2 := by
    intro t1 t2 hwt1 hwt2 hEq
    simpa [AlphaEqv, toDB] using
      IsAlphaTerms_of_toDBAux_eq_wt [] [] [] t1 t2 DBCtxRel.nil hwt1 hwt2 hEq

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

/-- De Bruijn term has no free-variable nodes. -/
def DBClosed : DBTerm -> Prop
| .bvar _ => True
| .fvar _ _ => False
| .const _ _ => True
| .app s t => DBClosed s ∧ DBClosed t
| .abs t => DBClosed t

theorem toDBAux_DBClosed_of_wt_covered :
    ∀ (ctx : List (String × HOLType)) (t : Term) (T : HOLType),
      t.HasType T ->
      (∀ x U, (Term.var x U).IsFreeVarIn t -> ∃ n, lookupBVar ctx x U = some n) ->
      DBClosed (toDBAux ctx t) := by
  intro ctx t T hty
  induction hty generalizing ctx with
  | var x T =>
      intro hCov
      have hfree : (Term.var x T).IsFreeVarIn (Term.var x T) := by
        simp [Term.IsFreeVarIn]
      rcases hCov x T hfree with ⟨n, hn⟩
      simp [toDBAux, hn, DBClosed]
  | const c T =>
      intro _
      simp [toDBAux, DBClosed]
  | app s t dT rT hs ht ihs iht =>
      intro hCov
      have hsCov : ∀ x U, (Term.var x U).IsFreeVarIn s -> ∃ n, lookupBVar ctx x U = some n := by
        intro x U hfree
        exact hCov x U (Or.inl hfree)
      have htCov : ∀ x U, (Term.var x U).IsFreeVarIn t -> ∃ n, lookupBVar ctx x U = some n := by
        intro x U hfree
        exact hCov x U (Or.inr hfree)
      exact And.intro (ihs ctx hsCov) (iht ctx htCov)
  | abs n dT rT t ht iht =>
      intro hCov
      have hBodyCov :
          ∀ x U, (Term.var x U).IsFreeVarIn t ->
          ∃ m, lookupBVar ((n, dT) :: ctx) x U = some m := by
        intro x U hfree
        by_cases hx : x = n
        · by_cases hU : U = dT
          · subst hx
            subst hU
            exact ⟨0, by simp [lookupBVar]⟩
          · have hneq : Term.var x U ≠ Term.var n dT := by
              intro hEq
              cases hEq
              exact hU rfl
            have hfreeAbs : (Term.var x U).IsFreeVarIn (Term.abs (Term.var n dT) t) :=
              And.intro hneq hfree
            rcases hCov x U hfreeAbs with ⟨m, hm⟩
            refine ⟨Nat.succ m, ?_⟩
            rw [lookupBVar_cons_miss ctx x n U dT (Or.inr hU)]
            simp [hm]
        · have hneq : Term.var x U ≠ Term.var n dT := by
            intro hEq
            cases hEq
            exact hx rfl
          have hfreeAbs : (Term.var x U).IsFreeVarIn (Term.abs (Term.var n dT) t) :=
            And.intro hneq hfree
          rcases hCov x U hfreeAbs with ⟨m, hm⟩
          refine ⟨Nat.succ m, ?_⟩
          rw [lookupBVar_cons_miss ctx x n U dT (Or.inl hx)]
          simp [hm]
      have hBodyClosed : DBClosed (toDBAux ((n, dT) :: ctx) t) :=
        iht ((n, dT) :: ctx) hBodyCov
      simpa [toDBAux, DBClosed] using hBodyClosed

theorem covered_of_toDBAux_DBClosed_wt :
    ∀ (ctx : List (String × HOLType)) (t : Term) (T : HOLType),
      t.HasType T ->
      DBClosed (toDBAux ctx t) ->
      ∀ x U, (Term.var x U).IsFreeVarIn t -> ∃ n, lookupBVar ctx x U = some n := by
  intro ctx t T hty
  induction hty generalizing ctx with
  | var x T =>
      intro hDb y U hfree
      have hEq : Term.var y U = Term.var x T := by
        simpa [Term.IsFreeVarIn] using hfree
      cases hEq
      cases hL : lookupBVar ctx x T with
      | none =>
          have : False := by
            have hDb' := hDb
            simp [toDBAux, DBClosed, hL] at hDb'
          exact False.elim this
      | some n =>
          exact ⟨n, rfl⟩
  | const c T =>
      intro _ x U hfree
      have : False := by
        simp [Term.IsFreeVarIn] at hfree
      exact False.elim this
  | app s t dT rT hs ht ihs iht =>
      intro hDb x U hfree
      have hPair : DBClosed (toDBAux ctx s) ∧ DBClosed (toDBAux ctx t) := by
        simpa [toDBAux, DBClosed] using hDb
      rcases hPair with ⟨hsDb, htDb⟩
      cases hfree with
      | inl hsFree => exact ihs ctx hsDb x U hsFree
      | inr htFree => exact iht ctx htDb x U htFree
  | abs n dT rT t ht iht =>
      intro hDb x U hfree
      rcases hfree with ⟨hneq, hfreeBody⟩
      have hBodyDb : DBClosed (toDBAux ((n, dT) :: ctx) t) := by
        simpa [toDBAux, DBClosed] using hDb
      rcases iht ((n, dT) :: ctx) hBodyDb x U hfreeBody with ⟨m, hm⟩
      cases m with
      | zero =>
          have hEq : x = n ∧ U = dT :=
            (lookupBVar_cons_eq_some_zero_iff ctx x n U dT).mp hm
          rcases hEq with ⟨hx, hU⟩
          apply False.elim
          apply hneq
          simp [hx, hU]
      | succ k =>
          have hSucc : (x ≠ n ∨ U ≠ dT) ∧ lookupBVar ctx x U = some k :=
            (lookupBVar_cons_eq_some_succ_iff ctx x n U dT k).mp hm
          exact ⟨k, hSucc.2⟩

theorem toDB_DBClosed_of_wt_closed :
    ∀ (t : Term), WellTyped t -> Closed t -> DBClosed (toDB t) := by
  intro t hwt hClosed
  rcases hwt with ⟨T, hty⟩
  unfold toDB
  apply toDBAux_DBClosed_of_wt_covered [] t T hty
  intro x U hfree
  exact False.elim (hClosed x U hfree)

theorem closed_of_toDB_DBClosed_wt :
    ∀ (t : Term), WellTyped t -> DBClosed (toDB t) -> Closed t := by
  intro t hwt hDb
  rcases hwt with ⟨T, hty⟩
  intro x U hfree
  have hCov : ∃ n, lookupBVar [] x U = some n := by
    have hDbAux : DBClosed (toDBAux [] t) := by simpa [toDB] using hDb
    exact covered_of_toDBAux_DBClosed_wt [] t T hty hDbAux x U hfree
  rcases hCov with ⟨n, hn⟩
  simp [lookupBVar] at hn

theorem closed_of_alpha_wt_left :
    ∀ (t1 t2 : Term),
      WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 -> Closed t1 -> Closed t2 := by
  intro t1 t2 hwt1 hwt2 hAlpha hClosed1
  have hEq : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
  have hDb1 : DBClosed (toDB t1) := toDB_DBClosed_of_wt_closed t1 hwt1 hClosed1
  have hDb2 : DBClosed (toDB t2) := by
    simpa [hEq] using hDb1
  exact closed_of_toDB_DBClosed_wt t2 hwt2 hDb2

/-- Variable `(x,T)` is disjoint from all binders in `ctx`. -/
def CtxDisjoint (ctx : List (String × HOLType)) (x : String) (T : HOLType) : Prop :=
  ∀ y U, (y, U) ∈ ctx -> (x ≠ y ∨ T ≠ U)

/-- De Bruijn term contains free-variable node `(x,T)`. -/
def DBHasFVar (x : String) (T : HOLType) : DBTerm -> Prop
| .bvar _ => False
| .fvar y U => x = y ∧ T = U
| .const _ _ => False
| .app s t => DBHasFVar x T s ∨ DBHasFVar x T t
| .abs t => DBHasFVar x T t

theorem dbSubst_filter_eq_of_no_DBHasFVar :
    ∀ (d : DBTerm) (i : List (Term × Term)) (x : String) (T : HOLType),
      ¬ DBHasFVar x T d ->
      dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) d = dbSubst i d := by
  intro d
  induction d with
  | bvar n =>
      intro i x T _
      rfl
  | fvar y U =>
      intro i x T hNo
      have hneq : Term.var y U ≠ Term.var x T := by
        intro hEq
        apply hNo
        cases hEq
        exact And.intro rfl rfl
      unfold dbSubst
      rw [find?_filter_eq_find?_of_var_ne i x y T U hneq]
  | const c U =>
      intro i x T _
      rfl
  | app s t ihs iht =>
      intro i x T hNo
      have hsNo : ¬ DBHasFVar x T s := by
        intro hs
        exact hNo (Or.inl hs)
      have htNo : ¬ DBHasFVar x T t := by
        intro ht
        exact hNo (Or.inr ht)
      simp [dbSubst, ihs i x T hsNo, iht i x T htNo]
  | abs body ih =>
      intro i x T hNo
      simp [dbSubst, ih i x T hNo]

theorem dbSubst_cons_eq_of_no_DBHasFVar :
    ∀ (d : DBTerm) (i : List (Term × Term)) (x : String) (T : HOLType) (s : Term),
      ¬ DBHasFVar x T d ->
      dbSubst ((Term.var x T, s) :: i) d = dbSubst i d := by
  intro d
  induction d with
  | bvar n =>
      intro i x T s _
      rfl
  | fvar y U =>
      intro i x T s hNo
      have hneq : Term.var y U ≠ Term.var x T := by
        intro hEq
        apply hNo
        cases hEq
        exact And.intro rfl rfl
      unfold dbSubst
      have hxyu : ¬ (x = y ∧ T = U) := by
        intro h
        rcases h with ⟨hxy, hTU⟩
        apply hneq
        subst hxy
        subst hTU
        rfl
      simp [List.find?, hxyu]
  | const c U =>
      intro i x T s _
      rfl
  | app a b iha ihb =>
      intro i x T s hNo
      have hNoA : ¬ DBHasFVar x T a := by
        intro ha
        exact hNo (Or.inl ha)
      have hNoB : ¬ DBHasFVar x T b := by
        intro hb
        exact hNo (Or.inr hb)
      simp [dbSubst, iha i x T s hNoA, ihb i x T s hNoB]
  | abs body ih =>
      intro i x T s hNo
      simp [dbSubst, ih i x T s hNo]

theorem lookupBVar_none_of_disjoint :
    ∀ (ctx : List (String × HOLType)) (x : String) (T : HOLType),
      CtxDisjoint ctx x T -> lookupBVar ctx x T = none := by
  intro ctx x T hDis
  induction ctx with
  | nil =>
      rfl
  | cons hd tl ih =>
      rcases hd with ⟨y, U⟩
      have hHead : x ≠ y ∨ T ≠ U := hDis y U (by simp)
      have hTail : CtxDisjoint tl x T := by
        intro y' U' hmem
        exact hDis y' U' (by simp [hmem])
      rw [lookupBVar_cons_miss tl x y T U hHead]
      simp [ih hTail]

theorem DBHasFVar_toDBAux_of_free :
    ∀ (ctx : List (String × HOLType)) (t : Term) (x : String) (T : HOLType),
      CtxDisjoint ctx x T -> (Term.var x T).IsFreeVarIn t -> DBHasFVar x T (toDBAux ctx t) := by
  intro ctx t
  induction t generalizing ctx with
  | var y U =>
      intro x T hDis hfree
      have hEq : Term.var x T = Term.var y U := by
        simpa [Term.IsFreeVarIn] using hfree
      cases hEq
      have hNone : lookupBVar ctx y U = none := lookupBVar_none_of_disjoint ctx y U hDis
      simp [toDBAux, DBHasFVar, hNone]
  | const c U =>
      intro x T _ hfree
      have : False := by
        simp [Term.IsFreeVarIn] at hfree
      exact False.elim this
  | app s t ihs iht =>
      intro x T hDis hfree
      cases hfree with
      | inl hs => exact Or.inl (ihs ctx x T hDis hs)
      | inr ht => exact Or.inr (iht ctx x T hDis ht)
  | abs n body ihn ihbody =>
      intro x T hDis hfree
      rcases hfree with ⟨hneq, hbody⟩
      cases n with
      | var y U =>
          have hHead : x ≠ y ∨ T ≠ U := var_ne_disj x y T U hneq
          have hDis' : CtxDisjoint ((y, U) :: ctx) x T := by
            intro y' U' hmem
            have hmem' : (y', U') = (y, U) ∨ (y', U') ∈ ctx := List.mem_cons.mp hmem
            cases hmem' with
            | inl hEq =>
                rcases Prod.mk.inj hEq with ⟨hy, hU⟩
                subst hy
                subst hU
                exact hHead
            | inr hTail =>
                exact hDis y' U' hTail
          have hRec : DBHasFVar x T (toDBAux ((y, U) :: ctx) body) :=
            ihbody ((y, U) :: ctx) x T hDis' hbody
          simpa [toDBAux, DBHasFVar] using hRec
      | const y U =>
          have hRec : DBHasFVar x T (toDBAux ctx body) := ihbody ctx x T hDis hbody
          simpa [toDBAux, DBHasFVar] using hRec
      | app n1 n2 =>
          have hRec : DBHasFVar x T (toDBAux ctx body) := ihbody ctx x T hDis hbody
          simpa [toDBAux, DBHasFVar] using hRec
      | abs n1 n2 =>
          have hRec : DBHasFVar x T (toDBAux ctx body) := ihbody ctx x T hDis hbody
          simpa [toDBAux, DBHasFVar] using hRec

theorem no_DBHasFVar_of_lookup_some :
    ∀ (ctx : List (String × HOLType)) (body : Term) (x : String) (T : HOLType) (n : Nat),
      lookupBVar ctx x T = some n ->
      DBHasFVar x T (toDBAux ctx body) -> False := by
  intro ctx body x T n hLookup hHas
  induction body generalizing ctx n with
  | var y U =>
      cases hL : lookupBVar ctx y U with
      | none =>
          have hEq : x = y ∧ T = U := by
            simpa [toDBAux, DBHasFVar, hL] using hHas
          rcases hEq with ⟨hx, hTU⟩
          subst hx
          subst hTU
          rw [hL] at hLookup
          simp at hLookup
      | some m =>
            simp [toDBAux, DBHasFVar, hL] at hHas
  | const c U =>
          simp [toDBAux, DBHasFVar] at hHas
  | app s t ihs iht =>
      have hSplit : DBHasFVar x T (toDBAux ctx s) ∨ DBHasFVar x T (toDBAux ctx t) := by
        simpa [toDBAux, DBHasFVar] using hHas
      cases hSplit with
          | inl hs => exact ihs ctx n hLookup hs
          | inr ht => exact iht ctx n hLookup ht
  | abs nvar body ihn ihbody =>
      cases nvar with
      | var y U =>
          have hBodyHas : DBHasFVar x T (toDBAux ((y, U) :: ctx) body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          by_cases hxyu : (x = y ∧ T = U)
          · have hLookup' : lookupBVar ((y, U) :: ctx) x T = some 0 := by
              simp [lookupBVar, hxyu]
            exact ihbody ((y, U) :: ctx) 0 hLookup' hBodyHas
          · have hLookup' : lookupBVar ((y, U) :: ctx) x T = some (Nat.succ n) := by
              simp [lookupBVar, hxyu, hLookup]
            exact ihbody ((y, U) :: ctx) (Nat.succ n) hLookup' hBodyHas
      | const y U =>
          have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          exact ihbody ctx n hLookup hBodyHas
      | app n1 n2 =>
          have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          exact ihbody ctx n hLookup hBodyHas
      | abs n1 n2 =>
          have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          exact ihbody ctx n hLookup hBodyHas

theorem no_DBHasFVar_under_bound :
    ∀ (ctx : List (String × HOLType)) (body : Term) (x : String) (T : HOLType),
      ¬ DBHasFVar x T (toDBAux ((x, T) :: ctx) body) := by
  intro ctx body x T
  have hLookup : lookupBVar ((x, T) :: ctx) x T = some 0 := by
    simp [lookupBVar]
  intro hHas
  exact no_DBHasFVar_of_lookup_some ((x, T) :: ctx) body x T 0 hLookup hHas

theorem dbSubst_filter_eq_under_bound :
    ∀ (ctx : List (String × HOLType)) (body : Term) (i : List (Term × Term)) (x : String) (T : HOLType),
      dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) (toDBAux ((x, T) :: ctx) body) =
        dbSubst i (toDBAux ((x, T) :: ctx) body) := by
  intro ctx body i x T
  apply dbSubst_filter_eq_of_no_DBHasFVar
  exact no_DBHasFVar_under_bound ctx body x T

theorem free_of_DBHasFVar_toDBAux :
    ∀ (ctx : List (String × HOLType)) (t : Term) (x : String) (T : HOLType),
      CtxDisjoint ctx x T -> DBHasFVar x T (toDBAux ctx t) -> (Term.var x T).IsFreeVarIn t := by
  intro ctx t
  induction t generalizing ctx with
  | var y U =>
      intro x T _ hHas
      cases hL : lookupBVar ctx y U with
      | none =>
          have hEq : x = y ∧ T = U := by
            simpa [toDBAux, DBHasFVar, hL] using hHas
          rcases hEq with ⟨hx, hT⟩
          subst hx
          subst hT
          simp [Term.IsFreeVarIn]
      | some n =>
          have : False := by
            simp [toDBAux, DBHasFVar, hL] at hHas
          exact False.elim this
  | const c U =>
      intro x T _ hHas
      simp [toDBAux, DBHasFVar] at hHas
  | app s t ihs iht =>
      intro x T hDis hHas
      have hSplit : DBHasFVar x T (toDBAux ctx s) ∨ DBHasFVar x T (toDBAux ctx t) := by
        simpa [toDBAux, DBHasFVar] using hHas
      cases hSplit with
      | inl hs => exact Or.inl (ihs ctx x T hDis hs)
      | inr ht => exact Or.inr (iht ctx x T hDis ht)
  | abs n body ihn ihbody =>
      intro x T hDis hHas
      cases n with
      | var y U =>
          have hBodyHas : DBHasFVar x T (toDBAux ((y, U) :: ctx) body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          have hHead : x ≠ y ∨ T ≠ U := by
            by_cases hxy : x = y
            · by_cases hTU : T = U
              · subst hxy
                subst hTU
                exact False.elim ((no_DBHasFVar_under_bound ctx body x T) hBodyHas)
              · exact Or.inr hTU
            · exact Or.inl hxy
          have hDis' : CtxDisjoint ((y, U) :: ctx) x T := by
            intro y' U' hmem
            have hmem' : (y', U') = (y, U) ∨ (y', U') ∈ ctx := List.mem_cons.mp hmem
            cases hmem' with
            | inl hEq =>
                rcases Prod.mk.inj hEq with ⟨hy, hU⟩
                subst hy
                subst hU
                exact hHead
            | inr hTail =>
                exact hDis y' U' hTail
          have hBodyFree : (Term.var x T).IsFreeVarIn body :=
            ihbody ((y, U) :: ctx) x T hDis' hBodyHas
          have hneqTerm : Term.var x T ≠ Term.var y U := by
            intro hEq
            cases hEq
            cases hHead with
            | inl hxy => exact (hxy rfl).elim
            | inr hTU => exact (hTU rfl).elim
          exact And.intro hneqTerm hBodyFree
      | const y U =>
          have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          have hBodyFree : (Term.var x T).IsFreeVarIn body := ihbody ctx x T hDis hBodyHas
          have hneqTerm : Term.var x T ≠ Term.const y U := by
            intro hEq
            cases hEq
          exact And.intro hneqTerm hBodyFree
      | app n1 n2 =>
          have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          have hBodyFree : (Term.var x T).IsFreeVarIn body := ihbody ctx x T hDis hBodyHas
          have hneqTerm : Term.var x T ≠ Term.app n1 n2 := by
            intro hEq
            cases hEq
          exact And.intro hneqTerm hBodyFree
      | abs n1 n2 =>
          have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
            simpa [toDBAux, DBHasFVar] using hHas
          have hBodyFree : (Term.var x T).IsFreeVarIn body := ihbody ctx x T hDis hBodyHas
          have hneqTerm : Term.var x T ≠ Term.abs n1 n2 := by
            intro hEq
            cases hEq
          exact And.intro hneqTerm hBodyFree

theorem DBHasFVar_toDB_of_free :
    ∀ (t : Term) (x : String) (T : HOLType),
      (Term.var x T).IsFreeVarIn t -> DBHasFVar x T (toDB t) := by
  intro t x T hfree
  unfold toDB
  apply DBHasFVar_toDBAux_of_free [] t x T
  · intro y U hmem
    simp at hmem
  · exact hfree

theorem free_of_DBHasFVar_toDB :
    ∀ (t : Term) (x : String) (T : HOLType),
      DBHasFVar x T (toDB t) -> (Term.var x T).IsFreeVarIn t := by
  intro t x T hHas
  unfold toDB at hHas
  apply free_of_DBHasFVar_toDBAux [] t x T
  · intro y U hmem
    simp at hmem
  · exact hHas

theorem free_var_iff_of_alpha_wt :
    ∀ (t1 t2 : Term) (x : String) (T : HOLType),
      WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 ->
      ((Term.var x T).IsFreeVarIn t1 ↔ (Term.var x T).IsFreeVarIn t2) := by
  intro t1 t2 x T hwt1 hwt2 hAlpha
  have hEq : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
  constructor
  · intro hfree1
    have hHas1 : DBHasFVar x T (toDB t1) := DBHasFVar_toDB_of_free t1 x T hfree1
    have hHas2 : DBHasFVar x T (toDB t2) := by
      simpa [hEq] using hHas1
    exact free_of_DBHasFVar_toDB t2 x T hHas2
  · intro hfree2
    have hHas2 : DBHasFVar x T (toDB t2) := DBHasFVar_toDB_of_free t2 x T hfree2
    have hHas1 : DBHasFVar x T (toDB t1) := by
      simpa [hEq] using hHas2
    exact free_of_DBHasFVar_toDB t1 x T hHas1

theorem IsFreeVarIn_app_arg_false :
    ∀ (a b t : Term), ¬ (Term.app a b).IsFreeVarIn t := by
  intro a b t
  induction t with
  | var x T =>
      simp [Term.IsFreeVarIn]
  | const c T =>
      simp [Term.IsFreeVarIn]
  | app s t ihs iht =>
      intro h
      cases h with
      | inl hs => exact ihs hs
      | inr ht => exact iht ht
  | abs n t ihn iht =>
      intro h
      exact iht h.2

theorem IsFreeVarIn_abs_arg_false :
    ∀ (a b t : Term), ¬ (Term.abs a b).IsFreeVarIn t := by
  intro a b t
  induction t with
  | var x T =>
      simp [Term.IsFreeVarIn]
  | const c T =>
      simp [Term.IsFreeVarIn]
  | app s t ihs iht =>
      intro h
      cases h with
      | inl hs => exact ihs hs
      | inr ht => exact iht ht
  | abs n t ihn iht =>
      intro h
      exact iht h.2

/-- De Bruijn term contains constant node `(c,T)`. -/
def DBHasConst (c : String) (T : HOLType) : DBTerm -> Prop
| .bvar _ => False
| .fvar _ _ => False
| .const c' T' => c = c' ∧ T = T'
| .app s t => DBHasConst c T s ∨ DBHasConst c T t
| .abs t => DBHasConst c T t

theorem DBHasConst_toDBAux_of_free :
    ∀ (ctx : List (String × HOLType)) (t : Term) (c : String) (T : HOLType),
      (Term.const c T).IsFreeVarIn t -> DBHasConst c T (toDBAux ctx t) := by
  intro ctx t
  induction t generalizing ctx with
  | var x U =>
      intro c T hfree
      simp [Term.IsFreeVarIn] at hfree
  | const c' U =>
      intro c T hfree
      simpa [toDBAux, DBHasConst, Term.IsFreeVarIn] using hfree
  | app s t ihs iht =>
      intro c T hfree
      cases hfree with
      | inl hs => exact Or.inl (ihs ctx c T hs)
      | inr ht => exact Or.inr (iht ctx c T ht)
  | abs n body ihn ihbody =>
      intro c T hfree
      cases n with
      | var x U =>
          have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
          have hRec : DBHasConst c T (toDBAux ((x, U) :: ctx) body) := ihbody ((x, U) :: ctx) c T hBody
          simpa [toDBAux, DBHasConst] using hRec
      | const x U =>
          have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
          have hRec : DBHasConst c T (toDBAux ctx body) := ihbody ctx c T hBody
          simpa [toDBAux, DBHasConst] using hRec
      | app n1 n2 =>
          have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
          have hRec : DBHasConst c T (toDBAux ctx body) := ihbody ctx c T hBody
          simpa [toDBAux, DBHasConst] using hRec
      | abs n1 n2 =>
          have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
          have hRec : DBHasConst c T (toDBAux ctx body) := ihbody ctx c T hBody
          simpa [toDBAux, DBHasConst] using hRec

theorem DBHasConst_toDBAux_ctx_irrel :
    ∀ (ctx : List (String × HOLType)) (t : Term) (c : String) (T : HOLType),
      DBHasConst c T (toDBAux ctx t) ↔ DBHasConst c T (toDBAux [] t) := by
  intro ctx t
  induction t generalizing ctx with
  | var x U =>
      intro c T
      cases h : lookupBVar ctx x U with
      | none => simp [toDBAux, DBHasConst, h, lookupBVar]
      | some n => simp [toDBAux, DBHasConst, h, lookupBVar]
  | const c' U =>
      intro c T
      simp [toDBAux, DBHasConst]
  | app s t ihs iht =>
      intro c T
      constructor
      · intro h
        cases h with
        | inl hs => exact Or.inl ((ihs ctx c T).mp hs)
        | inr ht => exact Or.inr ((iht ctx c T).mp ht)
      · intro h
        cases h with
        | inl hs => exact Or.inl ((ihs ctx c T).mpr hs)
        | inr ht => exact Or.inr ((iht ctx c T).mpr ht)
  | abs n body ihn ihbody =>
      intro c T
      cases n with
      | var x U =>
          have h1 : DBHasConst c T (toDBAux ((x, U) :: ctx) body) ↔ DBHasConst c T (toDBAux [] body) :=
            ihbody ((x, U) :: ctx) c T
          have h2 : DBHasConst c T (toDBAux ((x, U) :: []) body) ↔ DBHasConst c T (toDBAux [] body) :=
            ihbody ((x, U) :: []) c T
          exact Iff.trans h1 h2.symm
      | const x U =>
          simpa [toDBAux, DBHasConst] using (ihbody ctx c T)
      | app n1 n2 =>
          simpa [toDBAux, DBHasConst] using (ihbody ctx c T)
      | abs n1 n2 =>
          simpa [toDBAux, DBHasConst] using (ihbody ctx c T)

theorem free_const_of_DBHasConst_toDB_wt :
    ∀ (t : Term) (c : String) (T : HOLType),
      WellTyped t -> DBHasConst c T (toDB t) -> (Term.const c T).IsFreeVarIn t := by
  intro t c T hwt
  rcases hwt with ⟨Ty, hty⟩
  induction hty with
  | var x U =>
      intro hHas
      have : False := by
        simp [toDB, toDBAux, DBHasConst, lookupBVar] at hHas
      exact False.elim this
  | const c' U =>
      intro hHas
      have hEq : c = c' ∧ T = U := by
        simpa [toDB, toDBAux, DBHasConst] using hHas
      rcases hEq with ⟨hc, hT⟩
      subst hc
      subst hT
      simp [Term.IsFreeVarIn]
  | app s t dT rT hs ht ihs iht =>
      intro hHas
      have hSplit : DBHasConst c T (toDB s) ∨ DBHasConst c T (toDB t) := by
        simpa [toDB, toDBAux, DBHasConst] using hHas
      cases hSplit with
      | inl hsHas => exact Or.inl (ihs hsHas)
      | inr htHas => exact Or.inr (iht htHas)
  | abs x dT rT body hbody ih =>
      intro hHas
      have hBodyCtx : DBHasConst c T (toDBAux ((x, dT) :: []) body) := by
        simpa [toDB, toDBAux, DBHasConst] using hHas
      have hBody0 : DBHasConst c T (toDB body) :=
        (DBHasConst_toDBAux_ctx_irrel ((x, dT) :: []) body c T).mp hBodyCtx
      have hBodyFree : (Term.const c T).IsFreeVarIn body := ih hBody0
      have hneq : Term.const c T ≠ Term.var x dT := by
        intro hEq
        cases hEq
      exact And.intro hneq hBodyFree

theorem free_const_iff_of_alpha_wt :
    ∀ (t1 t2 : Term) (c : String) (T : HOLType),
      WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 ->
      ((Term.const c T).IsFreeVarIn t1 ↔ (Term.const c T).IsFreeVarIn t2) := by
  intro t1 t2 c T hwt1 hwt2 hAlpha
  have hEq : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
  constructor
  · intro hfree1
    have hHas1 : DBHasConst c T (toDB t1) := DBHasConst_toDBAux_of_free [] t1 c T hfree1
    have hHas2 : DBHasConst c T (toDB t2) := by
      simpa [hEq] using hHas1
    exact free_const_of_DBHasConst_toDB_wt t2 c T hwt2 hHas2
  · intro hfree2
    have hHas2 : DBHasConst c T (toDB t2) := DBHasConst_toDBAux_of_free [] t2 c T hfree2
    have hHas1 : DBHasConst c T (toDB t1) := by
      simpa [hEq] using hHas2
    exact free_const_of_DBHasConst_toDB_wt t1 c T hwt1 hHas1

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
          let i'' := (bvar, z) :: i'
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
        let i'' := (bvar, z) :: i'
        rcases iht i'' with ⟨t2, ht2⟩
        refine ⟨Term.abs z t2, ?_⟩
        simp [subst, i', bvar, ht1, hcap]
        have ht2' :
            subst
                ((Term.var n dT, Term.var (generateVariant t1 n dT) dT) ::
                  List.filter (fun p => !decide (p.fst = Term.var n dT)) i)
                t = some t2 := by
          simpa [i'', z, bvar] using ht2
        simp [z, Option.bind, ht2']
      · have hcap' : captureRisk bvar t i' = false := by
          cases hc : captureRisk bvar t i' <;> simp [hc] at hcap ⊢
        refine ⟨Term.abs bvar t1, ?_⟩
        simp [subst, i', bvar, ht1, hcap']

def SubstOk (i : List (Term × Term)) : Prop :=
  ∀ v t, (v, t) ∈ i → ∃ x T, v = Term.var x T ∧ t.HasType T

/-- No constant appears on substitution LHS. -/
def SubstNoConstLHS (i : List (Term × Term)) : Prop :=
  ∀ v t, (v, t) ∈ i -> ¬ ∃ c T, v = Term.const c T

theorem SubstOk.toNoConstLHS : ∀ (i : List (Term × Term)),
    SubstOk i -> SubstNoConstLHS i := by
  intro i hOk
  intro v t hmem hconst
  rcases hOk v t hmem with ⟨x, T, hv, _⟩
  rcases hconst with ⟨c, U, hc⟩
  subst hv
  cases hc

theorem SubstOk.filter : ∀ (i : List (Term × Term)) (bvar : Term),
    SubstOk i -> SubstOk (i.filter (fun p => !decide (p.fst = bvar))) := by
  intro i bvar hOk
  intro v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

theorem subst_hasType_of_SubstOk :
    ∀ (t : Term) (T : HOLType) (i : List (Term × Term)),
      t.HasType T -> SubstOk i -> ∃ t', subst i t = some t' ∧ t'.HasType T := by
  intro t T i hty
  induction hty generalizing i with
  | var x T =>
      intro hOk
      unfold subst
      cases hfind : i.find? (fun (y, _) => y = Term.var x T) with
      | none =>
          refine ⟨Term.var x T, ?_, ?_⟩
          · simp
          · exact Term.HasType.var x T
      | some p =>
          rcases p with ⟨v, s⟩
          have hmem : (v, s) ∈ i := List.mem_of_find?_eq_some hfind
          have hpred : (fun q : Term × Term => decide (q.fst = Term.var x T)) (v, s) = true :=
            List.find?_some (p := fun q : Term × Term => decide (q.fst = Term.var x T)) hfind
          have hv : v = Term.var x T := by
            simp at hpred
            exact hpred
          rcases hOk v s hmem with ⟨x', T', hv', hsTy⟩
          cases hv'
          cases hv
          refine ⟨s, ?_, ?_⟩
          · simp
          · exact hsTy
  | const c T =>
      intro _
      refine ⟨Term.const c T, ?_, ?_⟩
      · rfl
      · exact Term.HasType.const c T
  | app s t dT rT hs ht ihs iht =>
      intro hOk
      rcases ihs i hOk with ⟨s', hsEq, hsTy⟩
      rcases iht i hOk with ⟨t', htEq, htTy⟩
      refine ⟨Term.app s' t', ?_, ?_⟩
      · simp [subst, hsEq, htEq]
      · exact Term.HasType.app s' t' dT rT hsTy htTy
  | abs n dT rT body hbody ih =>
      intro hOk
      let bvar := Term.var n dT
      let i' := i.filter (fun p => !decide (p.fst = bvar))
      have hOk' : SubstOk i' := SubstOk.filter i bvar hOk
      rcases ih i' hOk' with ⟨body', hSubBody, hBodyTy⟩
      by_cases hcap : captureRisk bvar body i' = true
      · let z := Term.var (generateVariant body' n dT) dT
        let i'' := (bvar, z) :: i'
        have hzTy : z.HasType dT := by
          dsimp [z]
          exact Term.HasType.var _ _
        have hOk'' : SubstOk i'' := by
          intro v t hmem
          rcases List.mem_cons.mp hmem with hhead | htail
          · cases hhead
            refine ⟨n, dT, rfl, hzTy⟩
          · exact hOk' v t htail
        rcases ih i'' hOk'' with ⟨body'', hSubBody2, hBodyTy2⟩
        refine ⟨Term.abs z body'', ?_, ?_⟩
        · simp [subst, i', bvar, hSubBody, hcap]
          have hSubBody2' :
              subst
                  ((Term.var n dT, Term.var (generateVariant body' n dT) dT) ::
                    List.filter (fun p => !decide (p.fst = Term.var n dT)) i)
                  body = some body'' := by
            simpa [i'', z, bvar, i'] using hSubBody2
          simp [z, Option.bind, hSubBody2']
        · exact Term.HasType.abs (generateVariant body' n dT) dT rT body'' hBodyTy2
      · have hcap' : captureRisk bvar body i' = false := by
          cases hc : captureRisk bvar body i' <;> simp [hc] at hcap ⊢
        refine ⟨Term.abs bvar body', ?_, ?_⟩
        · simp [subst, i', bvar, hSubBody, hcap']
        · simpa [bvar] using (Term.HasType.abs n dT rT body' hBodyTy)

theorem welltyped_subst_of_SubstOk :
    ∀ (t : Term) (i : List (Term × Term)),
      WellTyped t -> SubstOk i -> ∃ t', subst i t = some t' ∧ WellTyped t' := by
  intro t i hwt hOk
  rcases hwt with ⟨T, hty⟩
  rcases subst_hasType_of_SubstOk t T i hty hOk with ⟨t', hs, hty'⟩
  exact ⟨t', hs, ⟨T, hty'⟩⟩

/-- Substitution is well-typed and all RHS terms are closed. -/
def SubstOkClosed (i : List (Term × Term)) : Prop :=
  ∀ v t, (v, t) ∈ i → (∃ x T, v = Term.var x T ∧ t.HasType T) ∧ Closed t

theorem SubstOkClosed.toSubstOk : ∀ (i : List (Term × Term)),
    SubstOkClosed i → SubstOk i := by
  intro i hOk
  intro v t hmem
  exact (hOk v t hmem).1

theorem SubstOkClosed.filter : ∀ (i : List (Term × Term)) (bvar : Term),
    SubstOkClosed i -> SubstOkClosed (i.filter (fun p => !decide (p.fst = bvar))) := by
  intro i bvar hOk
  intro v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

theorem captureRisk_false_of_closed_rhs_var :
    ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)),
      (∀ v t, (v, t) ∈ i → Closed t) ->
      captureRisk (Term.var x T) body i = false := by
  intro x T body i hClosed
  unfold captureRisk
  rw [List.any_eq_false]
  intro p hp
  rcases p with ⟨v, t⟩
  intro h
  have hPair : (Term.var x T).IsFreeVarIn t ∧ v.IsFreeVarIn body := by
    simpa using h
  exact (hClosed v t hp) x T hPair.1

theorem captureRisk_false_of_SubstOkClosed_filter_var :
    ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
      SubstOkClosed i ->
      captureRisk (Term.var x T) body (i.filter (fun p => !decide (p.fst = Term.var x T))) = false := by
  intro i x T body hOk
  apply captureRisk_false_of_closed_rhs_var
  intro v t hmem
  exact (hOk v t (List.mem_filter.mp hmem).1).2

theorem subst_abs_no_rename_of_SubstOkClosed :
    ∀ (i : List (Term × Term)) (x : String) (dT : HOLType) (t t' : Term),
      SubstOkClosed i ->
      subst (i.filter (fun p => !decide (p.fst = Term.var x dT))) t = some t' ->
      subst i (Term.abs (Term.var x dT) t) = some (Term.abs (Term.var x dT) t') := by
  intro i x dT t t' hOk ht
  have hcap :
      captureRisk (Term.var x dT) t (i.filter (fun p => !decide (p.fst = Term.var x dT))) = false :=
    captureRisk_false_of_SubstOkClosed_filter_var i x dT t hOk
  simp [subst, ht, hcap]

theorem subst_pair_welltyped_of_SubstOk :
    ∀ (t1 t2 : Term) (i : List (Term × Term)),
      (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
      ∃ t1' t2',
        subst i t1 = some t1' ∧ subst i t2 = some t2' ∧
        WellTyped t1' ∧ WellTyped t2' := by
  intro t1 t2 i hwtEither hOk hAlpha
  have hBoth : WellTyped t1 ∧ WellTyped t2 := AlphaEqv.welltyped_both_of_either hAlpha hwtEither
  have hwt1 : WellTyped t1 := hBoth.1
  have hwt2 : WellTyped t2 := hBoth.2
  rcases welltyped_subst_of_SubstOk t1 i hwt1 hOk with ⟨t1', hs1, hwt1'⟩
  rcases welltyped_subst_of_SubstOk t2 i hwt2 hOk with ⟨t2', hs2, hwt2'⟩
  exact ⟨t1', t2', hs1, hs2, hwt1', hwt2'⟩

  theorem subst_toDB_commute_of_abs_case :
    (∀ (n : String) (dT rT : HOLType) (body t' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      subst i (Term.abs (Term.var n dT) body) = some t' ->
      toDB t' = dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
    ∀ (t t' : Term) (i : List (Term × Term)),
      WellTyped t -> SubstOk i -> subst i t = some t' ->
      toDB t' = dbSubst i (toDB t) := by
    intro hAbs t t' i hwt hOk hSub
    rcases hwt with ⟨T, hty⟩
    revert t' i hOk hSub
    induction hty with
    | var x T =>
      intro t' i hOk hSub
      unfold subst at hSub
      cases hfind : i.find? (fun (y, _) => y = Term.var x T) with
      | none =>
        simp [hfind] at hSub
        cases hSub
        exact (dbSubst_fvar_eq_of_find_none i x T hfind).symm
      | some p =>
        simp [hfind] at hSub
        cases hSub
        exact (dbSubst_fvar_eq_of_find_some i x T p.1 p.2 hfind).symm
    | const c T =>
      intro t' i hOk hSub
      simp [subst] at hSub
      cases hSub
      rfl
    | app s t dT rT hs ht ihs iht =>
      intro t' i hOk hSub
      unfold subst at hSub
      cases hs' : subst i s with
      | none =>
        simp [hs'] at hSub
      | some s' =>
        cases ht' : subst i t with
        | none =>
          simp [hs', ht'] at hSub
        | some t'' =>
          simp [hs', ht'] at hSub
          cases hSub
          have hS : toDB s' = dbSubst i (toDB s) := ihs s' i hOk hs'
          have hT : toDB t'' = dbSubst i (toDB t) := iht t'' i hOk ht'
          calc
            toDB (Term.app s' t'') = DBTerm.app (toDB s') (toDB t'') := by rfl
            _ = DBTerm.app (dbSubst i (toDB s)) (dbSubst i (toDB t)) := by
              simp [hS, hT]
            _ = dbSubst i (toDB (Term.app s t)) := by
              rfl
    | abs n dT rT body hbody ihbody =>
      intro t' i hOk hSub
      exact hAbs n dT rT body t' i hbody hOk hSub

theorem subst_toDB_abs_case_of_branches :
    (∀ (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = false ->
      toDB (Term.abs (Term.var n dT) body') = dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
    (∀ (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = true ->
      let z := Term.var (generateVariant body' n dT) dT
      let i'' := (Term.var n dT, z) :: i'
      subst i'' body = some body'' ->
      toDB (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
        dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
    ∀ (n : String) (dT rT : HOLType) (body t' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      subst i (Term.abs (Term.var n dT) body) = some t' ->
      toDB t' = dbSubst i (toDB (Term.abs (Term.var n dT) body)) := by
  intro hNoCap hCap n dT rT body t' i hBodyTy hOk hSub
  let bvar := Term.var n dT
  let i' := i.filter (fun p => !decide (p.fst = bvar))
  unfold subst at hSub
  cases hBody : subst i' body with
  | none =>
      simp [i', bvar, hBody] at hSub
  | some body' =>
      by_cases hRisk : captureRisk bvar body i' = true
      · let z : Term := Term.var (generateVariant body' n dT) dT
        let i'' : List (Term × Term) := (Term.var n dT, z) :: i'
        cases hBody2 : subst i'' body with
        | none =>
            simp [i', bvar, hBody, hRisk, z, i'', hBody2] at hSub
        | some body'' =>
            simp [i', bvar, hBody, hRisk, z, i'', hBody2] at hSub
            cases hSub
            have hCapMain :=
              hCap n dT rT body body' body'' i hBodyTy hOk
                (by simpa [i', bvar] using hBody)
                hRisk
                (by simpa [z, i''] using hBody2)
            simpa [i', bvar, z, i''] using hCapMain
      · have hRiskFalse : captureRisk bvar body i' = false := by
          cases hc : captureRisk bvar body i' <;> simp [hc] at hRisk ⊢
        simp [i', bvar, hBody, hRiskFalse] at hSub
        cases hSub
        have hNoCapMain := hNoCap n dT rT body body' i hBodyTy hOk (by simpa [i', bvar] using hBody) hRiskFalse
        simpa [i', bvar] using hNoCapMain

theorem subst_toDB_abs_no_capture_of_ctx_eq :
    ∀ (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = false ->
      toDBAux ((n, dT) :: []) body' = dbSubst i' (toDBAux ((n, dT) :: []) body) ->
      toDB (Term.abs (Term.var n dT) body') = dbSubst i (toDB (Term.abs (Term.var n dT) body)) := by
  intro n dT rT body body' i hBodyTy hOk i' hBodySub hRiskFalse hCtxEq
  calc
    toDB (Term.abs (Term.var n dT) body') = DBTerm.abs (toDBAux ((n, dT) :: []) body') := by
      rfl
    _ = DBTerm.abs (dbSubst i' (toDBAux ((n, dT) :: []) body)) := by
      simp [hCtxEq]
    _ = DBTerm.abs (dbSubst i (toDBAux ((n, dT) :: []) body)) := by
      have hFilterBack :
          dbSubst i' (toDBAux ((n, dT) :: []) body) =
          dbSubst i (toDBAux ((n, dT) :: []) body) := by
        simpa [i'] using dbSubst_filter_eq_under_bound [] body i n dT
      simpa using congrArg DBTerm.abs hFilterBack
    _ = dbSubst i (toDB (Term.abs (Term.var n dT) body)) := by
      rfl

theorem subst_toDB_abs_capture_of_ctx_eq :
    ∀ (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = true ->
      let z := Term.var (generateVariant body' n dT) dT
      let i'' := (Term.var n dT, z) :: i'
      subst i'' body = some body'' ->
      toDBAux ((generateVariant body' n dT, dT) :: []) body'' =
        dbSubst i'' (toDBAux ((n, dT) :: []) body) ->
      toDB (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
        dbSubst i (toDB (Term.abs (Term.var n dT) body)) := by
  intro n dT rT body body' body'' i hBodyTy hOk i' hBodySub hRisk z i'' hBodySub2 hCtxEq
  let dBody := toDBAux ((n, dT) :: []) body
  have hNoBound : ¬ DBHasFVar n dT dBody := by
    simpa [dBody] using no_DBHasFVar_under_bound [] body n dT
  have hConsDrop :
      dbSubst ((Term.var n dT, z) :: i') dBody = dbSubst i' dBody := by
    simpa [dBody] using
      dbSubst_cons_eq_of_no_DBHasFVar dBody i' n dT z hNoBound
  have hFilterBack : dbSubst i' dBody = dbSubst i dBody := by
    simpa [dBody, i'] using dbSubst_filter_eq_under_bound [] body i n dT
  calc
    toDB (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
        DBTerm.abs (toDBAux ((generateVariant body' n dT, dT) :: []) body'') := by
      rfl
    _ = DBTerm.abs (dbSubst i'' dBody) := by
      simpa [dBody] using congrArg DBTerm.abs hCtxEq
    _ = DBTerm.abs (dbSubst i' dBody) := by
      simpa [i''] using congrArg DBTerm.abs hConsDrop
    _ = DBTerm.abs (dbSubst i dBody) := by
      simpa using congrArg DBTerm.abs hFilterBack
    _ = dbSubst i (toDB (Term.abs (Term.var n dT) body)) := by
      rfl

theorem subst_alpha_of_SubstOk_of_toDB_subst :
    (∀ (t t' : Term) (i : List (Term × Term)),
      WellTyped t -> SubstOk i -> subst i t = some t' ->
      toDB t' = dbSubst i (toDB t)) ->
    ∀ (t1 t2 : Term) (i : List (Term × Term)),
      (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
      ∃ t1' t2',
        subst i t1 = some t1' ∧ subst i t2 = some t2' ∧ AlphaEqv t1' t2' := by
  intro hToDB t1 t2 i hwtEither hOk hAlpha
  have hBoth : WellTyped t1 ∧ WellTyped t2 := AlphaEqv.welltyped_both_of_either hAlpha hwtEither
  have hwt1 : WellTyped t1 := hBoth.1
  have hwt2 : WellTyped t2 := hBoth.2
  rcases subst_pair_welltyped_of_SubstOk t1 t2 i hwtEither hOk hAlpha with
    ⟨t1', t2', hs1, hs2, hwt1', hwt2'⟩
  have hEqIn : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
  have hEq1 : toDB t1' = dbSubst i (toDB t1) := hToDB t1 t1' i hwt1 hOk hs1
  have hEq2 : toDB t2' = dbSubst i (toDB t2) := hToDB t2 t2' i hwt2 hOk hs2
  have hEqDb : dbSubst i (toDB t1) = dbSubst i (toDB t2) :=
    dbSubst_eq_of_eq i (toDB t1) (toDB t2) hEqIn
  have hEqOut : toDB t1' = toDB t2' := by
    calc
      toDB t1' = dbSubst i (toDB t1) := hEq1
      _ = dbSubst i (toDB t2) := hEqDb
      _ = toDB t2' := hEq2.symm
  have hAlphaOut : AlphaEqv t1' t2' := AlphaEqv_of_toDB_eq_wt t1' t2' hwt1' hwt2' hEqOut
  exact ⟨t1', t2', hs1, hs2, hAlphaOut⟩

theorem subst_alpha_of_SubstOk_of_abs_case :
    (∀ (n : String) (dT rT : HOLType) (body t' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      subst i (Term.abs (Term.var n dT) body) = some t' ->
      toDB t' = dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
    ∀ (t1 t2 : Term) (i : List (Term × Term)),
      (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
      ∃ t1' t2',
        subst i t1 = some t1' ∧ subst i t2 = some t2' ∧ AlphaEqv t1' t2' := by
  intro hAbs
  apply subst_alpha_of_SubstOk_of_toDB_subst
  intro t t' i hwt hOk hSub
  exact subst_toDB_commute_of_abs_case hAbs t t' i hwt hOk hSub

theorem subst_alpha_of_SubstOk_of_branches :
    (∀ (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = false ->
      toDB (Term.abs (Term.var n dT) body') = dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
    (∀ (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = true ->
      let z := Term.var (generateVariant body' n dT) dT
      let i'' := (Term.var n dT, z) :: i'
      subst i'' body = some body'' ->
      toDB (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
        dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
    ∀ (t1 t2 : Term) (i : List (Term × Term)),
      (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
      ∃ t1' t2',
        subst i t1 = some t1' ∧ subst i t2 = some t2' ∧ AlphaEqv t1' t2' := by
  intro hNoCap hCap
  apply subst_alpha_of_SubstOk_of_abs_case
  intro n dT rT body t' i hBodyTy hOk hSub
  exact subst_toDB_abs_case_of_branches hNoCap hCap n dT rT body t' i hBodyTy hOk hSub

theorem subst_alpha_of_SubstOk_of_ctx_branches :
    (∀ (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = false ->
      toDBAux ((n, dT) :: []) body' = dbSubst i' (toDBAux ((n, dT) :: []) body)) ->
    (∀ (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
      body.HasType rT -> SubstOk i ->
      let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
      subst i' body = some body' ->
      captureRisk (Term.var n dT) body i' = true ->
      let z := Term.var (generateVariant body' n dT) dT
      let i'' := (Term.var n dT, z) :: i'
      subst i'' body = some body'' ->
      toDBAux ((generateVariant body' n dT, dT) :: []) body'' =
        dbSubst i'' (toDBAux ((n, dT) :: []) body)) ->
    ∀ (t1 t2 : Term) (i : List (Term × Term)),
      (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
      ∃ t1' t2',
        subst i t1 = some t1' ∧ subst i t2 = some t2' ∧ AlphaEqv t1' t2' := by
  intro hNoCapCtx hCapCtx
  apply subst_alpha_of_SubstOk_of_branches
  · intro n dT rT body body' i hBodyTy hOk i' hBodySub hRiskFalse
    have hBodySub' :
        subst (i.filter (fun p => !decide (p.fst = Term.var n dT))) body = some body' := by
      simpa [i'] using hBodySub
    have hRiskFalse' :
        captureRisk (Term.var n dT) body (i.filter (fun p => !decide (p.fst = Term.var n dT))) = false := by
      simpa [i'] using hRiskFalse
    have hCtxEq' :
        toDBAux ((n, dT) :: []) body' =
          dbSubst (i.filter (fun p => !decide (p.fst = Term.var n dT))) (toDBAux ((n, dT) :: []) body) := by
      simpa [i'] using hNoCapCtx n dT rT body body' i hBodyTy hOk hBodySub' hRiskFalse'
    exact subst_toDB_abs_no_capture_of_ctx_eq n dT rT body body' i hBodyTy hOk hBodySub' hRiskFalse' hCtxEq'
  · intro n dT rT body body' body'' i hBodyTy hOk i' hBodySub hRisk z i'' hBodySub2
    have hBodySub' :
        subst (i.filter (fun p => !decide (p.fst = Term.var n dT))) body = some body' := by
      simpa [i'] using hBodySub
    have hRisk' :
        captureRisk (Term.var n dT) body (i.filter (fun p => !decide (p.fst = Term.var n dT))) = true := by
      simpa [i'] using hRisk
    have hBodySub2' :
        subst ((Term.var n dT, Term.var (generateVariant body' n dT) dT) ::
          (i.filter (fun p => !decide (p.fst = Term.var n dT)))) body = some body'' := by
      simpa [i', i'', z] using hBodySub2
    have hCtxEq' :
        toDBAux ((generateVariant body' n dT, dT) :: []) body'' =
          dbSubst ((Term.var n dT, Term.var (generateVariant body' n dT) dT) ::
            (i.filter (fun p => !decide (p.fst = Term.var n dT)))) (toDBAux ((n, dT) :: []) body) := by
      simpa [i', i'', z] using hCapCtx n dT rT body body' body'' i hBodyTy hOk hBodySub' hRisk' hBodySub2'
    exact subst_toDB_abs_capture_of_ctx_eq n dT rT body body' body'' i hBodyTy hOk hBodySub' hRisk' hBodySub2' hCtxEq'

theorem subst_alpha_of_SubstOk_of_toDBAux_subst :
    (∀ (ctx : List (String × HOLType)) (t t' : Term) (i : List (Term × Term)),
      WellTyped t -> SubstOk i -> subst i t = some t' ->
      toDBAux ctx t' = dbSubst i (toDBAux ctx t)) ->
    (∀ (n : String) (dT : HOLType) (body body' : Term) (i : List (Term × Term)),
      dbSubst i (toDBAux ((generateVariant body' n dT, dT) :: []) body) =
        dbSubst i (toDBAux ((n, dT) :: []) body)) ->
    ∀ (t1 t2 : Term) (i : List (Term × Term)),
      (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
      ∃ t1' t2', subst i t1 = some t1' ∧ subst i t2 = some t2' ∧ AlphaEqv t1' t2' := by
  intro hCtxComm hBridge
  apply subst_alpha_of_SubstOk_of_ctx_branches
  · intro n dT rT body body' i hBodyTy hOk i' hBodySub hRiskFalse
    have hOk' : SubstOk i' := by
      simpa [i'] using SubstOk.filter i (Term.var n dT) hOk
    have hBodySub' : subst i' body = some body' := by
      exact hBodySub
    exact hCtxComm ((n, dT) :: []) body body' i' ⟨rT, hBodyTy⟩ hOk' hBodySub'
  · intro n dT rT body body' body'' i hBodyTy hOk i' hBodySub hRisk z i'' hBodySub2
    have hOk' : SubstOk i' := by
      simpa [i'] using SubstOk.filter i (Term.var n dT) hOk
    have hzTy : z.HasType dT := by
      simpa [z] using (Term.HasType.var (generateVariant body' n dT) dT)
    have hOk'' : SubstOk i'' := by
      intro v t hmem
      have hmem' : (v, t) ∈ (Term.var n dT, z) :: i' := by
        simpa [i''] using hmem
      rcases List.mem_cons.mp hmem' with hhead | htail
      · cases hhead
        exact ⟨n, dT, rfl, hzTy⟩
      · exact hOk' v t htail
    have hComm :
        toDBAux ((generateVariant body' n dT, dT) :: []) body'' =
          dbSubst i'' (toDBAux ((generateVariant body' n dT, dT) :: []) body) :=
      hCtxComm ((generateVariant body' n dT, dT) :: []) body body'' i'' ⟨rT, hBodyTy⟩ hOk'' hBodySub2
    have hBridge' :
        dbSubst i'' (toDBAux ((generateVariant body' n dT, dT) :: []) body) =
          dbSubst i'' (toDBAux ((n, dT) :: []) body) :=
      hBridge n dT body body' i''
    exact Eq.trans hComm hBridge'

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
