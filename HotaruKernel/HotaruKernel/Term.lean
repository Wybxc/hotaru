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

abbrev WellTypedTerm := { t : Term // WellTyped t }

/-- Type inference function for terms. -/
def typeof? (t : Term) : Option HOLType :=
  match t with
  | .var _ T => some T
  | .const _ T => some T
  | .app s t =>
      match typeof? s, typeof? t with
      | some (.fun dT rT), some tT =>
          if dT = tT then some rT else none
      | _, _ => none
  | .abs (.var _ dT) t =>
      match typeof? t with
      | some rT => some (.fun dT rT)
      | none => none
  | _ => none

theorem welltyped_typeof? : ∀ (t : Term) (T : HOLType), Term.HasType t T → typeof? t = some T
    := by
  intros t T ht
  induction ht with simp [typeof?] <;> aesop

theorem typeof?_welltyped : ∀ (t : Term) (T : HOLType), typeof? t = some T → t.HasType T
    := by
  intros t T h
  induction t generalizing T with try simp [typeof?] at h; subst h
  | var x T' => apply Term.HasType.var
  | const c T' => apply Term.HasType.const
  | app s t ih_s ih_t =>
      unfold typeof? at h
      split at h
      · rename_i dT rT tT heq_s heq_t
        split at h <;> simp at h
        subst h
        apply Term.HasType.app
        · exact ih_s (.fun dT rT) heq_s
        · have : typeof? t = some dT := by
            rw [heq_t]; aesop
          exact ih_t dT this
      · simp at h
  | abs n t ih_n ih_t =>
      cases n with simp [typeof?] at h
      | var var_name dT =>
          split at h <;> simp at h
          subst h
          apply Term.HasType.abs
          aesop

def typeof (t : WellTypedTerm) : HOLType :=
  Option.get (typeof? t.1) <| by
    rcases t.2 with ⟨T, hHasType⟩
    have hSome : typeof? t.1 = some T := welltyped_typeof? t.1 T hHasType
    simp [hSome]

theorem typeof_welltyped : ∀ (t : WellTypedTerm) {T : HOLType}, typeof t = T → t.1.HasType T := by
  intro wt T hT
  rcases wt with ⟨t, hwt⟩
  rcases hwt with ⟨U, hHasType⟩
  have hTy : typeof? t = some U := welltyped_typeof? t U hHasType
  have hTypeof : typeof ⟨t, ⟨U, hHasType⟩⟩ = U := by
    unfold typeof
    simp [hTy]
  aesop

theorem welltyped_typeof : ∀ (t : WellTypedTerm) {T : HOLType}, t.1.HasType T → typeof t = T := by
  intro wt T hHasType
  rcases wt with ⟨t, hwt⟩
  have hTy : typeof? t = some T := welltyped_typeof? t T hHasType
  unfold typeof
  simp [hTy]

theorem welltyped_fun : ∀ (s t : Term), WellTyped (Term.app s t) → WellTyped s := by
  intros s t h
  rcases h with ⟨T, hT⟩
  cases hT with
  | app _ _ dT rT hs _ =>
  exact ⟨_, hs⟩

theorem welltyped_arg : ∀ (s t : Term), WellTyped (Term.app s t) → WellTyped t := by
  intros s t h
  rcases h with ⟨_, hT⟩
  cases hT with
  | app _ _ dT _ _ ht =>
      exact ⟨dT, ht⟩

theorem welltyped_bind : ∀ (x t : Term), WellTyped (Term.abs x t) → ∃ n T, x = Term.var n T := by
  intros x t h
  rcases h with ⟨_, hT⟩
  cases hT with
  | abs n dT _ _ _ =>
      exact ⟨n, dT, rfl⟩

theorem welltyped_body : ∀ (x t : Term), WellTyped (Term.abs x t) → WellTyped t := by
  intros x t h
  rcases h with ⟨_, hT⟩
  cases hT with
  | abs _ _ rT _ ht =>
      exact ⟨rT, ht⟩


-- theorem IsAlphaTerms_welltyped_iff :
--     ∀ {bv : List (Term × Term)} {t1 t2 : Term}, IsAlphaTerms bv t1 t2 → (WellTyped t1 ↔ WellTyped t2) := by
--   intro bv t1 t2 h
--   induction h with
--   | var bv x1 x2 T1 T2 hv =>
--       constructor <;> intro _ <;> exact ⟨_, Term.HasType.var _ _⟩
--   | const bv c1 c2 T1 T2 hv =>
--       constructor <;> intro _ <;> exact ⟨_, Term.HasType.const _ _⟩
--   | app bv s1 s2 t1 t2 hs ht ihs iht =>
--     exact hwt
--   | abs bv n1 n2 t1 t2 hwt hbody ih =>
--     exact hwt

-- theorem AlphaEqv.welltyped_iff : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → (WellTyped t1 ↔ WellTyped t2) := by
--   intro t1 t2 h
--   simpa [AlphaEqv] using IsAlphaTerms_welltyped_iff h

-- theorem AlphaEqv.welltyped_right : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → WellTyped t1 → WellTyped t2 := by
--   intro t1 t2 h hwt1
--   exact (AlphaEqv.welltyped_iff h).mp hwt1

-- theorem AlphaEqv.welltyped_left : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → WellTyped t2 → WellTyped t1 := by
--   intro t1 t2 h hwt2
--   exact (AlphaEqv.welltyped_iff h).mpr hwt2

-- theorem AlphaEqv.welltyped_both_of_either :
--     ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → (WellTyped t1 ∨ WellTyped t2) → (WellTyped t1 ∧ WellTyped t2) := by
--   intro t1 t2 hAlpha hEither
--   cases hEither with
--   | inl hwt1 => exact ⟨hwt1, AlphaEqv.welltyped_right hAlpha hwt1⟩
--   | inr hwt2 => exact ⟨AlphaEqv.welltyped_left hAlpha hwt2, hwt2⟩




-- /-- Lookup binder depth in a de Bruijn context. -/
-- def lookupBVar : List (String × HOLType) -> String -> HOLType -> Option Nat
-- | [], _, _ => none
-- | (y, Uy) :: ys, x, U =>
--     if (x = y ∧ U = Uy) then
--       some 0
--     else
--       Option.map Nat.succ (lookupBVar ys x U)

-- /-- Convert a named term to de Bruijn form under a context. -/
-- def toDBAux (ctx : List (String × HOLType)) : Term -> DBTerm
-- | .var x T =>
--     match lookupBVar ctx x T with
--   | some n => DBTerm.bvar n
--     | none => DBTerm.fvar x T
-- | .const c T => DBTerm.const c T
-- | .app s t => DBTerm.app (toDBAux ctx s) (toDBAux ctx t)
-- | .abs (.var x T) t => DBTerm.abs (toDBAux ((x, T) :: ctx) t)
-- | .abs _ t => DBTerm.abs (toDBAux ctx t)

-- /-- Convert a named term to de Bruijn form. -/
-- def toDB (t : Term) : DBTerm := toDBAux [] t


-- /-- Context-aware de Bruijn substitution: RHS terms are translated under the given context. -/
-- def dbSubstAux (ctx : List (String × HOLType)) (i : List (Term × Term)) : DBTerm -> DBTerm
-- | .bvar n => .bvar n
-- | .fvar x T =>
--   match i.find? (fun p => p.fst = Term.var x T) with
--   | some (_, t) => toDBAux ctx t
--   | none => .fvar x T
-- | .const c T => .const c T
-- | .app s t => .app (dbSubstAux ctx i s) (dbSubstAux ctx i t)
-- | .abs t => .abs (dbSubstAux ctx i t)

-- theorem dbSubstAux_nil_eq_dbSubst :
--   ∀ (i : List (Term × Term)) (t : DBTerm), dbSubstAux [] i t = dbSubst i t := by
--   intro i t
--   induction t with
--   | bvar n =>
--     rfl
--   | fvar x T =>
--     unfold dbSubstAux dbSubst
--     split <;> simp [toDB]
--   | const c T =>
--     rfl
--   | app s t ihs iht =>
--     simp [dbSubstAux, dbSubst, ihs, iht]
--   | abs t iht =>
--     simp [dbSubstAux, dbSubst, iht]

-- theorem dbSubst_refl : ∀ (t : DBTerm), dbSubst [] t = t := by
--   intro t
--   induction t with
--   | bvar n => rfl
--   | fvar x T => simp [dbSubst]
--   | const c T => rfl
--   | app s t ihs iht => simp [dbSubst, ihs, iht]
--   | abs t iht => simp [dbSubst, iht]

-- theorem dbSubst_eq_of_eq : ∀ (i : List (Term × Term)) (t1 t2 : DBTerm),
--     t1 = t2 -> dbSubst i t1 = dbSubst i t2 := by
--   intro i t1 t2 h
--   cases h
--   rfl

-- theorem dbSubst_fvar_eq_of_find_some :
--     ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (v s : Term),
--       i.find? (fun p => p.fst = Term.var x T) = some (v, s) ->
--       dbSubst i (DBTerm.fvar x T) = toDB s := by
--   intro i x T v s hFind
--   unfold dbSubst
--   simp [hFind]

-- theorem dbSubst_fvar_eq_of_find_none :
--     ∀ (i : List (Term × Term)) (x : String) (T : HOLType),
--       i.find? (fun p => p.fst = Term.var x T) = none ->
--       dbSubst i (DBTerm.fvar x T) = DBTerm.fvar x T := by
--   intro i x T hFind
--   unfold dbSubst
--   simp [hFind]

-- theorem dbSubstAux_fvar_eq_of_find_some :
--     ∀ (ctx : List (String × HOLType)) (i : List (Term × Term))
--       (x : String) (T : HOLType) (v s : Term),
--       i.find? (fun p => p.fst = Term.var x T) = some (v, s) ->
--       dbSubstAux ctx i (DBTerm.fvar x T) = toDBAux ctx s := by
--   intro ctx i x T v s hFind
--   unfold dbSubstAux
--   simp [hFind]

-- theorem dbSubstAux_fvar_eq_of_find_none :
--     ∀ (ctx : List (String × HOLType)) (i : List (Term × Term)) (x : String) (T : HOLType),
--       i.find? (fun p => p.fst = Term.var x T) = none ->
--       dbSubstAux ctx i (DBTerm.fvar x T) = DBTerm.fvar x T := by
--   intro ctx i x T hFind
--   unfold dbSubstAux
--   simp [hFind]

-- theorem find?_filter_eq_find?_of_var_ne :
--     ∀ (i : List (Term × Term)) (x y : String) (T U : HOLType),
--       Term.var y U ≠ Term.var x T ->
--       (i.filter (fun p => !decide (p.fst = Term.var x T))).find? (fun p => p.fst = Term.var y U)
--         = i.find? (fun p => p.fst = Term.var y U) := by
--   intro i x y T U hne
--   induction i with
--   | nil =>
--       simp
--   | cons p ps ih =>
--       rcases p with ⟨v, t⟩
--       by_cases hvx : v = Term.var x T
--       · have hvy : v ≠ Term.var y U := by
--           intro hvy
--           apply hne
--           calc
--             Term.var y U = v := hvy.symm
--             _ = Term.var x T := hvx
--         have hxyu : ¬ (x = y ∧ T = U) := by
--           intro h
--           rcases h with ⟨hxy, hTU⟩
--           apply hne
--           subst hxy
--           subst hTU
--           rfl
--         simp [List.find?, hvx, hxyu, ih]
--       · by_cases hvy : v = Term.var y U
--         · subst v
--           simp [List.find?, hvx]
--         · simp [List.find?, hvx, hvy, ih]

-- theorem lookupBVar_cons_hit :
--     ∀ (ctx : List (String × HOLType)) (x : String) (T : HOLType),
--       lookupBVar ((x, T) :: ctx) x T = some 0 := by
--   intro ctx x T
--   simp [lookupBVar]

-- theorem lookupBVar_cons_miss :
--     ∀ (ctx : List (String × HOLType)) (x y : String) (T U : HOLType),
--       (x ≠ y ∨ T ≠ U) ->
--       lookupBVar ((y, U) :: ctx) x T = Option.map Nat.succ (lookupBVar ctx x T) := by
--   intro ctx x y T U h
--   have hxyu : ¬(x = y ∧ T = U) := by
--     intro hxy
--     rcases hxy with ⟨hx, hT⟩
--     cases h with
--     | inl hxy' => exact hxy' hx
--     | inr hT' => exact hT' hT
--   simp [lookupBVar, hxyu]

-- theorem lookupBVar_cons_eq_some_zero_iff :
--     ∀ (ctx : List (String × HOLType)) (x y : String) (T U : HOLType),
--       lookupBVar ((y, U) :: ctx) x T = some 0 ↔ x = y ∧ T = U := by
--   intro ctx x y T U
--   by_cases h : (x = y ∧ T = U)
--   · simp [lookupBVar, h]
--   · simp [lookupBVar, h]

-- theorem lookupBVar_cons_eq_some_succ_iff :
--     ∀ (ctx : List (String × HOLType)) (x y : String) (T U : HOLType) (n : Nat),
--       lookupBVar ((y, U) :: ctx) x T = some (Nat.succ n) ↔
--       (x ≠ y ∨ T ≠ U) ∧ lookupBVar ctx x T = some n := by
--   intro ctx x y T U n
--   by_cases h : (x = y ∧ T = U)
--   · have hFalse : (x ≠ y ∨ T ≠ U) = False := by
--       apply propext
--       constructor
--       · intro h'
--         rcases h with ⟨hx, hT⟩
--         cases h' with
--         | inl hxy => exact (hxy hx).elim
--         | inr hTU => exact (hTU hT).elim
--       · intro h'
--         cases h'
--     simp [lookupBVar, h]
--   · have hTrue : (x ≠ y ∨ T ≠ U) = True := by
--       apply propext
--       constructor
--       · intro _
--         trivial
--       · intro _
--         by_cases hxy : x = y
--         · right
--           intro hTU
--           apply h
--           exact ⟨hxy, hTU⟩
--         · exact Or.inl hxy
--     simp [lookupBVar, h, hTrue]

-- /-- Relation between alpha-renaming environment and paired de Bruijn contexts. -/
-- inductive DBCtxRel : List (Term × Term) -> List (String × HOLType) -> List (String × HOLType) -> Prop
-- | nil : DBCtxRel [] [] []
-- | cons : ∀ (x y : String) (T1 T2 : HOLType)
--     (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType)),
--     DBCtxRel bv ctx1 ctx2 ->
--   DBCtxRel ((Term.var x T1, Term.var y T2) :: bv) ((x, T1) :: ctx1) ((y, T2) :: ctx2)

-- theorem var_ne_disj :
--     ∀ (x y : String) (T U : HOLType),
--       Term.var x T ≠ Term.var y U -> (x ≠ y ∨ T ≠ U) := by
--   intro x y T U h
--   by_cases hxy : x = y
--   · right
--     intro hTU
--     apply h
--     subst hxy
--     subst hTU
--     rfl
--   · exact Or.inl hxy

-- theorem lookupBVar_eq_of_IsAlphaVars_var :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (x1 x2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
--       lookupBVar ctx1 x1 T1 = lookupBVar ctx2 x2 T2 := by
--   intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha
--   induction hCtx generalizing x1 x2 T1 T2 with
--   | nil =>
--       dsimp [IsAlphaVars] at hAlpha
--       cases hAlpha
--       rfl
--   | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
--       dsimp [IsAlphaVars] at hAlpha
--       rcases hAlpha with hHit | hMiss
--       · rcases hHit with ⟨hx1, hx2⟩
--         cases hx1
--         cases hx2
--         simp [lookupBVar]
--       · rcases hMiss with ⟨hneq1, hneq2, hTail⟩
--         have hdisj1 : x1 ≠ x ∨ T1 ≠ TL := var_ne_disj x1 x T1 TL hneq1
--         have hdisj2 : x2 ≠ y ∨ T2 ≠ TR := var_ne_disj x2 y T2 TR hneq2
--         rw [lookupBVar_cons_miss ctx1 x1 x T1 TL hdisj1]
--         rw [lookupBVar_cons_miss ctx2 x2 y T2 TR hdisj2]
--         have hrec : lookupBVar ctx1 x1 T1 = lookupBVar ctx2 x2 T2 :=
--           ih x1 x2 T1 T2 hTail
--         simpa using congrArg (Option.map Nat.succ) hrec

-- theorem free_eq_of_IsAlphaVars_var_lookup_none :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (x1 x2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
--       lookupBVar ctx1 x1 T1 = none ->
--       x1 = x2 ∧ T1 = T2 := by
--   intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha hNone
--   induction hCtx generalizing x1 x2 T1 T2 with
--   | nil =>
--       dsimp [IsAlphaVars] at hAlpha
--       cases hAlpha
--       exact ⟨rfl, rfl⟩
--   | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
--       dsimp [IsAlphaVars] at hAlpha
--       rcases hAlpha with hHit | hMiss
--       · rcases hHit with ⟨hx1, _⟩
--         cases hx1
--         simp [lookupBVar] at hNone
--       · rcases hMiss with ⟨hneq1, _, hTail⟩
--         have hdisj1 : x1 ≠ x ∨ T1 ≠ TL := var_ne_disj x1 x T1 TL hneq1
--         rw [lookupBVar_cons_miss ctx1 x1 x T1 TL hdisj1] at hNone
--         cases htail : lookupBVar ctx1 x1 T1 with
--         | none =>
--             exact ih x1 x2 T1 T2 hTail htail
--         | some n =>
--             simp [htail] at hNone

-- theorem toDBAux_var_eq_of_IsAlphaVars :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (x1 x2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
--       toDBAux ctx1 (.var x1 T1) = toDBAux ctx2 (.var x2 T2) := by
--   intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha
--   have hLookup : lookupBVar ctx1 x1 T1 = lookupBVar ctx2 x2 T2 :=
--     lookupBVar_eq_of_IsAlphaVars_var bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha
--   cases hL : lookupBVar ctx1 x1 T1 with
--   | none =>
--       have hR : lookupBVar ctx2 x2 T2 = none := by simpa [hL] using hLookup.symm
--       have hFree : x1 = x2 ∧ T1 = T2 :=
--         free_eq_of_IsAlphaVars_var_lookup_none bv ctx1 ctx2 x1 x2 T1 T2 hCtx hAlpha hL
--       rcases hFree with ⟨hx, hT⟩
--       subst hx
--       subst hT
--       simp [toDBAux, hL, hR]
--   | some n =>
--       have hR : lookupBVar ctx2 x2 T2 = some n := by simpa [hL] using hLookup.symm
--       simp [toDBAux, hL, hR]

-- theorem const_eq_of_IsAlphaVars :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (c1 c2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       IsAlphaVars bv (.const c1 T1) (.const c2 T2) ->
--       c1 = c2 ∧ T1 = T2 := by
--   intro bv ctx1 ctx2 c1 c2 T1 T2 hCtx hAlpha
--   induction hCtx generalizing c1 c2 T1 T2 with
--   | nil =>
--       dsimp [IsAlphaVars] at hAlpha
--       cases hAlpha
--       exact ⟨rfl, rfl⟩
--   | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
--       dsimp [IsAlphaVars] at hAlpha
--       rcases hAlpha with hHit | hMiss
--       · rcases hHit with ⟨h1, _⟩
--         cases h1
--       · rcases hMiss with ⟨_, _, hTail⟩
--         exact ih c1 c2 T1 T2 hTail

-- theorem toDBAux_const_eq_of_IsAlphaVars :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (c1 c2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       IsAlphaVars bv (.const c1 T1) (.const c2 T2) ->
--       toDBAux ctx1 (.const c1 T1) = toDBAux ctx2 (.const c2 T2) := by
--   intro bv ctx1 ctx2 c1 c2 T1 T2 hCtx hAlpha
--   rcases const_eq_of_IsAlphaVars bv ctx1 ctx2 c1 c2 T1 T2 hCtx hAlpha with ⟨hc, hT⟩
--   subst hc
--   subst hT
--   rfl

-- theorem IsAlphaVars_const_refl_of_DBCtxRel :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType)) (c : String) (T : HOLType),
--       DBCtxRel bv ctx1 ctx2 -> IsAlphaVars bv (.const c T) (.const c T) := by
--   intro bv ctx1 ctx2 c T hCtx
--   induction hCtx with
--   | nil => simp [IsAlphaVars]
--   | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
--       right
--       constructor
--       · intro hEq
--         cases hEq
--       constructor
--       · intro hEq
--         cases hEq
--       · exact ih

-- theorem IsAlphaVars_of_toDBAux_const_eq :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (c1 c2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       toDBAux ctx1 (.const c1 T1) = toDBAux ctx2 (.const c2 T2) ->
--       IsAlphaVars bv (.const c1 T1) (.const c2 T2) := by
--   intro bv ctx1 ctx2 c1 c2 T1 T2 hCtx hEq
--   simp [toDBAux] at hEq
--   rcases hEq with ⟨hc, hT⟩
--   subst hc
--   subst hT
--   exact IsAlphaVars_const_refl_of_DBCtxRel bv ctx1 ctx2 c1 T1 hCtx

-- theorem IsAlphaVars_of_lookup_eq_some :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (x1 x2 : String) (T1 T2 : HOLType) (n : Nat),
--       DBCtxRel bv ctx1 ctx2 ->
--       lookupBVar ctx1 x1 T1 = some n ->
--       lookupBVar ctx2 x2 T2 = some n ->
--       IsAlphaVars bv (.var x1 T1) (.var x2 T2) := by
--   intro bv ctx1 ctx2 x1 x2 T1 T2 n hCtx hL1 hL2
--   induction hCtx generalizing x1 x2 T1 T2 n with
--   | nil =>
--       simp [lookupBVar] at hL1
--   | cons x y TL TR bv ctx1 ctx2 hCtx ih =>
--       cases n with
--       | zero =>
--           have h1 : x1 = x ∧ T1 = TL :=
--             (lookupBVar_cons_eq_some_zero_iff ctx1 x1 x T1 TL).mp hL1
--           have h2 : x2 = y ∧ T2 = TR :=
--             (lookupBVar_cons_eq_some_zero_iff ctx2 x2 y T2 TR).mp hL2
--           rcases h1 with ⟨hx1, hT1⟩
--           rcases h2 with ⟨hx2, hT2⟩
--           left
--           constructor
--           · cases hx1
--             cases hT1
--             rfl
--           · cases hx2
--             cases hT2
--             rfl
--       | succ n =>
--           have h1 : (x1 ≠ x ∨ T1 ≠ TL) ∧ lookupBVar ctx1 x1 T1 = some n :=
--             (lookupBVar_cons_eq_some_succ_iff ctx1 x1 x T1 TL n).mp hL1
--           have h2 : (x2 ≠ y ∨ T2 ≠ TR) ∧ lookupBVar ctx2 x2 T2 = some n :=
--             (lookupBVar_cons_eq_some_succ_iff ctx2 x2 y T2 TR n).mp hL2
--           rcases h1 with ⟨hdisj1, hTail1⟩
--           rcases h2 with ⟨hdisj2, hTail2⟩
--           have hneq1 : Term.var x1 T1 ≠ Term.var x TL := by
--             intro hEq
--             cases hEq
--             cases hdisj1 with
--             | inl hxy => exact (hxy rfl).elim
--             | inr hT => exact (hT rfl).elim
--           have hneq2 : Term.var x2 T2 ≠ Term.var y TR := by
--             intro hEq
--             cases hEq
--             cases hdisj2 with
--             | inl hxy => exact (hxy rfl).elim
--             | inr hT => exact (hT rfl).elim
--           right
--           exact ⟨hneq1, hneq2, ih x1 x2 T1 T2 n hTail1 hTail2⟩

-- theorem IsAlphaVars_of_lookup_none_eq :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (x : String) (T : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       lookupBVar ctx1 x T = none ->
--       lookupBVar ctx2 x T = none ->
--       IsAlphaVars bv (.var x T) (.var x T) := by
--   intro bv ctx1 ctx2 x T hCtx hNone1 hNone2
--   induction hCtx generalizing x T with
--   | nil =>
--       simp [IsAlphaVars]
--   | cons xl xr TL TR bv ctx1 ctx2 hCtx ih =>
--       have hdisj1 : x ≠ xl ∨ T ≠ TL := by
--         by_cases h : x = xl ∧ T = TL
--         · have : lookupBVar ((xl, TL) :: ctx1) x T = some 0 := by
--             simp [lookupBVar, h]
--           simp [hNone1] at this
--         · by_cases hxy : x = xl
--           · right
--             intro hT
--             exact h ⟨hxy, hT⟩
--           · exact Or.inl hxy
--       have hdisj2 : x ≠ xr ∨ T ≠ TR := by
--         by_cases h : x = xr ∧ T = TR
--         · have : lookupBVar ((xr, TR) :: ctx2) x T = some 0 := by
--             simp [lookupBVar, h]
--           simp [hNone2] at this
--         · by_cases hxy : x = xr
--           · right
--             intro hT
--             exact h ⟨hxy, hT⟩
--           · exact Or.inl hxy
--       have hTail1 : lookupBVar ctx1 x T = none := by
--         rw [lookupBVar_cons_miss ctx1 x xl T TL hdisj1] at hNone1
--         cases hlookup : lookupBVar ctx1 x T with
--         | none => rfl
--         | some n => simp [hlookup] at hNone1
--       have hTail2 : lookupBVar ctx2 x T = none := by
--         rw [lookupBVar_cons_miss ctx2 x xr T TR hdisj2] at hNone2
--         cases hlookup : lookupBVar ctx2 x T with
--         | none => rfl
--         | some n => simp [hlookup] at hNone2
--       have hneq1 : Term.var x T ≠ Term.var xl TL := by
--         intro hEq
--         cases hEq
--         cases hdisj1 with
--         | inl hxy => exact (hxy rfl).elim
--         | inr hT => exact (hT rfl).elim
--       have hneq2 : Term.var x T ≠ Term.var xr TR := by
--         intro hEq
--         cases hEq
--         cases hdisj2 with
--         | inl hxy => exact (hxy rfl).elim
--         | inr hT => exact (hT rfl).elim
--       right
--       exact ⟨hneq1, hneq2, ih x T hTail1 hTail2⟩

-- theorem IsAlphaVars_of_toDBAux_var_eq :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (x1 x2 : String) (T1 T2 : HOLType),
--       DBCtxRel bv ctx1 ctx2 ->
--       toDBAux ctx1 (.var x1 T1) = toDBAux ctx2 (.var x2 T2) ->
--       IsAlphaVars bv (.var x1 T1) (.var x2 T2) := by
--   intro bv ctx1 ctx2 x1 x2 T1 T2 hCtx hEq
--   dsimp [toDBAux] at hEq
--   cases hL1 : lookupBVar ctx1 x1 T1 with
--   | none =>
--       cases hL2 : lookupBVar ctx2 x2 T2 with
--       | none =>
--           simp [hL1, hL2] at hEq
--           rcases hEq with ⟨hx, hT⟩
--           subst hx
--           subst hT
--           exact IsAlphaVars_of_lookup_none_eq bv ctx1 ctx2 x1 T1 hCtx hL1 hL2
--       | some n =>
--           simp [hL1, hL2] at hEq
--   | some n =>
--       cases hL2 : lookupBVar ctx2 x2 T2 with
--       | none =>
--           simp [hL1, hL2] at hEq
--       | some m =>
--           have hnm : n = m := by
--             simp [hL1, hL2] at hEq
--             exact hEq
--           subst hnm
--           exact IsAlphaVars_of_lookup_eq_some bv ctx1 ctx2 x1 x2 T1 T2 n hCtx hL1 hL2

--   theorem toDBAux_eq_of_IsAlphaTerms_wt :
--     ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--       (t1 t2 : Term),
--       DBCtxRel bv ctx1 ctx2 ->
--       WellTyped t1 -> WellTyped t2 ->
--       IsAlphaTerms bv t1 t2 ->
--       toDBAux ctx1 t1 = toDBAux ctx2 t2 := by
--     intro bv ctx1 ctx2 t1 t2 hCtx hwt1 hwt2 hAlpha
--     induction hAlpha generalizing ctx1 ctx2 with
--     | var bv x1 x2 T1 T2 hv =>
--       exact toDBAux_var_eq_of_IsAlphaVars bv ctx1 ctx2 x1 x2 T1 T2 hCtx hv
--     | const bv c1 c2 T1 T2 hv =>
--       exact toDBAux_const_eq_of_IsAlphaVars bv ctx1 ctx2 c1 c2 T1 T2 hCtx hv
--     | app bv s1 s2 t1 t2 hwt hs ht ihs iht =>
--       rcases hwt1 with ⟨_, hty1⟩
--       rcases hwt2 with ⟨_, hty2⟩
--       cases hty1 with
--       | app _ _ _ _ hs1 ht1 =>
--         cases hty2 with
--         | app _ _ _ _ hs2 ht2 =>
--           have hsEq : toDBAux ctx1 s1 = toDBAux ctx2 s2 :=
--             ihs ctx1 ctx2 hCtx ⟨_, hs1⟩ ⟨_, hs2⟩
--           have htEq : toDBAux ctx1 t1 = toDBAux ctx2 t2 :=
--             iht ctx1 ctx2 hCtx ⟨_, ht1⟩ ⟨_, ht2⟩
--           simp [toDBAux, hsEq, htEq]
--     | abs bv n1 n2 t1 t2 hwt hbody ih =>
--       rcases hwt1 with ⟨_, hty1⟩
--       rcases hwt2 with ⟨_, hty2⟩
--       cases hty1 with
--       | abs x1 dT1 rT1 body1 hbody1 =>
--         cases hty2 with
--         | abs x2 dT2 rT2 body2 hbody2 =>
--           have hCtx' :
--             DBCtxRel
--             ((Term.var x1 dT1, Term.var x2 dT2) :: bv)
--             ((x1, dT1) :: ctx1)
--             ((x2, dT2) :: ctx2) := by
--             exact DBCtxRel.cons x1 x2 dT1 dT2 bv ctx1 ctx2 hCtx
--           have hRec :
--             toDBAux ((x1, dT1) :: ctx1) t1 =
--             toDBAux ((x2, dT2) :: ctx2) t2 :=
--             ih ((x1, dT1) :: ctx1) ((x2, dT2) :: ctx2) hCtx' ⟨rT1, hbody1⟩ ⟨rT2, hbody2⟩
--           simpa [toDBAux] using hRec

--   theorem IsAlphaTerms_of_toDBAux_eq_wt :
--       ∀ (bv : List (Term × Term)) (ctx1 ctx2 : List (String × HOLType))
--         (t1 t2 : Term),
--         DBCtxRel bv ctx1 ctx2 ->
--         WellTyped t1 -> WellTyped t2 ->
--         toDBAux ctx1 t1 = toDBAux ctx2 t2 ->
--         IsAlphaTerms bv t1 t2 := by
--     intro bv ctx1 ctx2 t1 t2 hCtx hwt1 hwt2 hEq
--     rcases hwt1 with ⟨T1, ht1⟩
--     revert bv ctx1 ctx2 t2 hCtx hwt2 hEq
--     induction ht1 with
--     | var x1 T1 =>
--         intro bv ctx1 ctx2 t2 hCtx hwt2 hEq
--         rcases hwt2 with ⟨T2, ht2⟩
--         cases ht2 with
--         | var x2 T2 =>
--             apply IsAlphaTerms.var
--             exact IsAlphaVars_of_toDBAux_var_eq bv ctx1 ctx2 x1 x2 T1 T2 hCtx hEq
--         | const c2 T2 =>
--           cases hL : lookupBVar ctx1 x1 T1 <;> simp [toDBAux, hL] at hEq
--         | app s2 t2 dT2 rT2 hs2 ht2 =>
--           cases hL : lookupBVar ctx1 x1 T1 <;> simp [toDBAux, hL] at hEq
--         | abs n2 dT2 rT2 body2 hbody2 =>
--           cases hL : lookupBVar ctx1 x1 T1 <;> simp [toDBAux, hL] at hEq
--     | const c1 T1 =>
--         intro bv ctx1 ctx2 t2 hCtx hwt2 hEq
--         rcases hwt2 with ⟨T2, ht2⟩
--         cases ht2 with
--         | var x2 T2 =>
--           cases hL : lookupBVar ctx2 x2 T2 <;> simp [toDBAux, hL] at hEq
--         | const c2 T2 =>
--             apply IsAlphaTerms.const
--             exact IsAlphaVars_of_toDBAux_const_eq bv ctx1 ctx2 c1 c2 T1 T2 hCtx hEq
--         | app s2 t2 dT2 rT2 hs2 ht2 =>
--           cases hEq
--         | abs n2 dT2 rT2 body2 hbody2 =>
--           cases hEq
--     | app s1 t1 dT1 rT1 hs1 ht1 ihs iht =>
--         intro bv ctx1 ctx2 u hCtx hwu hEq
--         rcases hwu with ⟨U, hu⟩
--         cases hu with
--         | var x2 T2 =>
--           cases hL : lookupBVar ctx2 x2 U <;> simp [toDBAux, hL] at hEq
--         | const c2 T2 =>
--             cases hEq
--         | app s2 t2 dT2 rT2 hs2 ht2 =>
--             have hEqApp :
--                 DBTerm.app (toDBAux ctx1 s1) (toDBAux ctx1 t1) =
--                 DBTerm.app (toDBAux ctx2 s2) (toDBAux ctx2 t2) := by
--               simpa [toDBAux] using hEq
--             have hInj : toDBAux ctx1 s1 = toDBAux ctx2 s2 ∧ toDBAux ctx1 t1 = toDBAux ctx2 t2 := by
--               injection hEqApp with hsEq htEq
--               exact ⟨hsEq, htEq⟩
--             have hsEq : toDBAux ctx1 s1 = toDBAux ctx2 s2 := hInj.1
--             have htEq : toDBAux ctx1 t1 = toDBAux ctx2 t2 := hInj.2
--             have hAlphaS : IsAlphaTerms bv s1 s2 :=
--               ihs bv ctx1 ctx2 s2 hCtx ⟨_, hs2⟩ hsEq
--             have hAlphaT : IsAlphaTerms bv t1 t2 :=
--               iht bv ctx1 ctx2 t2 hCtx ⟨dT2, ht2⟩ htEq
--             have hwtApp1 : WellTyped (Term.app s1 t1) :=
--               ⟨rT1, Term.HasType.app s1 t1 dT1 rT1 hs1 ht1⟩
--             have hwtApp2 : WellTyped (Term.app s2 t2) :=
--               ⟨_, Term.HasType.app s2 t2 dT2 _ hs2 ht2⟩
--             refine IsAlphaTerms.app bv s1 s2 t1 t2 ?_ hAlphaS hAlphaT
--             constructor <;> intro _
--             · exact hwtApp2
--             · exact hwtApp1
--         | abs n2 dT2 rT2 body2 hbody2 =>
--             cases hEq
--     | abs n1 dT1 rT1 body1 hbody1 ihbody =>
--         intro bv ctx1 ctx2 u hCtx hwu hEq
--         rcases hwu with ⟨U, hu⟩
--         cases hu with
--         | var x2 T2 =>
--           cases hL : lookupBVar ctx2 x2 U <;> simp [toDBAux, hL] at hEq
--         | const c2 T2 =>
--           cases hEq
--         | app s2 t2 dT2 rT2 hs2 ht2 =>
--           cases hEq
--         | abs n2 dT2 rT2 body2 hbody2 =>
--             have hEqBody :
--                 toDBAux ((n1, dT1) :: ctx1) body1 =
--                 toDBAux ((n2, dT2) :: ctx2) body2 := by
--               simpa [toDBAux] using hEq
--             have hCtx' :
--                 DBCtxRel ((Term.var n1 dT1, Term.var n2 dT2) :: bv)
--                   ((n1, dT1) :: ctx1) ((n2, dT2) :: ctx2) := by
--               exact DBCtxRel.cons n1 n2 dT1 dT2 bv ctx1 ctx2 hCtx
--             have hAlphaBody :
--                 IsAlphaTerms ((Term.var n1 dT1, Term.var n2 dT2) :: bv) body1 body2 :=
--               ihbody ((Term.var n1 dT1, Term.var n2 dT2) :: bv)
--                 ((n1, dT1) :: ctx1) ((n2, dT2) :: ctx2) body2 hCtx' ⟨_, hbody2⟩ hEqBody
--             have hwtAbs1 : WellTyped (Term.abs (Term.var n1 dT1) body1) :=
--               ⟨HOLType.fun dT1 rT1, Term.HasType.abs n1 dT1 rT1 body1 hbody1⟩
--             have hwtAbs2 : WellTyped (Term.abs (Term.var n2 dT2) body2) :=
--               ⟨_, Term.HasType.abs n2 dT2 _ body2 hbody2⟩
--             refine IsAlphaTerms.abs bv (Term.var n1 dT1) (Term.var n2 dT2) body1 body2 ?_ hAlphaBody
--             constructor <;> intro _
--             · exact hwtAbs2
--             · exact hwtAbs1

--   theorem toDB_eq_of_AlphaEqv_wt :
--     ∀ (t1 t2 : Term), WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 -> toDB t1 = toDB t2 := by
--     intro t1 t2 hwt1 hwt2 hAlpha
--     simpa [toDB] using toDBAux_eq_of_IsAlphaTerms_wt [] [] [] t1 t2 DBCtxRel.nil hwt1 hwt2 hAlpha

--   theorem AlphaEqv_of_toDB_eq_wt :
--       ∀ (t1 t2 : Term), WellTyped t1 -> WellTyped t2 -> toDB t1 = toDB t2 -> AlphaEqv t1 t2 := by
--     intro t1 t2 hwt1 hwt2 hEq
--     simpa [AlphaEqv, toDB] using
--       IsAlphaTerms_of_toDBAux_eq_wt [] [] [] t1 t2 DBCtxRel.nil hwt1 hwt2 hEq

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

-- /-- De Bruijn term has no free-variable nodes. -/
-- def DBClosed : DBTerm -> Prop
-- | .bvar _ => True
-- | .fvar _ _ => False
-- | .const _ _ => True
-- | .app s t => DBClosed s ∧ DBClosed t
-- | .abs t => DBClosed t

-- theorem toDBAux_DBClosed_of_wt_covered :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (T : HOLType),
--       t.HasType T ->
--       (∀ x U, (Term.var x U).IsFreeVarIn t -> ∃ n, lookupBVar ctx x U = some n) ->
--       DBClosed (toDBAux ctx t) := by
--   intro ctx t T hty
--   induction hty generalizing ctx with
--   | var x T =>
--       intro hCov
--       have hfree : (Term.var x T).IsFreeVarIn (Term.var x T) := by
--         simp [Term.IsFreeVarIn]
--       rcases hCov x T hfree with ⟨n, hn⟩
--       simp [toDBAux, hn, DBClosed]
--   | const c T =>
--       intro _
--       simp [toDBAux, DBClosed]
--   | app s t dT rT hs ht ihs iht =>
--       intro hCov
--       have hsCov : ∀ x U, (Term.var x U).IsFreeVarIn s -> ∃ n, lookupBVar ctx x U = some n := by
--         intro x U hfree
--         exact hCov x U (Or.inl hfree)
--       have htCov : ∀ x U, (Term.var x U).IsFreeVarIn t -> ∃ n, lookupBVar ctx x U = some n := by
--         intro x U hfree
--         exact hCov x U (Or.inr hfree)
--       exact And.intro (ihs ctx hsCov) (iht ctx htCov)
--   | abs n dT rT t ht iht =>
--       intro hCov
--       have hBodyCov :
--           ∀ x U, (Term.var x U).IsFreeVarIn t ->
--           ∃ m, lookupBVar ((n, dT) :: ctx) x U = some m := by
--         intro x U hfree
--         by_cases hx : x = n
--         · by_cases hU : U = dT
--           · subst hx
--             subst hU
--             exact ⟨0, by simp [lookupBVar]⟩
--           · have hneq : Term.var x U ≠ Term.var n dT := by
--               intro hEq
--               cases hEq
--               exact hU rfl
--             have hfreeAbs : (Term.var x U).IsFreeVarIn (Term.abs (Term.var n dT) t) :=
--               And.intro hneq hfree
--             rcases hCov x U hfreeAbs with ⟨m, hm⟩
--             refine ⟨Nat.succ m, ?_⟩
--             rw [lookupBVar_cons_miss ctx x n U dT (Or.inr hU)]
--             simp [hm]
--         · have hneq : Term.var x U ≠ Term.var n dT := by
--             intro hEq
--             cases hEq
--             exact hx rfl
--           have hfreeAbs : (Term.var x U).IsFreeVarIn (Term.abs (Term.var n dT) t) :=
--             And.intro hneq hfree
--           rcases hCov x U hfreeAbs with ⟨m, hm⟩
--           refine ⟨Nat.succ m, ?_⟩
--           rw [lookupBVar_cons_miss ctx x n U dT (Or.inl hx)]
--           simp [hm]
--       have hBodyClosed : DBClosed (toDBAux ((n, dT) :: ctx) t) :=
--         iht ((n, dT) :: ctx) hBodyCov
--       simpa [toDBAux, DBClosed] using hBodyClosed

-- theorem covered_of_toDBAux_DBClosed_wt :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (T : HOLType),
--       t.HasType T ->
--       DBClosed (toDBAux ctx t) ->
--       ∀ x U, (Term.var x U).IsFreeVarIn t -> ∃ n, lookupBVar ctx x U = some n := by
--   intro ctx t T hty
--   induction hty generalizing ctx with
--   | var x T =>
--       intro hDb y U hfree
--       have hEq : Term.var y U = Term.var x T := by
--         simpa [Term.IsFreeVarIn] using hfree
--       cases hEq
--       cases hL : lookupBVar ctx x T with
--       | none =>
--           have : False := by
--             have hDb' := hDb
--             simp [toDBAux, DBClosed, hL] at hDb'
--           exact False.elim this
--       | some n =>
--           exact ⟨n, rfl⟩
--   | const c T =>
--       intro _ x U hfree
--       have : False := by
--         simp [Term.IsFreeVarIn] at hfree
--       exact False.elim this
--   | app s t dT rT hs ht ihs iht =>
--       intro hDb x U hfree
--       have hPair : DBClosed (toDBAux ctx s) ∧ DBClosed (toDBAux ctx t) := by
--         simpa [toDBAux, DBClosed] using hDb
--       rcases hPair with ⟨hsDb, htDb⟩
--       cases hfree with
--       | inl hsFree => exact ihs ctx hsDb x U hsFree
--       | inr htFree => exact iht ctx htDb x U htFree
--   | abs n dT rT t ht iht =>
--       intro hDb x U hfree
--       rcases hfree with ⟨hneq, hfreeBody⟩
--       have hBodyDb : DBClosed (toDBAux ((n, dT) :: ctx) t) := by
--         simpa [toDBAux, DBClosed] using hDb
--       rcases iht ((n, dT) :: ctx) hBodyDb x U hfreeBody with ⟨m, hm⟩
--       cases m with
--       | zero =>
--           have hEq : x = n ∧ U = dT :=
--             (lookupBVar_cons_eq_some_zero_iff ctx x n U dT).mp hm
--           rcases hEq with ⟨hx, hU⟩
--           apply False.elim
--           apply hneq
--           simp [hx, hU]
--       | succ k =>
--           have hSucc : (x ≠ n ∨ U ≠ dT) ∧ lookupBVar ctx x U = some k :=
--             (lookupBVar_cons_eq_some_succ_iff ctx x n U dT k).mp hm
--           exact ⟨k, hSucc.2⟩

-- theorem toDB_DBClosed_of_wt_closed :
--     ∀ (t : Term), WellTyped t -> Closed t -> DBClosed (toDB t) := by
--   intro t hwt hClosed
--   rcases hwt with ⟨T, hty⟩
--   unfold toDB
--   apply toDBAux_DBClosed_of_wt_covered [] t T hty
--   intro x U hfree
--   exact False.elim (hClosed x U hfree)

-- theorem closed_of_toDB_DBClosed_wt :
--     ∀ (t : Term), WellTyped t -> DBClosed (toDB t) -> Closed t := by
--   intro t hwt hDb
--   rcases hwt with ⟨T, hty⟩
--   intro x U hfree
--   have hCov : ∃ n, lookupBVar [] x U = some n := by
--     have hDbAux : DBClosed (toDBAux [] t) := by simpa [toDB] using hDb
--     exact covered_of_toDBAux_DBClosed_wt [] t T hty hDbAux x U hfree
--   rcases hCov with ⟨n, hn⟩
--   simp [lookupBVar] at hn

-- theorem closed_of_alpha_wt_left :
--     ∀ (t1 t2 : Term),
--       WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 -> Closed t1 -> Closed t2 := by
--   intro t1 t2 hwt1 hwt2 hAlpha hClosed1
--   have hEq : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
--   have hDb1 : DBClosed (toDB t1) := toDB_DBClosed_of_wt_closed t1 hwt1 hClosed1
--   have hDb2 : DBClosed (toDB t2) := by
--     simpa [hEq] using hDb1
--   exact closed_of_toDB_DBClosed_wt t2 hwt2 hDb2

-- /-- Variable `(x,T)` is disjoint from all binders in `ctx`. -/
-- def CtxDisjoint (ctx : List (String × HOLType)) (x : String) (T : HOLType) : Prop :=
--   ∀ y U, (y, U) ∈ ctx -> (x ≠ y ∨ T ≠ U)

-- /-- De Bruijn term contains free-variable node `(x,T)`. -/
-- def DBHasFVar (x : String) (T : HOLType) : DBTerm -> Prop
-- | .bvar _ => False
-- | .fvar y U => x = y ∧ T = U
-- | .const _ _ => False
-- | .app s t => DBHasFVar x T s ∨ DBHasFVar x T t
-- | .abs t => DBHasFVar x T t

-- theorem dbSubst_filter_eq_of_no_DBHasFVar :
--     ∀ (d : DBTerm) (i : List (Term × Term)) (x : String) (T : HOLType),
--       ¬ DBHasFVar x T d ->
--       dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) d = dbSubst i d := by
--   intro d
--   induction d with
--   | bvar n =>
--       intro i x T _
--       rfl
--   | fvar y U =>
--       intro i x T hNo
--       have hneq : Term.var y U ≠ Term.var x T := by
--         intro hEq
--         apply hNo
--         cases hEq
--         exact And.intro rfl rfl
--       unfold dbSubst
--       rw [find?_filter_eq_find?_of_var_ne i x y T U hneq]
--   | const c U =>
--       intro i x T _
--       rfl
--   | app s t ihs iht =>
--       intro i x T hNo
--       have hsNo : ¬ DBHasFVar x T s := by
--         intro hs
--         exact hNo (Or.inl hs)
--       have htNo : ¬ DBHasFVar x T t := by
--         intro ht
--         exact hNo (Or.inr ht)
--       simp [dbSubst, ihs i x T hsNo, iht i x T htNo]
--   | abs body ih =>
--       intro i x T hNo
--       simp [dbSubst, ih i x T hNo]

-- theorem dbSubst_cons_eq_of_no_DBHasFVar :
--     ∀ (d : DBTerm) (i : List (Term × Term)) (x : String) (T : HOLType) (s : Term),
--       ¬ DBHasFVar x T d ->
--       dbSubst ((Term.var x T, s) :: i) d = dbSubst i d := by
--   intro d
--   induction d with
--   | bvar n =>
--       intro i x T s _
--       rfl
--   | fvar y U =>
--       intro i x T s hNo
--       have hneq : Term.var y U ≠ Term.var x T := by
--         intro hEq
--         apply hNo
--         cases hEq
--         exact And.intro rfl rfl
--       unfold dbSubst
--       have hxyu : ¬ (x = y ∧ T = U) := by
--         intro h
--         rcases h with ⟨hxy, hTU⟩
--         apply hneq
--         subst hxy
--         subst hTU
--         rfl
--       simp [List.find?, hxyu]
--   | const c U =>
--       intro i x T s _
--       rfl
--   | app a b iha ihb =>
--       intro i x T s hNo
--       have hNoA : ¬ DBHasFVar x T a := by
--         intro ha
--         exact hNo (Or.inl ha)
--       have hNoB : ¬ DBHasFVar x T b := by
--         intro hb
--         exact hNo (Or.inr hb)
--       simp [dbSubst, iha i x T s hNoA, ihb i x T s hNoB]
--   | abs body ih =>
--       intro i x T s hNo
--       simp [dbSubst, ih i x T s hNo]

-- theorem no_DBHasFVar_of_lookup_some :
--     ∀ (ctx : List (String × HOLType)) (body : Term) (x : String) (T : HOLType) (n : Nat),
--       lookupBVar ctx x T = some n ->
--       DBHasFVar x T (toDBAux ctx body) -> False := by
--   intro ctx body x T n hLookup hHas
--   induction body generalizing ctx n with
--   | var y U =>
--       cases hL : lookupBVar ctx y U with
--       | none =>
--           have hEq : x = y ∧ T = U := by
--             simpa [toDBAux, DBHasFVar, hL] using hHas
--           rcases hEq with ⟨hx, hTU⟩
--           subst hx
--           subst hTU
--           rw [hL] at hLookup
--           simp at hLookup
--       | some m =>
--             simp [toDBAux, DBHasFVar, hL] at hHas
--   | const c U =>
--           simp [toDBAux, DBHasFVar] at hHas
--   | app s t ihs iht =>
--       have hSplit : DBHasFVar x T (toDBAux ctx s) ∨ DBHasFVar x T (toDBAux ctx t) := by
--         simpa [toDBAux, DBHasFVar] using hHas
--       cases hSplit with
--           | inl hs => exact ihs ctx n hLookup hs
--           | inr ht => exact iht ctx n hLookup ht
--   | abs nvar body ihn ihbody =>
--       cases nvar with
--       | var y U =>
--           have hBodyHas : DBHasFVar x T (toDBAux ((y, U) :: ctx) body) := by
--             simpa [toDBAux, DBHasFVar] using hHas
--           by_cases hxyu : (x = y ∧ T = U)
--           · have hLookup' : lookupBVar ((y, U) :: ctx) x T = some 0 := by
--               simp [lookupBVar, hxyu]
--             exact ihbody ((y, U) :: ctx) 0 hLookup' hBodyHas
--           · have hLookup' : lookupBVar ((y, U) :: ctx) x T = some (Nat.succ n) := by
--               simp [lookupBVar, hxyu, hLookup]
--             exact ihbody ((y, U) :: ctx) (Nat.succ n) hLookup' hBodyHas
--       | const y U =>
--           have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
--             simpa [toDBAux, DBHasFVar] using hHas
--           exact ihbody ctx n hLookup hBodyHas
--       | app n1 n2 =>
--           have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
--             simpa [toDBAux, DBHasFVar] using hHas
--           exact ihbody ctx n hLookup hBodyHas
--       | abs n1 n2 =>
--           have hBodyHas : DBHasFVar x T (toDBAux ctx body) := by
--             simpa [toDBAux, DBHasFVar] using hHas
--           exact ihbody ctx n hLookup hBodyHas

-- theorem no_DBHasFVar_under_bound :
--     ∀ (ctx : List (String × HOLType)) (body : Term) (x : String) (T : HOLType),
--       ¬ DBHasFVar x T (toDBAux ((x, T) :: ctx) body) := by
--   intro ctx body x T
--   have hLookup : lookupBVar ((x, T) :: ctx) x T = some 0 := by
--     simp [lookupBVar]
--   intro hHas
--   exact no_DBHasFVar_of_lookup_some ((x, T) :: ctx) body x T 0 hLookup hHas

-- theorem dbSubst_filter_eq_under_bound :
--     ∀ (ctx : List (String × HOLType)) (body : Term) (i : List (Term × Term)) (x : String) (T : HOLType),
--       dbSubst (i.filter (fun p => !decide (p.fst = Term.var x T))) (toDBAux ((x, T) :: ctx) body) =
--         dbSubst i (toDBAux ((x, T) :: ctx) body) := by
--   intro ctx body i x T
--   apply dbSubst_filter_eq_of_no_DBHasFVar
--   exact no_DBHasFVar_under_bound ctx body x T

-- theorem dbSubstAux_filter_eq_of_no_DBHasFVar :
--     ∀ (ctx : List (String × HOLType)) (d : DBTerm) (i : List (Term × Term)) (x : String) (T : HOLType),
--       ¬ DBHasFVar x T d ->
--       dbSubstAux ctx (i.filter (fun p => !decide (p.fst = Term.var x T))) d = dbSubstAux ctx i d := by
--   intro ctx d
--   induction d with
--   | bvar n =>
--       intro i x T _
--       rfl
--   | fvar y U =>
--       intro i x T hNo
--       have hneq : Term.var y U ≠ Term.var x T := by
--         intro hEq
--         apply hNo
--         cases hEq
--         exact And.intro rfl rfl
--       unfold dbSubstAux
--       rw [find?_filter_eq_find?_of_var_ne i x y T U hneq]
--   | const c U =>
--       intro i x T _
--       rfl
--   | app a b iha ihb =>
--       intro i x T hNo
--       have hNoA : ¬ DBHasFVar x T a := by
--         intro ha
--         exact hNo (Or.inl ha)
--       have hNoB : ¬ DBHasFVar x T b := by
--         intro hb
--         exact hNo (Or.inr hb)
--       simp [dbSubstAux, iha i x T hNoA, ihb i x T hNoB]
--   | abs body ih =>
--       intro i x T hNo
--       simp [dbSubstAux, ih i x T hNo]

-- theorem dbSubstAux_cons_eq_of_no_DBHasFVar :
--     ∀ (ctx : List (String × HOLType)) (d : DBTerm) (i : List (Term × Term))
--       (x : String) (T : HOLType) (s : Term),
--       ¬ DBHasFVar x T d ->
--       dbSubstAux ctx ((Term.var x T, s) :: i) d = dbSubstAux ctx i d := by
--   intro ctx d
--   induction d with
--   | bvar n =>
--       intro i x T s _
--       rfl
--   | fvar y U =>
--       intro i x T s hNo
--       have hneq : Term.var y U ≠ Term.var x T := by
--         intro hEq
--         apply hNo
--         cases hEq
--         exact And.intro rfl rfl
--       unfold dbSubstAux
--       have hxyu : ¬ (x = y ∧ T = U) := by
--         intro h
--         rcases h with ⟨hxy, hTU⟩
--         apply hneq
--         subst hxy
--         subst hTU
--         rfl
--       simp [List.find?, hxyu]
--   | const c U =>
--       intro i x T s _
--       rfl
--   | app a b iha ihb =>
--       intro i x T s hNo
--       have hNoA : ¬ DBHasFVar x T a := by
--         intro ha
--         exact hNo (Or.inl ha)
--       have hNoB : ¬ DBHasFVar x T b := by
--         intro hb
--         exact hNo (Or.inr hb)
--       simp [dbSubstAux, iha i x T s hNoA, ihb i x T s hNoB]
--   | abs body ih =>
--       intro i x T s hNo
--       simp [dbSubstAux, ih i x T s hNo]

-- /-- De Bruijn term contains constant node `(c,T)`. -/
-- def DBHasConst (c : String) (T : HOLType) : DBTerm -> Prop
-- | .bvar _ => False
-- | .fvar _ _ => False
-- | .const c' T' => c = c' ∧ T = T'
-- | .app s t => DBHasConst c T s ∨ DBHasConst c T t
-- | .abs t => DBHasConst c T t

-- theorem DBHasConst_toDBAux_of_free :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (c : String) (T : HOLType),
--       (Term.const c T).IsFreeVarIn t -> DBHasConst c T (toDBAux ctx t) := by
--   intro ctx t
--   induction t generalizing ctx with
--   | var x U =>
--       intro c T hfree
--       simp [Term.IsFreeVarIn] at hfree
--   | const c' U =>
--       intro c T hfree
--       simpa [toDBAux, DBHasConst, Term.IsFreeVarIn] using hfree
--   | app s t ihs iht =>
--       intro c T hfree
--       cases hfree with
--       | inl hs => exact Or.inl (ihs ctx c T hs)
--       | inr ht => exact Or.inr (iht ctx c T ht)
--   | abs n body ihn ihbody =>
--       intro c T hfree
--       cases n with
--       | var x U =>
--           have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
--           have hRec : DBHasConst c T (toDBAux ((x, U) :: ctx) body) := ihbody ((x, U) :: ctx) c T hBody
--           simpa [toDBAux, DBHasConst] using hRec
--       | const x U =>
--           have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
--           have hRec : DBHasConst c T (toDBAux ctx body) := ihbody ctx c T hBody
--           simpa [toDBAux, DBHasConst] using hRec
--       | app n1 n2 =>
--           have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
--           have hRec : DBHasConst c T (toDBAux ctx body) := ihbody ctx c T hBody
--           simpa [toDBAux, DBHasConst] using hRec
--       | abs n1 n2 =>
--           have hBody : (Term.const c T).IsFreeVarIn body := hfree.2
--           have hRec : DBHasConst c T (toDBAux ctx body) := ihbody ctx c T hBody
--           simpa [toDBAux, DBHasConst] using hRec

-- theorem DBHasConst_toDBAux_ctx_irrel :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (c : String) (T : HOLType),
--       DBHasConst c T (toDBAux ctx t) ↔ DBHasConst c T (toDBAux [] t) := by
--   intro ctx t
--   induction t generalizing ctx with
--   | var x U =>
--       intro c T
--       cases h : lookupBVar ctx x U with
--       | none => simp [toDBAux, DBHasConst, h, lookupBVar]
--       | some n => simp [toDBAux, DBHasConst, h, lookupBVar]
--   | const c' U =>
--       intro c T
--       simp [toDBAux, DBHasConst]
--   | app s t ihs iht =>
--       intro c T
--       constructor
--       · intro h
--         cases h with
--         | inl hs => exact Or.inl ((ihs ctx c T).mp hs)
--         | inr ht => exact Or.inr ((iht ctx c T).mp ht)
--       · intro h
--         cases h with
--         | inl hs => exact Or.inl ((ihs ctx c T).mpr hs)
--         | inr ht => exact Or.inr ((iht ctx c T).mpr ht)
--   | abs n body ihn ihbody =>
--       intro c T
--       cases n with
--       | var x U =>
--           have h1 : DBHasConst c T (toDBAux ((x, U) :: ctx) body) ↔ DBHasConst c T (toDBAux [] body) :=
--             ihbody ((x, U) :: ctx) c T
--           have h2 : DBHasConst c T (toDBAux ((x, U) :: []) body) ↔ DBHasConst c T (toDBAux [] body) :=
--             ihbody ((x, U) :: []) c T
--           exact Iff.trans h1 h2.symm
--       | const x U =>
--           simpa [toDBAux, DBHasConst] using (ihbody ctx c T)
--       | app n1 n2 =>
--           simpa [toDBAux, DBHasConst] using (ihbody ctx c T)
--       | abs n1 n2 =>
--           simpa [toDBAux, DBHasConst] using (ihbody ctx c T)

-- theorem free_const_of_DBHasConst_toDB_wt :
--     ∀ (t : Term) (c : String) (T : HOLType),
--       WellTyped t -> DBHasConst c T (toDB t) -> (Term.const c T).IsFreeVarIn t := by
--   intro t c T hwt
--   rcases hwt with ⟨Ty, hty⟩
--   induction hty with
--   | var x U =>
--       intro hHas
--       have : False := by
--         simp [toDB, toDBAux, DBHasConst, lookupBVar] at hHas
--       exact False.elim this
--   | const c' U =>
--       intro hHas
--       have hEq : c = c' ∧ T = U := by
--         simpa [toDB, toDBAux, DBHasConst] using hHas
--       rcases hEq with ⟨hc, hT⟩
--       subst hc
--       subst hT
--       simp [Term.IsFreeVarIn]
--   | app s t dT rT hs ht ihs iht =>
--       intro hHas
--       have hSplit : DBHasConst c T (toDB s) ∨ DBHasConst c T (toDB t) := by
--         simpa [toDB, toDBAux, DBHasConst] using hHas
--       cases hSplit with
--       | inl hsHas => exact Or.inl (ihs hsHas)
--       | inr htHas => exact Or.inr (iht htHas)
--   | abs x dT rT body hbody ih =>
--       intro hHas
--       have hBodyCtx : DBHasConst c T (toDBAux ((x, dT) :: []) body) := by
--         simpa [toDB, toDBAux, DBHasConst] using hHas
--       have hBody0 : DBHasConst c T (toDB body) :=
--         (DBHasConst_toDBAux_ctx_irrel ((x, dT) :: []) body c T).mp hBodyCtx
--       have hBodyFree : (Term.const c T).IsFreeVarIn body := ih hBody0
--       have hneq : Term.const c T ≠ Term.var x dT := by
--         intro hEq
--         cases hEq
--       exact And.intro hneq hBodyFree

-- theorem free_const_iff_of_alpha_wt :
--     ∀ (t1 t2 : Term) (c : String) (T : HOLType),
--       WellTyped t1 -> WellTyped t2 -> AlphaEqv t1 t2 ->
--       ((Term.const c T).IsFreeVarIn t1 ↔ (Term.const c T).IsFreeVarIn t2) := by
--   intro t1 t2 c T hwt1 hwt2 hAlpha
--   have hEq : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
--   constructor
--   · intro hfree1
--     have hHas1 : DBHasConst c T (toDB t1) := DBHasConst_toDBAux_of_free [] t1 c T hfree1
--     have hHas2 : DBHasConst c T (toDB t2) := by
--       simpa [hEq] using hHas1
--     exact free_const_of_DBHasConst_toDB_wt t2 c T hwt2 hHas2
--   · intro hfree2
--     have hHas2 : DBHasConst c T (toDB t2) := DBHasConst_toDBAux_of_free [] t2 c T hfree2
--     have hHas1 : DBHasConst c T (toDB t1) := by
--       simpa [hEq] using hHas2
--     exact free_const_of_DBHasConst_toDB_wt t1 c T hwt1 hHas1

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



-- /-- Term variable substitution: now defined as `substAux` under empty context. -/
-- def subst (i : List (Term × Term)) : Term → Option Term := substAux [] i

-- theorem welltyped_substAux :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (i : List (Term × Term)),
--       WellTyped t -> ∃ t', substAux ctx i t = some t' := by
--   intro ctx t i hwt
--   rcases hwt with ⟨T, ht⟩
--   induction ht generalizing ctx i with
--   | var x T =>
--       unfold substAux
--       cases hLookup : lookupBVar ctx x T with
--       | some n =>
--         exact ⟨Term.var x T, by simp⟩
--       | none =>
--           cases hfind : i.find? (fun (y, _) => y = Term.var x T) with
--           | some p =>
--           exact ⟨p.2, by simp⟩
--           | none =>
--           exact ⟨Term.var x T, by simp⟩
--   | const c T =>
--       exact ⟨Term.const c T, rfl⟩
--   | app s t dT rT hs ht ihs iht =>
--       rcases ihs ctx i with ⟨s', hs'⟩
--       rcases iht ctx i with ⟨t', ht'⟩
--       refine ⟨Term.app s' t', ?_⟩
--       simp [substAux, hs', ht']
--   | abs n dT rT t ht iht =>
--       let bvar := Term.var n dT
--       let i' := i.filter (fun p => !decide (p.fst = bvar))
--       let ctx' := (n, dT) :: ctx
--       rcases iht ctx' i' with ⟨t1, ht1⟩
--       by_cases hcap : captureRisk bvar t i' = true
--       · let z := Term.var (generateVariant t1 n dT) dT
--         let i'' := (bvar, z) :: i'
--         rcases iht [] i'' with ⟨t2, ht2⟩
--         refine ⟨Term.abs z t2, ?_⟩
--         simp [substAux, bvar, i', ctx', ht1, hcap, z, i'', ht2]
--       · have hcap' : captureRisk bvar t i' = false := by
--           cases hc : captureRisk bvar t i' <;> simp [hc] at hcap ⊢
--         refine ⟨Term.abs bvar t1, ?_⟩
--         simp [substAux, bvar, i', ctx', ht1, hcap']

-- theorem welltyped_subst : ∀ (t : Term) (i : List (Term × Term)),
--     WellTyped t → ∃ t', subst i t = some t' := by
--   intro t i hwt
--   rcases welltyped_substAux [] t i hwt with ⟨t', hs⟩
--   exact ⟨t', by simpa [subst] using hs⟩

def SubstOk (i : List (Term × Term)) : Prop :=
  ∀ v t, (v, t) ∈ i → ∃ x T, v = Term.var x T ∧ t.HasType T

theorem SubstOk.filter : ∀ (i : List (Term × Term)) (bvar : Term),
    SubstOk i -> SubstOk (i.filter (fun p => !decide (p.fst = bvar))) := by
  intro i bvar hOk
  intro v t hmem
  exact hOk v t (List.mem_filter.mp hmem).1

-- theorem substAux_hasType_of_SubstOk :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (T : HOLType) (i : List (Term × Term)),
--       t.HasType T -> SubstOk i -> ∃ t', substAux ctx i t = some t' ∧ t'.HasType T := by
--   intro ctx t T i hty
--   induction hty generalizing ctx i with
--   | var x T =>
--       intro hOk
--       unfold substAux
--       cases hLookup : lookupBVar ctx x T with
--       | some n =>
--           refine ⟨Term.var x T, ?_, ?_⟩
--           · simp
--           · exact Term.HasType.var x T
--       | none =>
--           cases hfind : i.find? (fun (y, _) => y = Term.var x T) with
--           | none =>
--               refine ⟨Term.var x T, ?_, ?_⟩
--               · simp
--               · exact Term.HasType.var x T
--           | some p =>
--               rcases p with ⟨v, s⟩
--               have hmem : (v, s) ∈ i := List.mem_of_find?_eq_some hfind
--               have hpred : (fun q : Term × Term => decide (q.fst = Term.var x T)) (v, s) = true :=
--                 List.find?_some (p := fun q : Term × Term => decide (q.fst = Term.var x T)) hfind
--               have hv : v = Term.var x T := by
--                 simp at hpred
--                 exact hpred
--               rcases hOk v s hmem with ⟨x', T', hv', hsTy⟩
--               cases hv'
--               cases hv
--               refine ⟨s, ?_, ?_⟩
--               · simp
--               · exact hsTy
--   | const c T =>
--       intro _
--       refine ⟨Term.const c T, ?_, ?_⟩
--       · rfl
--       · exact Term.HasType.const c T
--   | app s t dT rT hs ht ihs iht =>
--       intro hOk
--       rcases ihs ctx i hOk with ⟨s', hsEq, hsTy⟩
--       rcases iht ctx i hOk with ⟨t', htEq, htTy⟩
--       refine ⟨Term.app s' t', ?_, ?_⟩
--       · simp [substAux, hsEq, htEq]
--       · exact Term.HasType.app s' t' dT rT hsTy htTy
--   | abs n dT rT body hbody ih =>
--       intro hOk
--       let bvar := Term.var n dT
--       let i' := i.filter (fun p => !decide (p.fst = bvar))
--       let ctx' := (n, dT) :: ctx
--       have hOk' : SubstOk i' := SubstOk.filter i bvar hOk
--       rcases ih ctx' i' hOk' with ⟨body', hSubBody, hBodyTy⟩
--       by_cases hcap : captureRisk bvar body i' = true
--       · let z := Term.var (generateVariant body' n dT) dT
--         let i'' := (bvar, z) :: i'
--         have hzTy : z.HasType dT := by
--           dsimp [z]
--           exact Term.HasType.var _ _
--         have hOk'' : SubstOk i'' := by
--           intro v t hmem
--           rcases List.mem_cons.mp hmem with hhead | htail
--           · cases hhead
--             refine ⟨n, dT, rfl, hzTy⟩
--           · exact hOk' v t htail
--         rcases ih [] i'' hOk'' with ⟨body'', hSubBody2Aux, hBodyTy2⟩
--         refine ⟨Term.abs z body'', ?_, ?_⟩
--         · simp [substAux, i', ctx', bvar, hSubBody, hcap, z, i'', hSubBody2Aux]
--         · exact Term.HasType.abs (generateVariant body' n dT) dT rT body'' hBodyTy2
--       · have hcap' : captureRisk bvar body i' = false := by
--           cases hc : captureRisk bvar body i' <;> simp [hc] at hcap ⊢
--         refine ⟨Term.abs bvar body', ?_, ?_⟩
--         · simp [substAux, i', ctx', bvar, hSubBody, hcap']
--         · simpa [bvar] using (Term.HasType.abs n dT rT body' hBodyTy)

-- theorem subst_hasType_of_SubstOk :
--     ∀ (t : Term) (T : HOLType) (i : List (Term × Term)),
--       t.HasType T -> SubstOk i -> ∃ t', subst i t = some t' ∧ t'.HasType T := by
--   intro t T i hty hOk
--   rcases substAux_hasType_of_SubstOk [] t T i hty hOk with ⟨t', hs, hty'⟩
--   exact ⟨t', by simpa [subst] using hs, hty'⟩

-- theorem HasType_of_substAux_of_SubstOk :
--     ∀ (ctx : List (String × HOLType)) (t t' : Term) (T : HOLType) (i : List (Term × Term)),
--       t.HasType T -> SubstOk i -> substAux ctx i t = some t' -> t'.HasType T := by
--   intro ctx t t' T i hty hOk hSub
--   rcases substAux_hasType_of_SubstOk ctx t T i hty hOk with ⟨u, huSub, huTy⟩
--   rw [huSub] at hSub
--   cases hSub
--   exact huTy

-- theorem welltyped_substAux_of_SubstOk :
--     ∀ (ctx : List (String × HOLType)) (t : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> ∃ t', substAux ctx i t = some t' ∧ WellTyped t' := by
--   intro ctx t i hwt hOk
--   rcases hwt with ⟨T, hty⟩
--   rcases substAux_hasType_of_SubstOk ctx t T i hty hOk with ⟨t', hs, hty'⟩
--   exact ⟨t', hs, ⟨T, hty'⟩⟩

-- theorem welltyped_subst_of_SubstOk :
--     ∀ (t : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> ∃ t', subst i t = some t' ∧ WellTyped t' := by
--   intro t i hwt hOk
--   rcases hwt with ⟨T, hty⟩
--   rcases subst_hasType_of_SubstOk t T i hty hOk with ⟨t', hs, hty'⟩
--   exact ⟨t', hs, ⟨T, hty'⟩⟩

-- /-- Substitution is well-typed and all RHS terms are closed. -/
-- def SubstOkClosed (i : List (Term × Term)) : Prop :=
--   ∀ v t, (v, t) ∈ i → (∃ x T, v = Term.var x T ∧ t.HasType T) ∧ Closed t

-- theorem SubstOkClosed.toSubstOk : ∀ (i : List (Term × Term)),
--     SubstOkClosed i → SubstOk i := by
--   intro i hOk
--   intro v t hmem
--   exact (hOk v t hmem).1

-- theorem SubstOkClosed.filter : ∀ (i : List (Term × Term)) (bvar : Term),
--     SubstOkClosed i -> SubstOkClosed (i.filter (fun p => !decide (p.fst = bvar))) := by
--   intro i bvar hOk
--   intro v t hmem
--   exact hOk v t (List.mem_filter.mp hmem).1

-- theorem captureRisk_false_of_closed_rhs_var :
--     ∀ (x : String) (T : HOLType) (body : Term) (i : List (Term × Term)),
--       (∀ v t, (v, t) ∈ i → Closed t) ->
--       captureRisk (Term.var x T) body i = false := by
--   intro x T body i hClosed
--   unfold captureRisk
--   rw [List.any_eq_false]
--   intro p hp
--   rcases p with ⟨v, t⟩
--   intro h
--   have hPair : (Term.var x T).IsFreeVarIn t ∧ v.IsFreeVarIn body := by
--     simpa using h
--   exact (hClosed v t hp) x T hPair.1

-- theorem captureRisk_false_of_SubstOkClosed_filter_var :
--     ∀ (i : List (Term × Term)) (x : String) (T : HOLType) (body : Term),
--       SubstOkClosed i ->
--       captureRisk (Term.var x T) body (i.filter (fun p => !decide (p.fst = Term.var x T))) = false := by
--   intro i x T body hOk
--   apply captureRisk_false_of_closed_rhs_var
--   intro v t hmem
--   exact (hOk v t (List.mem_filter.mp hmem).1).2

-- theorem subst_abs_no_rename_of_SubstOkClosed :
--     ∀ (i : List (Term × Term)) (x : String) (dT : HOLType) (t t' : Term),
--       SubstOkClosed i ->
--       substAux ((x, dT) :: []) (i.filter (fun p => !decide (p.fst = Term.var x dT))) t = some t' ->
--       subst i (Term.abs (Term.var x dT) t) = some (Term.abs (Term.var x dT) t') := by
--   intro i x dT t t' hOk ht
--   have hcap :
--       captureRisk (Term.var x dT) t (i.filter (fun p => !decide (p.fst = Term.var x dT))) = false :=
--     captureRisk_false_of_SubstOkClosed_filter_var i x dT t hOk
--   simp [subst, substAux, ht, hcap]

-- theorem subst_pair_welltyped_of_SubstOk :
--     ∀ (t1 t2 : Term) (i : List (Term × Term)),
--       (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
--       ∃ t1' t2',
--         subst i t1 = some t1' ∧ subst i t2 = some t2' ∧
--         WellTyped t1' ∧ WellTyped t2' := by
--   intro t1 t2 i hwtEither hOk hAlpha
--   have hBoth : WellTyped t1 ∧ WellTyped t2 := AlphaEqv.welltyped_both_of_either hAlpha hwtEither
--   have hwt1 : WellTyped t1 := hBoth.1
--   have hwt2 : WellTyped t2 := hBoth.2
--   rcases welltyped_subst_of_SubstOk t1 i hwt1 hOk with ⟨t1', hs1, hwt1'⟩
--   rcases welltyped_subst_of_SubstOk t2 i hwt2 hOk with ⟨t2', hs2, hwt2'⟩
--   exact ⟨t1', t2', hs1, hs2, hwt1', hwt2'⟩

--   theorem subst_toDB_commute_of_abs_case :
--     (∀ (n : String) (dT rT : HOLType) (body t' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       subst i (Term.abs (Term.var n dT) body) = some t' ->
--       toDB t' = dbSubst i (toDB (Term.abs (Term.var n dT) body))) ->
--     ∀ (t t' : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> subst i t = some t' ->
--       toDB t' = dbSubst i (toDB t) := by
--     intro hAbs t t' i hwt hOk hSub
--     rcases hwt with ⟨T, hty⟩
--     revert t' i hOk hSub
--     induction hty with
--     | var x T =>
--       intro t' i hOk hSub
--       have hSubAux : substAux [] i (Term.var x T) = some t' := by
--         simpa [subst] using hSub
--       unfold substAux at hSubAux
--       simp [lookupBVar] at hSubAux
--       cases hfind : i.find? (fun (y, _) => y = Term.var x T) with
--       | none =>
--         simp [hfind] at hSubAux
--         cases hSubAux
--         exact (dbSubst_fvar_eq_of_find_none i x T hfind).symm
--       | some p =>
--         simp [hfind] at hSubAux
--         cases hSubAux
--         exact (dbSubst_fvar_eq_of_find_some i x T p.1 p.2 hfind).symm
--     | const c T =>
--       intro t' i hOk hSub
--       have hSubAux : substAux [] i (Term.const c T) = some t' := by
--         simpa [subst] using hSub
--       simp [substAux] at hSubAux
--       cases hSubAux
--       rfl
--     | app s t dT rT hs ht ihs iht =>
--       intro t' i hOk hSub
--       have hSubAux : substAux [] i (Term.app s t) = some t' := by
--         simpa [subst] using hSub
--       unfold substAux at hSubAux
--       cases hs' : substAux [] i s with
--       | none =>
--         simp [hs'] at hSubAux
--       | some s' =>
--         cases ht' : substAux [] i t with
--         | none =>
--           simp [hs', ht'] at hSubAux
--         | some t'' =>
--           simp [hs', ht'] at hSubAux
--           cases hSubAux
--           have hsSub : subst i s = some s' := by simpa [subst] using hs'
--           have htSub : subst i t = some t'' := by simpa [subst] using ht'
--           have hS : toDB s' = dbSubst i (toDB s) := ihs s' i hOk hsSub
--           have hT : toDB t'' = dbSubst i (toDB t) := iht t'' i hOk htSub
--           calc
--             toDB (Term.app s' t'') = DBTerm.app (toDB s') (toDB t'') := by rfl
--             _ = DBTerm.app (dbSubst i (toDB s)) (dbSubst i (toDB t)) := by
--               simp [hS, hT]
--             _ = dbSubst i (toDB (Term.app s t)) := by
--               rfl
--     | abs n dT rT body hbody ihbody =>
--       intro t' i hOk hSub
--       exact hAbs n dT rT body t' i hbody hOk hSub

--   theorem substAux_toDBAux_commute_of_abs_case :
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body t' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       substAux ctx i (Term.abs (Term.var n dT) body) = some t' ->
--       toDBAux ctx t' = dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body))) ->
--     ∀ (ctx : List (String × HOLType)) (t t' : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> substAux ctx i t = some t' ->
--       toDBAux ctx t' = dbSubstAux ctx i (toDBAux ctx t) := by
--     intro hAbs ctx t t' i hwt hOk hSub
--     rcases hwt with ⟨T, hty⟩
--     revert t' i hOk hSub
--     induction hty with
--     | var x T =>
--       intro t' i hOk hSub
--       unfold substAux at hSub
--       cases hLookup : lookupBVar ctx x T with
--       | some n =>
--         simp [hLookup] at hSub
--         cases hSub
--         simp [toDBAux, hLookup, dbSubstAux]
--       | none =>
--         cases hfind : i.find? (fun (y, _) => y = Term.var x T) with
--         | none =>
--           simp [hLookup, hfind] at hSub
--           cases hSub
--           simp [toDBAux, dbSubstAux, hLookup, hfind]
--         | some p =>
--           simp [hLookup, hfind] at hSub
--           cases hSub
--           simp [toDBAux, dbSubstAux, hLookup, hfind]
--     | const c T =>
--       intro t' i hOk hSub
--       simp [substAux] at hSub
--       cases hSub
--       rfl
--     | app s t dT rT hs ht ihs iht =>
--       intro t' i hOk hSub
--       unfold substAux at hSub
--       cases hs' : substAux ctx i s with
--       | none =>
--         simp [hs'] at hSub
--       | some s' =>
--         cases ht' : substAux ctx i t with
--         | none =>
--           simp [hs', ht'] at hSub
--         | some t'' =>
--           simp [hs', ht'] at hSub
--           cases hSub
--           have hS : toDBAux ctx s' = dbSubstAux ctx i (toDBAux ctx s) := ihs s' i hOk hs'
--           have hT : toDBAux ctx t'' = dbSubstAux ctx i (toDBAux ctx t) := iht t'' i hOk ht'
--           calc
--           toDBAux ctx (Term.app s' t'') = DBTerm.app (toDBAux ctx s') (toDBAux ctx t'') := by rfl
--           _ = DBTerm.app (dbSubstAux ctx i (toDBAux ctx s)) (dbSubstAux ctx i (toDBAux ctx t)) := by
--             simp [hS, hT]
--           _ = dbSubstAux ctx i (toDBAux ctx (Term.app s t)) := by
--             rfl
--     | abs n dT rT body hbody ihbody =>
--       intro t' i hOk hSub
--       exact hAbs ctx n dT rT body t' i hbody hOk hSub

--   theorem substAux_toDBAux_abs_case_of_branches :
--       (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--         body.HasType rT -> SubstOk i ->
--         let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--         let ctx' := (n, dT) :: ctx
--         substAux ctx' i' body = some body' ->
--         captureRisk (Term.var n dT) body i' = false ->
--         toDBAux ctx (Term.abs (Term.var n dT) body') = dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body))) ->
--       (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
--         body.HasType rT -> SubstOk i ->
--         let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--         let ctx' := (n, dT) :: ctx
--         substAux ctx' i' body = some body' ->
--         captureRisk (Term.var n dT) body i' = true ->
--         let z := Term.var (generateVariant body' n dT) dT
--         let i'' := (Term.var n dT, z) :: i'
--         subst i'' body = some body'' ->
--         toDBAux ctx (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
--           dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body))) ->
--       ∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body t' : Term) (i : List (Term × Term)),
--         body.HasType rT -> SubstOk i ->
--         substAux ctx i (Term.abs (Term.var n dT) body) = some t' ->
--         toDBAux ctx t' = dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body)) := by
--     intro hNoCap hCap ctx n dT rT body t' i hBodyTy hOk hSub
--     let bvar := Term.var n dT
--     let i' := i.filter (fun p => !decide (p.fst = bvar))
--     let ctx' := (n, dT) :: ctx
--     unfold substAux at hSub
--     cases hBody : substAux ctx' i' body with
--     | none =>
--         simp [bvar, i', ctx', hBody] at hSub
--     | some body' =>
--         by_cases hRisk : captureRisk bvar body i' = true
--         · let z : Term := Term.var (generateVariant body' n dT) dT
--           let i'' : List (Term × Term) := (Term.var n dT, z) :: i'
--           cases hBody2 : subst i'' body with
--           | none =>
--               have hBody2Aux : substAux [] i'' body = none := by
--                 simpa [subst] using hBody2
--               simp [bvar, i', ctx', hBody, hRisk, z, i'', hBody2Aux] at hSub
--           | some body'' =>
--               have hBody2Aux : substAux [] i'' body = some body'' := by
--                 simpa [subst] using hBody2
--               simp [bvar, i', ctx', hBody, hRisk, z, i'', hBody2Aux] at hSub
--               cases hSub
--               have hCapMain :=
--                 hCap ctx n dT rT body body' body'' i hBodyTy hOk
--                   (by simpa [i', ctx', bvar] using hBody)
--                   hRisk
--                   (by simpa [z, i''] using hBody2)
--               simpa [bvar, i', ctx', z, i''] using hCapMain
--         · have hRiskFalse : captureRisk bvar body i' = false := by
--             cases hc : captureRisk bvar body i' <;> simp [hc] at hRisk ⊢
--           simp [bvar, i', ctx', hBody, hRiskFalse] at hSub
--           cases hSub
--           have hNoCapMain :=
--             hNoCap ctx n dT rT body body' i hBodyTy hOk
--               (by simpa [i', ctx', bvar] using hBody)
--               hRiskFalse
--           simpa [bvar, i', ctx'] using hNoCapMain

--   theorem substAux_toDBAux_commute_of_branches :
--       (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--         body.HasType rT -> SubstOk i ->
--         let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--         let ctx' := (n, dT) :: ctx
--         substAux ctx' i' body = some body' ->
--         captureRisk (Term.var n dT) body i' = false ->
--         toDBAux ctx (Term.abs (Term.var n dT) body') = dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body))) ->
--       (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
--         body.HasType rT -> SubstOk i ->
--         let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--         let ctx' := (n, dT) :: ctx
--         substAux ctx' i' body = some body' ->
--         captureRisk (Term.var n dT) body i' = true ->
--         let z := Term.var (generateVariant body' n dT) dT
--         let i'' := (Term.var n dT, z) :: i'
--         subst i'' body = some body'' ->
--         toDBAux ctx (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
--           dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body))) ->
--       ∀ (ctx : List (String × HOLType)) (t t' : Term) (i : List (Term × Term)),
--         WellTyped t -> SubstOk i -> substAux ctx i t = some t' ->
--         toDBAux ctx t' = dbSubstAux ctx i (toDBAux ctx t) := by
--     intro hNoCap hCap
--     apply substAux_toDBAux_commute_of_abs_case
--     intro ctx n dT rT body t' i hBodyTy hOk hSub
--     exact substAux_toDBAux_abs_case_of_branches hNoCap hCap ctx n dT rT body t' i hBodyTy hOk hSub

-- theorem substAux_toDBAux_abs_no_capture_of_ctx_eq :
--     ∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = false ->
--       toDBAux ctx' body' = dbSubstAux ctx i' (toDBAux ctx' body) ->
--       toDBAux ctx (Term.abs (Term.var n dT) body') =
--         dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body)) := by
--   intro ctx n dT rT body body' i hBodyTy hOk i' ctx' hBodySub hRiskFalse hCtxEq
--   let dBody := toDBAux ((n, dT) :: ctx) body
--   have hNoBound : ¬ DBHasFVar n dT dBody := by
--     simpa [dBody] using no_DBHasFVar_under_bound ctx body n dT
--   have hFilterBack :
--       dbSubstAux ctx i' dBody = dbSubstAux ctx i dBody := by
--     simpa [dBody, i'] using dbSubstAux_filter_eq_of_no_DBHasFVar ctx dBody i n dT hNoBound
--   calc
--     toDBAux ctx (Term.abs (Term.var n dT) body') = DBTerm.abs (toDBAux ctx' body') := by
--       rfl
--     _ = DBTerm.abs (dbSubstAux ctx i' dBody) := by
--       simpa [dBody, ctx'] using congrArg DBTerm.abs hCtxEq
--     _ = DBTerm.abs (dbSubstAux ctx i dBody) := by
--       simpa using congrArg DBTerm.abs hFilterBack
--     _ = dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body)) := by
--       simp [toDBAux, dbSubstAux, dBody]

-- theorem substAux_toDBAux_abs_capture_of_ctx_eq :
--     ∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType)
--       (body body' body'' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = true ->
--       let z := Term.var (generateVariant body' n dT) dT
--       let i'' := (Term.var n dT, z) :: i'
--       subst i'' body = some body'' ->
--       toDBAux ((generateVariant body' n dT, dT) :: ctx) body'' =
--         dbSubstAux ctx i'' (toDBAux ctx' body) ->
--       toDBAux ctx (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
--         dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body)) := by
--   intro ctx n dT rT body body' body'' i hBodyTy hOk i' ctx' hBodySub hRisk z i'' hBodySub2 hCtxEq
--   let dBody := toDBAux ((n, dT) :: ctx) body
--   have hNoBound : ¬ DBHasFVar n dT dBody := by
--     simpa [dBody] using no_DBHasFVar_under_bound ctx body n dT
--   have hConsDrop :
--       dbSubstAux ctx ((Term.var n dT, z) :: i') dBody =
--         dbSubstAux ctx i' dBody := by
--     simpa [dBody] using dbSubstAux_cons_eq_of_no_DBHasFVar ctx dBody i' n dT z hNoBound
--   have hFilterBack :
--       dbSubstAux ctx i' dBody =
--         dbSubstAux ctx i dBody := by
--     simpa [dBody, i'] using dbSubstAux_filter_eq_of_no_DBHasFVar ctx dBody i n dT hNoBound
--   calc
--     toDBAux ctx (Term.abs (Term.var (generateVariant body' n dT) dT) body'') =
--         DBTerm.abs (toDBAux ((generateVariant body' n dT, dT) :: ctx) body'') := by
--       rfl
--     _ = DBTerm.abs (dbSubstAux ctx i'' dBody) := by
--       simpa [dBody, ctx'] using congrArg DBTerm.abs hCtxEq
--     _ = DBTerm.abs (dbSubstAux ctx i' dBody) := by
--       simpa [i''] using congrArg DBTerm.abs hConsDrop
--     _ = DBTerm.abs (dbSubstAux ctx i dBody) := by
--       simpa using congrArg DBTerm.abs hFilterBack
--     _ = dbSubstAux ctx i (toDBAux ctx (Term.abs (Term.var n dT) body)) := by
--       simp [toDBAux, dbSubstAux, dBody]

-- theorem substAux_toDBAux_commute_of_ctx_branches :
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = false ->
--       toDBAux ctx' body' = dbSubstAux ctx i' (toDBAux ctx' body)) ->
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = true ->
--       let z := Term.var (generateVariant body' n dT) dT
--       let i'' := (Term.var n dT, z) :: i'
--       subst i'' body = some body'' ->
--       toDBAux ((generateVariant body' n dT, dT) :: ctx) body'' =
--         dbSubstAux ctx i'' (toDBAux ctx' body)) ->
--     ∀ (ctx : List (String × HOLType)) (t t' : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> substAux ctx i t = some t' ->
--       toDBAux ctx t' = dbSubstAux ctx i (toDBAux ctx t) := by
--   intro hNoCapCtx hCapCtx
--   apply substAux_toDBAux_commute_of_branches
--   · intro ctx n dT rT body body' i hBodyTy hOk i' ctx' hBodySub hRiskFalse
--     exact substAux_toDBAux_abs_no_capture_of_ctx_eq ctx n dT rT body body' i hBodyTy hOk
--       hBodySub hRiskFalse
--       (hNoCapCtx ctx n dT rT body body' i hBodyTy hOk hBodySub hRiskFalse)
--   · intro ctx n dT rT body body' body'' i hBodyTy hOk i' ctx' hBodySub hRisk z i'' hBodySub2
--     exact substAux_toDBAux_abs_capture_of_ctx_eq ctx n dT rT body body' body'' i hBodyTy hOk
--       hBodySub hRisk hBodySub2
--       (hCapCtx ctx n dT rT body body' body'' i hBodyTy hOk hBodySub hRisk hBodySub2)

-- theorem substAux_toDB_commute_of_ctx_branches :
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = false ->
--       toDBAux ctx' body' = dbSubstAux ctx i' (toDBAux ctx' body)) ->
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = true ->
--       let z := Term.var (generateVariant body' n dT) dT
--       let i'' := (Term.var n dT, z) :: i'
--       subst i'' body = some body'' ->
--       toDBAux ((generateVariant body' n dT, dT) :: ctx) body'' =
--         dbSubstAux ctx i'' (toDBAux ctx' body)) ->
--     ∀ (t t' : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> substAux [] i t = some t' ->
--       toDB t' = dbSubst i (toDB t) := by
--   intro hNoCapCtx hCapCtx t t' i hwt hOk hSub
--   have hAux : toDBAux [] t' = dbSubstAux [] i (toDBAux [] t) :=
--     substAux_toDBAux_commute_of_ctx_branches hNoCapCtx hCapCtx [] t t' i hwt hOk hSub
--   simpa [toDB] using (Eq.trans hAux (by simp [dbSubstAux_nil_eq_dbSubst]))

-- theorem substAux_alpha_of_SubstOk_of_toDB_substAux :
--     (∀ (t t' : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> substAux [] i t = some t' ->
--       toDB t' = dbSubst i (toDB t)) ->
--     ∀ (t1 t2 : Term) (i : List (Term × Term)),
--       (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
--       ∃ t1' t2',
--         substAux [] i t1 = some t1' ∧ substAux [] i t2 = some t2' ∧ AlphaEqv t1' t2' := by
--   intro hToDB t1 t2 i hwtEither hOk hAlpha
--   have hBoth : WellTyped t1 ∧ WellTyped t2 := AlphaEqv.welltyped_both_of_either hAlpha hwtEither
--   have hwt1 : WellTyped t1 := hBoth.1
--   have hwt2 : WellTyped t2 := hBoth.2
--   rcases welltyped_substAux [] t1 i hwt1 with ⟨t1', hs1⟩
--   rcases welltyped_substAux [] t2 i hwt2 with ⟨t2', hs2⟩
--   have hEqIn : toDB t1 = toDB t2 := toDB_eq_of_AlphaEqv_wt t1 t2 hwt1 hwt2 hAlpha
--   have hEq1 : toDB t1' = dbSubst i (toDB t1) := hToDB t1 t1' i hwt1 hOk hs1
--   have hEq2 : toDB t2' = dbSubst i (toDB t2) := hToDB t2 t2' i hwt2 hOk hs2
--   have hEqDb : dbSubst i (toDB t1) = dbSubst i (toDB t2) :=
--     dbSubst_eq_of_eq i (toDB t1) (toDB t2) hEqIn
--   have hEqOut : toDB t1' = toDB t2' := by
--     calc
--       toDB t1' = dbSubst i (toDB t1) := hEq1
--       _ = dbSubst i (toDB t2) := hEqDb
--       _ = toDB t2' := hEq2.symm
--   have hwt1' : WellTyped t1' := by
--     rcases hwt1 with ⟨T, hty1⟩
--     exact ⟨T, HasType_of_substAux_of_SubstOk [] t1 t1' T i hty1 hOk hs1⟩
--   have hwt2' : WellTyped t2' := by
--     rcases hwt2 with ⟨T, hty2⟩
--     exact ⟨T, HasType_of_substAux_of_SubstOk [] t2 t2' T i hty2 hOk hs2⟩
--   have hAlphaOut : AlphaEqv t1' t2' := AlphaEqv_of_toDB_eq_wt t1' t2' hwt1' hwt2' hEqOut
--   exact ⟨t1', t2', hs1, hs2, hAlphaOut⟩

-- theorem substAux_alpha_of_SubstOk_of_ctx_branches :
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = false ->
--       toDBAux ctx' body' = dbSubstAux ctx i' (toDBAux ctx' body)) ->
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = true ->
--       let z := Term.var (generateVariant body' n dT) dT
--       let i'' := (Term.var n dT, z) :: i'
--       subst i'' body = some body'' ->
--       toDBAux ((generateVariant body' n dT, dT) :: ctx) body'' =
--         dbSubstAux ctx i'' (toDBAux ctx' body)) ->
--     ∀ (t1 t2 : Term) (i : List (Term × Term)),
--       (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
--       ∃ t1' t2',
--         substAux [] i t1 = some t1' ∧ substAux [] i t2 = some t2' ∧ AlphaEqv t1' t2' := by
--   intro hNoCapCtx hCapCtx
--   apply substAux_alpha_of_SubstOk_of_toDB_substAux
--   intro t t' i hwt hOk hSub
--   exact substAux_toDB_commute_of_ctx_branches hNoCapCtx hCapCtx t t' i hwt hOk hSub

-- theorem substAux_alpha_of_SubstOk_of_toDBAux_substAux_and_ctx_bridges :
--     (∀ (ctx : List (String × HOLType)) (t t' : Term) (i : List (Term × Term)),
--       WellTyped t -> SubstOk i -> substAux ctx i t = some t' ->
--       toDBAux ctx t' = dbSubstAux ctx i (toDBAux ctx t)) ->
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       dbSubstAux ctx' i' (toDBAux ctx' body) = dbSubstAux ctx i' (toDBAux ctx' body)) ->
--     (∀ (ctx : List (String × HOLType)) (n : String) (dT rT : HOLType) (body body' body'' : Term) (i : List (Term × Term)),
--       body.HasType rT -> SubstOk i ->
--       let i' := i.filter (fun p => !decide (p.fst = Term.var n dT))
--       let ctx' := (n, dT) :: ctx
--       substAux ctx' i' body = some body' ->
--       captureRisk (Term.var n dT) body i' = true ->
--       let z := Term.var (generateVariant body' n dT) dT
--       let i'' := (Term.var n dT, z) :: i'
--       subst i'' body = some body'' ->
--       toDBAux ((generateVariant body' n dT, dT) :: ctx) body'' =
--         dbSubstAux ctx i'' (toDBAux ctx' body)) ->
--     ∀ (t1 t2 : Term) (i : List (Term × Term)),
--       (WellTyped t1 ∨ WellTyped t2) -> SubstOk i -> AlphaEqv t1 t2 ->
--       ∃ t1' t2',
--         substAux [] i t1 = some t1' ∧ substAux [] i t2 = some t2' ∧ AlphaEqv t1' t2' := by
--   intro hCtxComm hNoCapBridge hCapBridge
--   apply substAux_alpha_of_SubstOk_of_ctx_branches
--   · intro ctx n dT rT body body' i hBodyTy hOk i' ctx' hBodySub hRiskFalse
--     have hOk' : SubstOk i' := by
--       simpa [i'] using SubstOk.filter i (Term.var n dT) hOk
--     have hComm :
--         toDBAux ctx' body' = dbSubstAux ctx' i' (toDBAux ctx' body) :=
--       hCtxComm ctx' body body' i' ⟨rT, hBodyTy⟩ hOk' hBodySub
--     have hBridge' :=
--       hNoCapBridge ctx n dT rT body body' i hBodyTy hOk
--         (by simpa [i', ctx'] using hBodySub)
--     have hBridge :
--         dbSubstAux ctx' i' (toDBAux ctx' body) = dbSubstAux ctx i' (toDBAux ctx' body) := by
--       simpa [i', ctx'] using hBridge'
--     exact Eq.trans hComm hBridge
--   · intro ctx n dT rT body body' body'' i hBodyTy hOk i' ctx' hBodySub hRisk z i'' hBodySub2
--     have hBodySub' :
--         substAux ((n, dT) :: ctx) (i.filter (fun p => !decide (p.fst = Term.var n dT))) body = some body' := by
--       simpa [i', ctx'] using hBodySub
--     have hRisk' :
--         captureRisk (Term.var n dT) body (i.filter (fun p => !decide (p.fst = Term.var n dT))) = true := by
--       simpa [i'] using hRisk
--     have hBodySub2' :
--         subst ((Term.var n dT, Term.var (generateVariant body' n dT) dT) ::
--           (i.filter (fun p => !decide (p.fst = Term.var n dT)))) body = some body'' := by
--       simpa [i', i'', z] using hBodySub2
--     have hCap' := hCapBridge ctx n dT rT body body' body'' i hBodyTy hOk hBodySub' hRisk' hBodySub2'
--     simpa [i', i'', z, ctx'] using hCap'

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


-- private def instantiateCoreFuel : Nat → List (Term × Term) → List (String × HOLType) →
--     Term → Except Term Term
-- | 0, _env, _tyin, tm => .error tm
-- | _ + 1, env, tyin, .var x ty =>
--     let tm := Term.var x ty
--     let tm' := Term.var x (typeSubst tyin ty)
--     -- Check if tm' (the new instantiated variable) would cause a clash
--     match env.find? (fun (old, _) => old = tm') with
--     | some (_, orig) =>
--         if orig = tm then
--           .ok tm'
--         else
--           .error tm'
--     | none => .ok tm'
-- | _ + 1, _env, tyin, .const x ty =>
--     .ok (.const x (typeSubst tyin ty))
-- | fuel + 1, env, tyin, .app s t => do
--     let s' ← instantiateCoreFuel fuel env tyin s
--     let t' ← instantiateCoreFuel fuel env tyin t
--     .ok (Term.app s' t')
-- | fuel + 1, env, tyin, .abs v t =>
--     match v with
--     | .var x ty =>
--         let ty' := typeSubst tyin ty
--         let v' := Term.var x ty'
--         let env' := (v', v) :: env
--         let tre : Except Term Term := instantiateCoreFuel fuel env' tyin t
--         match tre with
--         | .ok t' => .ok (Term.abs v' t')
--         | .error w =>
--             if w ≠ v' then
--               .error w
--             else do
--               let t0 ← instantiateCoreFuel fuel [] tyin t
--               let x' := generateVariant t0 x ty'
--               let tSub? := subst [(Term.var x ty, Term.var x' ty)] t
--               match tSub? with
--               | none => .error w
--               | some tSub => do
--                   let env'' := (Term.var x' ty', Term.var x' ty) :: env
--                   let t'' ← instantiateCoreFuel fuel env'' tyin tSub
--                   .ok (Term.abs (Term.var x' ty') t'')
--     | _ => .error v

-- /-- Instantiate type variables in a term according to a substitution.
--     `env` tracks old/new binder correspondence to detect clashes. -/
-- def instantiateCore (env : List (Term × Term)) (tyin : List (String × HOLType))
--     (tm : Term) : Except Term Term :=
--   instantiateCoreFuel (2 * Term.size tm + 1) env tyin tm

-- /-- Instantiates type variables in a term according to a substitution.
--     Returns `none` only when a clash cannot be resolved. -/
-- def instantiate (tyin : List (String × HOLType)) (tm : Term) : Option Term :=
--   match instantiateCore [] tyin tm with
--   | .ok t => some t
--   | .error _ => none

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
