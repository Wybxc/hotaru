import HotaruKernel.Type
import HotaruKernel.Term
import Aesop

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
private def toDBAux (ctx : List (String × HOLType)) : Term -> Option DBTerm
| .var x T =>
    match ctx.idxOf? (x, T) with
    | some n => some (DBTerm.bvar n)
    | none => some (DBTerm.fvar x T)
| .const c T => some (DBTerm.const c T)
| .app s t => do
    let s' ← toDBAux ctx s
    let t' ← toDBAux ctx t
    some (DBTerm.app s' t')
| .abs (.var x T) t => do
    let t' ← toDBAux ((x, T) :: ctx) t
    some (DBTerm.abs t')
| .abs _ _ => none

/-- Convert a named term to de Bruijn form. -/
def Term.toDB (t : Term) : Option DBTerm := toDBAux [] t

theorem toDB_bvar : ∀ (ctx : List (String × HOLType)) (t : Term) (n : Nat),
    toDBAux ctx t = some (DBTerm.bvar n) →
    ∃ x T, ctx[n]? = some (x, T) ∧ t = .var x T := by
  intros ctx t n h
  induction t generalizing ctx with try simp at h
  | var x T =>
      sorry
  | app s t ihs iht =>
      sorry
  | abs n t ih =>
      sorry

/-- Proof skeleton: relation between alpha-renaming environment and de Bruijn contexts. -/
private inductive DBCtxRel :
    List (Term × Term) -> List (String × HOLType) -> List (String × HOLType) -> Prop
| nil : DBCtxRel [] [] []
| cons :
    ∀ (x y : String) (T1 T2 : HOLType)
      (bv : List (Term × Term)) (env1 env2 : List (String × HOLType)),
      DBCtxRel bv env1 env2 ->
      DBCtxRel ((.var x T1, .var y T2) :: bv) ((x, T1) :: env1) ((y, T2) :: env2)

/-- Key lookup lemma: head hit gives index 0. -/
@[aesop safe]
private theorem findIdx_cons_hit
    (env : List (String × HOLType)) (x : String) (T : HOLType) :
    ((x, T) :: env).findIdx? (fun (y, yT) => x = y ∧ T = yT) = some 0 := by
  simp [List.findIdx?, List.findIdx?.go]

/-- Key lookup lemma: head miss reduces to tail with succ. -/
@[aesop unsafe]
private theorem findIdx_cons_miss
    (env : List (String × HOLType))
    (x y : String) (T U : HOLType)
    (hmiss : x ≠ y ∨ T ≠ U) :
    ((y, U) :: env).findIdx? (fun (z, zT) => x = z ∧ T = zT) =
      Option.map Nat.succ (env.findIdx? (fun (z, zT) => x = z ∧ T = zT)) := by
  simp [List.findIdx?, List.findIdx?.go, Option.map]
  sorry

/-- Variable case bridge: alpha-variable relation implies equal de Bruijn translation. -/
private theorem toDBAux_var_eq_of_IsAlphaVars :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType),
      DBCtxRel bv env1 env2 ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
      toDBAux env1 (.var x1 T1) = toDBAux env2 (.var x2 T2) := by
  intro bv env1 env2 x1 x2 T1 T2 hRel hAlpha
  induction bv generalizing env1 env2 with cases hRel
  | nil =>
      simp at hAlpha
      simpa
  | cons b bvs ih =>
      simp at hAlpha
      rename_i x y T1_1 T2_1 env1 env2 a
      simp_all
      sorry

/-- Forward direction core lemma under related contexts. -/
private theorem toDBAux_eq_of_IsAlphaTerms :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (t1 t2 : Term),
      DBCtxRel bv env1 env2 ->
      IsAlphaTerms bv t1 t2 ->
      ∃ dt, toDBAux env1 t1 = some dt ∧ toDBAux env2 t2 = some dt := by
  intro bv env1 env2 t1 t2 hRel hAlpha
  induction hAlpha generalizing env1 env2 with try simp
  | var hRel hAlpha =>
      sorry
  | app hRel hAlpha ih1 ih2 =>
      sorry
  | abs hRel hAlpha ih =>
      sorry

/-- Reverse direction core lemma under related contexts. -/
private theorem IsAlphaTerms_of_toDBAux_eq :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (t1 t2 : Term) (dt : DBTerm),
      DBCtxRel bv env1 env2 ->
      toDBAux env1 t1 = some dt ->
      toDBAux env2 t2 = some dt ->
      IsAlphaTerms bv t1 t2 := by
  intro bv env1 env2 t1 t2 dt hRel h1 h2
  induction dt generalizing t1 t2 env1 env2 with
  | bvar n =>
      sorry
  | fvar x T =>
      sorry
  | const c T =>
      sorry
  | app s t ihs iht =>
      sorry
  | abs t ih =>
      sorry

theorem alpha_debrujin :
  ∀ t1 t2 : Term,
    AlphaEqv t1 t2 → ∃ dt, t1.toDB = some dt ∧ t2.toDB = some dt := by
  intros t1 t2 hAlpha
  rcases toDBAux_eq_of_IsAlphaTerms [] [] [] t1 t2 DBCtxRel.nil hAlpha with ⟨dt, h1, h2⟩
  exact ⟨dt, by simpa [Term.toDB] using h1, by simpa [Term.toDB] using h2⟩

theorem debrujin_alpha :
  ∀ (t1 t2 : Term) (dt : DBTerm),
    t1.toDB = some dt → t2.toDB = some dt → AlphaEqv t1 t2 := by
  intro t1 t2 dt h1 h2
  exact IsAlphaTerms_of_toDBAux_eq [] [] [] t1 t2 dt DBCtxRel.nil
    (by simpa [Term.toDB] using h1)
    (by simpa [Term.toDB] using h2)
