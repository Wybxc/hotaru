import HotaruKernel.Type
import HotaruKernel.Term
import Aesop

/-- De Bruijn representation used to reason about alpha-equivalence. -/
inductive DBTerm
| bvar : Nat -> DBTerm
| fvar : String -> HOLType -> DBTerm
| const : String -> HOLType -> DBTerm
| app : DBTerm -> DBTerm -> DBTerm
| abs : HOLType -> DBTerm -> DBTerm
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
    some (DBTerm.abs T t')
| .abs _ _ => none

/-- Convert a named term to de Bruijn form. -/
def Term.toDB (t : Term) : Option DBTerm := toDBAux [] t

theorem toDB_bvar : ∀ (ctx : List (String × HOLType)) (t : Term) (n : Nat),
    toDBAux ctx t = some (DBTerm.bvar n) →
    ∃ x T, ctx[n]? = some (x, T) ∧ t = .var x T := by
  intro ctx t n h
  cases t with try simp at h
  | var x T =>
      cases hidx : ctx.idxOf? (x, T) with
      | none =>
          simp [hidx] at h
      | some m =>
          have hm : m = n := by
            simpa [hidx] using h
          have hidx' : ctx.idxOf? (x, T) = some n := by
            simpa [hm] using hidx
          rcases (List.idxOf?_eq_some_iff (l := ctx) (a := (x, T)) (i := n)).1 hidx' with
            ⟨hn, hget, _⟩
          refine ⟨x, T, ?_, rfl⟩
          simpa [hget] using (List.getElem?_eq_getElem (l := ctx) (i := n) hn)
  | app s u =>
      cases hs : toDBAux ctx s <;> simp [hs] at h
      cases hu : toDBAux ctx u <;> simp [hu] at h
  | abs n1 body =>
      cases n1 with try simp at h
      | var x T => cases hb : toDBAux ((x, T) :: ctx) body <;> simp [hb] at h

theorem toDB_fvar : ∀ (ctx : List (String × HOLType)) (t : Term) (x : String) (T : HOLType),
    toDBAux ctx t = some (DBTerm.fvar x T) →
    (x, T) ∉ ctx ∧ t = .var x T := by
  intro ctx t x T h
  cases t with try simp at h
  | var y U =>
      cases hidx : ctx.idxOf? (y, U) with
      | none =>
          have hNot : (y, U) ∉ ctx :=
            (List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).1 hidx
          simp [hidx] at h
          rcases h with ⟨hx, hT⟩
          subst hx hT
          exact ⟨hNot, rfl⟩
      | some n =>
          simp [hidx] at h
  | app s u =>
      cases hs : toDBAux ctx s <;> simp [hs] at h
      cases hu : toDBAux ctx u <;> simp [hu] at h
  | abs n body =>
      cases n with try simp at h
      | var y U => cases hb : toDBAux ((y, U) :: ctx) body <;> simp [hb] at h

theorem toDB_const : ∀ (ctx : List (String × HOLType)) (t : Term) (c : String) (T : HOLType),
    toDBAux ctx t = some (DBTerm.const c T) →
    t = .const c T := by
  intro ctx t c T h
  cases t with try simp at h
  | var x U => cases hidx : ctx.idxOf? (x, U) <;> simp [hidx] at h
  | const c' T' =>
      rcases h with ⟨hc, hT⟩
      subst hc hT
      rfl
  | app s u =>
      cases hs : toDBAux ctx s <;> simp [hs] at h
      cases hu : toDBAux ctx u <;> simp [hu] at h
  | abs n body =>
      cases n with try simp at h
      | var x U => cases hb : toDBAux ((x, U) :: ctx) body <;> simp [hb] at h

theorem toDB_app : ∀ (ctx : List (String × HOLType)) (t : Term) (s' t' : DBTerm),
    toDBAux ctx t = some (DBTerm.app s' t') →
    ∃ s u, toDBAux ctx s = some s' ∧ toDBAux ctx u = some t' ∧ t = .app s u := by
  intros ctx t s' t' h
  cases t with try simp at h
  | var x U => cases hidx : ctx.idxOf? (x, U) <;> simp [hidx] at h
  | app s u =>
      cases hs : toDBAux ctx s with simp [hs] at h
      | some ds =>
          cases hu : toDBAux ctx u with simp [hu] at h
          | some du =>
              have happ : DBTerm.app ds du = DBTerm.app s' t' := by
                simpa [toDBAux, hs, hu] using h
              injection happ with hds hdu
              subst hds hdu
              exact ⟨s, u, hs, hu, rfl⟩
  | abs n body =>
      cases n with try simp at h
      | var x U => cases hb : toDBAux ((x, U) :: ctx) body <;> simp [hb] at h

theorem toDB_abs : ∀ (ctx : List (String × HOLType)) (t : Term) (dT : HOLType) (t' : DBTerm),
    toDBAux ctx t = some (DBTerm.abs dT t') →
    ∃ x t'', t = .abs (.var x dT) t'' ∧ toDBAux ((x, dT) :: ctx) t'' = some t' := by
  intro ctx t dT t' h
  cases t with try simp at h
  | var x U =>
      cases hidx : ctx.idxOf? (x, U) <;> simp [hidx] at h
  | app s u =>
      cases hs : toDBAux ctx s <;> simp [hs] at h
      cases hu : toDBAux ctx u <;> simp [hu] at h
  | abs n body =>
      cases n with try simp at h
      | var x U =>
          cases hb : toDBAux ((x, U) :: ctx) body with simp [hb] at h
          | some db =>
              have hAbs : DBTerm.abs U db = DBTerm.abs dT t' := by
                simpa [toDBAux, hb] using h
              injection hAbs with hU hdb
              subst hU hdb
              exact ⟨x, body, rfl, hb⟩

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
private theorem findIdx_cons_hit
    (env : List (String × HOLType)) (x : String) (T : HOLType) :
    ((x, T) :: env).findIdx? (fun (y, yT) => x = y ∧ T = yT) = some 0 := by
  simp [List.findIdx?, List.findIdx?.go]

/-- Key lookup lemma: head miss reduces to tail with succ. -/
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
private theorem IsAlphaVars_of_DBCtxRel_idxOf_eq :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType) (n : Nat),
      DBCtxRel bv env1 env2 ->
      env1.idxOf? (x1, T1) = some n ->
      env2.idxOf? (x2, T2) = some n ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) := by
  intro bv env1 env2 x1 x2 T1 T2 n hRel
  induction hRel generalizing n x1 x2 T1 T2 with
  | nil => aesop
  | cons x y TL TR bv env1 env2 hRel ih =>
      intro hIdx1 hIdx2
      cases n with
      | zero =>
          rcases (List.idxOf?_eq_some_iff (l := (x, TL) :: env1) (a := (x1, T1)) (i := 0)).1 hIdx1 with
            ⟨_, hGet1, _⟩
          rcases (List.idxOf?_eq_some_iff (l := (y, TR) :: env2) (a := (x2, T2)) (i := 0)).1 hIdx2 with
            ⟨_, hGet2, _⟩
          simp at hGet1 hGet2
          rcases hGet1 with ⟨hx1, hT1⟩
          rcases hGet2 with ⟨hx2, hT2⟩
          subst hx1 hT1 hx2 hT2
          simp [IsAlphaVars]
      | succ n =>
          rcases (List.idxOf?_eq_some_iff (l := (x, TL) :: env1) (a := (x1, T1)) (i := n.succ)).1 hIdx1 with
            ⟨_, _, hFirst1⟩
          rcases (List.idxOf?_eq_some_iff (l := (y, TR) :: env2) (a := (x2, T2)) (i := n.succ)).1 hIdx2 with
            ⟨_, _, hFirst2⟩
          have hneq1 : (Term.var x1 T1) ≠ (Term.var x TL) := by
            intro hEq
            have hPairEq : (x, TL) = (x1, T1) := by aesop
            exact (hFirst1 0 (Nat.succ_pos _)) (by simpa using hPairEq)
          have hneq2 : (Term.var x2 T2) ≠ (Term.var y TR) := by
            intro hEq
            have hPairEq : (y, TR) = (x2, T2) := by
              cases hEq
              rfl
            exact (hFirst2 0 (Nat.succ_pos _)) (by simpa using hPairEq)
          have hbeq1 : ((x, TL) == (x1, T1)) = false :=
            (beq_eq_false_iff_ne).2 (by exact fun hEq => hneq1 (by cases hEq; rfl))
          have hbeq2 : ((y, TR) == (x2, T2)) = false :=
            (beq_eq_false_iff_ne).2 (by exact fun hEq => hneq2 (by cases hEq; rfl))
          have hTailIdx1 : env1.idxOf? (x1, T1) = some n := by
            simpa [List.idxOf?_cons, hbeq1] using hIdx1
          have hTailIdx2 : env2.idxOf? (x2, T2) = some n := by
            simpa [List.idxOf?_cons, hbeq2] using hIdx2
          exact Or.inr ⟨hneq1, hneq2, ih x1 x2 T1 T2 n hTailIdx1 hTailIdx2⟩

private theorem IsAlphaVars_of_DBCtxRel_notin :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (x : String) (T : HOLType),
      DBCtxRel bv env1 env2 ->
      (x, T) ∉ env1 ->
      (x, T) ∉ env2 ->
      IsAlphaVars bv (.var x T) (.var x T) := by
  intro bv env1 env2 x T hRel
  induction hRel generalizing x T with
  | nil => aesop
  | cons xL xR TL TR bv env1 env2 hRel ih =>
      intro hNot1 hNot2
      have hneq1 : (Term.var x T) ≠ (Term.var xL TL) := by aesop
      have hneq2 : (Term.var x T) ≠ (Term.var xR TR) := by aesop
      have hTailNot1 : (x, T) ∉ env1 := by aesop
      have hTailNot2 : (x, T) ∉ env2 := by aesop
      aesop

private theorem IsAlphaTerms_of_toDBAux_eq :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (t1 t2 : Term) (dt : DBTerm),
      DBCtxRel bv env1 env2 ->
      toDBAux env1 t1 = some dt ->
      toDBAux env2 t2 = some dt ->
      IsAlphaTerms bv t1 t2 := by
  intro bv env1 env2 t1 t2 dt
  induction dt generalizing bv env1 env2 t1 t2 with
  | bvar n =>
      intro hRel h1 h2
      have ⟨x1, T1, hEnv1, hVar1⟩ := toDB_bvar env1 t1 n h1
      have ⟨x2, T2, hEnv2, hVar2⟩ := toDB_bvar env2 t2 n h2
      subst hVar1 hVar2
      have hIdx1 : env1.idxOf? (x1, T1) = some n := by
        cases hidx1 : env1.idxOf? (x1, T1) with
        | none =>
            simp [toDBAux, hidx1] at h1
        | some m =>
            have hm : m = n := by
              simpa [toDBAux, hidx1] using h1
            simp [hm]
      have hIdx2 : env2.idxOf? (x2, T2) = some n := by
        cases hidx2 : env2.idxOf? (x2, T2) <;> aesop
      apply IsAlphaTerms.var
      apply IsAlphaVars_of_DBCtxRel_idxOf_eq <;> aesop
  | fvar x T =>
      intro hRel h1 h2
      have ⟨hNot1, hVar1⟩ := toDB_fvar env1 t1 x T h1
      have ⟨hNot2, hVar2⟩ := toDB_fvar env2 t2 x T h2
      subst hVar1 hVar2
      apply IsAlphaTerms.var
      apply IsAlphaVars_of_DBCtxRel_notin <;> aesop
  | const c T =>
      intro hRel h1 h2
      have hConst1 : t1 = .const c T := toDB_const env1 t1 c T h1
      have hConst2 : t2 = .const c T := toDB_const env2 t2 c T h2
      subst hConst1 hConst2
      apply IsAlphaTerms.const
  | app s t ihs iht =>
      intro hRel h1 h2
      rcases toDB_app env1 t1 s t h1 with ⟨s1, t1', hs1, ht1, ht1eq⟩
      rcases toDB_app env2 t2 s t h2 with ⟨s2, t2', hs2, ht2, ht2eq⟩
      subst ht1eq ht2eq
      apply IsAlphaTerms.app
      apply ihs <;> aesop
      apply iht <;> aesop
  | abs dT t ih =>
      intro hRel h1 h2
      rcases toDB_abs env1 t1 dT t h1 with ⟨x1, b1, ht1eq, hb1⟩
      rcases toDB_abs env2 t2 dT t h2 with ⟨x2, b2, ht2eq, hb2⟩
      subst ht1eq ht2eq
      have hBody : IsAlphaTerms ((Term.var x1 dT, Term.var x2 dT) :: bv) b1 b2 :=
        ih ((Term.var x1 dT, Term.var x2 dT) :: bv)
          ((x1, dT) :: env1) ((x2, dT) :: env2) b1 b2
          (DBCtxRel.cons x1 x2 dT dT bv env1 env2 hRel) hb1 hb2
      have hTy : ∃ T, (Term.var x1 dT).HasType T ∧ (Term.var x2 dT).HasType T :=
        ⟨dT, Term.HasType.var x1 dT, Term.HasType.var x2 dT⟩
      apply IsAlphaTerms.abs <;> aesop

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
