import HotaruKernel.Type
import HotaruKernel.Term
import HotaruKernel.Alpha
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
def toDBAux (ctx : List (String × HOLType)) : Term -> DBTerm
| .var x T =>
    match ctx.idxOf? (x, T) with
    | some n => DBTerm.bvar n
    | none => DBTerm.fvar x T
| .const c T => DBTerm.const c T
| .app s t =>
    let s' := toDBAux ctx s
    let t' := toDBAux ctx t
    DBTerm.app s' t'
| .abs x T t =>
    let t' := toDBAux ((x, T) :: ctx) t
    DBTerm.abs T t'

/-- Convert a named term to de Bruijn form. -/
def Term.toDB (t : Term) : DBTerm := toDBAux [] t

theorem toDB_bvar : ∀ (ctx : List (String × HOLType)) (t : Term) (n : Nat),
    toDBAux ctx t = DBTerm.bvar n →
    ∃ x T, ctx[n]? = some (x, T) ∧ t = .var x T := by
  intro ctx t n h
  cases t with
  | var x T =>
      cases hidx : ctx.idxOf? (x, T) with
      | none =>
          simp [toDBAux, hidx] at h
      | some m =>
          have hm : m = n := by
            simpa [toDBAux, hidx] using h
          have hidx' : ctx.idxOf? (x, T) = some n := by
            simpa [hm] using hidx
          rcases (List.idxOf?_eq_some_iff (l := ctx) (a := (x, T)) (i := n)).1 hidx' with
            ⟨hn, hget, _⟩
          refine ⟨x, T, ?_, rfl⟩
          simpa [hget] using (List.getElem?_eq_getElem (l := ctx) (i := n) hn)
  | const c T =>
      simp [toDBAux] at h
  | app s u =>
      simp [toDBAux] at h
  | abs x T body =>
      simp [toDBAux] at h

theorem toDB_fvar : ∀ (ctx : List (String × HOLType)) (t : Term) (x : String) (T : HOLType),
    toDBAux ctx t = DBTerm.fvar x T →
    (x, T) ∉ ctx ∧ t = .var x T := by
  intro ctx t x T h
  cases t with
  | var y U =>
      cases hidx : ctx.idxOf? (y, U) with
      | none =>
          have hNot : (y, U) ∉ ctx :=
            (List.idxOf?_eq_none_iff (l := ctx) (a := (y, U))).1 hidx
          have hEq : DBTerm.fvar y U = DBTerm.fvar x T := by
            simpa [toDBAux, hidx] using h
          injection hEq with hx hT
          subst hx hT
          exact ⟨hNot, rfl⟩
      | some n =>
          simp [toDBAux, hidx] at h
  | const c U =>
      simp [toDBAux] at h
  | app s u =>
      simp [toDBAux] at h
  | abs y U body =>
      simp [toDBAux] at h

theorem toDB_const : ∀ (ctx : List (String × HOLType)) (t : Term) (c : String) (T : HOLType),
    toDBAux ctx t = DBTerm.const c T →
    t = .const c T := by
  intro ctx t c T h
  cases t with
  | var x U =>
      cases hidx : ctx.idxOf? (x, U) <;> simp [toDBAux, hidx] at h
  | const c' T' =>
      have hEq : DBTerm.const c' T' = DBTerm.const c T := by
        simpa [toDBAux] using h
      injection hEq with hc hT
      subst hc hT
      rfl
  | app s u =>
      simp [toDBAux] at h
  | abs x U body =>
      simp [toDBAux] at h

theorem toDB_app : ∀ (ctx : List (String × HOLType)) (t : Term) (s' t' : DBTerm),
    toDBAux ctx t = DBTerm.app s' t' →
    ∃ s u, toDBAux ctx s = s' ∧ toDBAux ctx u = t' ∧ t = .app s u := by
  intros ctx t s' t' h
  cases t with
  | var x U =>
      cases hidx : ctx.idxOf? (x, U) <;> simp [toDBAux, hidx] at h
  | const c U =>
      simp [toDBAux] at h
  | app s u =>
      have happ : DBTerm.app (toDBAux ctx s) (toDBAux ctx u) = DBTerm.app s' t' := by
        simpa [toDBAux] using h
      injection happ with hs hu
      exact ⟨s, u, hs, hu, rfl⟩
  | abs x U body =>
      simp [toDBAux] at h

theorem toDB_abs : ∀ (ctx : List (String × HOLType)) (t : Term) (dT : HOLType) (t' : DBTerm),
    toDBAux ctx t = DBTerm.abs dT t' →
    ∃ x t'', t = .abs x dT t'' ∧ toDBAux ((x, dT) :: ctx) t'' = t' := by
  intro ctx t dT t' h
  cases t with
  | var x U =>
      cases hidx : ctx.idxOf? (x, U) <;> simp [toDBAux, hidx] at h
  | const c U =>
      simp [toDBAux] at h
  | app s u =>
      simp [toDBAux] at h
  | abs x U body =>
      have hAbs : DBTerm.abs U (toDBAux ((x, U) :: ctx) body) = DBTerm.abs dT t' := by
        simpa [toDBAux] using h
      injection hAbs with hU hBody
      subst hU
      exact ⟨x, body, rfl, hBody⟩

/-- Proof skeleton: relation between alpha-renaming environment and de Bruijn contexts. -/
private inductive DBCtxRel :
    List (Term × Term) -> List (String × HOLType) -> List (String × HOLType) -> Prop
| nil : DBCtxRel [] [] []
| cons :
    ∀ (x y : String) (T1 T2 : HOLType)
      (bv : List (Term × Term)) (env1 env2 : List (String × HOLType)),
      DBCtxRel bv env1 env2 ->
      DBCtxRel ((.var x T1, .var y T2) :: bv) ((x, T1) :: env1) ((y, T2) :: env2)

/-- Variable case bridge: alpha-variable relation implies equal de Bruijn translation. -/
private theorem toDBAux_var_eq_of_IsAlphaVars :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (x1 x2 : String) (T1 T2 : HOLType),
      DBCtxRel bv env1 env2 ->
      IsAlphaVars bv (.var x1 T1) (.var x2 T2) ->
      toDBAux env1 (.var x1 T1) = toDBAux env2 (.var x2 T2) := by
  intro bv env1 env2 x1 x2 T1 T2 hRel hAlpha
  induction hRel generalizing x1 x2 T1 T2 with
  | nil =>
      change (Term.var x1 T1 = Term.var x2 T2) at hAlpha
      cases hAlpha
      simp [toDBAux]
  | cons x y TL TR bv env1 env2 hRel ih =>
      change
        ((Term.var x1 T1 = Term.var x TL ∧ Term.var x2 T2 = Term.var y TR) ∨
          (Term.var x1 T1 ≠ Term.var x TL ∧ Term.var x2 T2 ≠ Term.var y TR ∧
            IsAlphaVars bv (Term.var x1 T1) (Term.var x2 T2))) at hAlpha
      rcases hAlpha with hHit | hMiss
      · rcases hHit with ⟨h1, h2⟩
        cases h1
        cases h2
        simp [toDBAux, List.idxOf?_cons]
      · rcases hMiss with ⟨hneq1, hneq2, hTail⟩
        have hTailEq : toDBAux env1 (.var x1 T1) = toDBAux env2 (.var x2 T2) :=
          ih x1 x2 T1 T2 hTail
        have hbeq1 : ((x, TL) == (x1, T1)) = false := (beq_eq_false_iff_ne).2 (by aesop)
        have hbeq2 : ((y, TR) == (x2, T2)) = false := (beq_eq_false_iff_ne).2 (by aesop)
        cases hidx1 : env1.idxOf? (x1, T1) with
        | none =>
            cases hidx2 : env2.idxOf? (x2, T2) with
            | none =>
                have hEqVar : x1 = x2 ∧ T1 = T2 := by
                  simpa [toDBAux, hidx1, hidx2] using hTailEq
                rcases hEqVar with ⟨hx, hT⟩
                subst hx hT
                simp [toDBAux, List.idxOf?_cons, hbeq1, hbeq2, hidx1, hidx2]
            | some n2 => aesop
        | some n1 =>
            cases hidx2 : env2.idxOf? (x2, T2) with
            | none => aesop
            | some n2 =>
                have hn : n1 = n2 := by
                  simpa [toDBAux, hidx1, hidx2] using hTailEq
                subst hn
                simp [toDBAux, List.idxOf?_cons, hbeq1, hbeq2, hidx1, hidx2]

/-- Forward direction core lemma under related contexts. -/
private theorem toDBAux_eq_of_IsAlphaTerms :
    ∀ (bv : List (Term × Term)) (env1 env2 : List (String × HOLType))
      (t1 t2 : Term),
      DBCtxRel bv env1 env2 ->
      IsAlphaTerms bv t1 t2 ->
      ∃ dt, toDBAux env1 t1 = dt ∧ toDBAux env2 t2 = dt := by
  intro bv env1 env2 t1 t2 hRel hAlpha
  induction hAlpha generalizing env1 env2 with
  | var bv x1 x2 T1 T2 hAlphaVar =>
      have hEq := toDBAux_var_eq_of_IsAlphaVars bv env1 env2 x1 x2 T1 T2 hRel hAlphaVar
      refine ⟨toDBAux env1 (.var x1 T1), rfl, ?_⟩
      exact hEq.symm
  | const bv c T =>
      refine ⟨DBTerm.const c T, ?_, ?_⟩ <;> simp [toDBAux]
  | app bv s1 s2 t1 t2 hAlphaS hAlphaT ihS ihT =>
      rcases ihS env1 env2 hRel with ⟨ds, hs1, hs2⟩
      rcases ihT env1 env2 hRel with ⟨dt, ht1, ht2⟩
      refine ⟨DBTerm.app ds dt, ?_, ?_⟩
      · simp [toDBAux, hs1, ht1]
      · simp [toDBAux, hs2, ht2]
  | abs bv n1 n2 T t1 t2 hBody ih =>
      have hRel' :
          DBCtxRel ((.var n1 T, .var n2 T) :: bv) ((n1, T) :: env1) ((n2, T) :: env2) :=
        DBCtxRel.cons n1 n2 T T bv env1 env2 hRel
      rcases ih ((n1, T) :: env1) ((n2, T) :: env2) hRel' with ⟨db, hb1, hb2⟩
      refine ⟨DBTerm.abs T db, ?_, ?_⟩
      · simp [toDBAux, hb1]
      · simp [toDBAux, hb2]

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
      toDBAux env1 t1 = dt ->
      toDBAux env2 t2 = dt ->
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
          simpa [hidx1] using congrArg some hm
      have hIdx2 : env2.idxOf? (x2, T2) = some n := by
        cases hidx2 : env2.idxOf? (x2, T2) with
        | none =>
            simp [toDBAux, hidx2] at h2
        | some m =>
          have hm : m = n := by
            simpa [toDBAux, hidx2] using h2
          simpa [hidx2] using congrArg some hm
      exact IsAlphaTerms.var bv x1 x2 T1 T2
        (IsAlphaVars_of_DBCtxRel_idxOf_eq bv env1 env2 x1 x2 T1 T2 n hRel hIdx1 hIdx2)
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
      · exact ihs bv env1 env2 s1 s2 hRel hs1 hs2
      · exact iht bv env1 env2 t1' t2' hRel ht1 ht2
  | abs dT t ih =>
      intro hRel h1 h2
      rcases toDB_abs env1 t1 dT t h1 with ⟨x1, b1, ht1eq, hb1⟩
      rcases toDB_abs env2 t2 dT t h2 with ⟨x2, b2, ht2eq, hb2⟩
      subst ht1eq ht2eq
      have hBody : IsAlphaTerms ((Term.var x1 dT, Term.var x2 dT) :: bv) b1 b2 :=
        ih ((Term.var x1 dT, Term.var x2 dT) :: bv)
          ((x1, dT) :: env1) ((x2, dT) :: env2) b1 b2
          (DBCtxRel.cons x1 x2 dT dT bv env1 env2 hRel) hb1 hb2
      exact IsAlphaTerms.abs bv x1 x2 dT b1 b2 hBody

theorem alpha_debrujin :
  ∀ t1 t2 : Term,
    AlphaEqv t1 t2 → t1.toDB = t2.toDB := by
  intros t1 t2 hAlpha
  rcases toDBAux_eq_of_IsAlphaTerms [] [] [] t1 t2 DBCtxRel.nil hAlpha with ⟨dt, h1, h2⟩
  have ht1 : t1.toDB = dt := by simpa [Term.toDB] using h1
  have ht2 : t2.toDB = dt := by simpa [Term.toDB] using h2
  exact ht1.trans ht2.symm

theorem debrujin_alpha :
  ∀ (t1 t2 : Term),
    t1.toDB = t2.toDB → AlphaEqv t1 t2 := by
  intro t1 t2 hEq
  exact IsAlphaTerms_of_toDBAux_eq [] [] [] t1 t2 t1.toDB DBCtxRel.nil
    (by simp [Term.toDB])
    (by simpa [Term.toDB] using hEq.symm)
