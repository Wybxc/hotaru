import HotaruKernel.Type
import HotaruKernel.Term
import Aesop

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
| const : ∀ (bv : List (Term × Term)) (c : String) (T : HOLType),
          IsAlphaTerms bv (.const c T) (.const c T)
| app : ∀ (bv : List (Term × Term)) (s1 s2 t1 t2 : Term),
          IsAlphaTerms bv s1 s2 → IsAlphaTerms bv t1 t2 → IsAlphaTerms bv (.app s1 t1) (.app s2 t2)
| abs : ∀ (bv : List (Term × Term)) (n1 n2 t1 t2 : Term),
          (∃ m1 m2 T, n1 = Term.var m1 T ∧ n2 = Term.var m2 T) →
          IsAlphaTerms ((n1, n2) :: bv) t1 t2 → IsAlphaTerms bv (.abs n1 t1) (.abs n2 t2)

/-- Predicate for alpha-equivalence of terms. -/
def AlphaEqv (t1 t2 : Term) : Prop :=
  IsAlphaTerms [] t1 t2

def IsTrivialRenaming (bv : List (Term × Term)) : Prop :=
  match bv with
  | [] => true
  | (b1, b2) :: bvs => b1 = b2 ∧ IsTrivialRenaming bvs

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

theorem IsAlphaTerms_refl : ∀ (bv : List (Term × Term)) (t : Term), IsTrivialRenaming bv → WellTyped t → IsAlphaTerms bv t t
    := by
  intro bv t
  induction t generalizing bv with
  | var x T =>
      intro h _
      apply IsAlphaTerms.var
      exact IsAlphaVars_refl bv (Term.var x T) h
  | const c T =>
      intro h _
      exact IsAlphaTerms.const bv c T
  | app s t ih_s ih_t =>
      intro h hwt
      apply IsAlphaTerms.app
      · apply ih_s
        · exact h
        · exact welltyped_fun s t hwt
      · apply ih_t
        · exact h
        · exact welltyped_arg s t hwt
  | abs n t ih_n ih_t =>
      intro h hwt
      apply IsAlphaTerms.abs
      · rcases welltyped_bind n t hwt with ⟨n', dT, hn⟩
        subst hn
        exact ⟨n', n', dT, rfl, rfl⟩
      · have h' : IsTrivialRenaming ((n, n) :: bv) := by
          simp [IsTrivialRenaming, h]
        apply ih_t
        · exact h'
        · exact welltyped_body n t hwt

def swap_renaming : List (Term × Term) -> List (Term × Term)
| [] => []
| (a, b) :: bvs => (b, a) :: swap_renaming bvs

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

theorem IsAlphaTerms_symm :
  ∀ (bv : List (Term × Term)) (t1 t2 : Term),
    IsAlphaTerms bv t1 t2 → IsAlphaTerms (swap_renaming bv) t2 t1 := by
  intro bv t1 t2 h
  induction h with
  | var bv x1 x2 T1 T2 hv =>
    apply IsAlphaTerms.var
    apply IsAlphaVars_symm
    aesop
  | const bv c T => apply IsAlphaTerms.const
  | app bv s1 s2 t1 t2 hs ht ihs iht =>
      apply IsAlphaTerms.app
      · simpa using ihs
      · simpa using iht
  | abs bv n1 n2 t1 t2 hwt hbody ih =>
      rcases hwt with ⟨m1, m2, T, hn1, hn2⟩
      simpa [swap_renaming] using
      (IsAlphaTerms.abs (swap_renaming bv) n2 n1 t2 t1 ⟨m2, m1, T, hn2, hn1⟩ ih)

inductive RenamingChain :
  List (Term × Term) -> List (Term × Term) -> List (Term × Term) -> Prop
| nil : RenamingChain [] [] []
| cons :
  ∀ (n1 n2 n3 : Term)
    (bv12 bv23 bv13 : List (Term × Term)),
    RenamingChain bv12 bv23 bv13 ->
    RenamingChain ((n1, n2) :: bv12) ((n2, n3) :: bv23) ((n1, n3) :: bv13)

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
    | var =>
        apply IsAlphaTerms.var
        apply IsAlphaVars_trans <;> aesop
  | const bv c T =>
    cases h23 with
    | const => apply IsAlphaTerms.const
  | app bv s1 s2 t1 t2 hs12 ht12 ihs iht =>
    cases h23 with
    | app bv s2 s3 t2 t3 hs23 ht23 =>
      apply IsAlphaTerms.app <;> aesop
  | abs bv n1 n2 t1 t2 hwt12 hbody12 ih =>
    cases h23 with
    | abs bv n2 n3 t2 t3 hwt23 hbody23 =>
      apply IsAlphaTerms.abs
      · rcases hwt12 with ⟨m1, m2, T12, hn1, hn2l⟩
        rcases hwt23 with ⟨m2', m3, T23, hn2r, hn3⟩
        have hEqN2 : Term.var m2 T12 = Term.var m2' T23 := by
            calc
              Term.var m2 T12 = n2 := by simpa using hn2l.symm
              _ = Term.var m2' T23 := by simpa using hn2r
        have hTyEq : T12 = T23 := by
            cases hEqN2
            rfl
        cases hTyEq
        exact ⟨m1, m3, T12, hn1, hn3⟩
      apply ih <;> try simpa
      apply RenamingChain.cons; simpa

theorem AlphaEqv.refl : ∀ (t : Term), WellTyped t → AlphaEqv t t
    := by
  intro t hwt
  simpa [AlphaEqv] using IsAlphaTerms_refl [] t (by simp [IsTrivialRenaming]) hwt

theorem AlphaEqv.symm : ∀ {t1 t2 : Term}, AlphaEqv t1 t2 → AlphaEqv t2 t1
    := by
  intro t1 t2 h
  simpa [AlphaEqv, swap_renaming] using IsAlphaTerms_symm [] t1 t2 h

theorem AlphaEqv.trans : ∀ {t1 t2 t3 : Term}, AlphaEqv t1 t2 → AlphaEqv t2 t3 → AlphaEqv t1 t3
    := by
  intro t1 t2 t3 h12 h23
  exact IsAlphaTerms_trans [] [] [] t1 t2 t3 RenamingChain.nil h12 h23

noncomputable instance : DecidableRel AlphaEqv := by
  intro t1 t2
  classical
  infer_instance

instance : Setoid WellTypedTerm where
  r x y := AlphaEqv x.1 y.1
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      exact AlphaEqv.refl x.1 x.2
    · intro x y h
      exact AlphaEqv.symm h
    · intro x y z hxy hyz
      exact AlphaEqv.trans hxy hyz

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
def Term.toDB? (t : Term) : Option DBTerm := toDBAux [] t

def WellTypedTerm.toDB (t : WellTypedTerm) : DBTerm :=
  Option.get (t.1.toDB?) <| by
  have hSomeCtx :
    ∀ (ctx : List (String × HOLType)) (tm : Term) (T : HOLType),
      tm.HasType T → ∃ dt, toDBAux ctx tm = some dt := by
    intro ctx tm T hHasType
    induction hHasType generalizing ctx with
    | var x T =>
      cases hidx : ctx.idxOf? (x, T) with
      | none =>
        exact ⟨DBTerm.fvar x T, by simp [toDBAux, hidx]⟩
      | some n =>
        exact ⟨DBTerm.bvar n, by simp [toDBAux, hidx]⟩
    | const c T =>
      exact ⟨DBTerm.const c T, by simp [toDBAux]⟩
    | app s u dT rT hs ht ihs iht =>
      rcases ihs ctx with ⟨ds, hds⟩
      rcases iht ctx with ⟨du, hdu⟩
      exact ⟨DBTerm.app ds du, by simp [toDBAux, hds, hdu]⟩
    | abs n dT rT body hBody ih =>
      rcases ih ((n, dT) :: ctx) with ⟨db, hdb⟩
      exact ⟨DBTerm.abs dT db, by simp [toDBAux, hdb]⟩
  rcases t with ⟨tm, hwt⟩
  rcases hwt with ⟨T, hHasType⟩
  rcases hSomeCtx [] tm T hHasType with ⟨dt, hdt⟩
  have hSome : tm.toDB? = some dt := by simpa [Term.toDB?] using hdt
  simp [hSome]

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
      ∃ dt, toDBAux env1 t1 = some dt ∧ toDBAux env2 t2 = some dt := by
  intro bv env1 env2 t1 t2 hRel hAlpha
  induction hAlpha generalizing env1 env2 with
  | var bv x1 x2 T1 T2 hAlphaVar =>
      have hEq := toDBAux_var_eq_of_IsAlphaVars bv env1 env2 x1 x2 T1 T2 hRel hAlphaVar
      cases hidx1 : env1.idxOf? (x1, T1) with
      | none =>
          refine ⟨DBTerm.fvar x1 T1, ?_, ?_⟩
          · simp [toDBAux, hidx1]
          · calc
              toDBAux env2 (.var x2 T2) = toDBAux env1 (.var x1 T1) := by simpa using hEq.symm
              _ = some (DBTerm.fvar x1 T1) := by simp [toDBAux, hidx1]
      | some n =>
          refine ⟨DBTerm.bvar n, ?_, ?_⟩
          · simp [toDBAux, hidx1]
          · calc
              toDBAux env2 (.var x2 T2) = toDBAux env1 (.var x1 T1) := by simpa using hEq.symm
              _ = some (DBTerm.bvar n) := by simp [toDBAux, hidx1]
  | const bv c T =>
      refine ⟨DBTerm.const c T, ?_, ?_⟩ <;> simp [toDBAux]
  | app bv s1 s2 t1 t2 hAlphaS hAlphaT ihS ihT =>
      rcases ihS env1 env2 hRel with ⟨ds, hs1, hs2⟩
      rcases ihT env1 env2 hRel with ⟨dt, ht1, ht2⟩
      refine ⟨DBTerm.app ds dt, ?_, ?_⟩
      · simp [toDBAux, hs1, ht1]
      · simp [toDBAux, hs2, ht2]
  | abs bv n1 n2 t1 t2 hNames hBody ih =>
      rcases hNames with ⟨m1, m2, T, hn1, hn2⟩
      subst hn1 hn2
      have hRel' :
          DBCtxRel ((.var m1 T, .var m2 T) :: bv) ((m1, T) :: env1) ((m2, T) :: env2) :=
        DBCtxRel.cons m1 m2 T T bv env1 env2 hRel
      rcases ih ((m1, T) :: env1) ((m2, T) :: env2) hRel' with ⟨db, hb1, hb2⟩
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
  ∀ t1 t2 : WellTypedTerm,
    AlphaEqv t1 t2 → t1.toDB = t2.toDB := by
  intros t1 t2 hAlpha
  rcases toDBAux_eq_of_IsAlphaTerms [] [] [] t1.1 t2.1 DBCtxRel.nil hAlpha with ⟨dt, h1, h2⟩
  have h1' : t1.1.toDB? = some dt := by simpa [Term.toDB?] using h1
  have h2' : t2.1.toDB? = some dt := by simpa [Term.toDB?] using h2
  have ht1 : t1.toDB = dt := by simp [WellTypedTerm.toDB, h1']
  have ht2 : t2.toDB = dt := by simp [WellTypedTerm.toDB, h2']
  exact ht1.trans ht2.symm

theorem debrujin_alpha :
  ∀ (t1 t2 : WellTypedTerm),
    t1.toDB = t2.toDB → AlphaEqv t1 t2 := by
  intro t1 t2 hEq
  have h1 : t1.1.toDB? = some t1.toDB := by
    simp [WellTypedTerm.toDB]
  have h2 : t2.1.toDB? = some t1.toDB := by
    calc
      t2.1.toDB? = some t2.toDB := by simp [WellTypedTerm.toDB]
      _ = some t1.toDB := by simp [hEq]
  exact IsAlphaTerms_of_toDBAux_eq [] [] [] t1.1 t2.1 t1.toDB DBCtxRel.nil
    (by simpa [Term.toDB?] using h1)
    (by simpa [Term.toDB?] using h2)
