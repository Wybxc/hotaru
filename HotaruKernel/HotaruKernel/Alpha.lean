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
| abs : ∀ (bv : List (Term × Term)) (n1 n2 : String) (T : HOLType) (t1 t2 : Term),
          IsAlphaTerms (((.var n1 T), (.var n2 T)) :: bv) t1 t2 → IsAlphaTerms bv (.abs n1 T t1) (.abs n2 T t2)

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
      intro _ _
      exact IsAlphaTerms.const bv c T
  | app s t ih_s ih_t =>
      intro h hwt
      apply IsAlphaTerms.app
      · exact ih_s bv h (welltyped_fun s t hwt)
      · exact ih_t bv h (welltyped_arg s t hwt)
  | abs n dT t ih_t =>
      intro h hwt
      apply IsAlphaTerms.abs
      have h' : IsTrivialRenaming ((Term.var n dT, Term.var n dT) :: bv) := by
        simp [IsTrivialRenaming, h]
      exact ih_t ((Term.var n dT, Term.var n dT) :: bv) h' (welltyped_body n dT t hwt)

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
      exact IsAlphaTerms.var (swap_renaming bv) x2 x1 T2 T1 (IsAlphaVars_symm bv (.var x1 T1) (.var x2 T2) hv)
  | const bv c T =>
      exact IsAlphaTerms.const (swap_renaming bv) c T
  | app bv s1 s2 t1 t2 hs ht ihs iht =>
      exact IsAlphaTerms.app (swap_renaming bv) s2 s1 t2 t1 ihs iht
  | abs bv n1 n2 T t1 t2 hbody ih =>
      simpa [swap_renaming] using
        (IsAlphaTerms.abs (swap_renaming bv) n2 n1 T t2 t1 ih)

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
  induction h12 generalizing bv23 bv13 t3 with
  | var bv x1 x2 T1 T2 hv12 =>
      intro h23
      cases h23 with
      | var _ _ _ _ _ hv23 =>
          apply IsAlphaTerms.var
          exact IsAlphaVars_trans bv bv23 bv13 _ _ _ hchain hv12 hv23
  | const bv c T =>
      intro h23
      cases h23 with
      | const => exact IsAlphaTerms.const bv13 c T
  | app bv s1 s2 t1 t2 hs12 ht12 ihs iht =>
      intro h23
      cases h23 with
      | app _ _ _ _ _ hs23 ht23 =>
          apply IsAlphaTerms.app
          · exact ihs _ _ _ hchain hs23
          · exact iht _ _ _ hchain ht23
  | abs bv n1 n2 T t1 t2 hbody12 ih =>
      intro h23
      cases h23 with
      | abs _ _ n3 _ _ t3 hbody23 =>
          apply IsAlphaTerms.abs
          exact ih
            _ _ _
            (RenamingChain.cons (Term.var n1 T) (Term.var n2 T) (Term.var n3 T) bv bv23 bv13 hchain)
            hbody23

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
