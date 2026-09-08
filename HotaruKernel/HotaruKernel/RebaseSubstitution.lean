import HotaruKernel.SignatureExtension
import HotaruKernel.Substitution

namespace HotaruKernel

variable {s u : Signature}

theorem Term.rebase_rename {ctx dst : List HolType} (t : Term s ctx a)
    (h : s.Extends u) (r : Renaming ctx dst) :
    (t.rename r).rebase h = (t.rebase h).rename r := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar => rfl
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf r) (ihx r)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _) (ihr _)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _) (ihq _)
  | lam hv b ih => exact congrArg (Term.lam _) (ih r.lift)

theorem Term.rebase_weaken {ctx : List HolType} (t : Term s ctx a) (h : s.Extends u) :
    (t.weaken (b := b)).rebase h = (t.rebase h).weaken := t.rebase_rename h BVar.succ

theorem Term.rebase_substBound {ctx dst : List HolType} (t : Term s ctx a)
    (h : s.Extends u) (r : BoundSubst s ctx dst) (q : BoundSubst u ctx dst)
    (hr : ∀ a (v : BVar ctx a), (r v).rebase h = q v) :
    (t.substBound r).rebase h = (t.rebase h).substBound q := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar v => exact hr _ v
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ hr) (ihx _ _ hr)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ hr) (ihr _ _ hr)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ hr) (ihq _ _ hr)
  | lam hv b ih =>
    apply congrArg (Term.lam _)
    apply ih r.lift q.lift
    intro a v
    cases v with
    | zero => rfl
    | succ v => exact ((r v).rebase_weaken h).trans (congrArg Term.weaken (hr _ v))

theorem Term.rebase_open {ctx : List HolType} (t : Term s (a :: ctx) b)
    (x : Term s ctx a) (h : s.Extends u) :
    (t.open x).rebase h = (t.rebase h).open (x.rebase h) := by
  apply t.rebase_substBound
  intro a v
  cases v <;> rfl

theorem Term.rebase_substFree {ctx dst : List HolType} (t : Term s ctx a)
    (h : s.Extends u) (r : FreeSubst s dst) (q : FreeSubst u dst) (k : Renaming ctx dst)
    (hr : ∀ n a hv hu, (r n a hv).rebase h = q n a hu) :
    (t.substFree r k).rebase h = (t.rebase h).substFree q k := by
  induction t generalizing dst with
  | fvar n a hv => exact hr n a hv _
  | bvar => rfl
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ _ hr) (ihx _ _ _ hr)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ _ hr) (ihr _ _ _ hr)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ _ hr) (ihq _ _ _ hr)
  | lam hv b ih =>
    apply congrArg (Term.lam _)
    apply ih r.lift q.lift k.lift
    intro n a hv hu
    exact ((r n a hv).rebase_weaken h).trans (congrArg Term.weaken (hr n a hv hu))

theorem Term.rebase_close {ctx : List HolType} (t : Term s ctx b) (h : s.Extends u)
    (n : String) (a : HolType) : (t.close n a).rebase h = (t.rebase h).close n a := by
  apply t.rebase_substFree
  intro k b hv hu
  by_cases ht : b = a
  · subst b
    by_cases hn : k = n <;> simp [FreeSubst.close, hn, rebase]
  · simp [FreeSubst.close, ht, rebase]

theorem Term.rebase_abstract {ctx : List HolType} (t : Term s ctx b) (h : s.Extends u)
    (n : String) (a : HolType) (hv : s.validType a = true) :
    (t.abstract n a hv).rebase h = (t.rebase h).abstract n a (h.validType a hv) :=
  congrArg (Term.lam _) (t.rebase_close h n a)

def Replacement.rebase (r : Replacement s) (h : s.Extends u) : Replacement u :=
  ⟨r.type, r.name, r.value.rebase h⟩

def Substitution.rebase (rs : Substitution s) (h : s.Extends u) : Substitution u :=
  rs.map (fun r => r.rebase h)

theorem Substitution.lookup_rebase (rs : Substitution s) (h : s.Extends u)
    (n : String) (a : HolType) (hv : s.validType a = true) (hu : u.validType a = true) :
    (rs.lookup n a hv).rebase h = (rs.rebase h).lookup n a hu := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [rebase, List.map_cons, lookup, Replacement.rebase]
    by_cases ht : r.type = a
    · subst a
      by_cases hn : r.name = n
      · simp [hn]
      · simpa [hn] using ih
    · simpa [ht] using ih

theorem Substitution.apply_rebase (rs : Substitution s) (t : Closed s a) (h : s.Extends u) :
    (rs.apply t).rebase h = (rs.rebase h).apply (t.rebase h) := by
  apply t.rebase_substFree
  exact fun n a hv hu => rs.lookup_rebase h n a hv hu

def RewriteEntry.rebase (r : RewriteEntry s) (h : s.Extends u) : RewriteEntry u :=
  ⟨r.type, r.name, r.left.rebase h, r.right.rebase h, r.hypotheses.map (Term.rebase h)⟩

theorem rewriteSubst_rebase (rs : List (RewriteEntry s)) (h : s.Extends u) (side : Bool) :
    (rewriteSubst rs side).rebase h = rewriteSubst (rs.map (fun r => r.rebase h)) side := by
  simp only [Substitution.rebase, rewriteSubst, List.map_map]
  apply List.map_congr_left
  intro r _
  cases side <;> rfl

theorem rewriteHypotheses_rebase (rs : List (RewriteEntry s)) (h : s.Extends u) :
    (rewriteHypotheses rs).map (Term.rebase h) =
      rewriteHypotheses (rs.map (fun r => r.rebase h)) := by
  simp only [rewriteHypotheses, List.map_flatMap, List.flatMap_map, RewriteEntry.rebase]

theorem rebase_filter (hs : List (Formula s)) (p : Formula s) (h : s.Extends u) :
    (hs.filter (fun q => decide (¬ q.Equivalent p))).map (Term.rebase h) =
      (hs.map (Term.rebase h)).filter (fun q => decide (¬ q.Equivalent (p.rebase h))) := by
  induction hs with
  | nil => rfl
  | cons q qs ih =>
    by_cases he : q.Equivalent p
    · have he' : (q.rebase h).Equivalent (p.rebase h) := by
        simpa only [Term.Equivalent, Term.logical_rebase] using he
      simpa [he, he'] using ih
    · have he' : ¬ (q.rebase h).Equivalent (p.rebase h) := by
        simpa only [Term.Equivalent, Term.logical_rebase] using he
      simpa [he, he'] using ih

end HotaruKernel
