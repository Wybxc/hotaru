import HotaruKernel.SubstitutionLemmas

namespace HotaruKernel

/-! Mixed substitution is a proof intermediate for composing the executable
free and bound substitutions under arbitrary nested binders. -/
def Term.bind {ctx dst : List HolType} (r : FreeSubst s dst) (q : BoundSubst s ctx dst) :
    Term s ctx a → Term s dst a
  | .fvar n a h => r n a h
  | .bvar v => q v
  | .const n t i h v => .const n t i h v
  | .app f x => .app (f.bind r q) (x.bind r q)
  | .lam h b => .lam h (b.bind r.lift q.lift)
  | .equal l t => .equal (l.bind r q) (t.bind r q)
  | .imp p t => .imp (p.bind r q) (t.bind r q)

theorem Term.rename_comp {ctx dst out : List HolType} (t : Term s ctx a)
    (r : Renaming ctx dst) (q : Renaming dst out) (u : Renaming ctx out)
    (h : ∀ a (v : BVar ctx a), q (r v) = u v) : (t.rename r).rename q = t.rename u := by
  induction t generalizing dst out with
  | fvar => rfl
  | bvar v => exact congrArg Term.bvar (h _ v)
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf r q u h) (ihx r q u h)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ _ h) (ihr _ _ _ h)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ _ h) (ihq _ _ _ h)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih r.lift q.lift u.lift
    intro a v
    cases v with
    | zero => rfl
    | succ v => exact congrArg BVar.succ (h _ v)

theorem Term.rename_weaken {ctx dst : List HolType} (t : Term s ctx a)
    (r : Renaming ctx dst) : (t.weaken (b := b)).rename r.lift = (t.rename r).weaken := by
  have hl := t.rename_comp (out := b :: dst) BVar.succ r.lift
    (fun v => BVar.succ (r v)) (fun _ _ => rfl)
  have hr := t.rename_comp (out := b :: dst) r BVar.succ
    (fun v => BVar.succ (r v)) (fun _ _ => rfl)
  exact hl.trans hr.symm

theorem Term.bind_rename {ctx dst out : List HolType} (t : Term s ctx a)
    (r : FreeSubst s dst) (q : BoundSubst s ctx dst) (k : Renaming dst out)
    (r' : FreeSubst s out) (q' : BoundSubst s ctx out)
    (hr : ∀ n a hv, (r n a hv).rename k = r' n a hv)
    (hq : ∀ a (v : BVar ctx a), (q v).rename k = q' v) :
    (t.bind r q).rename k = t.bind r' q' := by
  induction t generalizing dst out with
  | fvar n a hv => exact hr n a hv
  | bvar v => exact hq _ v
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ _ _ _ hr hq) (ihx _ _ _ _ _ hr hq)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ _ _ _ hr hq) (ihr _ _ _ _ _ hr hq)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ _ _ _ hr hq) (ihq _ _ _ _ _ hr hq)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih r.lift q.lift k.lift r'.lift q'.lift
    · intro n a hv
      exact (Term.rename_weaken (r n a hv) k).trans (congrArg Term.weaken (hr n a hv))
    · intro a v
      cases v with
      | zero => rfl
      | succ v => exact (Term.rename_weaken (q v) k).trans (congrArg Term.weaken (hq _ v))

theorem Term.rename_bind {ctx dst out : List HolType} (t : Term s ctx a)
    (k : Renaming ctx dst) (r : FreeSubst s out) (q : BoundSubst s dst out)
    (q' : BoundSubst s ctx out) (hq : ∀ a (v : BVar ctx a), q (k v) = q' v) :
    (t.rename k).bind r q = t.bind r q' := by
  induction t generalizing dst out with
  | fvar => rfl
  | bvar v => exact hq _ v
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ _ _ hq) (ihx _ _ _ _ hq)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ _ _ hq) (ihr _ _ _ _ hq)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ _ _ hq) (ihq _ _ _ _ hq)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih k.lift r.lift q.lift q'.lift
    intro a v
    cases v with
    | zero => rfl
    | succ v => exact congrArg Term.weaken (hq _ v)

theorem Term.bind_weaken {ctx dst : List HolType} (t : Term s ctx a)
    (r : FreeSubst s dst) (q : BoundSubst s ctx dst) :
    (t.weaken (b := b)).bind r.lift q.lift = (t.bind r q).weaken := by
  have hl := t.rename_bind (dst := b :: ctx) (out := b :: dst) BVar.succ r.lift q.lift
    (fun v => (q v).weaken) (fun _ _ => rfl)
  have hr := t.bind_rename (out := b :: dst) r q BVar.succ r.lift (fun v => (q v).weaken)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
  exact hl.trans hr.symm

theorem Term.bind_comp {ctx dst out : List HolType} (t : Term s ctx a)
    (r : FreeSubst s dst) (q : BoundSubst s ctx dst)
    (r' : FreeSubst s out) (q' : BoundSubst s dst out)
    (r'' : FreeSubst s out) (q'' : BoundSubst s ctx out)
    (hr : ∀ n a hv, (r n a hv).bind r' q' = r'' n a hv)
    (hq : ∀ a (v : BVar ctx a), (q v).bind r' q' = q'' v) :
    (t.bind r q).bind r' q' = t.bind r'' q'' := by
  induction t generalizing dst out with
  | fvar n a hv => exact hr n a hv
  | bvar v => exact hq _ v
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ _ _ _ _ hr hq) (ihx _ _ _ _ _ _ hr hq)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ _ _ _ _ hr hq) (ihr _ _ _ _ _ _ hr hq)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ _ _ _ _ hr hq) (ihq _ _ _ _ _ _ hr hq)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih r.lift q.lift r'.lift q'.lift r''.lift q''.lift
    · intro n a hv
      exact (Term.bind_weaken (r n a hv) r' q').trans (congrArg Term.weaken (hr n a hv))
    · intro a v
      cases v with
      | zero => rfl
      | succ v => exact (Term.bind_weaken (q v) r' q').trans (congrArg Term.weaken (hq _ v))

theorem Term.substFree_bind {ctx dst : List HolType} (t : Term s ctx a)
    (r : FreeSubst s dst) (k : Renaming ctx dst) (q : BoundSubst s ctx dst)
    (hq : ∀ a (v : BVar ctx a), q v = .bvar (k v)) : t.substFree r k = t.bind r q := by
  induction t generalizing dst with
  | fvar => rfl
  | bvar v => exact (hq _ v).symm
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ _ hq) (ihx _ _ _ hq)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ _ hq) (ihr _ _ _ hq)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ _ hq) (ihq _ _ _ hq)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih r.lift k.lift q.lift
    intro a v
    cases v with
    | zero => rfl
    | succ v => exact congrArg Term.weaken (hq _ v)

theorem Term.substBound_bind {ctx dst : List HolType} (t : Term s ctx a)
    (q : BoundSubst s ctx dst) (r : FreeSubst s dst)
    (hr : ∀ n a hv, r n a hv = .fvar n a hv) : t.substBound q = t.bind r q := by
  induction t generalizing dst with
  | fvar n a hv => exact (hr n a hv).symm
  | bvar => rfl
  | const => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _ _ hr) (ihx _ _ hr)
  | equal l r ihl ihr => exact congrArg₂ Term.equal (ihl _ _ hr) (ihr _ _ hr)
  | imp p q ihp ihq => exact congrArg₂ Term.imp (ihp _ _ hr) (ihq _ _ hr)
  | lam hv b ih =>
    apply congrArg (Term.lam hv)
    apply ih q.lift r.lift
    intro n a hv
    exact congrArg Term.weaken (hr n a hv)

theorem Term.bind_id {ctx : List HolType} (t : Term s ctx a)
    (r : FreeSubst s ctx) (q : BoundSubst s ctx ctx)
    (hr : ∀ n a hv, r n a hv = .fvar n a hv)
    (hq : ∀ a (v : BVar ctx a), q v = .bvar v) : t.bind r q = t := by
  rw [← t.substFree_bind r (fun v => v) q hq]
  exact t.substFree_eq r (fun v => v) (fun n a hv _ => hr n a hv) (fun _ _ => rfl)

theorem Term.weaken_open {ctx : List HolType} (t : Term s ctx a) (x : Term s ctx b) :
    t.weaken.open x = t := by
  let r : FreeSubst s ctx := fun n a hv => .fvar n a hv
  have h := t.weaken.substBound_bind (BoundSubst.single x) r (fun _ _ _ => rfl)
  change t.weaken.substBound (BoundSubst.single x) = t
  rw [h]
  have hr := t.rename_bind BVar.succ r (BoundSubst.single x) (fun v => .bvar v)
    (fun _ _ => rfl)
  exact hr.trans (t.bind_id r (fun v => .bvar v) (fun _ _ _ => rfl) (fun _ _ => rfl))

theorem Substitution.apply_nil (t : Closed s a) : Substitution.apply [] t = t :=
  t.substFree_eq _ _ (fun _ _ _ _ => rfl) (fun _ _ => rfl)

theorem Renaming.lift_id {ctx : List HolType} :
    (Renaming.lift (fun (v : BVar ctx _) => v) : Renaming (a :: ctx) (a :: ctx)) =
      (fun {_} v => v) := by
  funext b v
  cases v <;> rfl

theorem Substitution.apply_abstract (rs : Substitution s) (t : Closed s b)
    (n : String) (a : HolType) (hv : s.validType a = true) :
    rs.apply (t.abstract n a hv) =
      .lam hv ((t.close n a).substFree rs.lookup.lift (fun v => v)) := by
  simp only [apply, Term.abstract, Term.substFree, Renaming.lift_id]

@[simp] theorem Substitution.apply_imp (rs : Substitution s) (p q : Formula s) :
    rs.apply (.imp p q) = .imp (rs.apply p) (rs.apply q) := rfl

theorem Substitution.apply_cons_close (t : Closed s a) (entry : Replacement s)
    (rs : Substitution s) :
    ((t.close entry.name entry.type).substFree rs.lookup.lift (fun v => v)).open entry.value =
      Substitution.apply (entry :: rs) t := by
  let empty : BoundSubst s [] [entry.type] := fun v => nomatch v
  let emptyOut : BoundSubst s [] [] := fun v => nomatch v
  let bound : BoundSubst s [entry.type] [entry.type] := fun v => .bvar v
  let identity : FreeSubst s [] := fun n a hv => .fvar n a hv
  let intermediate : FreeSubst s [entry.type] := fun n a hv =>
    (FreeSubst.close entry.name entry.type n a hv).bind rs.lookup.lift bound
  have hc := t.substFree_bind (FreeSubst.close entry.name entry.type) BVar.succ empty
    (fun _ v => nomatch v)
  have hf := (t.close entry.name entry.type).substFree_bind rs.lookup.lift
    (fun v => v) bound (fun _ _ => rfl)
  have ho := ((t.close entry.name entry.type).substFree rs.lookup.lift (fun v => v)).substBound_bind
    (BoundSubst.single entry.value) identity (fun _ _ _ => rfl)
  change _ = t.substFree (Substitution.lookup (entry :: rs)) (fun v => v)
  rw [t.substFree_bind _ (fun v => v) emptyOut (fun _ v => nomatch v)]
  change ((t.close entry.name entry.type).substFree rs.lookup.lift (fun v => v)).substBound
    (BoundSubst.single entry.value) = _
  rw [ho, hf]
  change ((t.substFree (FreeSubst.close entry.name entry.type) BVar.succ).bind
    rs.lookup.lift bound).bind identity (BoundSubst.single entry.value) = _
  rw [hc, t.bind_comp _ empty rs.lookup.lift bound intermediate empty
    (fun _ _ _ => rfl) (fun _ v => nomatch v)]
  apply t.bind_comp _ empty identity (BoundSubst.single entry.value)
    (Substitution.lookup (entry :: rs)) emptyOut
  · intro n a hv
    change ((FreeSubst.close entry.name entry.type n a hv).bind rs.lookup.lift bound).bind
      identity (BoundSubst.single entry.value) = Substitution.lookup (entry :: rs) n a hv
    by_cases ht : a = entry.type
    · subst a
      by_cases hn : n = entry.name
      · subst n
        simp [FreeSubst.close, Substitution.lookup, Term.bind, bound, BoundSubst.single]
      · have hn' : entry.name ≠ n := Ne.symm hn
        simp only [FreeSubst.close, ↓reduceDIte, hn, ↓reduceIte, Term.bind,
          Substitution.lookup, hn']
        exact ((rs.lookup n entry.type hv).weaken.substBound_bind
          (BoundSubst.single entry.value) identity (fun _ _ _ => rfl)).symm.trans
          (Term.weaken_open _ _)
    · have ht' : entry.type ≠ a := Ne.symm ht
      simp only [FreeSubst.close, ht, ↓reduceDIte, Term.bind, Substitution.lookup, ht']
      exact ((rs.lookup n a hv).weaken.substBound_bind
        (BoundSubst.single entry.value) identity (fun _ _ _ => rfl)).symm.trans
        (Term.weaken_open _ _)
  · intro a v
    cases v

end HotaruKernel
