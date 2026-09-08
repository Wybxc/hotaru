import HotaruKernel.Syntax

namespace HotaruKernel

variable {ctx : List HolType}

theorem BVar.index_heq (v : BVar ctx a) (w : BVar ctx b) (h : v.index = w.index) :
    a = b ∧ HEq v w := by
  induction v generalizing b with
  | zero =>
    cases w with
    | zero => exact ⟨rfl, HEq.rfl⟩
    | succ w => simp [index] at h
  | succ v ih =>
    cases w with
    | zero => simp [index] at h
    | succ w =>
      obtain ⟨rfl, hw⟩ := ih w (Nat.add_right_cancel h)
      cases eq_of_heq hw
      exact ⟨rfl, HEq.rfl⟩

theorem Term.raw_heq (t : Term s ctx a) (u : Term s ctx b) (h : t.raw = u.raw) :
    a = b ∧ HEq t u := by
  induction t generalizing b with
  | fvar n a hv =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.fvar.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, HEq.rfl⟩
  | bvar v =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.bvar.injEq] at h
    obtain ⟨rfl, he⟩ := v.index_heq _ h
    cases eq_of_heq he
    exact ⟨rfl, HEq.rfl⟩
  | const n scheme i hd hv =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.const.injEq] at h
    rename_i scheme' i' hd' hv'
    rcases h with ⟨rfl, rfl⟩
    have ht : scheme = scheme' := Option.some.inj (hd.symm.trans hd')
    subst scheme'
    exact ⟨rfl, HEq.rfl⟩
  | app f x ihf ihx =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.app.injEq] at h
    rcases h with ⟨hf, hx⟩
    obtain ⟨ht, he⟩ := ihf _ hf
    cases ht
    cases eq_of_heq he
    obtain ⟨_, he⟩ := ihx _ hx
    cases eq_of_heq he
    exact ⟨rfl, HEq.rfl⟩
  | lam hv body ih =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.lam.injEq] at h
    rcases h with ⟨rfl, hb⟩
    obtain ⟨rfl, he⟩ := ih _ hb
    cases eq_of_heq he
    exact ⟨rfl, HEq.rfl⟩
  | equal l r ihl ihr =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.equal.injEq] at h
    rcases h with ⟨hl, hr⟩
    obtain ⟨rfl, he⟩ := ihl _ hl
    cases eq_of_heq he
    obtain ⟨_, he⟩ := ihr _ hr
    cases eq_of_heq he
    exact ⟨rfl, HEq.rfl⟩
  | imp p q ihp ihq =>
    cases u <;> simp only [raw, reduceCtorEq, RawTerm.imp.injEq] at h
    rcases h with ⟨hp, hq⟩
    obtain ⟨_, he⟩ := ihp _ hp
    cases eq_of_heq he
    obtain ⟨_, he⟩ := ihq _ hq
    cases eq_of_heq he
    exact ⟨rfl, HEq.rfl⟩

theorem Term.raw_injective : Function.Injective (Term.raw (s := s) (ctx := ctx) (a := a)) :=
  fun t u h => eq_of_heq (t.raw_heq u h).2

instance : DecidableEq (Term s ctx a) := fun t u =>
  decidable_of_iff (t.raw = u.raw) ⟨fun h => eq_of_heq (t.raw_heq u h).2, congrArg Term.raw⟩

end HotaruKernel
