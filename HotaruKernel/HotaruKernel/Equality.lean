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

def Term.rawEq {ctx dst : List HolType} {a b : HolType}
    (t : Term s ctx a) (u : Term s dst b) : Bool :=
  match t with
  | .fvar n a _ =>
      match u with
      | .fvar m b _ => decide (n = m) && decide (a = b)
      | _ => false
  | .bvar v =>
      match u with
      | .bvar w => decide (v.index = w.index)
      | _ => false
  | .const n _ i _ _ =>
      match u with
      | .const m _ j _ _ => decide (n = m) && decide (i = j)
      | _ => false
  | .app f x =>
      match u with
      | .app g y => f.rawEq g && x.rawEq y
      | _ => false
  | @Term.lam _ a _ _ _ body =>
      match u with
      | @Term.lam _ b _ _ _ other => decide (a = b) && body.rawEq other
      | _ => false
  | .equal l r =>
      match u with
      | .equal l' r' => l.rawEq l' && r.rawEq r'
      | _ => false
  | .imp p q =>
      match u with
      | .imp p' q' => p.rawEq p' && q.rawEq q'
      | _ => false

theorem Term.rawEq_correct {ctx dst : List HolType} {a b : HolType}
    (t : Term s ctx a) (u : Term s dst b) :
    t.rawEq u = true ↔ t.raw = u.raw := by
  induction t generalizing dst b with
  | fvar n a _ => cases u <;> simp [rawEq, raw]
  | bvar v => cases u <;> simp [rawEq, raw]
  | const n scheme i _ _ => cases u <;> simp [rawEq, raw]
  | app f x ihf ihx => cases u <;> simp [rawEq, raw, ihf, ihx]
  | lam _ body ih => cases u <;> simp [rawEq, raw, ih]
  | equal l r ihl ihr => cases u <;> simp [rawEq, raw, ihl, ihr]
  | imp p q ihp ihq => cases u <;> simp [rawEq, raw, ihp, ihq]

instance : DecidableEq (Term s ctx a) := fun t u =>
  decidable_of_iff (t.rawEq u = true) ⟨
    fun h => eq_of_heq (t.raw_heq u ((t.rawEq_correct u).mp h)).2,
    fun h => (t.rawEq_correct u).mpr (congrArg Term.raw h)⟩

end HotaruKernel
