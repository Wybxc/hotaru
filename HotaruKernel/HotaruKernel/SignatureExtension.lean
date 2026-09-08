import HotaruKernel.TypeInstantiation
import HotaruKernel.LogicalEquality

namespace HotaruKernel

variable {s u v : Signature}

structure Signature.Extends (s u : Signature) : Prop where
  typeOps : ∀ n arity, s.typeOps.lookup n = some arity → u.typeOps.lookup n = some arity
  constants : ∀ n scheme,
    s.constants.lookup n = some scheme → u.constants.lookup n = some scheme

theorem Signature.Extends.refl (s : Signature) : s.Extends s :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Signature.Extends.trans (h : s.Extends u) (k : u.Extends v) : s.Extends v :=
  ⟨fun n a ha => k.typeOps n a (h.typeOps n a ha),
   fun n a ha => k.constants n a (h.constants n a ha)⟩

theorem Signature.Extends.validType (h : s.Extends u) (a : HolType) :
    s.validType a = true → u.validType a = true := by
  induction a using HolType.rec
    (motive_2 := fun args => ∀ a ∈ args, s.validType a = true → u.validType a = true) with
  | var n => simp [Signature.validType]
  | bool => simp [Signature.validType]
  | fn a b ha hb =>
    simp only [Signature.validType, Bool.and_eq_true]
    exact fun ⟨h₁, h₂⟩ => ⟨ha h₁, hb h₂⟩
  | op n args ih =>
    rw [Signature.validType_op_iff, Signature.validType_op_iff]
    exact fun ⟨ht, ha⟩ => ⟨h.typeOps n _ ht, fun a hm => ih a hm (ha a hm)⟩
  | nil a ha => cases ha
  | cons a args ha ih b hb hv =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha hv
    · exact ih b hb hv

theorem Signature.Extends.validSubst (h : s.Extends u) (i : TypeSubst) (hi : i.Valid s) :
    i.Valid u := fun entry he => h.validType _ (hi entry he)

def Term.rebase {ctx : List HolType} (h : s.Extends u) : Term s ctx a → Term u ctx a
  | .fvar n a hv => .fvar n a (h.validType a hv)
  | .bvar v => .bvar v
  | .const n scheme i hd hv => .const n scheme i (h.constants n scheme hd) (h.validType _ hv)
  | .app f x => .app (f.rebase h) (x.rebase h)
  | .lam hv b => .lam (h.validType _ hv) (b.rebase h)
  | .equal l r => .equal (l.rebase h) (r.rebase h)
  | .imp p q => .imp (p.rebase h) (q.rebase h)

theorem Term.raw_rebase {ctx : List HolType} (t : Term s ctx a) (h : s.Extends u) :
    (t.rebase h).raw = t.raw := by
  induction t <;> simp_all [rebase, raw]

theorem Term.logical_rebase {ctx : List HolType} (t : Term s ctx a) (h : s.Extends u) :
    (t.rebase h).logical = t.logical := by
  induction t <;> simp_all [rebase, logical]

theorem Term.freeVars_rebase {ctx : List HolType} (t : Term s ctx a) (h : s.Extends u) :
    (t.rebase h).freeVars = t.freeVars := by
  induction t <;> simp_all [rebase, freeVars]

theorem Term.rebase_refl {ctx : List HolType} (t : Term s ctx a) :
    t.rebase (.refl s) = t := Term.raw_injective (t.raw_rebase _)

theorem Term.rebase_trans {ctx : List HolType} (t : Term s ctx a)
    (h : s.Extends u) (k : u.Extends v) : (t.rebase h).rebase k = t.rebase (h.trans k) := by
  apply Term.raw_injective
  simp only [raw_rebase]

theorem Term.rebase_injective {ctx : List HolType} (h : s.Extends u) :
    Function.Injective (Term.rebase (a := a) (ctx := ctx) h) := by
  intro t v hv
  apply Term.raw_injective
  have he := congrArg Term.raw hv
  simpa only [raw_rebase] using he

theorem Term.rebase_instType {ctx : List HolType} (t : Term s ctx a)
    (h : s.Extends u) (i : TypeSubst) (hi : i.Valid s) :
    (t.instType i hi).rebase h = (t.rebase h).instType i (h.validSubst i hi) := by
  apply Term.raw_injective
  simp only [raw_rebase, raw_instType]

def Signature.addType (s : Signature) (n : QName) (arity : Nat) : Signature :=
  { s with typeOps := (n, arity) :: s.typeOps }

theorem Signature.extends_addType (s : Signature) (n : QName) (arity : Nat)
    (fresh : s.typeOps.lookup n = none) : s.Extends (s.addType n arity) := by
  constructor
  · intro k a ha
    have hn : k ≠ n := by intro hn; subst k; rw [fresh] at ha; cases ha
    simp [addType, List.lookup_cons, beq_eq_false_iff_ne.mpr hn, ha]
  · exact fun _ _ h => h

def Signature.addConstant (s : Signature) (n : QName) (scheme : HolType) : Signature :=
  { s with constants := (n, scheme) :: s.constants }

theorem Signature.extends_addConstant (s : Signature) (n : QName) (scheme : HolType)
    (fresh : s.constants.lookup n = none) : s.Extends (s.addConstant n scheme) := by
  constructor
  · exact fun _ _ h => h
  · intro k a ha
    have hn : k ≠ n := by intro hn; subst k; rw [fresh] at ha; cases ha
    simp [addConstant, List.lookup_cons, beq_eq_false_iff_ne.mpr hn, ha]

def Signature.WellFormed (s : Signature) : Prop :=
  (s.typeOps.map Prod.fst).Nodup ∧ (s.constants.map Prod.fst).Nodup ∧
    ∀ entry ∈ s.constants, s.validType entry.2 = true

instance (s : Signature) : Decidable s.WellFormed :=
  inferInstanceAs (Decidable ((s.typeOps.map Prod.fst).Nodup ∧
    (s.constants.map Prod.fst).Nodup ∧ ∀ entry ∈ s.constants, s.validType entry.2 = true))

private theorem not_mem_keys {entries : List (QName × α)} {n : QName}
    (h : entries.lookup n = none) : n ∉ entries.map Prod.fst := by
  intro hn
  obtain ⟨entry, he, hn⟩ := List.mem_map.mp hn
  have hf := List.lookup_eq_none_iff.mp h entry he
  simp [hn] at hf

theorem Signature.WellFormed.addType {s : Signature} (h : s.WellFormed)
    (n : QName) (arity : Nat) (fresh : s.typeOps.lookup n = none) :
    (s.addType n arity).WellFormed := by
  refine ⟨?_, h.2.1, ?_⟩
  · exact List.nodup_cons.mpr ⟨not_mem_keys fresh, h.1⟩
  · intro entry he
    exact (s.extends_addType n arity fresh).validType _ (h.2.2 entry he)

theorem Signature.WellFormed.addConstant {s : Signature} (h : s.WellFormed)
    (n : QName) (scheme : HolType) (fresh : s.constants.lookup n = none)
    (valid : s.validType scheme = true) : (s.addConstant n scheme).WellFormed := by
  refine ⟨h.1, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨not_mem_keys fresh, h.2.1⟩
  · intro entry he
    apply (s.extends_addConstant n scheme fresh).validType
    rcases List.mem_cons.mp he with rfl | he
    · exact valid
    · exact h.2.2 entry he

end HotaruKernel
