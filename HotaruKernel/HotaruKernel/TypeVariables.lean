import HotaruKernel.TypeInstantiation

namespace HotaruKernel

mutual
def HolType.vars : HolType → List String
  | .var n => [n]
  | .bool => []
  | .fn a b => a.vars ++ b.vars
  | .op _ args => HolType.varsArgs args

def HolType.varsArgs : List HolType → List String
  | [] => []
  | a :: args => a.vars ++ HolType.varsArgs args
end

theorem HolType.inst_injective_on_vars (a : HolType) (i j : TypeSubst) :
    a.inst i = a.inst j → ∀ n ∈ a.vars, (HolType.var n).inst i = (HolType.var n).inst j := by
  induction a using HolType.rec
    (motive_2 := fun args => HolType.instArgs i args = HolType.instArgs j args →
      ∀ n ∈ HolType.varsArgs args, (HolType.var n).inst i = (HolType.var n).inst j) with
  | var k =>
    intro h n hn
    have hn' : n = k := by simpa [vars] using hn
    subst n
    exact h
  | bool => intro _ n hn; cases hn
  | fn a b ha hb =>
    intro h n hn
    obtain ⟨h₁, h₂⟩ := HolType.fn.inj h
    rcases List.mem_append.mp hn with hn | hn
    · exact ha h₁ n hn
    · exact hb h₂ n hn
  | op n args ih =>
    intro h
    exact ih (HolType.op.inj h).2
  | nil h n hn => cases hn
  | cons a args ha ih h n hn =>
    obtain ⟨h₁, h₂⟩ := List.cons.inj h
    rcases List.mem_append.mp hn with hn | hn
    · exact ha h₁ n hn
    · exact ih h₂ n hn

theorem TypeModel.interp_congr_vars (m n : TypeModel) (hop : m.typeOp = n.typeOp)
    (a : HolType) :
    (∀ k ∈ a.vars, m.typeVar k = n.typeVar k) → m.interp a = n.interp a := by
  induction a using HolType.rec
    (motive_2 := fun args => (∀ k ∈ HolType.varsArgs args, m.typeVar k = n.typeVar k) →
      args.map m.interp = args.map n.interp) with
  | var k => exact fun h => h k (List.mem_cons_self ..)
  | bool => exact fun _ => rfl
  | fn a b ha hb =>
    intro h
    have h₁ := ha (fun k hk => h k (List.mem_append_left _ hk))
    have h₂ := hb (fun k hk => h k (List.mem_append_right _ hk))
    change (m.interp a → m.interp b) = (n.interp a → n.interp b)
    rw [h₁, h₂]
  | op name args ih =>
    intro h
    rw [interp_op, interp_op, hop, ih h]
  | nil h => rfl
  | cons a args ha ih h =>
    have h₁ := ha (fun k hk => h k (List.mem_append_left _ hk))
    have h₂ := ih (fun k hk => h k (List.mem_append_right _ hk))
    exact congrArg₂ List.cons h₁ h₂

end HotaruKernel
