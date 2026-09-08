import HotaruKernel.OperatorTransport

namespace HotaruKernel

def assignedType : List String → List Type → String → Type
  | name :: names, A :: args, k => if k = name then A else assignedType names args k
  | _, _, _ => Unit

theorem assignedType_nonempty (names : List String) (args : List Type)
    (hne : ∀ A ∈ args, Nonempty A) (k : String) : Nonempty (assignedType names args k) := by
  induction names generalizing args with
  | nil => exact ⟨()⟩
  | cons name names ih =>
    cases args with
    | nil => exact ⟨()⟩
    | cons A args =>
      unfold assignedType
      split
      · exact hne A (List.mem_cons_self ..)
      · exact ih args (fun B hb => hne B (List.mem_cons_of_mem _ hb))

theorem assignedType_map (names : List String) (v : String → Type)
    (k : String) (hk : k ∈ names) : assignedType names (names.map v) k = v k := by
  induction names with
  | nil => cases hk
  | cons name names ih =>
    simp only [List.map_cons, assignedType]
    split
    · rename_i he
      exact congrArg v he.symm
    · rename_i he
      exact ih ((List.mem_cons.mp hk).resolve_left he)

def PolymorphicModel.parameterModel (p : PolymorphicModel s)
    (names : List String) (args : List Type) (hne : ∀ A ∈ args, Nonempty A) : TypeModel where
  typeVar := assignedType names args
  typeOp := p.typeOp
  var_nonempty := assignedType_nonempty names args hne
  op_nonempty := p.op_nonempty

theorem TypeModel.parameters_nonempty (m : TypeModel) (names : List String) :
    ∀ A ∈ names.map m.typeVar, Nonempty A := by
  intro A ha
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp ha
  exact m.var_nonempty name

theorem PolymorphicModel.parameterModel_var (p : PolymorphicModel s)
    (names : List String) (m : TypeModel) (k : String) (hk : k ∈ names) :
    (p.parameterModel names (names.map m.typeVar) (m.parameters_nonempty names)).typeVar k =
      m.typeVar k := assignedType_map names m.typeVar k hk

end HotaruKernel
