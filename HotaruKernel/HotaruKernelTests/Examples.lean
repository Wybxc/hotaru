import HotaruKernel.Kernel

namespace HotaruKernel.Examples

def theory : Theory := ⟨{}, []⟩

def types : TypeModel where
  typeVar := fun _ => Nat
  typeOp := fun _ _ => Unit
  var_nonempty := fun _ => ⟨0⟩
  op_nonempty := fun _ _ _ => ⟨()⟩

def polymorphicModel : PolymorphicModel theory.signature where
  typeOp := types.typeOp
  op_nonempty := types.op_nonempty
  constant := fun _ _ h => False.elim (by simp [theory] at h)
  constant_support := by intro _ _ h; simp [theory] at h

noncomputable def model : Model theory.signature := polymorphicModel.atTypes types rfl

theorem models : Models theory polymorphicModel :=
  fun _ _ _ _ h => False.elim (List.not_mem_nil h)

noncomputable def valuation : FreeEnv model :=
  fun a _ => Classical.choice (model.toTypeModel.interp_nonempty a)

def falsehood : Formula theory.signature :=
  .equal (.lam (by decide +kernel) (.bvar .zero))
    (.lam (by decide +kernel) (.equal (.bvar .zero) (.bvar .zero)))

theorem falsehood_not_derivable : ¬ Derivable theory [] falsehood := by
  intro d
  have h := d.sound polymorphicModel models types rfl valuation
    (fun _ hp => False.elim (List.not_mem_nil hp))
  have he := (eval_equal_true _ _ _ _ _).mp h
  have hf := congrFun he false
  simp [Term.eval, BoundEnv.cons] at hf

def x : RawTerm := .fvar "x" .bool
def y : RawTerm := .fvar "y" .bool
def z : RawTerm := .fvar "z" .bool
def identity : RawTerm := .lam .bool (.bvar 0)
def contextFunction : RawTerm := .fvar "h" (.fn .bool .bool)

-- All five public operations participate in this proof, including a hypothesis.
def composed : Except KernelError (Thm theory) := do
  let beta ← Kernel.BETA_CONV theory (.app identity x)
  let abstraction ← Kernel.ABS theory "x" .bool beta
  let argument ← Kernel.ASSUME theory (.equal y z)
  let application ← Kernel.MK_COMB theory abstraction argument
  let context ← Kernel.REFL theory contextFunction
  Kernel.MK_COMB theory context application

def observe (r : Except KernelError (Thm t)) :
    Except KernelError (List RawTerm × RawTerm) :=
  r.map fun th => (th.assumptions.map Term.raw, th.conclusion.raw)

def expected : RawTerm := .equal
  (.app contextFunction (.app (.lam .bool (.app identity (.bvar 0))) y))
  (.app contextFunction (.app identity z))

theorem composed_output : observe composed = .ok ([.equal y z], expected) := by decide +kernel

theorem composed_succeeds : ∃ th, composed = .ok th := by
  have h := composed_output
  cases hc : composed with
  | error e => rw [observe, hc] at h; cases h
  | ok th => exact ⟨th, rfl⟩

theorem composed_sound (th : Thm theory) (h : composed = .ok th) :
    theory.Entails th.assumptions th.conclusion := Kernel.success_sound composed th h

end HotaruKernel.Examples
