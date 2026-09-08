import HotaruKernel.Kernel

namespace HotaruKernel

structure Sequent where
  assumptions : List RawTerm
  conclusion : RawTerm
  deriving Repr, DecidableEq

def Sequent.WellFormed (s : Signature) (q : Sequent) : Prop :=
  (∀ p ∈ q.assumptions, HasType s [] p .bool) ∧ HasType s [] q.conclusion .bool

def Thm.sequent (th : Thm t) : Sequent :=
  ⟨th.assumptions.map Term.raw, th.conclusion.raw⟩

theorem Thm.sequent_wellFormed (th : Thm t) : th.sequent.WellFormed t.signature := by
  refine ⟨?_, th.conclusion.hasType⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.hasType

theorem Kernel.success_wellFormed (operation : Except KernelError (Thm t)) (th : Thm t)
    (_h : operation = .ok th) : th.sequent.WellFormed t.signature := th.sequent_wellFormed

end HotaruKernel
