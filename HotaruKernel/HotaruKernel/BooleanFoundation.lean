import HotaruKernel.Semantics

namespace HotaruKernel

def truth (s : Signature) : Formula s :=
  let identity : Closed s (.fn .bool .bool) :=
    .lam (by simp [Signature.validType]) (.bvar .zero)
  .equal identity identity

theorem truth_freeVars (s : Signature) : (truth s).freeVars = [] := rfl

def impAntisym (p q : Formula s) : Formula s :=
  .imp (.imp p q) (.imp (.imp q p) (.equal p q))

/-! The Boolean logical axiom schema is explicit. Its interpretation theorem
is proved from Bool, independently of the deductive system and theory axioms. -/
inductive BooleanAxiom (s : Signature) : Formula s → Prop where
  | impAntisym (p q : Formula s) : BooleanAxiom s (HotaruKernel.impAntisym p q)

theorem BooleanAxiom.sound {p : Formula s} (h : BooleanAxiom s p)
    (m : Model s) (f : FreeEnv m) : p.eval m f BoundEnv.nil = true := by
  classical
  cases h with
  | impAntisym p q =>
    change (!(!p.eval m f BoundEnv.nil || q.eval m f BoundEnv.nil) ||
      (!(!q.eval m f BoundEnv.nil || p.eval m f BoundEnv.nil) ||
        decide (p.eval m f BoundEnv.nil = q.eval m f BoundEnv.nil))) = true
    generalize p.eval m f BoundEnv.nil = a
    generalize q.eval m f BoundEnv.nil = b
    cases a <;> cases b <;> simp

end HotaruKernel
