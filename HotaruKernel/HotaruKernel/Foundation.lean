import HotaruKernel.Infinity
import HotaruKernel.TheoryExtension

namespace HotaruKernel.Foundation

def indName : QName := ⟨"min", "ind"⟩
def selectName : QName := ⟨"min", "@"⟩
def alpha : HolType := .var "a"
def beta : HolType := .var "b"
def ind : HolType := .op indName []
def selectType : HolType := .fn (.fn alpha .bool) alpha
def signature : Signature := ⟨[(indName, 0)], [(selectName, selectType)]⟩

theorem wellFormed : signature.WellFormed := by decide +kernel
theorem alpha_valid : signature.validType alpha = true := by decide +kernel
theorem beta_valid : signature.validType beta = true := by decide +kernel
theorem ind_valid : signature.validType ind = true := by decide +kernel
theorem function_valid : signature.validType (.fn alpha beta) = true := by decide +kernel
theorem predicate_valid : signature.validType (.fn alpha .bool) = true := by decide +kernel

def select {ctx : List HolType} : Term signature ctx selectType :=
  .const selectName selectType [] (by decide +kernel) (by decide +kernel)

def etaAxiom : Formula signature :=
  Term.forallT (.lam function_valid
    (.equal (.lam alpha_valid (.app (.bvar (.succ .zero)) (.bvar .zero)))
      (.bvar .zero))) function_valid

def selectAxiom : Formula signature :=
  Term.forallT (.lam predicate_valid (Term.forallT (.lam alpha_valid
    (.imp (.app (.bvar (.succ .zero)) (.bvar .zero))
      (.app (.bvar (.succ .zero)) (.app select (.bvar (.succ .zero)))))) alpha_valid))
    predicate_valid

def infinityAxiom : Formula signature := Term.infiniteT signature [] ind ind_valid

def boolCasesAxiom : Formula signature :=
  let hb : signature.validType .bool = true := by decide +kernel
  Term.forallT (.lam hb (.imp (Term.equal (.bvar .zero) .trueT).notT
    (.equal (.bvar .zero) .falseT))) hb

def theory : Theory := ⟨signature, [etaAxiom, selectAxiom, infinityAxiom, boolCasesAxiom], .local⟩

def eta : Thm theory := ⟨[], etaAxiom, .axiom _ (List.mem_cons_self ..), theory.origin⟩
def selection : Thm theory := ⟨[], selectAxiom,
  .axiom _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), theory.origin⟩
def infinity : Thm theory := ⟨[], infinityAxiom,
  .axiom _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))), theory.origin⟩
def boolCases : Thm theory := ⟨[], boolCasesAxiom,
  .axiom _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), theory.origin⟩

theorem eta_valid (m : Model signature) (f : FreeEnv m) :
    etaAxiom.eval m f BoundEnv.nil = true := by
  apply (Term.eval_forallT _ _ _ _ _).mpr
  intro g
  apply (eval_equal_true _ _ _ _ _).mpr
  rfl

theorem boolCases_valid (m : Model signature) (f : FreeEnv m) :
    boolCasesAxiom.eval m f BoundEnv.nil = true := by
  apply (Term.eval_forallT _ _ _ _ _).mpr
  intro b
  change ((!((Term.equal (.bvar .zero) .trueT).notT.eval m f
    (BoundEnv.cons (a := .bool) b BoundEnv.nil))) ||
    (Term.equal (.bvar .zero) .falseT).eval m f
      (BoundEnv.cons (a := .bool) b BoundEnv.nil)) = true
  rw [Term.eval_notT]
  simp only [Term.eval, BoundEnv.cons]
  rw [Term.eval_trueT m f (BoundEnv.cons (a := .bool) b BoundEnv.nil),
    Term.eval_falseT m f (BoundEnv.cons (a := .bool) b BoundEnv.nil)]
  cases b <;> simp

end HotaruKernel.Foundation
