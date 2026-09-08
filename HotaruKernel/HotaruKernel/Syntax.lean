import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! Locally nameless HOL syntax. Built-in equality is represented directly. -/
namespace HotaruKernel

structure QName where
  theory : String
  name : String
  deriving DecidableEq, Repr

inductive HolType where
  | var : String → HolType
  | bool : HolType
  | fn : HolType → HolType → HolType
  | op : QName → List HolType → HolType
  deriving Repr

mutual
def HolType.decEq : (a b : HolType) → Decidable (a = b)
  | .var n, .var m => decidable_of_iff (n = m) (by simp)
  | .bool, .bool => isTrue rfl
  | .fn a b, .fn c d =>
      letI := HolType.decEq a c
      letI := HolType.decEq b d
      decidable_of_iff (a = c ∧ b = d) (by simp)
  | .op n xs, .op m ys =>
      letI := HolType.listDecEq xs ys
      decidable_of_iff (n = m ∧ xs = ys) (by simp)
  | .var _, .bool | .var _, .fn .. | .var _, .op ..
  | .bool, .var _ | .bool, .fn .. | .bool, .op ..
  | .fn .., .var _ | .fn .., .bool | .fn .., .op ..
  | .op .., .var _ | .op .., .bool | .op .., .fn .. => isFalse (by intro h; cases h)

def HolType.listDecEq : (xs ys : List HolType) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      letI := HolType.decEq x y
      letI := HolType.listDecEq xs ys
      decidable_of_iff (x = y ∧ xs = ys) (by simp)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq HolType := HolType.decEq

abbrev TypeSubst := List (String × HolType)

def HolType.inst (s : TypeSubst) : HolType → HolType
  | .var n => (s.lookup n).getD (.var n)
  | .bool => .bool
  | .fn a b => .fn (a.inst s) (b.inst s)
  | .op n args => .op n (args.attach.map (fun t => t.val.inst s))
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem t.property) (by omega)

structure Signature where
  typeOps : List (QName × Nat) := []
  constants : List (QName × HolType) := []
  deriving DecidableEq, Repr

def Signature.validType (s : Signature) : HolType → Bool
  | .var _ => true
  | .bool => true
  | .fn a b => s.validType a && s.validType b
  | .op n args => s.typeOps.lookup n == some args.length &&
      args.attach.all (fun t => s.validType t.val)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem t.property) (by omega)

abbrev FVar := String × HolType

inductive RawTerm where
  | fvar : String → HolType → RawTerm
  | bvar : Nat → RawTerm
  | const : QName → TypeSubst → RawTerm
  | app : RawTerm → RawTerm → RawTerm
  | lam : HolType → RawTerm → RawTerm
  | equal : RawTerm → RawTerm → RawTerm
  deriving DecidableEq, Repr

inductive BVar : List HolType → HolType → Type where
  | zero {ctx : List HolType} : BVar (a :: ctx) a
  | succ {ctx : List HolType} : BVar ctx a → BVar (b :: ctx) a

def BVar.index {ctx : List HolType} : BVar ctx a → Nat
  | .zero => 0
  | .succ v => v.index + 1

inductive Term (s : Signature) : List HolType → HolType → Type where
  | fvar {ctx : List HolType} (n : String) (a : HolType)
      (valid : s.validType a = true) : Term s ctx a
  | bvar {ctx : List HolType} : BVar ctx a → Term s ctx a
  | const {ctx : List HolType} (n : QName) (scheme : HolType) (inst : TypeSubst)
      (declared : s.constants.lookup n = some scheme)
      (valid : s.validType (scheme.inst inst) = true) : Term s ctx (scheme.inst inst)
  | app {ctx : List HolType} : Term s ctx (.fn a b) → Term s ctx a → Term s ctx b
  | lam {ctx : List HolType} (valid : s.validType a = true) :
      Term s (a :: ctx) b → Term s ctx (.fn a b)
  | equal {ctx : List HolType} : Term s ctx a → Term s ctx a → Term s ctx .bool

variable {ctx dst : List HolType}

abbrev Closed (s : Signature) (a : HolType) := Term s [] a
abbrev Formula (s : Signature) := Closed s .bool

def Term.raw {ctx : List HolType} : Term s ctx a → RawTerm
  | .fvar n a _ => .fvar n a
  | .bvar v => .bvar v.index
  | .const n _ i _ _ => .const n i
  | .app f x => .app f.raw x.raw
  | @Term.lam _ a _ _ _ b => .lam a b.raw
  | .equal l r => .equal l.raw r.raw

def Term.freeVars {ctx : List HolType} : Term s ctx a → List FVar
  | .fvar n a _ => [(n, a)]
  | .bvar _ => []
  | .const .. => []
  | .app f x => f.freeVars ++ x.freeVars
  | .lam _ b => b.freeVars
  | .equal l r => l.freeVars ++ r.freeVars

abbrev Renaming (ctx dst : List HolType) := ∀ {a}, BVar ctx a → BVar dst a

def Renaming.lift (r : Renaming ctx dst) : Renaming (a :: ctx) (a :: dst)
  | _, .zero => .zero
  | _, .succ v => .succ (r v)

def Term.rename {ctx dst : List HolType} (r : Renaming ctx dst) : Term s ctx a → Term s dst a
  | .fvar n a h => .fvar n a h
  | .bvar v => .bvar (r v)
  | .const n t i h v => .const n t i h v
  | .app f x => .app (f.rename r) (x.rename r)
  | .lam h b => .lam h (b.rename r.lift)
  | .equal l t => .equal (l.rename r) (t.rename r)

def Term.weaken (t : Term s ctx a) : Term s (b :: ctx) a := t.rename BVar.succ

abbrev BoundSubst (s : Signature) (ctx dst : List HolType) :=
  ∀ {a}, BVar ctx a → Term s dst a

def BoundSubst.lift (r : BoundSubst s ctx dst) : BoundSubst s (a :: ctx) (a :: dst)
  | _, .zero => .bvar .zero
  | _, .succ v => (r v).weaken

def Term.substBound {ctx dst : List HolType} (r : BoundSubst s ctx dst) :
    Term s ctx a → Term s dst a
  | .fvar n a h => .fvar n a h
  | .bvar v => r v
  | .const n t i h v => .const n t i h v
  | .app f x => .app (f.substBound r) (x.substBound r)
  | .lam h b => .lam h (b.substBound r.lift)
  | .equal l t => .equal (l.substBound r) (t.substBound r)

def BoundSubst.single (x : Term s ctx a) : BoundSubst s (a :: ctx) ctx
  | _, .zero => x
  | _, .succ v => .bvar v

def Term.open (b : Term s (a :: ctx) t) (x : Term s ctx a) : Term s ctx t :=
  b.substBound (BoundSubst.single x)

-- A free substitution is lifted under binders, so replacements cannot be captured.
abbrev FreeSubst (s : Signature) (ctx : List HolType) :=
  (n : String) → (a : HolType) → s.validType a = true → Term s ctx a

def FreeSubst.lift (r : FreeSubst s ctx) : FreeSubst s (a :: ctx) :=
  fun n t h => (r n t h).weaken

def Term.substFree {ctx dst : List HolType} (r : FreeSubst s dst) (q : Renaming ctx dst) :
    Term s ctx a → Term s dst a
  | .fvar n a h => r n a h
  | .bvar v => .bvar (q v)
  | .const n t i h v => .const n t i h v
  | .app f x => .app (f.substFree r q) (x.substFree r q)
  | .lam h b => .lam h (b.substFree r.lift q.lift)
  | .equal l t => .equal (l.substFree r q) (t.substFree r q)

def FreeSubst.close (n : String) (a : HolType) : FreeSubst s (a :: ctx) :=
  fun m b h => if ht : b = a then
    if m = n then ht ▸ Term.bvar BVar.zero else .fvar m b h
  else .fvar m b h

def FreeSubst.single (n : String) (a : HolType) (x : Term s ctx a) : FreeSubst s ctx :=
  fun m b h => if ht : b = a then
    if m = n then ht ▸ x else .fvar m b h
  else .fvar m b h

def Term.replace (t : Term s ctx b) (n : String) (a : HolType)
    (x : Term s ctx a) : Term s ctx b :=
  t.substFree (FreeSubst.single n a x) (fun v => v)

def Term.close (t : Term s ctx b) (n : String) (a : HolType) : Term s (a :: ctx) b :=
  t.substFree (FreeSubst.close n a) BVar.succ

def Term.abstract (t : Term s ctx b) (n : String) (a : HolType)
    (h : s.validType a = true) : Term s ctx (.fn a b) :=
  .lam h (t.close n a)

end HotaruKernel
