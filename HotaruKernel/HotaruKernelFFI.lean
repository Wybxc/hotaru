import HotaruKernel
import Lean

/-! JSON transport and exports. No foreign implementation replaces kernel code. -/
namespace HotaruKernel
open Lean

deriving instance ToJson, FromJson for QName
deriving instance ToJson, FromJson for HolType
deriving instance ToJson, FromJson for RawTerm
deriving instance ToJson, FromJson for Execution.Inference
deriving instance ToJson, FromJson for Execution.Command
deriving instance ToJson for KernelError

namespace FFI

structure Response where
  state : Execution.State
  success : Bool
  json : String

def errorJson (kind : String) (detail : Json) : String :=
  (Json.mkObj [("ok", toJson false), ("kind", toJson kind), ("error", detail)]).compress

def applyCommands (s : Execution.State) (input : String) : Except String Execution.State :=
  match Json.parse input with
  | .error e => .error (errorJson "json" (toJson e))
  | .ok json =>
    match (fromJson? json : Except String (List Execution.Command)) with
    | .error e => .error (errorJson "command" (toJson e))
    | .ok commands =>
      match Execution.run s commands with
      | .error e => .error (errorJson "kernel" (toJson e))
      | .ok result => .ok result.state

@[export hotaru_lean_new]
def newState (_ : Unit) : Execution.State := Execution.initial

@[export hotaru_lean_apply]
def apply (s : Execution.State) (input : String) : Response :=
  match applyCommands s input with
  | .error e => ⟨s, false, e⟩
  | .ok next => ⟨next, true, (Json.mkObj [
      ("ok", toJson true), ("theoremCount", toJson next.theorems.length)]).compress⟩

@[export hotaru_lean_response_state]
def responseState (r : Response) : Execution.State := r.state

@[export hotaru_lean_response_success]
def responseSuccess (r : Response) : Bool := r.success

@[export hotaru_lean_response_json]
def responseJson (r : Response) : String := r.json

@[export hotaru_lean_theorem]
def theoremJson (s : Execution.State) (index : UInt64) : Response :=
  match s.get index.toNat with
  | .error e => ⟨s, false, errorJson "kernel" (toJson e)⟩
  | .ok th => ⟨s, true, (Json.mkObj [
      ("ok", toJson true),
      ("assumptions", toJson (th.assumptions.map Term.raw)),
      ("conclusion", toJson th.conclusion.raw)]).compress⟩

theorem applyCommands_spec (s next : Execution.State) (input : String)
    (h : applyCommands s input = .ok next) :
    ∃ (json : Json) (commands : List Execution.Command) (result : Execution.Result s commands),
      Json.parse input = .ok json ∧ fromJson? json = .ok commands ∧
      Execution.run s commands = .ok result ∧ result.state = next := by
  cases hj : Json.parse input with
  | error e => simp [applyCommands, hj] at h
  | ok json =>
    cases hc : (fromJson? json : Except String (List Execution.Command)) with
    | error e => simp [applyCommands, hj, hc] at h
    | ok commands =>
      cases hr : Execution.run s commands with
      | error e => simp [applyCommands, hj, hc, hr] at h
      | ok result =>
        simp only [applyCommands, hj, hc, hr, Except.ok.injEq] at h
        exact ⟨json, commands, result, rfl, hc, hr, h⟩

theorem applyCommands_extends (s next : Execution.State) (input : String)
    (h : applyCommands s input = .ok next) : s.theory.Extends next.theory := by
  obtain ⟨_, _, result, _, _, _, rfl⟩ := applyCommands_spec s next input h
  exact result.extension

theorem apply_failure (s : Execution.State) (input error : String)
    (h : applyCommands s input = .error error) : (apply s input).state = s := by
  simp [apply, h]

theorem applyCommands_sound (s next : Execution.State) (input : String)
    (_h : applyCommands s input = .ok next) (th : Thm next.theory)
    (_mem : th ∈ next.theorems) : next.theory.Entails th.assumptions th.conclusion :=
  th.sound

end FFI
end HotaruKernel
