import Gimle.Asgard.Model.Declaration
import Gimle.Asgard.Compile.Syntax

namespace Gimle.Asgard.Tests.Declarations
open Polynomial Model

def constant : Body := {
  program := ⟨[], equations% { c := rat(1, 3); }⟩
  observations := [⟨⟨"obs-c", "c", .output⟩, "c"⟩]
}
example : (Declaration.polynomial constant).validate = .ok () := by decide
example : (Declaration.polynomial { constant with observations := [] }).validate = .ok () := by decide

/-- A forward reference is valid metadata, even though the old ordered resolver fails. -/
def forward : Body := {
  program := ⟨[⟨"input-x", "x", .input⟩], equations% { z := y + x; y := x; }⟩
  observations := [⟨⟨"obs-x", "x", .output⟩, "input-x"⟩]
}
example : (Declaration.polynomial forward).validate = .ok () := by decide
example : forward.program.resolve = none := by decide


/-- Input, derivative, state, IC and observation orders are deliberately different.
Axis/state display names coincide; explicit roles and IDs keep them separate. -/
def field : Body := {
  program := ⟨[⟨"state-y", "y", .state⟩, ⟨"param-a", "a", .parameter⟩,
    ⟨"state-x", "x", .state⟩, ⟨"param-unused", "unused", .parameter⟩],
    equations% { dy := -x; dx := a * y; energy := x^2 + y^2; }⟩
  parameters := [⟨"param-unused", 7⟩, ⟨"param-a", 1 / 3⟩]
  observations := [⟨⟨"obs-y", "y", .output⟩, "state-y"⟩,
    ⟨⟨"obs-energy", "E", .output⟩, "energy"⟩]
}
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩]
  initialPorts := [⟨"initial-y", "y0", .initial⟩, ⟨"initial-x", "x0", .initial⟩]
  initialValues := [⟨"initial-x", 1 / 2⟩, ⟨"initial-y", -2⟩]
  axis := ⟨"time-axis", "x"⟩
  evolveAlong := "time-axis"
  start := 2 / 3
}
example : (Declaration.continuous field evolution).validate = .ok () := by decide
example : (evolution.system field).valid = true := by decide
example : (Declaration.continuous field evolution).body.program = field.program := rfl
example : evolution.start = (2 / 3 : ℚ) := rfl

-- Literal AST, precedence and exact rational notation remain inspectable.
example : (poly% rat(1, 3) * x + y^2) =
    NamedExpr.add (.mul (.constant (1 / 3)) (.var "x")) ((NamedExpr.var "y").pow 2) := rfl

-- Arbitrary finite interfaces; no fixed dimension is encoded by the declaration API.
def many (n : Nat) : Body := {
  program := ⟨(List.range n).map (fun i => ⟨s!"input-{i}", s!"x{i}", .input⟩), []⟩
}
example : (Declaration.polynomial (many 17)).validate = .ok () := by decide
example : (Declaration.polynomial (many 0)).validate = .ok () := by decide

-- Declaration validation intentionally does not claim auxiliary schedulability.
example : (Declaration.polynomial {
    program := ⟨[], equations% { x := y; y := x; }⟩ }).validate = .ok () := by decide

-- Missing names identify both the assignment and its unresolved variable.
example : (Declaration.polynomial { program := ⟨[], equations% { z := missing; }⟩ }).validate =
    .error ⟨.unknownReference, "z", "missing"⟩ := by decide
example : (Declaration.continuous { field with program :=
    { field.program with assignments := equations% { dy := x0; dx := y; } } } evolution).validate =
    .error ⟨.unknownReference, "dy", "x0"⟩ := by decide

-- Exact binding coverage includes unused parameters; extra/duplicate values fail.
example : (Declaration.continuous { field with parameters := [] } evolution).validate =
    .error ⟨.missingBinding, "parameters", "param-a"⟩ := by decide
example : (Declaration.continuous { field with parameters :=
    field.parameters ++ [⟨"typo", 1⟩] } evolution).validate =
    .error ⟨.unknownReference, "parameters", "typo"⟩ := by decide
example : (Declaration.continuous { field with parameters :=
    field.parameters ++ [⟨"param-a", 2⟩] } evolution).validate =
    .error ⟨.duplicateBinding, "parameters", "param-a"⟩ := by decide
example : (Declaration.continuous field { evolution with initialValues := [] }).validate =
    .error ⟨.missingBinding, "initialValues", "initial-y"⟩ := by decide
example : (Declaration.continuous field { evolution with initialValues :=
    evolution.initialValues ++ [⟨"initial-y", 0⟩] }).validate =
    .error ⟨.duplicateBinding, "initialValues", "initial-y"⟩ := by decide

-- Binding to a display name or wrong source role is not ID lookup.
example : (Declaration.continuous field { evolution with
    states := [⟨"x", "dx", "initial-x"⟩] }).validate =
    .error ⟨.unknownReference, "states", "x"⟩ := by decide
example : (Declaration.continuous field { evolution with
    states := [⟨"param-a", "dx", "initial-x"⟩] }).validate =
    .error ⟨.unknownReference, "states", "param-a"⟩ := by decide
example : (Declaration.continuous field { evolution with
    states := [⟨"state-x", "state-y", "initial-x"⟩] }).validate =
    .error ⟨.unknownReference, "state-x", "state-y"⟩ := by decide
example : (Declaration.continuous field { evolution with
    states := [⟨"state-x", "dx", "unknown-ic"⟩] }).validate =
    .error ⟨.unknownReference, "state-x", "unknown-ic"⟩ := by decide
example : (Declaration.continuous field { evolution with states := [] }).validate =
    .error ⟨.missingBinding, "states", "state-y"⟩ := by decide
example : (Declaration.continuous field { evolution with states :=
    [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dx", "initial-y"⟩] }).validate =
    .error ⟨.duplicateBinding, "derivatives", "dx"⟩ := by decide
example : (Declaration.continuous field { evolution with states :=
    [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-x"⟩] }).validate =
    .error ⟨.duplicateBinding, "initials", "initial-x"⟩ := by decide
example : (Declaration.continuous field { evolution with evolveAlong := "x" }).validate =
    .error ⟨.wrongAxis, "evolveAlong", "x"⟩ := by decide
example : (Declaration.continuous field { evolution with axis := ⟨"", "t"⟩ }).validate =
    .error ⟨.emptyId, "axis", "t"⟩ := by decide

-- Input/observation names may coincide, but stable interface IDs may not.
example : (Declaration.polynomial { forward with observations :=
    [⟨⟨"input-x", "x", .output⟩, "input-x"⟩] }).validate =
    .error ⟨.duplicateId, "interface", "input-x"⟩ := by decide
example : (Declaration.polynomial { forward with observations :=
    [⟨⟨"obs-1", "x", .output⟩, "input-x"⟩,
     ⟨⟨"obs-2", "x", .output⟩, "y"⟩] }).validate =
    .error ⟨.duplicateName, "observations", "x"⟩ := by decide
example : (Declaration.polynomial { constant with observations :=
    [⟨⟨"obs", "result", .output⟩, "missing"⟩] }).validate =
    .error ⟨.unknownReference, "obs", "missing"⟩ := by decide
example : (Declaration.polynomial { program :=
    ⟨[⟨"p", "x", .input⟩, ⟨"p", "y", .input⟩], []⟩ }).validate =
    .error ⟨.duplicateId, "source", "p"⟩ := by decide
example : (Declaration.polynomial { program :=
    ⟨[⟨"p", "x", .input⟩, ⟨"q", "x", .input⟩], []⟩ }).validate =
    .error ⟨.duplicateName, "source", "x"⟩ := by decide
example : (Declaration.polynomial { program := ⟨[⟨"p", "", .input⟩], []⟩ }).validate =
    .error ⟨.emptyName, "source", "p"⟩ := by decide

-- No suffix inference: a driver named u0 is not an initial value or fixed input.
example : (Declaration.polynomial { program := ⟨[⟨"u", "u0", .driver⟩], []⟩ }).validate =
    .error ⟨.unsupportedRole, "u", "u0"⟩ := by decide
example : (Declaration.polynomial field).validate =
    .error ⟨.unsupportedRole, "state-y", "y"⟩ := by decide
example : (Declaration.polynomial { constant with observations :=
    [⟨⟨"obs", "c", .initial⟩, "c"⟩] }).validate =
    .error ⟨.unsupportedRole, "obs", "c"⟩ := by decide

-- Repeated selection is explicit; orphan IC data must never be silently dropped.
example : (Declaration.polynomial { forward with observations :=
    [⟨⟨"obs-a", "first", .output⟩, "input-x"⟩,
     ⟨⟨"obs-b", "second", .output⟩, "input-x"⟩] }).validate = .ok () := by decide
example : (Declaration.continuous field { evolution with
    initialPorts := evolution.initialPorts ++ [⟨"orphan", "orphan0", .initial⟩]
    initialValues := evolution.initialValues ++ [⟨"orphan", 0⟩] }).validate =
    .error ⟨.missingBinding, "initials", "orphan"⟩ := by decide

#print axioms Declaration.check_source
end Gimle.Asgard.Tests.Declarations
