module

public import Gimle.Asgard.Examples.ThreeState
-- `decide` reads numerals that `toString` prints; core does not expose them.
import all Init.Data.Repr
import all Init.Data.Int.Repr

/-! Coverage for the coupled three-state model.

The model itself is in `Examples/ThreeState.lean`. These checks establish that
its deliberate order mismatches, shared forward auxiliaries, unused parameter
and reused observation display names are accepted for the stated reasons, and
that neighbouring invalid bindings are rejected rather than silently repaired. -/

@[expose] public section

namespace Gimle.Asgard.Tests.ThreeState
open _root_.Gimle.Asgard.Polynomial Model Examples.ThreeState

/-! ## Nothing is silently reordered -/

/-- Reversing every declared list leaves the compiled field, observations and
initial data identical, because every binding is by stable ID. The `abbrev`s
keep the state and observation counts reducible to numerals. -/
abbrev permuted : Body := { body (1 / 3) (1 / 2) 2 with
  program := { (body (1 / 3) (1 / 2) 2).program with
    inputs := (body (1 / 3) (1 / 2) 2).program.inputs.reverse
    assignments := (body (1 / 3) (1 / 2) 2).program.assignments.reverse }
  parameters := (body (1 / 3) (1 / 2) 2).parameters.reverse }
abbrev permutedEvolution : Evolution := { evolution with
  initialPorts := evolution.initialPorts.reverse
  initialValues := evolution.initialValues.reverse }
def permutedModel : ContinuousModel permuted permutedEvolution :=
  (compileContinuous permuted permutedEvolution).toOption.get (by decide +kernel)

example : permutedModel.rates.expressions = model.rates.expressions := by decide +kernel
example : permutedModel.outputs.expressions = model.outputs.expressions := by decide +kernel
example : permutedModel.initials = model.initials := by decide +kernel

/-- Reordering only the observation interface permutes outputs and leaves the
state feedback alone: a display choice is not a change of coordinates. -/
def reordered : Body := { body (1 / 3) (1 / 2) 2 with
  observations := (body (1 / 3) (1 / 2) 2).observations.reverse }
def reorderedModel : ContinuousModel reordered evolution :=
  (compileContinuous reordered evolution).toOption.get (by decide +kernel)

example : reorderedModel.rates.expressions = model.rates.expressions := by decide +kernel
example : reorderedModel.outputs.expressions =
    fun i => model.outputs.expressions i.rev := by decide +kernel

/-! ## Shared, forward and unused declarations -/

-- sqx/sqy/sqz are read by both V and dissipation and declared after both uses.
example : (compileContinuous (body (1 / 3) (1 / 2) 2) evolution).isOk = true := by decide +kernel

-- An auxiliary cycle is rejected even though no observation selects it.
example : (compileContinuous { body (1 / 3) (1 / 2) 2 with program := { (body (1 / 3) (1 / 2) 2).program with
    assignments := (body (1 / 3) (1 / 2) 2).program.assignments ++ equations% { p := q; q := p; } } }
    evolution).isOk = false := by decide +kernel

-- State feedback is not an auxiliary cycle: the states are inputs to the RHS.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) evolution).validate = .ok () := by decide

-- The unused parameter must still be bound exactly once.
example : (Declaration.continuous { body (1 / 3) (1 / 2) 2 with parameters :=
    [⟨"param-a", 1 / 3⟩, ⟨"param-b", 1 / 2⟩, ⟨"param-c", 2⟩] } evolution).validate =
    .error ⟨.missingBinding, "parameters", "param-unused"⟩ := by decide
example : (Declaration.continuous { body (1 / 3) (1 / 2) 2 with parameters :=
    (body (1 / 3) (1 / 2) 2).parameters ++ [⟨"param-unused", 9⟩] } evolution).validate =
    .error ⟨.duplicateBinding, "parameters", "param-unused"⟩ := by decide

/-! ## Observation identities -/

-- obs-z/obs-x/obs-y reuse the state display names z/x/y with distinct IDs.
example : (body (1 / 3) (1 / 2) 2).observations.map (fun o => o.port.name) = ["z", "x", "y", "V"] := by decide
example : (body (1 / 3) (1 / 2) 2).observations.map Observation.sourceId =
    ["state-z", "state-x", "state-y", "V"] := by decide

-- Reusing a display name within the observation interface is still rejected.
example : (Declaration.continuous { body (1 / 3) (1 / 2) 2 with observations :=
    (body (1 / 3) (1 / 2) 2).observations ++ [⟨⟨"obs-dup", "V", .output⟩, "state-x"⟩] } evolution).validate =
    .error ⟨.duplicateName, "observations", "V"⟩ := by decide

-- An observation port may not reuse a source ID.
example : (Declaration.continuous { body (1 / 3) (1 / 2) 2 with observations :=
    (body (1 / 3) (1 / 2) 2).observations ++ [⟨⟨"state-x", "w", .output⟩, "state-x"⟩] } evolution).validate =
    .error ⟨.duplicateId, "interface", "state-x"⟩ := by decide

-- Selecting a missing source names both the observation and the reference.
example : (Declaration.continuous { body (1 / 3) (1 / 2) 2 with observations :=
    (body (1 / 3) (1 / 2) 2).observations ++ [⟨⟨"obs-w", "w", .output⟩, "missing"⟩] } evolution).validate =
    .error ⟨.unknownReference, "obs-w", "missing"⟩ := by decide

/-! ## Rejection of invalid state, initial and axis bindings -/

-- Binding by display name rather than by stable ID is not a lookup.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    states := [⟨"x", "dx", "initial-x"⟩] }).validate =
    .error ⟨.unknownReference, "states", "x"⟩ := by decide

-- A parameter is not a state.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    states := [⟨"param-a", "dx", "initial-x"⟩] }).validate =
    .error ⟨.unknownReference, "states", "param-a"⟩ := by decide

-- Two states may not share a derivative or an initial port.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dx", "initial-y"⟩,
      ⟨"state-z", "dz", "initial-z"⟩] }).validate =
    .error ⟨.duplicateBinding, "derivatives", "dx"⟩ := by decide
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-x"⟩,
      ⟨"state-z", "dz", "initial-z"⟩] }).validate =
    .error ⟨.duplicateBinding, "initials", "initial-x"⟩ := by decide

-- Dropping a state leaves its declared input unbound.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩] }).validate =
    .error ⟨.missingBinding, "states", "state-z"⟩ := by decide

-- Every initial port needs exactly one value, and orphan data is not dropped.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    initialValues := [⟨"initial-y", 2⟩, ⟨"initial-x", 1⟩] }).validate =
    .error ⟨.missingBinding, "initialValues", "initial-z"⟩ := by decide
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with
    initialPorts := evolution.initialPorts ++ [⟨"orphan", "w0", .initial⟩]
    initialValues := evolution.initialValues ++ [⟨"orphan", 0⟩] }).validate =
    .error ⟨.missingBinding, "initials", "orphan"⟩ := by decide

-- The axis is its own namespace and is checked against evolveAlong.
example : (Declaration.continuous (body (1 / 3) (1 / 2) 2) { evolution with evolveAlong := "t" }).validate =
    .error ⟨.wrongAxis, "evolveAlong", "t"⟩ := by decide

/-! ## The parameterisation and the viewer

`body` is parameterised so downstream proofs can instantiate other exact
triples. Compilation is checked per instantiation, not generically. -/

example : (compileContinuous (body 1 1 1) evolution).isOk = true := by decide +kernel
example : (compileContinuous (body 0 0 0) evolution).isOk = true := by decide +kernel

-- Changing a coefficient changes the compiled field and nothing else.
example : ((compileContinuous (body 1 (1 / 2) 2) evolution).toOption.get
    (by decide +kernel)).initials = model.initials := by decide +kernel
example : ¬ ((compileContinuous (body 1 (1 / 2) 2) evolution).toOption.get
    (by decide +kernel)).rates.expressions = model.rates.expressions := by decide +kernel

-- The viewer entry point is checked, not merely rendered: a `#html` command
-- displays a layout failure as a paragraph and cannot fail `lake build`.
example : overview.isOk = true := by decide +kernel

-- V is reachable at its own observation index.
example : model.outputs.circuit.run model.initial energyIndex = 6 := energy_at_initial

/-! ## The exact data downstream proofs depends on -/

example : evolution.start = (2 : ℚ) := rfl
example : model.initials = ![1, 2, -1] := by decide +kernel
example : List.ofFn evolution.stateIds = ["state-x", "state-y", "state-z"] := by decide

end Gimle.Asgard.Tests.ThreeState
