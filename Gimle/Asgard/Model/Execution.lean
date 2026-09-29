import Gimle.Asgard.Model.Driven
import Gimle.Asgard.Simulation.Driven

/-! Optional execution adapters retain compiler-derived syntax and interfaces.
These imports do not belong to the core circuit or semantic modules. -/
namespace Gimle.Asgard.Model
open Polynomial

private def Body.sourceIds (b : Body) : List String :=
  (b.program.inputs ++ b.program.assignments.map Assignment.output).map Port.id

/-- The request contains the SAME compiled observation circuit, with original
source mappings. Binary64 samples are numerical observations, not exact inputs. -/
def PolynomialModel.pointRequest {b : Body} (p : PolynomialModel b)
    (requestId artifactId : String) (points : Array (Array Float)) :
    Simulation.Rational.Request b.runtimePorts.length b.observations.length := {
  circuit := p.outputs.circuit
  inputs := b.runtimePorts
  outputs := b.observations.map Observation.port
  sourceIds := b.sourceIds
  outputSources := b.observations.map Observation.sourceId
  requestId := requestId
  artifactId := artifactId
  settings := .points points
}

private def Body.statePorts (b : Body) (e : Evolution) : Except String (List Port) :=
  e.states.mapM fun binding => do
    let some port := b.program.inputs.find? (·.id == binding.stateId)
      | throw "missing compiled state port"
    return port

/-- Ordered derivatives and exact IC/start come directly from the accepted model.
The Euler step/count are numerical settings, separate from these model data. -/
def ContinuousModel.eulerRequest {b : Body} {e : Evolution} (p : ContinuousModel b e)
    (requestId artifactId : String) (step : Float) (steps : Nat) :
    Except String (Simulation.Rational.Request e.states.length e.states.length) := do
  let inputs ← b.statePorts e
  let outputs ← e.states.mapM fun binding => do
    let some a := b.program.assignments.find? (·.output.id == binding.derivativeId)
      | throw "missing compiled derivative port"
    return {a.output with role := .output}
  return {
    circuit := p.rates.circuit
    inputs := inputs
    outputs := outputs
    sourceIds := b.sourceIds
    outputSources := e.states.map Dynamics.StateBinding.derivativeId
    initialization := some ⟨(List.ofFn p.initials).toArray, e.start, e.axis.id⟩
    requestId := requestId
    artifactId := artifactId
    settings := .euler step steps
  }

/-- Observations have their own interface; display permutations do not change
state coordinates or the field passed to Euler. -/
def ContinuousModel.observationRequest {b : Body} {e : Evolution} (p : ContinuousModel b e)
    (requestId artifactId : String) (points : Array (Array Float)) :
    Except String (Simulation.Rational.Request e.states.length b.observations.length) := do
  return {
    circuit := p.outputs.circuit
    inputs := ← b.statePorts e
    outputs := b.observations.map Observation.port
    sourceIds := b.sourceIds
    outputSources := b.observations.map Observation.sourceId
    requestId := requestId
    artifactId := artifactId
    settings := .points points
  }

/-- Driver ports come from the declaration in `DriverBinding.ports` order, each
derivative port tagged with its driver; the field, derivative ports and exact
initial data are the accepted model's. The samples are the runtime's held
driver, one row per interval, not the declared signal. -/
def DrivenModel.eulerRequest {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (requestId artifactId : String) (step : Float) (steps : Nat)
    (samples : Array (Array ℚ)) :
    Except String (Simulation.Driven.Request (DriverBinding.width ds) e.states.length) := do
  let drivers ← (DriverBinding.ports ds).mapM fun id => do
    let some port := b.program.inputs.find? (·.id == id) | throw "missing driver port"
    return ⟨port, (ds.find? (·.derivativeId == some id)).map DriverBinding.driverId⟩
  let outputs ← e.states.mapM fun binding => do
    let some a := b.program.assignments.find? (·.output.id == binding.derivativeId)
      | throw "missing compiled derivative port"
    return {a.output with role := .output}
  return {
    circuit := p.rates.circuit
    drivers := drivers
    states := ← b.statePorts e
    outputs := outputs
    sourceIds := b.sourceIds
    outputSources := e.states.map Dynamics.StateBinding.derivativeId
    initialization := ⟨(List.ofFn p.initials).toArray, e.start, e.axis.id⟩
    requestId := requestId
    artifactId := artifactId
    step := step
    steps := steps
    samples := samples
  }

end Gimle.Asgard.Model
