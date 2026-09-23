import Gimle.Asgard.Model.Continuous
import Gimle.Asgard.Simulation.Rational

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

end Gimle.Asgard.Model
