import Gimle.Asgard.Examples.ThreeState
import Gimle.Asgard.Model.Execution

/-! Optional numerical handoff for the shared three-state research model.

Separate from `Examples/ThreeState.lean` on purpose: this module reaches the
Python process client, which is not required to use or prove properties of
the model's mathematical definitions.

Requests reuse the compiled circuits; no second translation happens. The step
1/8 is a power of two and exact in binary64, so it is not itself a rounding
source. Worker output is numerical evidence and never a theorem. -/
namespace Gimle.Asgard.Examples.ThreeState
open Polynomial Model


/-- 33 rows from t=2 to t=6 inclusive: the response includes the initial row and
2 + 32*(1/8) = 6. Exact initial state, start and axis come from the model. -/
def eulerRequest : Simulation.Rational.Request 3 3 :=
  (model.eulerRequest "three-state-euler" "compiled-three-state-field" 0.125 32).toOption.get
    (by decide +kernel)

/-- Evaluate returned rows through the same compiled observation circuit, so V
is never retyped downstream. -/
def observationRequest (rows : Array (Array Float)) :
    Except String (Simulation.Rational.Request 3 4) :=
  model.observationRequest "three-state-observations" "compiled-three-state-observations" rows

/-- One concrete observation request, used to check the interface below. -/
def initialRowRequest : Simulation.Rational.Request 3 4 :=
  (observationRequest #[#[1, 2, -1]]).toOption.get (by decide +kernel)

example : eulerRequest.circuit = model.rates.circuit := rfl
example : eulerRequest.outputSources = ["dx", "dy", "dz"] := by decide +kernel
example : initialRowRequest.circuit = model.outputs.circuit := rfl
example : initialRowRequest.outputSources = ["state-z", "state-x", "state-y", "V"] := by
  decide +kernel

end Gimle.Asgard.Examples.ThreeState
