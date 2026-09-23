import Gimle.Asgard.Examples.EquationModels
import Gimle.Asgard.Simulation.Protocol

/-! Optional numerical requests for the exact equation models.
Euler executes their vector field; its arrays are not continuous realizations. -/
namespace Gimle.Asgard.Simulation.EquationRequests
open Examples

def energy : Request 2 1 where
  circuit := EquationModels.energy
  inputs := PolynomialCompiler.energyProgram.inputs
  outputs := [EquationModels.energyOutput]
  requestId := "compiled-energy-points"
  artifactId := "lean-equations-energy"
  settings := .points #[#[0, 0], #[1, 0], #[1, 1], #[1, 2]]

/-- Numerical conversion is explicit. These fixed initial/start values are 0/1;
this helper makes no general exact-real-to-binary64 claim. -/
private def toFloat (q : ℚ) : Float :=
  (if q.num < 0 then -q.num.natAbs.toFloat else q.num.natAbs.toFloat) / q.den.toFloat

def oscillator : Request 2 2 where
  circuit := EquationModels.oscillator
  inputs := PolynomialCompiler.oscillatorProgram.inputs
  outputs := PolynomialCompiler.oscillatorProgram.assignments.map Polynomial.Assignment.output
  requestId := "compiled-damped-oscillator"
  artifactId := "lean-equations-damped-oscillator"
  settings := .euler (List.ofFn (fun i => toFloat (EquationModels.model.initial i))).toArray
    (toFloat EquationModels.model.start) 0.125 32

/-- Asymmetric point evaluation independently detects lost damping and swapped derivatives. -/
def oscillatorPoint : Request 2 2 :=
  {oscillator with requestId := "compiled-damped-rhs", settings := .points #[#[1, 2]]}

/-- A separate numerical experiment, explicitly with different initial data. -/
def oscillatorStep : Request 2 2 :=
  {oscillator with requestId := "compiled-damped-step", settings := .euler #[1, 2] 0 0.125 1}

end Gimle.Asgard.Simulation.EquationRequests
