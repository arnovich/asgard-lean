import Gimle.Asgard.Dynamics
import Gimle.Asgard.Compile.Syntax
import Gimle.Asgard.Examples.Oscillator

/-! The oscillator now has generated integrator feedback, with initial-condition
ports x0/y0 and a named real time axis. Its equations are
  x′(t) = y(t), y′(t) = −x(t) − 2y(t), x(0)=x0, y(0)=y0.
Both derivatives and the initial values are properties of the actual closed
circuit. This example reuses the existing explicit solution; general linear
existence and uniqueness belong to the subsequent ODE milestone. -/
namespace Gimle.Asgard.Examples.Feedback
open Polynomial Dynamics

def noDrivers : Signal 0 := fun _ i => Fin.elim0 i

abbrev oscillator : System := {
  program := {
    inputs := [⟨"state-x", "x", .state⟩, ⟨"state-y", "y", .state⟩]
    assignments := equations% {
      dx := y;
      dy := -x - 2 * y;
    }
  }
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩]
  externalIds := []
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-y", "y0", .initial⟩]
  axis := ⟨"physical-time", "t"⟩
  evolveAlong := "physical-time"
}

def prepared : Prepared oscillator := oscillator.prepare.get (by decide)

/-- Inspect this value: it contains initial routing and a trace around an
integrator bank, rather than only the derivative computation. -/
def circuit : Dynamics.Circuit 2 2 := prepared.circuit

/-- The independent named equations and generated feedback have exactly the
same trajectories for the same time axis, initial values and state ordering. -/
theorem source_iff_feedback (time : TimeDomain) (initial : Point 2) (state : Signal 2) :
    oscillator.Solves time noDrivers initial state ↔
      circuit.Rel time (fun _ => initial) state := by
  have h := prepared.solves_iff_circuit time noDrivers initial state
  have hi : @signalAppend 0 2 noDrivers (fun _ => initial) =
      (fun _ => initial) := by
    funext t i
    simp [signalAppend, pointAppend]
  change oscillator.Solves time _ initial state ↔ circuit.Rel time _ state at h
  rwa [hi] at h

/-- Both generated derivative outputs agree with the written equations. -/
theorem field_equations (x : Point 2) : prepared.field.run x = ![x 1, -x 0 - 2*x 1] := by
  have es : prepared.expressions =
      ([Expr.var 1, .add (.neg (.var 0)) (.neg (.mul (.constant 2) (.var 1)))] : List (Expr 2)) := by decide
  have inputs : prepared.inputRoute = (fun i => i) := by decide +kernel
  have outputs : prepared.outputRoute = (fun i => i) := by decide +kernel
  simp only [Prepared.field, Gimle.Asgard.Circuit.run, Polynomial.route_correct,
    compileList, compileOutputs_correct, inputs, outputs]
  funext i
  fin_cases i <;> simp [es, Expr.eval, sub_eq_add_neg] <;> rfl

/-- This states the two ODE equations and initial conditions of the generated
closed circuit on the explicit forward half-line. -/
theorem circuit_equations (time : TimeDomain) (initial : Point 2) (state : Signal 2) :
    circuit.Rel time (fun _ => initial) state ↔
      "physical-time" = time.axis ∧ state time.start = initial ∧
      ∀ t ∈ time.domain,
        HasDerivWithinAt (fun t => state t 0) (state t 1) time.domain t ∧
        HasDerivWithinAt (fun t => state t 1) (-state t 0 - 2*state t 1) time.domain t := by
  have h := prepared.circuit_correct time noDrivers initial state
  have hi : @signalAppend 0 2 noDrivers (fun _ => initial) =
      (fun _ => initial) := by
    funext t i
    simp [signalAppend, pointAppend]
  have initialRoute : prepared.initialRoute = (fun i => i) := by decide +kernel
  change circuit.Rel time _ state ↔ "physical-time" = time.axis ∧
    state time.start = (fun i => initial (prepared.initialRoute i)) ∧
    ∀ t ∈ time.domain, ∀ i : Fin 2, HasDerivWithinAt (fun t => state t i)
      (prepared.field.run (@pointAppend 0 2 (fun i => Fin.elim0 i) (state t)) i) time.domain t at h
  rw [hi, initialRoute] at h
  have hp (x : Point 2) : @pointAppend 0 2 (fun i => Fin.elim0 i) x = x := by
    funext i
    simp [pointAppend]
  simpa only [hp, field_equations, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- A nonempty example: the established explicit oscillator trajectory satisfies
both integrators and both initial-value wires of the generated feedback circuit. -/
theorem explicit_solution (x0 y0 : ℝ) :
    circuit.Rel ⟨"physical-time", 0⟩ (fun _ => ![x0, y0])
      (fun t => ![Oscillator.position x0 y0 t, Oscillator.velocity x0 y0 t]) := by
  rw [circuit_equations]
  refine ⟨rfl, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [Oscillator.position, Oscillator.velocity]
  · intro t _
    have h := (Oscillator.solvesEquations _ _).mp (Oscillator.explicitSolution x0 y0) t
    exact ⟨h.1.hasDerivWithinAt, h.2.hasDerivWithinAt⟩

#print axioms source_iff_feedback
#print axioms explicit_solution

end Gimle.Asgard.Examples.Feedback
