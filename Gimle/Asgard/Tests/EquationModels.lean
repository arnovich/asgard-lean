import Gimle.Asgard.Examples.EquationModels
import Gimle.Asgard.Simulation.EquationRequests

namespace Gimle.Asgard.Tests.EquationModels
open Examples.EquationModels

/-- Asymmetric values expose accidental output selection or state permutation. -/
example : energy.run ![1, 2] 0 = 10 := by rw [energy_formula]; norm_num
example : oscillator.run ![1, 2] = ![(2 : ℝ), -5] := by
  rw [oscillator_equations]
  norm_num
example : oscillator.run ![1, 2] ≠ ![(-5 : ℝ), 2] := by
  intro h
  have := congrFun h 0
  rw [oscillator_equations] at this
  norm_num at this

example : Simulation.EquationRequests.energy.circuit = energy := rfl
example : Simulation.EquationRequests.oscillator.circuit = oscillator := rfl

example : oscillator.run ![0, 1] 1 ≠ (2 : ℝ) := by
  rw [oscillator_equations]
  norm_num

/-- A changed time-axis binding cannot realize the original problem. -/
example (state : Dynamics.Signal 2) :
    ¬ (Dynamics.close (d := 0) (n := 2) "s" oscillator).Rel problem.time
      (Dynamics.signalAppend noDrivers (fun _ => problem.initial)) state := by
  rw [Dynamics.close_correct]
  rintro ⟨bad, _⟩
  exact (by decide : ("s" : String) ≠ "t") bad

/-- The original oscillator initialization is part of its exact trajectory claim. -/
example (state : Dynamics.Signal 2) (h : Realizes state) :
    state 0 = ![(1 : ℝ), 0] := by
  have initial := ((problem.solves_iff_realizes state).mpr ((realizes_iff state).mp h)).1
  ext i
  have coordinate := congrFun initial i
  fin_cases i <;>
    simpa [problem, model, Dynamics.Linear.RationalProblem.problem] using coordinate

example (state : Dynamics.Signal 2) (h : Realizes state) : state 0 ≠ ![(0 : ℝ), 0] := by
  have initial := ((problem.solves_iff_realizes state).mpr ((realizes_iff state).mp h)).1
  intro wrong
  have hx := congrFun initial 0
  norm_num [problem, model, Dynamics.Linear.RationalProblem.problem, wrong] at hx

#print axioms energy_formula
#print axioms realizes_iff
#print axioms exists_realization
#print axioms unique_realization
end Gimle.Asgard.Tests.EquationModels
