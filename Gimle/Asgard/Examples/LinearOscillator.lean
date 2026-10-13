import Gimle.Asgard.Dynamics.Linear
import Gimle.Asgard.Examples.Oscillator

/-! The autonomous oscillator is an exact matrix initial-value problem. Its
compiled feedback circuit has the known explicit trajectory, shifted to the
problem's starting time. Uniqueness concerns the forward domain only. -/
namespace Gimle.Asgard.Examples.LinearOscillator
open Dynamics

/-- The same ordered state names accompany the matrix, initial point and output. -/
def names : Fin 2 → String := !["x", "y"]

/-- x′ = y and y′ = −x − 2y, in ordered coordinates [x,y]. -/
def matrix : Linear.Matrix 2 := ![![0, 1], ![-1, -2]]

def problem (start x0 y0 : ℝ) : Linear.Problem 2 := {
  names := names
  matrix := matrix
  initial := ![x0, y0]
  time := ⟨"t", start⟩
}

/-- The previous explicit trajectory, translated to the specified initial time. -/
noncomputable def explicitState (start x0 y0 : ℝ) : Signal 2 :=
  fun t => ![Oscillator.position x0 y0 (t - start), Oscillator.velocity x0 y0 (t - start)]

@[simp] theorem matrix_equations (x : Point 2) :
    matrix.eval x = ![x 1, -x 0 - 2*x 1] := by
  funext i
  fin_cases i
  · simp [Linear.Matrix.eval, matrix, Fin.sum_univ_two]
  · simp [Linear.Matrix.eval, matrix, Fin.sum_univ_two]
    ring

/-- The generated matrix field preserves the established oscillator vector field. -/
theorem field_eq (x : Point 2) : matrix.field.run x = Oscillator.vectorField.run x := by
  calc
    matrix.field.run x = ![x 1, -x 0 - 2*x 1] := by simp
    _ = Oscillator.vectorField.run ![x 0, x 1] := (Oscillator.vectorFieldEquations _ _).symm
    _ = Oscillator.vectorField.run x := by
      congr 1
      ext i
      fin_cases i <;> rfl

/-- Both derivatives and the initial conditions hold after shifting time. -/
theorem explicit_solves (start x0 y0 : ℝ) :
    (problem start x0 y0).Solves (explicitState start x0 y0) := by
  constructor
  · ext i
    fin_cases i <;> simp [explicitState, problem, Oscillator.position, Oscillator.velocity]
  · intro t _ i
    have old := (Oscillator.solvesEquations _ _).mp
      (Oscillator.explicitSolution x0 y0) (t - start)
    have shiftedX := old.1.comp t ((hasDerivAt_id t).sub_const start)
    have shiftedY := old.2.comp t ((hasDerivAt_id t).sub_const start)
    fin_cases i
    · convert! shiftedX.hasDerivWithinAt (s := (problem start x0 y0).time.domain) using 1
      simp [problem, explicitState, matrix_equations]
    · convert! shiftedY.hasDerivWithinAt (s := (problem start x0 y0).time.domain) using 1
      simp [problem, explicitState, matrix_equations]

/-- This is a solution of the actual compiled integrator feedback circuit. -/
theorem explicit_realizes (start x0 y0 : ℝ) :
    (problem start x0 y0).Realizes (explicitState start x0 y0) :=
  ((problem start x0 y0).solves_iff_realizes _).mp (explicit_solves start x0 y0)

/-- Every accepted target trajectory agrees with the established explicit formula
on the entire forward domain. No assertion is made about earlier signal values. -/
theorem realization_eq_explicit (start x0 y0 : ℝ) (state : Signal 2)
    (realized : (problem start x0 y0).Realizes state) (t : ℝ) (ht : start ≤ t) :
    state t = ![Oscillator.position x0 y0 (t - start), Oscillator.velocity x0 y0 (t - start)] :=
  (problem start x0 y0).unique_realization realized (explicit_realizes start x0 y0)
    (show t ∈ (problem start x0 y0).time.domain from ht)

#print axioms field_eq
#print axioms explicit_solves
#print axioms explicit_realizes
#print axioms realization_eq_explicit

end Gimle.Asgard.Examples.LinearOscillator
