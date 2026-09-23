import Gimle.Asgard.Examples.PolynomialCompiler
import Gimle.Asgard.Examples.LinearDiagram

/-! A single equation source for compilation, properties and optional execution.
The readable `energyProgram` and `oscillatorProgram` live in PolynomialCompiler.
No numerical settings or Python imports participate in these definitions. -/
namespace Gimle.Asgard.Examples.EquationModels
open Polynomial

/-- Select the energy output from the declared [s,d,energy] assignment order. -/
def energy : Circuit 2 1 :=
  .compose PolynomialCompiler.energyCircuit (route (fun _ : Fin 1 => (2 : Fin 3)))

def energyOutput : Port := PolynomialCompiler.energyProgram.assignments[2].output

/-- E(x,y)=(x+y)²+(x-y)²=2x²+2y² for every real input. -/
theorem energy_formula (x : Point 2) : energy.run x 0 = 2*x 0^2 + 2*x 1^2 := by
  simpa [energy, Circuit.run] using PolynomialCompiler.energy_identity x

/-- Both derivatives are compiled from dx:=y; dy:=-x-2*y, in that order. -/
def oscillator : Circuit 2 2 := PolynomialCompiler.oscillatorCircuit

theorem oscillator_equations (x : Point 2) :
    oscillator.run x = ![x 1, -x 0 - 2*x 1] := PolynomialCompiler.oscillator_equations x

/-- Extract the linear analysis model from those same resolved expressions. -/
def matrix : Dynamics.Linear.Matrix 2 := fun i =>
  (Dynamics.LinearSyntax.coefficients PolynomialCompiler.oscillatorExpressions[i]).get
    (by fin_cases i <;> decide)

theorem matrix_accepted (i : Fin 2) :
    Dynamics.LinearSyntax.coefficients PolynomialCompiler.oscillatorExpressions[i] =
      some (matrix i) := by fin_cases i <;> decide +kernel

/-- Exact initial data are shared by formal semantics and the numerical request.
The fixed values 0 and 1 are exactly representable in binary64. -/
def model : Dynamics.Linear.RationalProblem 2 where
  names := fun i => PolynomialCompiler.inputs[i].name
  matrix := matrix
  initial := ![1, 0]
  axis := "t"
  start := 0

noncomputable def problem : Dynamics.Linear.Problem 2 := model.problem

theorem field_correct (x : Point 2) : oscillator.run x = problem.matrix.eval x := by
  rw [show oscillator = compileOutputs (fun i => PolynomialCompiler.oscillatorExpressions[i])
    from rfl, compileOutputs_correct]
  funext i
  exact Dynamics.LinearSyntax.coefficients_correct _ _ (matrix_accepted i) x

/-- Close the original equation-compiled field, rather than a separately emitted matrix field. -/
def feedback : Dynamics.Circuit 2 2 := Dynamics.close (d := 0) (n := 2) model.axis oscillator

def noDrivers : Dynamics.Signal 0 := fun _ i => Fin.elim0 i

def Realizes (state : Dynamics.Signal 2) : Prop :=
  feedback.Rel problem.time
    (Dynamics.signalAppend noDrivers (fun _ => problem.initial)) state

/-- The actual compiled feedback has exactly the linear problem's trajectories,
with identical state order, initial data, time axis and forward domain. -/
theorem realizes_iff (state : Dynamics.Signal 2) : Realizes state ↔ problem.Realizes state := by
  have appended (t : ℝ) : pointAppend (noDrivers t) (state t) = state t := by
    ext i
    fin_cases i <;> rfl
  rw [Realizes, feedback, Dynamics.close_correct, ← problem.solves_iff_realizes]
  simp only [appended, field_correct, Dynamics.Linear.Problem.Solves,
    show model.axis = problem.time.axis from rfl, true_and]

theorem exists_realization : ∃ state, Realizes state := by
  obtain ⟨state, h⟩ := problem.exists_realization
  exact ⟨state, (realizes_iff state).mpr h⟩

theorem unique_realization {x y : Dynamics.Signal 2} (hx : Realizes x) (hy : Realizes y) :
    Set.EqOn x y problem.time.domain :=
  problem.unique_realization ((realizes_iff x).mp hx) ((realizes_iff y).mp hy)

/-- Relate this derived model to the established damped-oscillator analysis. -/
theorem problem_eq : problem = LinearOscillator.problem 0 1 0 := by
  have hm : matrix = LinearOscillator.matrix := by decide +kernel
  simp [problem, model, Dynamics.Linear.RationalProblem.problem,
    LinearOscillator.problem, hm, LinearOscillator.names, PolynomialCompiler.inputs]
  constructor <;> ext i <;> fin_cases i <;> norm_num

#print axioms energy_formula
#print axioms field_correct
#print axioms realizes_iff
#print axioms exists_realization
#print axioms unique_realization
end Gimle.Asgard.Examples.EquationModels
