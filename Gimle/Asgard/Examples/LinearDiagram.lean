import Gimle.Asgard.Dynamics.Diagram
import Gimle.Asgard.Examples.LinearOscillator

namespace Gimle.Asgard.Examples.LinearOscillator

/-- Exact demo inputs belong to the same model used for compilation and proofs. -/
def demo : Dynamics.Linear.RationalProblem 2 where
  names := names
  matrix := matrix
  initial := ![1, 0]
  axis := "t"
  start := 0

theorem demo_problem : demo.problem = problem 0 1 0 := by
  simp [demo, Dynamics.Linear.RationalProblem.problem, problem]
  ext i
  fin_cases i <;> norm_num

theorem demo_exists : ∃ state, demo.problem.Realizes state := demo.problem.exists_realization

#print axioms demo_problem
#print axioms demo_exists
end Gimle.Asgard.Examples.LinearOscillator
