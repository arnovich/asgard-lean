import Gimle.Asgard.AlgebraicCompiler

namespace Gimle.Asgard.Algebraic.Examples

/-- The source equations are z = z/2 + u and y = z.
The compiler emits exact typed circuits for both the loop and its elimination. -/
def halfLoop : Problem 1 1 1 where
  matrix := !![1/2]
  offset := ⟨!![1], ![0]⟩
  output := ⟨!![1, 0], ![0]⟩

def halfInverse : Inverse halfLoop.matrix where
  value := !![2]
  left := by ext i j; fin_cases i; fin_cases j; norm_num [halfLoop, Matrix.mul_apply]
  right := by ext i j; fin_cases i; fin_cases j; norm_num [halfLoop, Matrix.mul_apply]

def loopDomain (z : Point 1) : Prop := -2 ≤ z 0 ∧ z 0 ≤ 2
def inputDomain (u : Point 1) : Prop := -1 ≤ u 0 ∧ u 0 ≤ 1

@[simp] theorem half_solution (u : Point 1) :
    (halfLoop.solutionCircuit halfInverse.value).run u = ![2 * u 0] := by
  rw [Problem.solution_correct]
  ext i
  fin_cases i
  simp [halfLoop, halfInverse, Affine.eval,
    realMatrix, Matrix.mulVec, dotProduct]

theorem half_membership (u : Point 1) (hu : inputDomain u) :
    loopDomain ((halfLoop.solutionCircuit halfInverse.value).run u) := by
  simp only [half_solution, loopDomain, Matrix.cons_val_zero]
  rcases hu with ⟨hl, hh⟩
  constructor <;> linarith

/-- For each u in [-1,1], exactly one z in [-2,2] satisfies the original loop.
Every original output equals the output of the compiler-produced circuit. -/
theorem half_correct (u : Point 1) (hu : inputDomain u) :
    (∃! z, loopDomain z ∧ halfLoop.loopAffine.circuit.run (pointAppend z u) = z) ∧
    ∀ y, Rel halfLoop.loopAffine.circuit halfLoop.output.circuit loopDomain u y ↔
      y = (halfLoop.eliminatedCircuit halfInverse.value).run u :=
  halfLoop.eliminate_correct halfInverse loopDomain inputDomain half_membership u hu

/-- Coupled source: z₀ = z₁/2 + u₀, z₁ = u₁, y = z₀.
The nonsymmetric matrix exercises port order and inverse multiplication order. -/
def coupled : Problem 2 2 1 where
  matrix := !![0, 1/2; 0, 0]
  offset := ⟨!![1, 0; 0, 1], ![0, 0]⟩
  output := ⟨!![1, 0, 0, 0], ![0]⟩

def coupledInverse : Inverse coupled.matrix where
  value := !![1, 1/2; 0, 1]
  left := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [coupled, Matrix.mul_apply, Fin.sum_univ_two]
  right := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [coupled, Matrix.mul_apply, Fin.sum_univ_two]

theorem coupled_solution (u : Point 2) :
    (coupled.solutionCircuit coupledInverse.value).run u = ![u 0 + u 1 / 2, u 1] := by
  rw [Problem.solution_correct]
  ext i
  fin_cases i <;> simp [coupled, coupledInverse, Affine.eval, realMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

#print axioms half_correct
#print axioms coupled_solution
end Gimle.Asgard.Algebraic.Examples
