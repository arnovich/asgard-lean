import Gimle.Asgard.AlgebraicDeclaration
import Gimle.Asgard.Examples.AlgebraicFeedback

/-! The source equations `z = z/2 + u` and `y = z`, declared with the loop domain
`z ∈ [-2, 2]`, the admitted inputs `u ∈ [-1, 1]` and the supplied inverse `2` of
`1 - 1/2`. The membership obligation is `half_membership`. -/
namespace Gimle.Asgard.Algebraic.Examples
open Polynomial Matrix

def halfDeclaration : Declaration 1 1 1 where
  loop := ![⟨"z", "z", .state⟩]
  external := ![⟨"u", "u", .input⟩]
  outputs := ![⟨"y", "y", .output⟩]
  problem := halfLoop
  inverse := !![2]
  domain := loopDomain
  admitted := inputDomain
  membership := half_membership

#guard halfDeclaration.validate matches .ok ()
#guard halfDeclaration.compile matches .ok _

/-- The accepted declaration, with its evidence checked by the kernel. -/
def halfModel : AlgebraicModel halfDeclaration where
  valid := by decide +kernel
  inverse := halfInverse
  supplied := rfl

/-- The eliminated circuit returns `2u`. -/
theorem half_eliminated (u : Point 1) : halfModel.circuit.run u = ![2 * u 0] := by
  rw [AlgebraicModel.circuit, Problem.output_correct]
  change halfLoop.output.circuit.run
    (pointAppend ((halfLoop.solutionCircuit halfInverse.value).run u) u) = _
  rw [half_solution, Affine.circuit_correct]
  ext i
  fin_cases i
  simp [halfLoop, Affine.eval, realMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For each admitted `u ∈ [-1, 1]`, the declared equations hold of exactly
`y = 2u`. -/
theorem half_declared (u : Point 1) (hu : inputDomain u) (y : Point 1) :
    halfDeclaration.Solves u y ↔ y = ![2 * u 0] := by
  rw [halfModel.solves_iff_eliminated u hu, half_eliminated]

#print axioms half_eliminated
#print axioms half_declared
end Gimle.Asgard.Algebraic.Examples
