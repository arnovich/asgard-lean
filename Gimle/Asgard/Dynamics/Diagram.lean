import Gimle.Asgard.Dynamics.Linear

/-! Exact rational data for a linear initial-value problem. -/
namespace Gimle.Asgard.Dynamics.Linear

/-- An executable exact subset of the real-valued initial-value problem. -/
structure RationalProblem (n : Nat) where
  names : Fin n → String
  matrix : Matrix n
  initial : Fin n → ℚ
  axis : String
  start : ℚ

noncomputable def RationalProblem.problem {n : Nat} (p : RationalProblem n) : Problem n where
  names := p.names
  matrix := p.matrix
  initial := fun i => p.initial i
  time := ⟨p.axis, p.start⟩

end Gimle.Asgard.Dynamics.Linear
