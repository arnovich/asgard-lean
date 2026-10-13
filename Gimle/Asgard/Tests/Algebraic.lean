import Gimle.Asgard.AlgebraicCompiler

namespace Gimle.Asgard.Algebraic.Tests

-- An invertible but noncontractive loop is legitimate stateless algebra.
example (u z : ℝ) : z = 2 * z + u ↔ z = -u := by constructor <;> intro h <;> linarith

-- A singular equation can have no solution or many solutions.
example : ¬ ∃ z : ℝ, z = z + 1 := by rintro ⟨z, h⟩; linarith
example : ∃ z w : ℝ, z ≠ w ∧ z = z ∧ w = w := ⟨0, 1, by norm_num, rfl, rfl⟩

-- Invertibility does not ensure membership in a restricted loop domain.
example : ¬ ∃ z : ℝ, (-1 ≤ z ∧ z ≤ 1) ∧ z = z / 2 + 1 := by
  rintro ⟨z, ⟨hl, hu⟩, h⟩
  linarith

/-- Exercise the actual compiler and existence/uniqueness API for z=2z+u. -/
def noncontractive : Problem 1 1 1 where
  matrix := !![2]
  offset := ⟨!![1], ![0]⟩
  output := ⟨!![1, 0], ![0]⟩

def noncontractiveInverse : Inverse noncontractive.matrix where
  value := !![-1]
  left := by ext i j; fin_cases i; fin_cases j; norm_num [noncontractive, Matrix.mul_apply]
  right := by ext i j; fin_cases i; fin_cases j; norm_num [noncontractive, Matrix.mul_apply]

theorem noncontractive_exists_unique (u : Point 1) :
    ∃! z, True ∧ noncontractive.loopAffine.circuit.run (pointAppend z u) = z :=
  (noncontractive.eliminate_correct noncontractiveInverse (fun _ => True)
    (fun _ => True) (fun _ _ => trivial) u trivial).1

/-- The inverse certificate API cannot accept I-M=0. -/
example : ¬ Nonempty (Inverse (!![1] : RationalMatrix 1 1)) := by
  rintro ⟨inv⟩
  have h := congrFun (congrFun inv.left 0) 0
  norm_num [Matrix.mul_apply] at h

#print axioms noncontractive_exists_unique

end Gimle.Asgard.Algebraic.Tests
