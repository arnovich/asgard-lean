import Gimle.Asgard.Circuit
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact real interpretation; this does not assert correctness of floating-point execution. -/

namespace Gimle.Asgard

abbrev Point (dimension : Nat) := Fin dimension → ℝ

@[simp] def pointLeft {left right : Nat} (point : Point (left + right)) : Point left :=
  fun coordinate => point ⟨coordinate.val, Nat.lt_of_lt_of_le coordinate.isLt (Nat.le_add_right _ _)⟩

@[simp] def pointRight {left right : Nat} (point : Point (left + right)) : Point right :=
  fun coordinate => point ⟨left + coordinate.val, Nat.add_lt_add_left coordinate.isLt left⟩

@[simp] def pointAppend {left right : Nat}
    (leftPoint : Point left) (rightPoint : Point right) : Point (left + right) :=
  fun coordinate =>
    if inside : coordinate.val < left then
      leftPoint ⟨coordinate.val, inside⟩
    else
      rightPoint ⟨coordinate.val - left, by omega⟩

@[simp] theorem pointLeft_pointAppend {left right : Nat}
    (leftPoint : Point left) (rightPoint : Point right) :
    pointLeft (pointAppend leftPoint rightPoint) = leftPoint := by
  funext coordinate
  simp [pointLeft, pointAppend]

@[simp] theorem pointRight_pointAppend {left right : Nat}
    (leftPoint : Point left) (rightPoint : Point right) :
    pointRight (pointAppend leftPoint rightPoint) = rightPoint := by
  funext coordinate
  simp [pointRight, pointAppend]

/-- Circuit behavior is derived from its typed syntax, never supplied separately. -/
@[simp] def Circuit.run {input output : Nat} :
    Circuit input output → Point input → Point output
  | .id, point => point
  | .const value, _ => ![(value : ℝ)]
  | .scalar value, point => ![(value : ℝ) * point 0]
  | .add, point => ![point 0 + point 1]
  | .multiplication, point => ![point 0 * point 1]
  | .split, point => ![point 0, point 0]
  | .swap, point => ![point 1, point 0]
  | .terminal, _ => fun coordinate => Fin.elim0 coordinate
  | .compose left right, point => right.run (left.run point)
  | .parallel left right, point =>
      pointAppend (left.run (pointLeft point)) (right.run (pointRight point))

end Gimle.Asgard
