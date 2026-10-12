import Gimle.Asgard.Examples.AIF

/-! Exact source, state-order and fixed-driver regressions for the AIF circuit. -/
namespace Gimle.Asgard.Tests.AIF
open Gimle.Asgard.Examples.AIF

example (eta : ℝ) : field.run ![eta,0,0,0,0] = ![0,0,2,0] := by
  rw [field_equations]
  ext i
  fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

/-- Omitting sequestration changes the compiled controller output. -/
theorem sequestration_is_present : field.run ![8,0,0,1,1] 2 = -6 := by
  rw [field_equations]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

/-- Eta remains a real runtime coordinate; it is not specialized to ten. -/
theorem parameter_changes_field :
    field.run ![8,0,0,1,1] 2 ≠ field.run ![12,0,0,1,1] 2 := by
  rw [field_equations, field_equations]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

example (eta : ℝ) (state : Dynamics.Signal 4) (h : Realizes eta state) : state 0 = 0 :=
  ((realizes_iff eta state).mp h).1

example (x : Point 4) : output.run x 0 = x 1 := output_correct x

#print axioms sequestration_is_present
#print axioms parameter_changes_field
end Gimle.Asgard.Tests.AIF
