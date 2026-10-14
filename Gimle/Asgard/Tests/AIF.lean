import Gimle.Asgard.Examples.AIF

/-! Exact source, state-order and fixed-driver regressions for the AIF circuit. -/
namespace Gimle.Asgard.Tests.AIF
open Gimle.Asgard.Examples.AIF

theorem initial_field (eta : ℝ) : field.run ![eta,0,0,0,0] = ![0,0,2,0] := by
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

theorem initial_state (eta : ℝ) (state : Dynamics.Signal 4) (h : Realizes eta state) : state 0 = 0 :=
  ((realizes_iff eta state).mp h).1

theorem observed_species (x : Point 4) : output.run x 0 = x 1 := output_correct x

/-- The feedback relation excludes a changed initial physical state. -/
theorem nonzero_initial_rejected (eta : ℝ) (state : Dynamics.Signal 4)
    (initial : state 0 ≠ 0) : ¬ Realizes eta state := by
  intro realized
  exact initial ((realizes_iff eta state).mp realized).1

/-- Observation routing distinguishes the second species from all other wires. -/
theorem observation_routing : output.run ![3,5,7,11] 0 = 5 := by
  rw [output_correct]
  rfl

/-- Distinct species values check both plant wires and both sequestration outputs. -/
theorem full_field_routing : field.run ![2,3,5,7,11] = ![4,-2,-152,-149] := by
  rw [field_equations]
  ext i
  fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

#print axioms full_field_routing
#print axioms initial_field
#print axioms initial_state
#print axioms observed_species
#print axioms nonzero_initial_rejected
#print axioms observation_routing
#print axioms sequestration_is_present
#print axioms parameter_changes_field
end Gimle.Asgard.Tests.AIF
