import Gimle.Asgard.Examples.PartialFeedback
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Regression tests for continuous feedback over a partial real field (task 042).

The field's generators read the time of the forward domain, drivers feed the
field beside the state, and a domain violation at a single time, including one
caused by a driver, removes every relation output. -/
namespace Gimle.Asgard.Tests.PartialFeedback
open Gimle.Asgard.RealAtomics Gimle.Asgard.Examples.PartialFeedback

/-- `x' = cos t` reads the axis: `sin` solves it from `0`. -/
def clock : Fin 1 → Expr 1 (0 + 1) := fun _ => .generated .cos 0

example : (vectorField clock).CloseRel "t" time
    (Dynamics.signalAppend noDrivers (fun _ => ![0])) (fun t => ![Real.sin t]) := by
  rw [Expr.close_correct]
  refine ⟨rfl, by simp [time], fun t _ => ⟨fun _ => trivial, fun i => ?_⟩⟩
  fin_cases i
  simpa [clock, Expr.value, Unary.value, timeAxis] using
    HasDerivAt.hasDerivWithinAt (Real.hasDerivAt_sin t)

/-- The axis is time, not the state: `x' = cos x` is not solved by `sin`. -/
example : ¬ (vectorField (fun _ => .unary .cos (.input 0) : Fin 1 → Expr 1 (0 + 1))).CloseRel
    "t" time (Dynamics.signalAppend noDrivers (fun _ => ![0])) (fun t => ![Real.sin t]) := by
  rw [Expr.close_correct]
  rintro ⟨-, -, h⟩
  have hmem : Real.pi / 2 ∈ time.domain := by
    change (0 : ℝ) ≤ Real.pi / 2
    positivity
  have deriv := (h _ hmem).2 0
  simp only [Expr.value, Unary.value, append_noDrivers, Matrix.cons_val_zero,
    Real.sin_pi_div_two] at deriv
  have unique := (HasDerivAt.hasDerivWithinAt (Real.hasDerivAt_sin (Real.pi / 2))
    (s := time.domain)).derivWithin (uniqueDiffOn_Ici 0 _ hmem)
  rw [deriv.derivWithin (uniqueDiffOn_Ici 0 _ hmem), Real.cos_pi_div_two] at unique
  have : 0 < Real.cos 1 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by
    linarith [Real.pi_gt_three]⟩
  linarith

/-- A driver feeds the field: `x' = log u` with `u = 1` is solved by a constant. -/
def logDriven : Fin 1 → Expr 1 (1 + 1) := fun _ => .unary .log (.input 0)

example : (vectorField logDriven).CloseRel "t" time
    (Dynamics.signalAppend (fun _ => ![1]) (fun _ => ![5])) (fun _ => ![5]) := by
  rw [Expr.close_correct]
  refine ⟨rfl, rfl, fun t _ => ⟨fun _ => ?_, fun i => ?_⟩⟩
  · simp [logDriven, Expr.Defined, Expr.value, Unary.Domain, pointAppend]
  · simpa [logDriven, Expr.value, Unary.value, pointAppend] using
      hasDerivWithinAt_const t time.domain (5 : ℝ)

/-- A driver leaving the field's domain at one time removes every output, even
a state that satisfies the totalized ODE (`log 0 = 0`). -/
example (state : Dynamics.Signal 1) : ¬ (vectorField logDriven).CloseRel "t" time
    (Dynamics.signalAppend (fun t => ![1 - t]) (fun _ => ![5])) state := by
  rw [Expr.close_correct]
  rintro ⟨-, -, h⟩
  have := (h 1 (by simp [time, Dynamics.TimeDomain.domain])).1 0
  simp [logDriven, Expr.Defined, Expr.value, Unary.Domain, pointAppend] at this

/-- The relation holds for the expected axis name only. -/
example : ¬ (vectorField growth).CloseRel "s" time
    (Dynamics.signalAppend noDrivers (fun _ => ![1])) solution := by
  rw [Expr.close_correct]
  rintro ⟨h, -⟩
  simp [time] at h

/--
info: 'Gimle.Asgard.RealAtomics.Circuit.close_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Circuit.close_correct
/--
info: 'Gimle.Asgard.RealAtomics.Expr.close_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Expr.close_correct
/--
info: 'Gimle.Asgard.RealAtomics.vectorField_defined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms vectorField_defined
/--
info: 'Gimle.Asgard.RealAtomics.vectorField_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms vectorField_value
/--
info: 'Gimle.Asgard.Examples.PartialFeedback.growth_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms growth_solution
/--
info: 'Gimle.Asgard.Examples.PartialFeedback.falling_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms falling_rejected
/--
info: 'Gimle.Asgard.Examples.PartialFeedback.stuck_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stuck_rejected

end Gimle.Asgard.Tests.PartialFeedback
