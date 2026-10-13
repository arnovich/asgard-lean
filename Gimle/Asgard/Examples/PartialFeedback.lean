import Gimle.Asgard.RealAtomics.Feedback
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! A continuous model whose field is a partial real function.

growth:   x' = sqrt(x),            x(0) = 1
leaving:  x' = -1 + 0 * sqrt(x),   x(0) = 1

`x(t) = (1 + t/2)²` solves growth and stays in `sqrt`'s domain for every
`t ≥ 0`, so it is a relation output. Two signals satisfy the ODE read through
the totalized `value` but not the relation: `x(t) = 1 - t` for leaving, which
leaves the domain at `t > 1` although its zero multiplier discards the root, and
the constant `x = -1` for growth, where the totalized `sqrt(-1) = 0` makes it a
fixed point. Neither is an output: `Defined` is required at every time of the
forward domain. No existence, uniqueness, or numerical claim is made. -/
namespace Gimle.Asgard.Examples.PartialFeedback
open Gimle.Asgard.RealAtomics

def time : Dynamics.TimeDomain := ⟨"t", 0⟩

def noDrivers : Dynamics.Signal 0 := fun _ i => Fin.elim0 i

def root : Expr 1 (0 + 1) := .unary .sqrt (.input 0)

def growth : Fin 1 → Expr 1 (0 + 1) := fun _ => root

def leaving : Fin 1 → Expr 1 (0 + 1) := fun _ =>
  .binary .add (.constant (-1)) (.binary .mul (.constant 0) root)

noncomputable def solution : Dynamics.Signal 1 := fun t => ![(1 + t / 2) ^ 2]

def falling : Dynamics.Signal 1 := fun t => ![1 - t]

def stuck : Dynamics.Signal 1 := fun _ => ![-1]

@[simp] theorem append_noDrivers (t : ℝ) (x : Point 1) : pointAppend (noDrivers t) x = x := by
  funext i
  fin_cases i
  simp [pointAppend]

/-- The explicit solution is an output of the partial-field relation. -/
theorem growth_solution : (vectorField growth).CloseRel "t" time
    (Dynamics.signalAppend noDrivers (fun _ => ![1])) solution := by
  rw [Expr.close_correct]
  refine ⟨rfl, by simp [solution, time], fun t ht => ?_⟩
  have ht : 0 ≤ t := ht
  have hpos : 0 ≤ 1 + t / 2 := by linarith
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [growth, root, Expr.Defined, Unary.Domain, Expr.value, append_noDrivers,
      true_and]
    simp only [solution, Matrix.cons_val_zero]
    positivity
  · fin_cases i
    simp only [growth, root, Expr.value, Unary.value, append_noDrivers, solution]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.sqrt_sq hpos]
    have h : HasDerivAt (fun t : ℝ => (1 + t / 2) ^ 2) (1 + t / 2) t := by
      have inner : HasDerivAt (fun t : ℝ => 1 + t / 2) (1 / 2) t :=
        HasDerivAt.const_add 1 (HasDerivAt.div_const (hasDerivAt_id' t) 2)
      exact HasDerivAt.congr_deriv (HasDerivAt.fun_pow inner 2) (by push_cast; ring)
    exact HasDerivAt.hasDerivWithinAt h

/-- `falling` satisfies `leaving` read through the totalized value at every time. -/
theorem falling_totalized (t : ℝ) :
    HasDerivWithinAt (fun t => falling t 0)
      ((leaving 0).value (timeAxis t) (pointAppend (noDrivers t) (falling t))) time.domain t := by
  simp only [leaving, root, Expr.value, Unary.value, Binary.value, append_noDrivers, falling]
  norm_num
  exact HasDerivAt.hasDerivWithinAt (by simpa using HasDerivAt.const_sub 1 (hasDerivAt_id t))

/-- A trajectory that leaves `sqrt`'s domain is no output, although a zero
multiplier discards the root and the totalized ODE holds everywhere. -/
theorem falling_rejected : ¬ (vectorField leaving).CloseRel "t" time
    (Dynamics.signalAppend noDrivers (fun _ => ![1])) falling := by
  rw [Expr.close_correct]
  rintro ⟨-, -, h⟩
  have := ((h 2 (by simp [time, Dynamics.TimeDomain.domain])).1 0)
  simp only [leaving, root, Expr.Defined, Expr.value, Unary.Domain, Binary.Domain,
    append_noDrivers, falling] at this
  norm_num at this

/-- The constant `-1` is a fixed point of the totalized growth field. -/
theorem stuck_totalized (t : ℝ) :
    HasDerivWithinAt (fun t => stuck t 0)
      ((growth 0).value (timeAxis t) (pointAppend (noDrivers t) (stuck t))) time.domain t := by
  simp only [growth, root, Expr.value, Unary.value, append_noDrivers, stuck]
  norm_num
  exact hasDerivWithinAt_const t _ (-1)

/-- The totalized value at an undefined point is never a relation output. -/
theorem stuck_rejected : ¬ (vectorField growth).CloseRel "t" time
    (Dynamics.signalAppend noDrivers (fun _ => ![-1])) stuck := by
  rw [Expr.close_correct]
  rintro ⟨-, -, h⟩
  have := ((h 0 (by simp [time, Dynamics.TimeDomain.domain])).1 0)
  simp only [growth, root, Expr.Defined, Expr.value, Unary.Domain, append_noDrivers,
    stuck] at this
  norm_num at this

#print axioms growth_solution
#print axioms falling_rejected
#print axioms stuck_rejected
end Gimle.Asgard.Examples.PartialFeedback
