import Gimle.Asgard.RealAtomics.Laws
import Gimle.Asgard.Examples.RealAtomics

namespace Gimle.Asgard.Tests.RealAtomics
open Gimle.Asgard.RealAtomics

/-- Invalid primitive domains must survive compilation and downstream zero. -/
def invalid : Expr 0 1 := .binary .mul (.constant 0) (.unary .log (.input 0))

example : ¬ invalid.Defined ![] ![-1] := by
  simp [invalid, Expr.Defined, Expr.value, Unary.Domain, Binary.Domain]

example (y : Point 1) : ¬ invalid.compile.Rel ![] ![-1] y := by
  rw [Expr.compile_rel]
  simp [invalid, Expr.Defined, Expr.value, Unary.Domain, Binary.Domain]

/-- Primitive values are checked against concrete independent expectations. -/
example : (Expr.unary .abs (.input 0) : Expr 0 1).compile.Rel ![] ![-3] ![3] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .sqrt (.input 0) : Expr 0 1).compile.Rel ![] ![4] ![2] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .sqrt (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![0] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .log (.input 0) : Expr 0 1).compile.Rel ![] ![1] ![0] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .exp (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![1] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .sin (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![0] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .cos (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![1] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .sinh (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![0] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .cosh (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![1] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .tanh (.input 0) : Expr 0 1).compile.Rel ![] ![0] ![0] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .neg (.input 0) : Expr 0 1).compile.Rel ![] ![3] ![-3] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary (.naturalPower 3) (.input 0) : Expr 0 1).compile.Rel ![] ![-2] ![-8] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary (.rationalPower (-1)) (.input 0) : Expr 0 1).compile.Rel ![] ![2] ![1/2] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.binary .realPower (.input 0) (.input 1) : Expr 0 2).compile.Rel ![] ![2,3] ![8] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Binary.Domain, Binary.value]

example : (Expr.binary .division (.input 0) (.input 1) : Expr 0 2).compile.Rel ![] ![6,2] ![3] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Binary.Domain, Binary.value]

example : (Expr.constant (1/3) : Expr 0 0).compile.Rel ![] ![] ![1/3] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value]

/-- Fractional powers and nonzero values distinguish primitive dispatch. -/
example : (Expr.unary (.rationalPower (1/2)) (.input 0) : Expr 0 1).compile.Rel
    ![] ![4] ![2] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value,
    ← Real.sqrt_eq_rpow]

example : (Expr.binary .realPower (.input 0) (.input 1) : Expr 0 2).compile.Rel
    ![] ![9,1/2] ![3] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Binary.Domain, Binary.value,
    ← Real.sqrt_eq_rpow]

example : (Expr.unary .cos (.input 0) : Expr 0 1).compile.Rel ![] ![Real.pi] ![-1] := by
  simp [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example : (Expr.unary .sinh (.input 0) : Expr 0 1).compile.Rel ![] ![Real.log 2] ![3/4] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value,
    Real.sinh_log (by norm_num : (0:ℝ) < 2)]

example : (Expr.unary .cosh (.input 0) : Expr 0 1).compile.Rel ![] ![Real.log 2] ![5/4] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value,
    Real.cosh_log (by norm_num : (0:ℝ) < 2)]

example : (Expr.unary .tanh (.input 0) : Expr 0 1).compile.Rel ![] ![Real.log 2] ![3/5] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value,
    Real.tanh_eq_sinh_div_cosh, Real.sinh_log (by norm_num : (0:ℝ) < 2),
    Real.cosh_log (by norm_num : (0:ℝ) < 2)]

/-- Unlike sqrt, the positive-base power fragment excludes zero. -/
example (y : Point 1) : ¬ (Expr.unary (.rationalPower (1/2)) (.input 0) :
    Expr 0 1).compile.Rel ![] ![0] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Unary.Domain]

/-- Strict domain rejection, irrespective of any totalized auxiliary value. -/
example (y : Point 1) : ¬ (Expr.unary .sqrt (.input 0) : Expr 0 1).compile.Rel ![] ![-1] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Unary.Domain]

example (y : Point 1) : ¬ (Expr.unary .log (.input 0) : Expr 0 1).compile.Rel ![] ![0] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Unary.Domain]

example (y : Point 1) :
    ¬ (Expr.binary .division (.input 0) (.input 1) : Expr 0 2).compile.Rel ![] ![1,0] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Binary.Domain]

example (y : Point 1) :
    ¬ (Expr.binary .realPower (.input 0) (.input 1) : Expr 0 2).compile.Rel ![] ![-2,2] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Binary.Domain]

example (y : Point 1) :
    ¬ (Expr.binary .realPower (.input 0) (.input 1) : Expr 0 2).compile.Rel ![] ![0,3] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Binary.Domain]

example (y : Point 1) :
    ¬ (Expr.unary (.rationalPower 0) (.input 0) : Expr 0 1).compile.Rel ![] ![-1] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Unary.Domain]

example : (Expr.unary (.naturalPower 0) (.input 0) : Expr 0 1).compile.Rel ![] ![-1] ![1] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example (y : Point 1) : ¬ (Expr.unary (.naturalPower 0) (.unary .log (.input 0)) :
    Expr 0 1).compile.Rel ![] ![-1] y := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value, Unary.Domain]

example (y : Point 0) : ¬ (Gimle.Asgard.RealAtomics.Circuit.compose (.unary .log) (.embed .terminal) :
    Gimle.Asgard.RealAtomics.Circuit 0 1 0).Rel ![] ![-1] y := by
  simp [Gimle.Asgard.RealAtomics.Circuit.rel_iff, Gimle.Asgard.RealAtomics.Circuit.Defined, Unary.Domain]

example (y : Point 0) : ¬ (Gimle.Asgard.RealAtomics.Circuit.compose (.parallel (.unary .log) (.embed .id))
    (.embed (Wiring.discard 2)) : Gimle.Asgard.RealAtomics.Circuit 0 2 0).Rel ![] ![-1,7] y := by
  simp [Gimle.Asgard.RealAtomics.Circuit.rel_iff, Gimle.Asgard.RealAtomics.Circuit.Defined, Unary.Domain, pointLeft]

/-- A generator has zero ordinary inputs and observes the selected axis. -/
example : (Gimle.Asgard.RealAtomics.Circuit.generator .sin 1 : Gimle.Asgard.RealAtomics.Circuit 2 0 1).Rel ![0,Real.pi/2] ![] ![1] := by
  simp [Gimle.Asgard.RealAtomics.Circuit.Rel, Unary.Domain, Unary.value, Real.sin_pi_div_two]

example : ¬ (Gimle.Asgard.RealAtomics.Circuit.generator .sin 0 : Gimle.Asgard.RealAtomics.Circuit 2 0 1).Rel ![0,Real.pi/2] ![] ![1] := by
  simp [Gimle.Asgard.RealAtomics.Circuit.Rel, Unary.Domain, Unary.value]

example : (Gimle.Asgard.RealAtomics.Circuit.unary .sin : Gimle.Asgard.RealAtomics.Circuit 2 1 1).Rel ![0,Real.pi/2] ![0] ![0] := by
  simp [Gimle.Asgard.RealAtomics.Circuit.Rel, Unary.Domain, Unary.value]

example : (Expr.generated .exp 1 : Expr 2 3).compile.Rel ![7,0] ![2,3,4] ![1] := by
  simp [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

example (y : Point 1) : ¬ (Expr.generated .log 1 : Expr 2 0).compile.Rel ![1,0] ![] y := by
  simp [Expr.compile_rel, Expr.Defined, Unary.Domain]

/-- Shared/repeated inputs retain asymmetric order; the middle input is unused. -/
def shared : Expr 0 3 := .binary .division (.binary .add (.input 2) (.input 2))
  (.binary .add (.constant 1) (.unary (.naturalPower 2) (.input 0)))

example (unused : ℝ) : shared.compile.Rel ![] ![2,unused,5] ![2] := by
  simp only [Expr.compile_scalar, shared, Expr.Defined, Expr.value, Unary.Domain,
    Unary.value, Binary.Domain, Binary.value, Matrix.cons_val]
  norm_num

example : ¬ shared.compile.Rel ![] ![5,0,2] ![2] := by
  simp only [Expr.compile_scalar, shared, Expr.Defined, Expr.value, Unary.Domain,
    Unary.value, Binary.Domain, Binary.value, Matrix.cons_val]
  norm_num

/-- sqrt(x²) cannot be rewritten to x on negative inputs. -/
example : ¬ (Expr.unary .sqrt (.unary (.naturalPower 2) (.input 0)) :
    Expr 0 1).compile.Rel ![] ![-2] ![-2] := by
  norm_num [Expr.compile_scalar, Expr.Defined, Expr.value, Unary.Domain, Unary.value]

/-- The concrete paired circuit exercises generator wiring and the nonlinear
division channel, with magnitude 5/6 at the 3-4-5 point. -/
example : Examples.RealAtomics.circuit.Rel ![0] ![3,4] ![4,5/6] := by
  have h := Examples.RealAtomics.circuit_behavior ![0] ![3,4]
  norm_num [Examples.RealAtomics.magnitude, Examples.RealAtomics.radius,
    Expr.value, Unary.value, Binary.value] at h
  exact h

#print axioms Expr.compile_rel
#print axioms Examples.RealAtomics.circuit_magnitude_bound

end Gimle.Asgard.Tests.RealAtomics
