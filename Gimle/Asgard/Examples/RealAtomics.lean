import Gimle.Asgard.RealAtomics.Laws

/-! Two ordinary inputs [x,y] and one explicit axis [t].

r(x,y) = sqrt(x²+y²)
wave(t,x,y) = log(exp(y)) + sin(t) = y + sin(t)
magnitude(x,y) = r(x,y)/(1+r(x,y))

The circuit returns [wave,magnitude]. We prove every intermediate operation is
defined and 0 ≤ magnitude < 1 for every real x,y. The sine generator reads t
from the axis context and consumes zero ordinary wires. No numerical or series
approximation is used. -/
namespace Gimle.Asgard.Examples.RealAtomics
open Gimle.Asgard.RealAtomics

def radius : Expr 1 2 :=
  .unary .sqrt (.binary .add (.unary (.naturalPower 2) (.input 0))
    (.unary (.naturalPower 2) (.input 1)))

def magnitude : Expr 1 2 :=
  .binary .division radius (.binary .add (.constant 1) radius)

def wave : Expr 1 2 :=
  .binary .add (.unary .log (.unary .exp (.input 1))) (.generated .sin 0)

def simplerWave : Expr 1 2 := .binary .add (.input 1) (.generated .sin 0)

def circuit : Gimle.Asgard.RealAtomics.Circuit 1 2 2 := wave.compile.pair magnitude.compile

theorem radius_value (axes : Point 1) (x : Point 2) :
    radius.value axes x = Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := rfl

theorem radius_nonneg (axes : Point 1) (x : Point 2) : 0 ≤ radius.value axes x :=
  Real.sqrt_nonneg _

theorem radius_defined (axes : Point 1) (x : Point 2) : radius.Defined axes x := by
  simp only [radius, Expr.Defined, Expr.value, Unary.Domain, Unary.value, Binary.Domain,
    Binary.value, true_and]
  positivity

theorem magnitude_defined (axes : Point 1) (x : Point 2) : magnitude.Defined axes x := by
  have positive : 0 < 1 + radius.value axes x := by linarith [radius_nonneg axes x]
  simp [magnitude, Expr.Defined, Expr.value, Binary.Domain, Binary.value,
    radius_defined, ne_of_gt positive]

theorem magnitude_range (axes : Point 1) (x : Point 2) :
    0 ≤ magnitude.value axes x ∧ magnitude.value axes x < 1 := by
  have nonneg := radius_nonneg axes x
  have positive : 0 < 1 + radius.value axes x := by linarith
  simp only [magnitude, Expr.value, Binary.value, Rat.cast_one]
  change 0 ≤ radius.value axes x / (1 + radius.value axes x) ∧
    radius.value axes x / (1 + radius.value axes x) < 1
  constructor
  · exact div_nonneg nonneg (le_of_lt positive)
  · apply (div_lt_one positive).mpr
    linarith

theorem wave_defined (axes : Point 1) (x : Point 2) : wave.Defined axes x := by
  simp [wave, Expr.Defined, Expr.value, Unary.Domain, Binary.Domain, Unary.value, Real.exp_pos]

/-- Optimize the wave channel as an equality of partial circuit relations. -/
theorem wave_rewrite : Circuit.EquivalentOn (fun _ _ => True) wave.compile simplerWave.compile := by
  apply Expr.rewrite
  · intros
    simp [wave_defined, simplerWave, Expr.Defined, Unary.Domain, Binary.Domain]
  · intros
    simp [wave, simplerWave, Expr.value, Unary.value, Binary.value, Real.log_exp]

/-- Both channels are admitted for every input, in the declared output order. -/
theorem circuit_behavior (axes : Point 1) (x : Point 2) :
    circuit.Rel axes x ![x 1 + Real.sin (axes 0), magnitude.value axes x] := by
  rw [Circuit.rel_iff]
  constructor
  · simp [circuit, Circuit.pair_defined, Expr.compile_defined, wave_defined, magnitude_defined]
  · simp [circuit, Circuit.pair_value, Expr.compile_value, wave, Expr.value,
      Unary.value, Binary.value, Real.log_exp]
    funext i
    fin_cases i <;> rfl

/-- The bound is about the actual operational circuit output, not just an
auxiliary value function outside its domain. -/
theorem circuit_magnitude_bound (axes : Point 1) (x : Point 2) (y : Point 2)
    (admitted : circuit.Rel axes x y) : 0 ≤ y 1 ∧ y 1 < 1 := by
  have equal := circuit.deterministic axes x y _ admitted (circuit_behavior axes x)
  rw [equal]
  exact magnitude_range axes x

#print axioms wave_rewrite
#print axioms circuit_behavior
#print axioms circuit_magnitude_bound
end Gimle.Asgard.Examples.RealAtomics
