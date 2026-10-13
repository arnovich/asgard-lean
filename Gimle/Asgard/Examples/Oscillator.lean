import Gimle.Asgard.Examples.EnergyDemo
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Both ODE equations are modeled using the circuit vector field:
x′ = y and y′ = -x - 2y. Trajectories live on ℝ. This explicit solution model
does not add a primitive circuit trace or claim numerical integration accuracy. -/

namespace Gimle.Asgard.Oscillator

-- Duplicate (x,y) into (x,y,x,y); select y and calculate -x-2y.
def vectorField : Circuit 2 2 :=
  .compose (.compose EnergyDemo.duplicate EnergyDemo.interleave)
    (.parallel (.parallel .terminal .id)
      (.compose (.parallel (.scalar (-1)) (.scalar (-2))) .add))

theorem vectorFieldEquations (x y : ℝ) :
    vectorField.run ![x, y] = ![y, -x - 2*y] := by
  funext coordinate
  fin_cases coordinate <;>
    dsimp [vectorField, EnergyDemo.duplicate, EnergyDemo.interleave,
      Circuit.run, pointLeft, pointRight, pointAppend]
  norm_num
  ring

-- The derivative is the output of the actual circuit evaluated at the current state.
def Solves (x y : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt x (vectorField.run ![x t, y t] 0) t ∧
    HasDerivAt y (vectorField.run ![x t, y t] 1) t

theorem solvesEquations (x y : ℝ → ℝ) :
    Solves x y ↔ ∀ t, HasDerivAt x (y t) t ∧ HasDerivAt y (-x t - 2*y t) t := by
  simp [Solves, vectorFieldEquations]

-- Explicit solutions exist for EVERY real initial position and velocity.
-- These formulas avoid making the safety statement conditional on an empty class.
noncomputable def position (x₀ y₀ t : ℝ) : ℝ :=
  (x₀ + (x₀+y₀)*t) * Real.exp (-t)

noncomputable def velocity (x₀ y₀ t : ℝ) : ℝ :=
  (y₀ - (x₀+y₀)*t) * Real.exp (-t)

theorem explicitSolution (x₀ y₀ : ℝ) : Solves (position x₀ y₀) (velocity x₀ y₀) := by
  rw [solvesEquations]
  intro t
  have exponential := (hasDerivAt_id t).neg.exp
  have linear := (hasDerivAt_id t).const_mul (x₀+y₀)
  constructor
  · have derivative := (linear.const_add x₀).mul exponential
    dsimp only [position, velocity]
    convert! derivative using 1
    simp only [Pi.neg_apply, id_eq]
    ring
  · have derivative := (linear.const_sub y₀).mul exponential
    dsimp only [position, velocity]
    convert! derivative using 1
    simp only [Pi.neg_apply, id_eq]
    ring

theorem initialState (x₀ y₀ : ℝ) : position x₀ y₀ 0 = x₀ ∧ velocity x₀ y₀ 0 = y₀ := by
  simp [position, velocity]


#print axioms explicitSolution
#print axioms initialState

end Gimle.Asgard.Oscillator
