import Gimle.Asgard.Examples.EnergyDemo
import Gimle.Asgard.Examples.Oscillator

/-!
Feasibility example: a compiler proved correct for every polynomial expression
in the fixed ordered context [x,y]. This uses the existing real feedforward
Asgard circuit fragment, not the Python equation parser or numerical runtime.
The source evaluator is defined independently of compilation.
-/
namespace Gimle.Asgard.VerifiedTranslation

/-- Polynomial source expressions. Variables refer to the ordered input [x,y]. -/
inductive Expr where
  | var (coordinate : Fin 2)
  | constant (value : ℚ)
  | add (left right : Expr)
  | mul (left right : Expr)
  | neg (argument : Expr)

/-- Mathematical meaning of the source language, independent of circuits. -/
noncomputable def Expr.eval (input : Point 2) : Expr → ℝ
  | .var coordinate => input coordinate
  | .constant value => value
  | .add left right => left.eval input + right.eval input
  | .mul left right => left.eval input * right.eval input
  | .neg argument => -argument.eval input

/-- Both branches of a binary expression receive the SAME [x,y] environment. -/
def copyInputs : Circuit 2 4 :=
  .compose EnergyDemo.duplicate EnergyDemo.interleave

theorem copyInputs_correct (input : Point 2) :
    copyInputs.run input = pointAppend input input := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [copyInputs, EnergyDemo.duplicate, EnergyDemo.interleave,
      Circuit.run, pointAppend, pointLeft, pointRight]

/-- Compile two outputs while explicitly sharing the ordered input environment. -/
def pair (left right : Circuit 2 1) : Circuit 2 2 :=
  .compose copyInputs (.parallel left right)

theorem pair_correct (left right : Circuit 2 1) (input : Point 2) :
    (pair left right).run input = ![left.run input 0, right.run input 0] := by
  simp only [pair, Circuit.run, copyInputs_correct,
    pointLeft_pointAppend, pointRight_pointAppend]
  funext coordinate
  fin_cases coordinate <;> simp [pointAppend]

/-- A total structural compiler into the existing primitive circuit vocabulary. -/
def Expr.compile : Expr → Circuit 2 1
  | .var coordinate =>
      if coordinate = 0 then .parallel .id .terminal else .parallel .terminal .id
  | .constant value => .compose (.parallel .terminal .terminal) (.const value)
  | .add left right => .compose (pair left.compile right.compile) .add
  | .mul left right => .compose (pair left.compile right.compile) .multiplication
  | .neg argument => .compose argument.compile (.scalar (-1))

/-- The compiler preserves meaning for EVERY expression and EVERY real input. -/
theorem compile_correct (expression : Expr) (input : Point 2) :
    expression.compile.run input 0 = expression.eval input := by
  induction expression with
  | var coordinate =>
      fin_cases coordinate <;>
        simp [Expr.compile, Expr.eval, Circuit.run, pointAppend, pointLeft, pointRight]
  | constant value => simp [Expr.compile, Expr.eval, Circuit.run]
  | add left right leftCorrect rightCorrect =>
      simp [Expr.compile, Expr.eval, pair_correct, leftCorrect, rightCorrect]
  | mul left right leftCorrect rightCorrect =>
      simp [Expr.compile, Expr.eval, pair_correct, leftCorrect, rightCorrect]
  | neg argument argumentCorrect =>
      simp [Expr.compile, Expr.eval, argumentCorrect]

/-- Equality of two expressions is preserved as a relation, without solving it. -/
theorem equation_correct (left right : Expr) (input : Point 2) :
    left.compile.run input 0 = right.compile.run input 0 ↔
      left.eval input = right.eval input := by
  rw [compile_correct, compile_correct]

def x : Expr := .var 0
def y : Expr := .var 1

def square (expression : Expr) : Expr := .mul expression expression

-- E(x,y) = (x+y)^2 + (x-y)^2, written in the source language.
def energyExpression : Expr :=
  .add (square (.add x y)) (square (.add x (.neg y)))

-- The compiled result has the same behavior as the existing Asgard energy circuit.
theorem energy_matches (input : Point 2) :
    energyExpression.compile.run input 0 = EnergyDemo.energy.run input 0 := by
  rw [compile_correct, EnergyDemo.energyIdentity]
  simp only [energyExpression, square, x, y, Expr.eval]
  ring

-- Exact fractions, unused inputs and repeated variables all belong to the language.
example (input : Point 2) :
    (Expr.constant (1 / 3)).compile.run input 0 = (1 / 3 : ℝ) := by
  rw [compile_correct]
  norm_num [Expr.eval]

example (input : Point 2) :
    (Expr.add x x).compile.run input 0 = 2 * input 0 := by
  rw [compile_correct]
  simp [Expr.eval, x]
  ring

-- An asymmetric expression checks which coordinate is x and which is y.
example : (Expr.add x (.neg y)).compile.run ![2, 5] 0 = -3 := by
  rw [compile_correct]
  norm_num [Expr.eval, x, y]

-- Compile BOTH oscillator RHS expressions using the same [x,y] input context.
def oscillatorField : Circuit 2 2 :=
  pair y.compile (Expr.add (.neg x) (.neg (.mul (.constant 2) y))).compile

theorem oscillatorField_equations (input : Point 2) :
    oscillatorField.run input = ![input 1, -input 0 - 2 * input 1] := by
  simp [oscillatorField, pair_correct, compile_correct, Expr.eval, x, y, sub_eq_add_neg]

/-- Circuit trajectory semantics for the generated field, on the same ℝ domain. -/
def CompiledSolves (position velocity : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt position (oscillatorField.run ![position t, velocity t] 0) t ∧
    HasDerivAt velocity (oscillatorField.run ![position t, velocity t] 1) t

/-- Translation preserves the existing oscillator's FULL solution predicate. -/
theorem oscillator_solutions_iff (position velocity : ℝ → ℝ) :
    CompiledSolves position velocity ↔ Oscillator.Solves position velocity := by
  rw [Oscillator.solvesEquations]
  simp [CompiledSolves, oscillatorField_equations]

/-- Initial values are preserved too; no existence assumption is hidden here. -/
theorem oscillator_initial_solutions_iff
    (position velocity : ℝ → ℝ) (initialX initialY : ℝ) :
    (CompiledSolves position velocity ∧ position 0 = initialX ∧ velocity 0 = initialY) ↔
      (Oscillator.Solves position velocity ∧ position 0 = initialX ∧ velocity 0 = initialY) := by
  rw [oscillator_solutions_iff]

-- Existence comes from the separate explicit-solution proof, not from compilation.
theorem compiled_explicit_solution (initialX initialY : ℝ) :
    CompiledSolves (Oscillator.position initialX initialY) (Oscillator.velocity initialX initialY) :=
  (oscillator_solutions_iff _ _).mpr (Oscillator.explicitSolution initialX initialY)

-- A concrete negative check: addition cannot implement multiplication.
theorem wrong_multiplication_rejected :
    (Circuit.compose (pair x.compile y.compile) Circuit.add).run ![2, 3] 0 ≠
      (Expr.mul x y).eval ![2, 3] := by
  norm_num [pair_correct, compile_correct, Expr.eval, x, y]

#print axioms compile_correct
#print axioms equation_correct
#print axioms energy_matches
#print axioms oscillator_initial_solutions_iff
#print axioms compiled_explicit_solution
#print axioms wrong_multiplication_rejected

end Gimle.Asgard.VerifiedTranslation
