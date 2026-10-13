import Gimle.Asgard.Compile.Syntax
import Gimle.Asgard.Compile.Interchange
import Gimle.Asgard.Examples.EnergyDemo
import Gimle.Asgard.Examples.Oscillator

/-! Editable equations compiled to primitive circuits, with universal real
correctness proofs. Open this file in VS Code and inspect the AST definitions. -/
namespace Gimle.Asgard.Examples.PolynomialCompiler
open Polynomial

def inputs : List Port := [⟨"state-x", "x", .state⟩, ⟨"state-y", "y", .state⟩]

/-- Every assignment output is retained, in the declared order [s,d,energy]. -/
def energyProgram : Program := {
  inputs := inputs
  assignments := equations% {
    s := x + y;
    d := x - y;
    energy := s ^ 2 + d ^ 2;
  }
}

/-- Resolution is executable and contains no arithmetic proof tactic. -/
def energyExpressions : List (Expr 2) := energyProgram.resolve.get (by decide)

def energyCircuit : Circuit 2 3 := compileList energyExpressions

theorem energy_resolved : energyProgram.resolve = some energyExpressions := by decide

/-- The named source equations and all three compiled outputs have identical solutions. -/
theorem energy_satisfaction (x : Point 2) (outputs : List ℝ) :
    energyProgram.Satisfies x outputs ↔ List.ofFn (energyCircuit.run x) = outputs :=
  energyProgram.satisfies_iff_compiled energyExpressions energy_resolved x outputs

/-- E(x,y) = (x+y)² + (x-y)² = 2x²+2y² for every real input. -/
theorem energy_identity (x : Point 2) :
    energyCircuit.run x 2 = 2 * x 0 ^ 2 + 2 * x 1 ^ 2 := by
  rw [show energyCircuit = compileOutputs (fun i => energyExpressions[i]) from rfl,
    compileOutputs_correct]
  have ast : energyExpressions[2] =
      Expr.add
        (.mul (.mul (.constant 1) (.add (.var 0) (.var 1))) (.add (.var 0) (.var 1)))
        (.mul (.mul (.constant 1) (.add (.var 0) (.neg (.var 1)))) (.add (.var 0) (.neg (.var 1)))) := by decide
  change Expr.eval x energyExpressions[2] = _
  rw [ast]
  simp only [Expr.eval, Rat.cast_one, one_mul]
  ring

theorem energy_matches (x : Point 2) :
    energyCircuit.run x 2 = EnergyDemo.energy.run x 0 := by
  rw [energy_identity, EnergyDemo.energyIdentity]

/-- Only the two vector-field RHS values are compiled here, not an integrator. -/
def oscillatorProgram : Program := {
  inputs := inputs
  assignments := equations% {
    dx := y;
    dy := -x - 2 * y;
  }
}

def oscillatorExpressions : List (Expr 2) := oscillatorProgram.resolve.get (by decide)
def oscillatorCircuit : Circuit 2 2 := compileList oscillatorExpressions

theorem oscillator_equations (x : Point 2) :
    oscillatorCircuit.run x = ![x 1, -x 0 - 2 * x 1] := by
  rw [show oscillatorCircuit = compileOutputs (fun i => oscillatorExpressions[i]) from rfl,
    compileOutputs_correct]
  have ast : oscillatorExpressions =
      [Expr.var 1, .add (.neg (.var 0)) (.neg (.mul (.constant 2) (.var 1)))] := by decide
  funext i
  fin_cases i <;> simp [ast, Expr.eval, sub_eq_add_neg]

/-- An incorrect damping sign disagrees with the equations at a concrete input. -/
theorem changed_damping_rejected :
    oscillatorCircuit.run ![0, 1] 1 ≠ (1 : ℝ) * 2 := by
  rw [oscillator_equations]
  norm_num

def energyExport : Except String Lean.Json :=
  Interchange.exportPython energyCircuit inputs (energyProgram.assignments.map Assignment.output)

def oscillatorExport : Except String Lean.Json :=
  Interchange.exportPython oscillatorCircuit inputs (oscillatorProgram.assignments.map Assignment.output)

#print axioms energy_satisfaction
#print axioms energy_identity
#print axioms oscillator_equations
#print axioms changed_damping_rejected

end Gimle.Asgard.Examples.PolynomialCompiler
