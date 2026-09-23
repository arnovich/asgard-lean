import Gimle.Asgard.Algebraic

/-! Executable construction of the eliminated typed circuits from exact rational
source equations. The supplied inverse must carry checked product equations. -/
namespace Gimle.Asgard.Algebraic
open Polynomial Matrix

/-- Simultaneous equations z=M z+b(u), and ordered affine observable outputs. -/
structure Problem (n d o : Nat) where
  matrix : RationalMatrix n n
  offset : Affine d n
  output : Affine (n + d) o

def Problem.loopAffine {n d o : Nat} (p : Problem n d o) : Affine (n + d) n where
  coefficients := fun i => Fin.addCases (p.matrix i) (p.offset.coefficients i)
  constant := p.offset.constant

@[simp] theorem Problem.loop_correct {n d o : Nat} (p : Problem n d o)
    (z : Point n) (u : Point d) :
    p.loopAffine.circuit.run (pointAppend z u) = realMatrix p.matrix *ᵥ z + p.offset.eval u := by
  rw [Affine.circuit_correct]
  funext i
  simp [loopAffine, Affine.eval, realMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_add, pointAppend]
  ring

private def sumExpressions {d : Nat} : List (Expr d) → Expr d
  | [] => .constant 0
  | e :: es => .add e (sumExpressions es)

private theorem sumExpressions_eval {d : Nat} (es : List (Expr d)) (u : Point d) :
    (sumExpressions es).eval u = (es.map (Expr.eval u)).sum := by
  induction es with
  | nil => simp [sumExpressions, Expr.eval]
  | cons e es ih => simp [sumExpressions, Expr.eval, ih]

/-- Rational inverse multiplication is compiled as exact sums and products. -/
def Problem.solutionExpression {n d o : Nat} (p : Problem n d o)
    (inverse : RationalMatrix n n) (i : Fin n) : Expr d :=
  sumExpressions (List.ofFn (fun j => .mul (.constant (inverse i j)) (p.offset.expression j)))

@[simp] theorem Problem.solutionExpression_correct {n d o : Nat} (p : Problem n d o)
    (inverse : RationalMatrix n n) (i : Fin n) (u : Point d) :
    (p.solutionExpression inverse i).eval u = (realMatrix inverse *ᵥ p.offset.eval u) i := by
  simp [solutionExpression, sumExpressions_eval, List.map_ofFn, List.sum_ofFn,
    Expr.eval, realMatrix, Matrix.mulVec, dotProduct]

def Problem.solutionCircuit {n d o : Nat} (p : Problem n d o)
    (inverse : RationalMatrix n n) : Circuit d n :=
  compileOutputs (p.solutionExpression inverse)

@[simp] theorem Problem.solution_correct {n d o : Nat} (p : Problem n d o)
    (inverse : RationalMatrix n n) (u : Point d) :
    (p.solutionCircuit inverse).run u = realMatrix inverse *ᵥ p.offset.eval u := by
  simp [solutionCircuit]

/-- Preserve the external vector while wiring all eliminated loop coordinates. -/
def Problem.eliminatedCircuit {n d o : Nat} (p : Problem n d o)
    (inverse : RationalMatrix n n) : Circuit d o :=
  .compose (compileOutputs (Fin.addCases (p.solutionExpression inverse) Expr.var)) p.output.circuit

@[simp] theorem Problem.output_correct {n d o : Nat} (p : Problem n d o)
    (inverse : RationalMatrix n n) (u : Point d) :
    (p.eliminatedCircuit inverse).run u =
      p.output.circuit.run (pointAppend ((p.solutionCircuit inverse).run u) u) := by
  simp only [eliminatedCircuit, Circuit.run, compileOutputs_correct, solution_correct]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [pointAppend]
  · intro j
    simp [pointAppend, Expr.eval]

/-- Verified equation-to-feedforward translation: no external solver or iteration
is trusted. Domain membership is an explicit obligation for every admitted input. -/
theorem Problem.eliminate_correct {n d o : Nat} (p : Problem n d o)
    (inverse : Inverse p.matrix) (domain : Point n → Prop) (admitted : Point d → Prop)
    (membership : ∀ u, admitted u → domain ((p.solutionCircuit inverse.value).run u))
    (u : Point d) (hu : admitted u) :
    (∃! z, domain z ∧ p.loopAffine.circuit.run (pointAppend z u) = z) ∧
    ∀ y, Rel p.loopAffine.circuit p.output.circuit domain u y ↔
      y = (p.eliminatedCircuit inverse.value).run u :=
  elimination_correct p.loopAffine.circuit p.output.circuit (p.solutionCircuit inverse.value)
    (p.eliminatedCircuit inverse.value) domain admitted p.matrix inverse p.offset.eval
    p.loop_correct (p.solution_correct _) (fun u => (p.output_correct _ u).symm)
    membership u hu

#print axioms Problem.loop_correct
#print axioms Problem.solution_correct
#print axioms Problem.output_correct
#print axioms Problem.eliminate_correct
end Gimle.Asgard.Algebraic
