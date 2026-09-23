import Gimle.Asgard.Compile.Polynomial
import Mathlib.Data.Matrix.Basic

/-! Stateless real algebraic feedback. No time, delay, iteration or integrator.
The finite coordinate order is [loop, external]; external may pack inputs and
fixed parameters. Exact rational affine compilation preserves solution sets. -/
namespace Gimle.Asgard.Algebraic
open Polynomial Matrix

def semanticId : String := "asgard.algebraic.real.affine.v1"

/-- The declared loop domain is part of the relation, even for invertible loops. -/
def Rel {n d o : Nat} (loop : Circuit (n + d) n) (output : Circuit (n + d) o)
    (domain : Point n → Prop) (u : Point d) (y : Point o) : Prop :=
  ∃ z, domain z ∧ loop.run (pointAppend z u) = z ∧ output.run (pointAppend z u) = y

/-- Independent ordered source equations, before compiling any circuit. -/
def Solves {n d o : Nat} (rhs : Fin n → Expr (n + d))
    (output : Fin o → Expr (n + d)) (domain : Point n → Prop)
    (u : Point d) (y : Point o) : Prop :=
  ∃ z, domain z ∧ (∀ i, (rhs i).eval (pointAppend z u) = z i) ∧
    (∀ i, (output i).eval (pointAppend z u) = y i)

/-- Acyclic polynomial compilation changes neither hidden nor observable solutions.
This theorem deliberately makes no existence or uniqueness assertion. -/
theorem compile_correct {n d o : Nat} (rhs : Fin n → Expr (n + d))
    (output : Fin o → Expr (n + d)) (domain : Point n → Prop)
    (u : Point d) (y : Point o) :
    Solves rhs output domain u y ↔
      Rel (compileOutputs rhs) (compileOutputs output) domain u y := by
  simp only [Solves, Rel, compileOutputs_correct, funext_iff]

abbrev RationalMatrix (m n : Nat) := Matrix (Fin m) (Fin n) ℚ

noncomputable def realMatrix {m n : Nat} (a : RationalMatrix m n) :
    Matrix (Fin m) (Fin n) ℝ := a.map (fun q => (q : ℝ))

/-- Exact affine rows are compiled using the established polynomial compiler. -/
structure Affine (d n : Nat) where
  coefficients : RationalMatrix n d
  constant : Fin n → ℚ

private def sumExpr {d : Nat} : List (Expr d) → Expr d
  | [] => .constant 0
  | e :: es => .add e (sumExpr es)

private theorem sumExpr_eval {d : Nat} (es : List (Expr d)) (u : Point d) :
    (sumExpr es).eval u = (es.map (Expr.eval u)).sum := by
  induction es with
  | nil => simp [sumExpr, Expr.eval]
  | cons e es ih => simp [sumExpr, Expr.eval, ih]

def Affine.expression {d n : Nat} (a : Affine d n) (i : Fin n) : Expr d :=
  .add (.constant (a.constant i)) (sumExpr (List.ofFn
    (fun j => .mul (.constant (a.coefficients i j)) (.var j))))

noncomputable def Affine.eval {d n : Nat} (a : Affine d n) (u : Point d) : Point n :=
  (fun i => (a.constant i : ℝ)) + realMatrix a.coefficients *ᵥ u

@[simp] theorem Affine.expression_eval {d n : Nat} (a : Affine d n)
    (i : Fin n) (u : Point d) : (a.expression i).eval u = a.eval u i := by
  simp [expression, sumExpr_eval, List.map_ofFn, List.sum_ofFn, Expr.eval,
    eval, realMatrix, Matrix.mulVec, dotProduct]

def Affine.circuit {d n : Nat} (a : Affine d n) : Circuit d n :=
  compileOutputs a.expression

@[simp] theorem Affine.circuit_correct {d n : Nat} (a : Affine d n) (u : Point d) :
    a.circuit.run u = a.eval u := by simp [circuit]

/-- A supplied rational inverse is evidence only when both products are checked. -/
structure Inverse {n : Nat} (matrix : RationalMatrix n n) where
  value : RationalMatrix n n
  left : value * (1 - matrix) = 1
  right : (1 - matrix) * value = 1

private theorem realMatrix_mul {m n k : Nat} (a : RationalMatrix m n)
    (b : RationalMatrix n k) : realMatrix (a * b) = realMatrix a * realMatrix b := by
  ext i j
  simp [realMatrix, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul]

private theorem realMatrix_one {n : Nat} : realMatrix (1 : RationalMatrix n n) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [realMatrix, Matrix.one_apply, h]

private theorem realMatrix_sub {m n : Nat} (a b : RationalMatrix m n) :
    realMatrix (a - b) = realMatrix a - realMatrix b := by
  ext i j
  simp [realMatrix]

/-- This equivalence establishes the entire ambient solution set, not just a
chosen fixed point. Domain membership is handled separately below. -/
theorem fixedPoint_iff {n : Nat} (m : RationalMatrix n n) (inv : Inverse m)
    (b z : Point n) : realMatrix m *ᵥ z + b = z ↔ z = realMatrix inv.value *ᵥ b := by
  have hl : realMatrix inv.value * (1 - realMatrix m) = 1 := by
    rw [← realMatrix_one, ← realMatrix_sub, ← realMatrix_mul, inv.left]
  have hr : (1 - realMatrix m) * realMatrix inv.value = 1 := by
    rw [← realMatrix_one, ← realMatrix_sub, ← realMatrix_mul, inv.right]
  have rearrange : realMatrix m *ᵥ z + b = z ↔ (1 - realMatrix m) *ᵥ z = b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    constructor <;> intro h <;> funext i
    · have hi := congrFun h i
      change z i - (realMatrix m *ᵥ z) i = b i
      change (realMatrix m *ᵥ z) i + b i = z i at hi
      linarith
    · have hi := congrFun h i
      change (realMatrix m *ᵥ z) i + b i = z i
      change z i - (realMatrix m *ᵥ z) i = b i at hi
      linarith
  rw [rearrange]
  constructor
  · intro h
    have := congrArg (fun x => realMatrix inv.value *ᵥ x) h
    simpa only [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec] using this
  · intro h
    rw [h, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]

/-- Elimination relative to original typed circuits. All original solutions are
retained; membership is required before claiming a total deterministic output. -/
theorem elimination_correct {n d o : Nat} (loop : Circuit (n + d) n)
    (output : Circuit (n + d) o) (solution : Circuit d n) (eliminated : Circuit d o)
    (domain : Point n → Prop) (admitted : Point d → Prop)
    (m : RationalMatrix n n) (inv : Inverse m) (offset : Point d → Point n)
    (loop_eq : ∀ z u, loop.run (pointAppend z u) = realMatrix m *ᵥ z + offset u)
    (solution_eq : ∀ u, solution.run u = realMatrix inv.value *ᵥ offset u)
    (output_eq : ∀ u, output.run (pointAppend (solution.run u) u) = eliminated.run u)
    (membership : ∀ u, admitted u → domain (solution.run u))
    (u : Point d) (hu : admitted u) :
    (∃! z, domain z ∧ loop.run (pointAppend z u) = z) ∧
      ∀ y, Rel loop output domain u y ↔ y = eliminated.run u := by
  have unique (z : Point n) : loop.run (pointAppend z u) = z ↔ z = solution.run u := by
    rw [loop_eq, fixedPoint_iff, solution_eq]
  refine ⟨⟨solution.run u, ⟨membership u hu, (unique _).mpr rfl⟩,
    fun z hz => (unique z).mp hz.2⟩, ?_⟩
  intro y
  constructor
  · rintro ⟨z, _, hz, hy⟩
    rw [(unique z).mp hz, output_eq] at hy
    exact hy.symm
  · intro hy
    exact ⟨solution.run u, membership u hu, (unique _).mpr rfl,
      (output_eq u).trans hy.symm⟩

#print axioms compile_correct
#print axioms Affine.circuit_correct
#print axioms fixedPoint_iff
#print axioms elimination_correct
end Gimle.Asgard.Algebraic
