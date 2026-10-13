import Gimle.Asgard.Dynamics.Feedback
import Gimle.Asgard.Dynamics.LinearAnalysis
import Gimle.Asgard.Dynamics.LinearSyntax
import Mathlib.Algebra.BigOperators.Fin

/-! Explicit autonomous homogeneous rational linear ODE problems.
State coordinates and their initial values use the same finite ordered context.
Compilation and existence are separate statements. -/
namespace Gimle.Asgard.Dynamics.Linear

open Polynomial

abbrev Matrix (n : Nat) := Fin n → Fin n → ℚ

/-- A complete forward initial-value problem. Names are display metadata; the
finite index is the authoritative ordered coordinate in every component. -/
structure Problem (n : Nat) where
  names : Fin n → String
  matrix : Matrix n
  initial : Point n
  time : TimeDomain

noncomputable def Matrix.eval {n : Nat} (a : Matrix n) (x : Point n) : Point n :=
  fun i => ∑ j, (a i j : ℝ) * x j

private def sumExpressions {n : Nat} : List (Expr n) → Expr n
  | [] => .constant 0
  | e :: es => .add e (sumExpressions es)

private theorem sumExpressions_eval {n : Nat} (es : List (Expr n)) (x : Point n) :
    (sumExpressions es).eval x = (es.map (Expr.eval x)).sum := by
  induction es with
  | nil => simp [sumExpressions, Expr.eval]
  | cons e es ih => simp [sumExpressions, Expr.eval, ih]

/-- Each row is compiled by the general polynomial compiler, with exact scalars. -/
def Matrix.expression {n : Nat} (a : Matrix n) (i : Fin n) : Expr n :=
  sumExpressions (List.ofFn (fun j => .mul (.constant (a i j)) (.var j)))

@[simp] theorem Matrix.expression_eval {n : Nat} (a : Matrix n) (i : Fin n) (x : Point n) :
    (a.expression i).eval x = a.eval x i := by
  simp [expression, sumExpressions_eval, List.map_ofFn, List.sum_ofFn, Expr.eval, eval]

def Matrix.field {n : Nat} (a : Matrix n) : Gimle.Asgard.Circuit n n :=
  compileOutputs a.expression

@[simp] theorem Matrix.field_correct {n : Nat} (a : Matrix n) (x : Point n) :
    a.field.run x = a.eval x := by
  simp [field]

/-- Adapt the no-driver context using a proved route, without changing state order. -/
def Matrix.autonomousField {n : Nat} (a : Matrix n) : Gimle.Asgard.Circuit (0 + n) n :=
  .compose (route (fun i => Fin.natAdd 0 i)) a.field

@[simp] theorem Matrix.autonomousField_correct {n : Nat} (a : Matrix n)
    (u : Point 0) (x : Point n) :
    a.autonomousField.run (pointAppend u x) = a.eval x := by
  simp [autonomousField, Gimle.Asgard.Circuit.run, pointAppend]

/-- Ordered initial-state ports feed an integrator bank closed around the field. -/
def Problem.circuit {n : Nat} (p : Problem n) : Circuit (0 + n) n :=
  close (d := 0) p.time.axis p.matrix.autonomousField

/-- Source semantics mention the rational matrix, never the compiled circuit. -/
def Problem.Solves {n : Nat} (p : Problem n) (state : Signal n) : Prop :=
  state p.time.start = p.initial ∧
  ∀ t ∈ p.time.domain, ∀ i,
    HasDerivWithinAt (fun t => state t i) (p.matrix.eval (state t) i) p.time.domain t

private def noDrivers : Signal 0 := fun _ i => Fin.elim0 i

/-- Target semantics include the same time axis, start and ordered initial data. -/
def Problem.Realizes {n : Nat} (p : Problem n) (state : Signal n) : Prop :=
  p.circuit.Rel p.time (signalAppend noDrivers (fun _ => p.initial)) state

/-- This equivalence does not depend on, or assert, an existence theorem. -/
theorem Problem.solves_iff_realizes {n : Nat} (p : Problem n) (state : Signal n) :
    p.Solves state ↔ p.Realizes state := by
  unfold Problem.Realizes Problem.circuit
  rw [close_correct]
  simp only [Matrix.autonomousField_correct, true_and, Problem.Solves]

/-- The canonical solution is defined independently of compilation. -/
noncomputable def Problem.solution {n : Nat} (p : Problem n) : Signal n :=
  LinearAnalysis.solution (LinearAnalysis.rationalOperator p.matrix) p.time.start p.initial

theorem Problem.solution_solves {n : Nat} (p : Problem n) : p.Solves p.solution := by
  refine ⟨LinearAnalysis.solution_initial _ _ _, ?_⟩
  intro t _ i
  have h := (hasDerivAt_pi.mp (LinearAnalysis.solution_hasDerivAt
    (LinearAnalysis.rationalOperator p.matrix) p.time.start p.initial t)) i
  simpa only [Problem.solution, LinearAnalysis.rationalOperator_apply, Matrix.eval] using
    h.hasDerivWithinAt (s := p.time.domain)

/-- Global existence uses linear analysis, separately from trajectory preservation. -/
theorem Problem.exists_realization {n : Nat} (p : Problem n) :
    ∃ state, p.Realizes state :=
  ⟨p.solution, (p.solves_iff_realizes _).mp p.solution_solves⟩

/-- Any two solutions agree for every future time, including the initial instant. -/
theorem Problem.unique {n : Nat} (p : Problem n) {x y : Signal n}
    (hx : p.Solves x) (hy : p.Solves y) : Set.EqOn x y p.time.domain := by
  apply LinearAnalysis.unique_on (LinearAnalysis.rationalOperator p.matrix)
    p.time.start x y (hx.1.trans hy.1.symm)
  · simpa only [LinearAnalysis.rationalOperator_apply, Matrix.eval, TimeDomain.domain] using hx.2
  · simpa only [LinearAnalysis.rationalOperator_apply, Matrix.eval, TimeDomain.domain] using hy.2

theorem Problem.unique_realization {n : Nat} (p : Problem n) {x y : Signal n}
    (hx : p.Realizes x) (hy : p.Realizes y) : Set.EqOn x y p.time.domain :=
  p.unique ((p.solves_iff_realizes _).mpr hx) ((p.solves_iff_realizes _).mpr hy)

/-- Checked source expressions and a matrix problem have the same derivative
requirements whenever every row's exact coefficient extraction succeeds. -/
theorem Problem.solves_iff_expressions {n : Nat} (p : Problem n)
    (rhs : Fin n → Expr n)
    (accepted : ∀ i, LinearSyntax.coefficients (rhs i) = some (p.matrix i))
    (state : Signal n) : p.Solves state ↔
      state p.time.start = p.initial ∧ ∀ t ∈ p.time.domain, ∀ i,
        HasDerivWithinAt (fun t => state t i) ((rhs i).eval (state t)) p.time.domain t := by
  have equal (i : Fin n) (x : Point n) : (rhs i).eval x = p.matrix.eval x i :=
    LinearSyntax.coefficients_correct _ _ (accepted i) x
  simp only [equal, Problem.Solves]

#print axioms Problem.solves_iff_realizes
#print axioms Problem.solution_solves
#print axioms Problem.exists_realization
#print axioms Problem.unique_realization
#print axioms Problem.solves_iff_expressions

end Gimle.Asgard.Dynamics.Linear
