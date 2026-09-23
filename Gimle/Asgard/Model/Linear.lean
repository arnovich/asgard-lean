import Gimle.Asgard.Model.Continuous

/-! Optional homogeneous-linear analysis of the ORIGINAL compiled RHS. Exact
constant arithmetic is folded for recognition, with its own preservation lemma. -/
namespace Gimle.Asgard.Model
open Polynomial

private def constantAdd {n : Nat} (a b : Expr n) : Expr n :=
  match a, b with
  | .constant q, .constant r => .constant (q + r)
  | _, _ => .add a b
private def constantMul {n : Nat} (a b : Expr n) : Expr n :=
  match a, b with
  | .constant q, .constant r => .constant (q * r)
  | _, _ => .mul a b
private def constantNeg {n : Nat} (a : Expr n) : Expr n :=
  match a with
  | .constant q => .constant (-q)
  | _ => .neg a

private theorem constantAdd_eval {n : Nat} (a b : Expr n) (x : Point n) :
    (constantAdd a b).eval x = a.eval x + b.eval x := by
  cases a <;> cases b <;> simp [constantAdd, Expr.eval]
private theorem constantMul_eval {n : Nat} (a b : Expr n) (x : Point n) :
    (constantMul a b).eval x = a.eval x * b.eval x := by
  cases a <;> cases b <;> simp [constantMul, Expr.eval]
private theorem constantNeg_eval {n : Nat} (a : Expr n) (x : Point n) :
    (constantNeg a).eval x = -(a.eval x) := by
  cases a <;> simp [constantNeg, Expr.eval]

def foldConstants {n : Nat} : Expr n → Expr n
  | .var i => .var i
  | .constant q => .constant q
  | .add a b => constantAdd (foldConstants a) (foldConstants b)
  | .mul a b => constantMul (foldConstants a) (foldConstants b)
  | .neg a => constantNeg (foldConstants a)

theorem foldConstants_correct {n : Nat} (e : Expr n) (x : Point n) :
    (foldConstants e).eval x = e.eval x := by
  induction e <;> simp_all [foldConstants, Expr.eval,
    constantAdd_eval, constantMul_eval, constantNeg_eval]

structure LinearView {b : Body} {e : Evolution} (p : ContinuousModel b e) where
  matrix : Dynamics.Linear.Matrix e.states.length
  accepted : ∀ i, Dynamics.LinearSyntax.coefficients (foldConstants (p.rates.expressions i)) =
    some (matrix i)

/-- Failure means this recognizer did not establish homogeneous linearity.
The already compiled polynomial model and its correspondence remain available. -/
def ContinuousModel.linear {b : Body} {e : Evolution} (p : ContinuousModel b e) :
    Option (LinearView p) :=
  match h : Dynamics.resolveTable (fun i =>
      Dynamics.LinearSyntax.coefficients (foldConstants (p.rates.expressions i))) with
  | none => none
  | some matrix => some ⟨matrix, Dynamics.resolveTable_correct _ _ h⟩

noncomputable def LinearView.problem {b : Body} {e : Evolution} {p : ContinuousModel b e}
    (linear : LinearView p) : Dynamics.Linear.Problem e.states.length := {
  names := e.stateIds
  matrix := linear.matrix
  initial := p.initial
  time := e.time
}

theorem LinearView.rhs_correct {b : Body} {e : Evolution} {p : ContinuousModel b e}
    (linear : LinearView p) (x : Point e.states.length) (i : Fin e.states.length) :
    (p.rates.expressions i).eval x = linear.matrix.eval x i := by
  rw [← foldConstants_correct (p.rates.expressions i) x]
  exact Dynamics.LinearSyntax.coefficients_correct _ _ (linear.accepted i) x

/-- Analysis is connected to the original RHS; feedback does not use a replacement
matrix circuit. Recognizer acceptance is an explicit hypothesis of every result. -/
theorem LinearView.source_iff {b : Body} {e : Evolution} {p : ContinuousModel b e}
    (linear : LinearView p) (state : Dynamics.Signal e.states.length) :
    b.Solves e state ↔ linear.problem.Solves state := by
  rw [p.solves_iff_field]
  simp only [linear.rhs_correct, Dynamics.Linear.Problem.Solves, problem]

theorem LinearView.exists_realization {b : Body} {e : Evolution} {p : ContinuousModel b e}
    (linear : LinearView p) : ∃ state, p.Realizes state := by
  refine ⟨linear.problem.solution, (p.solves_iff_realizes _).mp ?_⟩
  exact (linear.source_iff _).mpr linear.problem.solution_solves

theorem LinearView.unique_realization {b : Body} {e : Evolution} {p : ContinuousModel b e}
    (linear : LinearView p) {x y : Dynamics.Signal e.states.length}
    (hx : p.Realizes x) (hy : p.Realizes y) : Set.EqOn x y e.time.domain := by
  exact linear.problem.unique
    ((linear.source_iff _).mp ((p.solves_iff_realizes _).mpr hx))
    ((linear.source_iff _).mp ((p.solves_iff_realizes _).mpr hy))

#print axioms foldConstants_correct
#print axioms LinearView.rhs_correct
#print axioms LinearView.exists_realization
#print axioms LinearView.unique_realization
end Gimle.Asgard.Model
