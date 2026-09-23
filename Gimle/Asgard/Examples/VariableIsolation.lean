import Gimle.Asgard.Compile.Isolation

/-! Isolate the middle variable without changing the order of its neighbours.
The equation is 2*z + u = z + 3*v, so z = 3*v - u.
For u(t)=t and v(t)=2*t+1, the solution is z(t)=5*t+3, with z(0)=3.
This is pointwise algebraic elimination, not differentiation or ODE solving. -/
namespace Gimle.Asgard.Examples.VariableIsolation
open Polynomial Normalization Isolation

/-- Original coordinate order is [u,z,v]. The selected coordinate occurs on
both sides. The right side also includes a beta-reducible application (λw.3*w) v. -/
def equation : Equation 2 where
  lhs := .add (.mul (.constant 2) (.var 1)) (.var 0)
  rhs := .add (.var 1) (.apply (.mul (.constant 3) (.var 0)) (.var 2))

/-- Explicitly select z while retaining the remaining order [u,v]. -/
def order : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def prepared : Prepared equation order := (equation.prepare order).get (by decide)

theorem valuation (u v z : ℝ) : reconstruct order ![u,v] z = ![u,z,v] := by
  funext i
  fin_cases i <;> simp [reconstruct, order, Equiv.swap_apply_def]

theorem coefficient (u v : ℝ) : prepared.coefficient.eval ![u,v] = 1 := by
  rw [Decomposition.coefficient_correct, Equation.residual_correct, Equation.residual_correct,
    valuation, valuation]
  simp [equation, Source.eval]
  ring

theorem offset (u v : ℝ) : prepared.offset.eval ![u,v] = u - 3*v := by
  rw [Decomposition.offset_correct, Equation.residual_correct, valuation]
  simp [equation, Source.eval]

def circuit : Circuit 2 1 := (prepared.solution (.constant 1)).compile

theorem circuit_value (u v : ℝ) : circuit.run ![u,v] 0 = 3*v-u := by
  simp [circuit, Decomposition.solution_correct, offset, Expr.eval]

/-- The compiled solution preserves both directions of the source equation and
any additional constraint on the original [u,z,v] valuation. -/
theorem preserves (u v z : ℝ) (constraint : Point 3 → Prop) :
    (equation.Satisfies ![u,z,v] ∧ constraint ![u,z,v]) ↔
      z = circuit.run ![u,v] 0 ∧ constraint ![u,circuit.run ![u,v] 0,v] := by
  have valid : prepared.coefficient.eval ![u,v] * (Expr.constant 1).eval ![u,v] = 1 := by
    rw [coefficient]
    norm_num [Expr.eval]
  simpa only [valuation, circuit] using
    prepared.solution_iff (.constant 1) ![u,v] valid constraint z

/-- Initial data is retained as an explicit constraint on the full trajectory. -/
theorem initialized_family (z : ℝ → ℝ) :
    ((∀ t, equation.Satisfies ![t,z t,2*t+1]) ∧ z 0 = 3) ↔
      z = fun t => 5*t+3 := by
  have valid (t : ℝ) : prepared.coefficient.eval ![t,2*t+1] *
      (Expr.constant 1).eval ![t,2*t+1] = 1 := by
    rw [coefficient]
    norm_num [Expr.eval]
  have h := prepared.family_iff (.constant 1) (fun t : ℝ => ![t,2*t+1])
    valid (fun path => path 0 1 = 3) z
  have values : (fun t : ℝ => circuit.run ![t,2*t+1] 0) = fun t => 5*t+3 := by
    funext t
    rw [circuit_value]
    ring
  change ((∀ t, equation.Satisfies (reconstruct order ![t,2*t+1] (z t))) ∧
      (reconstruct order ![0,2*0+1] (z 0)) 1 = 3) ↔
    z = (fun t => circuit.run ![t,2*t+1] 0) ∧
      (reconstruct order ![0,2*0+1] (circuit.run ![0,2*0+1] 0)) 1 = 3 at h
  simp only [valuation, Matrix.cons_val] at h
  rw [values] at h
  norm_num [circuit_value] at h
  exact h

#print axioms preserves
#print axioms initialized_family
end Gimle.Asgard.Examples.VariableIsolation
