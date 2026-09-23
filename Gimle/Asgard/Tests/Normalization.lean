import Gimle.Asgard.Compile.Normalization
import Gimle.Asgard.Compile.Isolation
import Gimle.Asgard.Examples.VariableIsolation

namespace Gimle.Asgard.Tests.Normalization
open Polynomial Gimle.Asgard.Normalization Isolation

/-- (λx. (λy. x+y) u) 3: the free u must not be captured by either binder. -/
def nested : Source 1 :=
  .apply (.apply (.add (.var 1) (.var 0)) (.var 1)) (.constant 3)

example (u : ℝ) : nested.compile.run ![u] 0 = 3 + u := by
  rw [Source.compile_correct]
  simp [nested, Source.eval]

/-- The inner zero coordinate is a distinct binder, even when displayed with
the same name: (λx. (λx. x) 7) 3 = 7. -/
example : (Source.apply (.apply (.var 0) (.constant 7)) (.constant 3) :
    Source 0).normalize = Expr.constant 7 := by decide

example : (Source.apply (.constant 5) (.var 0) : Source 1).normalize =
    Expr.constant 5 := by decide

/-- An argument depending on two free variables retains their asymmetric order. -/
def twoFree : Source 2 :=
  .apply (.add (.var 0) (.var 2)) (.add (.var 0) (.mul (.constant 2) (.var 1)))

example (u v : ℝ) : twoFree.compile.run ![u,v] 0 = u + 3*v := by
  rw [Source.compile_correct]
  simp [twoFree, Source.eval]
  ring

example : twoFree.compile.run ![2,7] 0 ≠ twoFree.compile.run ![7,2] 0 := by
  simp [twoFree, Source.compile_correct, Source.eval]
  norm_num

example : (Source.add (.constant (1/3)) (.constant (2/3)) : Source 0).normalize =
    Expr.constant 1 := by
  norm_num [Source.normalize, Gimle.Asgard.Normalization.add]

example : (Source.neg (.neg (.mul (.constant 1) (.add (.var 0) (.constant 0)))) :
    Source 1).normalize = Expr.var 0 := by decide

example : (Source.mul (.constant 0) (.var 0) : Source 1).normalize =
    Expr.constant 0 := by decide

example : (Source.mul (.var 0) (.constant 0) : Source 1).normalize =
    Expr.constant 0 := by decide

/-- The selected middle coordinate is removed without swapping surrounding
external coordinates, even in a larger context. -/
theorem select_middle : (select (2 : Fin 5)).toFun = ![1,2,0,3,4] := by
  funext i
  fin_cases i <;> decide

example : reconstruct (select (2 : Fin 5)) ![2,5,11,17] 7 = ![2,5,7,11,17] := by
  funext i
  change Fin.cons (α := fun _ => ℝ) 7 ![2,5,11,17] ((select (2 : Fin 5)).toFun i) = _
  rw [select_middle]
  fin_cases i <;> rfl

open Examples.VariableIsolation

example : circuit.run ![2,7] 0 = 19 := by rw [circuit_value]; norm_num

/-- Swapping externals or changing the isolated output breaks the equation. -/
example : ¬ equation.Satisfies ![7,19,2] := by
  change ¬ (2*(19:ℝ)+7 = 19+3*2)
  norm_num

example : ¬ equation.Satisfies ![2,18,7] := by
  change ¬ (2*(18:ℝ)+2 = 18+3*7)
  norm_num

/-- A valid algebraic output does not discharge an incompatible domain. -/
example : ¬ ∃ z, equation.Satisfies ![2,z,7] ∧ z ≤ 10 := by
  rintro ⟨z, hz, hbound⟩
  have h := (preserves 2 7 z (fun x => x 1 ≤ 10)).mp ⟨hz, hbound⟩
  norm_num [circuit_value] at h

/-- An initial value contradicting the retained equation is rejected. -/
example : ¬ ∃ z : ℝ → ℝ, (∀ t, equation.Satisfies ![t,z t,2*t+1]) ∧ z 0 = 4 := by
  rintro ⟨z, hz, hinit⟩
  have h := hz 0
  change 2*z 0+0 = z 0+3*(2*0+1) at h
  rw [hinit] at h
  norm_num at h

def nonlinear : Equation 1 where
  lhs := .mul (.var 0) (.var 0)
  rhs := .constant 1

example : (nonlinear.prepare (select 0)).isNone = true := by decide

/-- Unsupported nonlinear structure can still have a real solution. -/
example : nonlinear.Satisfies ![1,7] := by
  norm_num [nonlinear, Equation.Satisfies, Source.eval]

/-- Variable coefficients are supported only with the explicit inverse identity.
Here u*z=1 is isolated on the restricted domain u*u=1 using inverse u. -/
def variableCoefficient : Equation 1 where
  lhs := .mul (.var 1) (.var 0)
  rhs := .constant 1

def variablePrepared : Prepared variableCoefficient (select 0) :=
  (variableCoefficient.prepare (select 0)).get (by decide)

theorem variable_coefficient (u : ℝ) : variablePrepared.coefficient.eval ![u] = u := by
  rw [Decomposition.coefficient_correct, Equation.residual_correct, Equation.residual_correct]
  simp [variableCoefficient, Source.eval]


theorem variable_offset (u : ℝ) : variablePrepared.offset.eval ![u] = -1 := by
  rw [Decomposition.offset_correct, Equation.residual_correct]
  simp [variableCoefficient, Source.eval]


example (u z : ℝ) (domain : u*u=1) :
    variableCoefficient.Satisfies (reconstruct (select 0) ![u] z) ↔ z = u := by
  have valid : variablePrepared.coefficient.eval ![u] * (Expr.var 0).eval ![u] = 1 := by
    simpa [variable_coefficient, Expr.eval] using domain
  have h := variablePrepared.solution_iff (.var 0) ![u] valid (fun _ => True) z
  simpa [Decomposition.solution_correct, variable_offset, Expr.eval] using h

example : ¬ (variablePrepared.coefficient.eval ![0] * (Expr.var 0).eval ![0] = 1) := by
  norm_num [variable_coefficient, Expr.eval]

/-- Merely being nonzero does not make the supplied inverse u correct. -/
example : ¬ (variablePrepared.coefficient.eval ![2] * (Expr.var 0).eval ![2] = 1) := by
  norm_num [variable_coefficient, Expr.eval]

/-- Zero coefficients may be decomposed, but no inverse witness is admissible. -/
def zeroCoefficient : Equation 0 where
  lhs := .add (.var 0) (.constant 1)
  rhs := .var 0

def zeroPrepared : Prepared zeroCoefficient (select 0) :=
  (zeroCoefficient.prepare (select 0)).get (by decide)

example (inverse : Expr 0) (u : Point 0) :
    ¬ (zeroPrepared.coefficient.eval u * inverse.eval u = 1) := by
  have h : zeroPrepared.coefficient.eval u = 0 := by
    rw [Decomposition.coefficient_correct, Equation.residual_correct, Equation.residual_correct]
    simp [zeroCoefficient, Source.eval]
  simp [h]

example : ¬ zeroCoefficient.Satisfies ![0] := by
  norm_num [zeroCoefficient, Equation.Satisfies, Source.eval]

/-- Positive zero-external case with an exact non-unit rational inverse. -/
def rationalEquation : Equation 0 where
  lhs := .mul (.constant 3) (.var 0)
  rhs := .constant 2

def rationalPrepared : Prepared rationalEquation (select 0) :=
  (rationalEquation.prepare (select 0)).get (by decide)

theorem rational_coefficient (u : Point 0) : rationalPrepared.coefficient.eval u = 3 := by
  rw [Decomposition.coefficient_correct, Equation.residual_correct, Equation.residual_correct]
  norm_num [rationalEquation, Source.eval]

theorem rational_offset (u : Point 0) : rationalPrepared.offset.eval u = -2 := by
  rw [Decomposition.offset_correct, Equation.residual_correct]
  norm_num [rationalEquation, Source.eval]

example : (rationalPrepared.solution (.constant (1/3))).compile.run ![] 0 = (2:ℝ)/3 := by
  simp [Decomposition.solution_correct, rational_offset, Expr.eval]
  norm_num

example (z : ℝ) : rationalEquation.Satisfies ![z] ↔ z = (2:ℝ)/3 := by
  have valid : rationalPrepared.coefficient.eval ![] * (Expr.constant (1/3)).eval ![] = 1 := by
    norm_num [rational_coefficient, Expr.eval]
  have h := rationalPrepared.solution_iff (.constant (1/3)) ![] valid (fun _ => True) z
  simpa [Decomposition.solution_correct, rational_offset, Expr.eval, div_eq_mul_inv, mul_comm] using h

#print axioms Source.normalize_correct
#print axioms Prepared.solution_iff
#print axioms Prepared.family_iff
end Gimle.Asgard.Tests.Normalization
