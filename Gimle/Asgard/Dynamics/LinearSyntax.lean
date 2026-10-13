import Gimle.Asgard.Compile.Polynomial

/-! A checked, deliberately syntactic homogeneous linear fragment. Acceptance
extracts exact rational coefficients; rejection makes no claim of nonlinearity
or insolubility. No ODE existence theorem follows from polynomial compilation. -/
namespace Gimle.Asgard.Dynamics.LinearSyntax
open Polynomial

abbrev Coefficients (n : Nat) := Fin n → ℚ

/-- Read variables, zero, sums, negation and multiplication by a literal scalar.
Nonzero offsets and products without a literal scalar are outside this fragment. -/
def coefficients {n : Nat} : Expr n → Option (Coefficients n)
  | .var i => some (fun j => if j = i then 1 else 0)
  | .constant q => if q = 0 then some (fun _ => 0) else none
  | .add a b => do
      let ca ← coefficients a
      let cb ← coefficients b
      return fun j => ca j + cb j
  | .neg a => (coefficients a).map (fun ca j => -(ca j))
  | .mul (.constant q) b => (coefficients b).map (fun cb j => q * cb j)
  | .mul a (.constant q) => (coefficients a).map (fun ca j => ca j * q)
  | .mul _ _ => none

/-- Independent exact linear evaluation over real input coordinates. -/
noncomputable def evaluate {n : Nat} (c : Coefficients n) (x : Point n) : ℝ :=
  ∑ j, (c j : ℝ) * x j

@[simp] theorem evaluate_zero {n : Nat} (x : Point n) :
    evaluate (fun _ => 0) x = 0 := by simp [evaluate]

@[simp] theorem evaluate_add {n : Nat} (a b : Coefficients n) (x : Point n) :
    evaluate (fun j => a j + b j) x = evaluate a x + evaluate b x := by
  simp [evaluate, add_mul, Finset.sum_add_distrib]

@[simp] theorem evaluate_neg {n : Nat} (a : Coefficients n) (x : Point n) :
    evaluate (fun j => -(a j)) x = -(evaluate a x) := by
  simp [evaluate, Finset.sum_neg_distrib]

@[simp] theorem evaluate_scale_left {n : Nat} (q : ℚ) (a : Coefficients n) (x : Point n) :
    evaluate (fun j => q * a j) x = (q : ℝ) * evaluate a x := by
  simp [evaluate, Finset.mul_sum, mul_assoc]

@[simp] theorem evaluate_scale_right {n : Nat} (q : ℚ) (a : Coefficients n) (x : Point n) :
    evaluate (fun j => a j * q) x = evaluate a x * (q : ℝ) := by
  simp only [evaluate, Rat.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem scale_left_correct {n : Nat} (q : ℚ) (e : Expr n)
    (c : Coefficients n) (x : Point n)
    (ih : ∀ a, coefficients e = some a → e.eval x = evaluate a x)
    (accepted : (coefficients e).map (fun a j => q * a j) = some c) :
    (q : ℝ) * e.eval x = evaluate c x := by
  cases hc : coefficients e with
  | none => simp [hc] at accepted
  | some a =>
      simp [hc] at accepted
      subst c
      rw [evaluate_scale_left, ih _ hc]

private theorem scale_right_correct {n : Nat} (q : ℚ) (e : Expr n)
    (c : Coefficients n) (x : Point n)
    (ih : ∀ a, coefficients e = some a → e.eval x = evaluate a x)
    (accepted : (coefficients e).map (fun a j => a j * q) = some c) :
    e.eval x * (q : ℝ) = evaluate c x := by
  cases hc : coefficients e with
  | none => simp [hc] at accepted
  | some a =>
      simp [hc] at accepted
      subst c
      rw [evaluate_scale_right, ih _ hc]

/-- Accepted coefficients give the source expression's value for every real
input, independently of circuit compilation and any ODE well-posedness claim. -/
theorem coefficients_correct {n : Nat} (e : Expr n) (c : Coefficients n)
    (accepted : coefficients e = some c) (x : Point n) :
    e.eval x = evaluate c x := by
  induction e generalizing c with
  | var i =>
      simp only [coefficients, Option.some.injEq] at accepted
      subst c
      simp only [Expr.eval, evaluate]
      have delta : (fun j : Fin n => ((if j = i then 1 else 0 : ℚ) : ℝ) * x j) =
          (fun j => if j = i then x i else 0) := by
        funext j
        split_ifs with h
        · subst j; simp
        · simp
      rw [delta]
      simp
  | constant q =>
      by_cases hq : q = 0
      · subst q
        simp only [coefficients, ↓reduceIte, Option.some.injEq] at accepted
        subst c
        simp [Expr.eval]
      · simp [coefficients, hq] at accepted
  | add a b ha hb =>
      cases hca : coefficients a with
      | none => simp [coefficients, hca] at accepted
      | some ca =>
          cases hcb : coefficients b with
          | none => simp [coefficients, hca, hcb] at accepted
          | some cb =>
              simp [coefficients, hca, hcb] at accepted
              subst c
              rw [evaluate_add, Expr.eval, ha _ hca, hb _ hcb]
  | neg a ha =>
      cases hca : coefficients a with
      | none => simp [coefficients, hca] at accepted
      | some ca =>
          simp [coefficients, hca] at accepted
          subst c
          rw [evaluate_neg, Expr.eval, ha _ hca]
  | mul a b ha hb =>
      cases a <;> first
        | exact scale_left_correct _ _ _ _ hb accepted
        | skip
      all_goals cases b <;> first
        | exact scale_right_correct _ _ _ _ ha accepted
        | contradiction

/-- The existing verified expression compiler preserves the checked linear
interpretation as well; this adds no new circuit constructor. -/
theorem compiled_correct {n : Nat} (e : Expr n) (c : Coefficients n)
    (accepted : coefficients e = some c) (x : Point n) :
    e.compile.run x 0 = ∑ j, (c j : ℝ) * x j :=
  (Expr.compile_correct e x).trans (coefficients_correct e c accepted x)

-- Scope checks include nonlinear blow-up syntax and affine offsets.
example : coefficients (Expr.mul (n := 1) (.var 0) (.var 0)) = none := rfl
example : coefficients (Expr.constant (n := 2) 1) = none := by decide
example : coefficients (Expr.add (n := 2) (.var 0) (.constant 1)) = none := by decide
example : coefficients (Expr.mul (n := 2) (.constant (1 / 3)) (.var 1)) =
    some (fun j => if j = 1 then (1 / 3 : ℚ) else 0) := by decide +kernel
example : coefficients (Expr.mul (n := 2) (.var 1) (.constant (-2))) =
    some (fun j => if j = 1 then (-2 : ℚ) else 0) := by decide +kernel
example : coefficients (Expr.constant (n := 0) 0) = some Fin.elim0 := by decide +kernel

example : coefficients (Expr.add (n := 3)
    (.mul (.constant (1 / 3)) (.var 2))
    (.neg (.add (.var 0) (.var 2)))) = some ![-1, 0, -2 / 3] := by decide +kernel
example : coefficients (Expr.mul (n := 2)
    (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) = none := rfl

#print axioms coefficients_correct
#print axioms compiled_correct

end Gimle.Asgard.Dynamics.LinearSyntax
