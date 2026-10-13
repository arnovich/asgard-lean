import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Exact exponential polynomials for the mild vorticity expansion.

The carrier is independent of viscosity: an index `rate` holds a rational
polynomial `p`, denoting `p(t) exp(-ν rate t)`. Evaluation is an algebra map.
Differentiation and Duhamel integration depend on viscosity. These operations
compute exact expressions; their coefficient sizes are not analytic bounds.
-/
namespace Gimle.Asgard.Streams

/-- Finite sums of rational polynomials times indexed heat exponentials. -/
abbrev ExpPoly := AddMonoidAlgebra (Polynomial ℚ) ℕ

namespace ExpPoly

open Polynomial

/-- Addition of exponential indices is multiplication of their real values. -/
noncomputable def expHom (ν t : ℝ) : Multiplicative ℕ →* ℝ where
  toFun k := Real.exp (-(ν * ((Multiplicative.toAdd k : ℕ) : ℝ) * t))
  map_one' := by simp
  map_mul' a b := by
    simp [Nat.cast_add, mul_add, Real.exp_add, mul_comm]

/-- Exact real interpretation, preserving the rational algebra operations. -/
noncomputable def eval (ν t : ℝ) : ExpPoly →ₐ[ℚ] ℝ :=
  AddMonoidAlgebra.liftNCAlgHom (Polynomial.aeval t) (expHom ν t)
    (fun _ _ => Commute.all _ _)

@[simp] theorem eval_single (ν t : ℝ) (rate : ℕ) (p : ℚ[X]) :
    eval ν t (AddMonoidAlgebra.single rate p) =
      Polynomial.aeval t p * Real.exp (-(ν * rate * t)) := by
  simp [eval, expHom]

@[simp] theorem eval_mul (ν t : ℝ) (P Q : ExpPoly) :
    eval ν t (P * Q) = eval ν t P * eval ν t Q := map_mul _ _ _

/-- The polynomial antiderivative with zero constant coefficient. -/
noncomputable def integrate (p : ℚ[X]) : ℚ[X] :=
  p.sum fun n a => Polynomial.monomial (n + 1) (a / (n + 1))

@[simp] theorem derivative_integrate (p : ℚ[X]) : (integrate p).derivative = p := by
  unfold integrate
  simp only [Polynomial.sum_def, map_sum, Polynomial.derivative_monomial_succ]
  have h (n : ℕ) : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [div_mul_cancel₀ _ (h _)]
  exact Polynomial.sum_monomial_eq p

@[simp] theorem integrate_eval_zero (p : ℚ[X]) : (integrate p).eval 0 = 0 := by
  simp [integrate, Polynomial.eval_sum, Polynomial.eval_monomial]
  simp [Polynomial.sum_def]

theorem integrate_add (p q : ℚ[X]) : integrate (p + q) = integrate p + integrate q := by
  unfold integrate
  apply Polynomial.sum_add_index <;> intros <;> simp [add_div]

theorem integrate_smul (a : ℚ) (p : ℚ[X]) : integrate (a • p) = a • integrate p := by
  unfold integrate
  rw [Polynomial.sum_smul_index, Polynomial.smul_sum]
  · simp only [Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro n hn
    simp [Polynomial.smul_monomial, smul_eq_mul, mul_div_assoc]
  · intro n
    simp

@[simp] theorem integrate_monomial (n : ℕ) (a : ℚ) :
    integrate (monomial n a) = monomial (n + 1) (a / (n + 1)) := by
  simp [integrate]

/-- Finite integration-by-parts inverse: `n` applications of `c⁻¹ (p - D …)`. -/
noncomputable def inverseAux (c : ℚ) : ℕ → ℚ[X] → ℚ[X]
  | 0, _ => 0
  | n + 1, p => c⁻¹ • (p - inverseAux c n p.derivative)

/-- Once the derivative vanishes, the finite inverse solves the exact equation. -/
theorem inverseAux_spec (c : ℚ) (hc : c ≠ 0) (n : ℕ) (p : ℚ[X])
    (hn : Polynomial.derivative^[n] p = 0) :
    c • inverseAux c n p + (inverseAux c n p).derivative = p := by
  induction n generalizing p with
  | zero => simpa [inverseAux] using hn.symm
  | succ n ih =>
      have hd : Polynomial.derivative^[n] p.derivative = 0 := by
        simpa only [Function.iterate_succ_apply] using hn
      have hi := ih p.derivative hd
      have hs : p.derivative - (inverseAux c n p.derivative).derivative =
          c • inverseAux c n p.derivative := by
        calc
          _ = (c • inverseAux c n p.derivative +
              (inverseAux c n p.derivative).derivative) -
              (inverseAux c n p.derivative).derivative := congrArg (fun z => z - _) hi.symm
          _ = _ := add_sub_cancel_right _ _
      simp only [inverseAux, smul_smul, mul_inv_cancel₀ hc, one_smul,
        Polynomial.derivative_smul, Polynomial.derivative_sub]
      rw [hs, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_add_cancel]

/-- The polynomial part of the nonresonant Duhamel antiderivative. -/
noncomputable def inverse (c : ℚ) (p : ℚ[X]) : ℚ[X] :=
  inverseAux c (p.natDegree + 1) p

theorem inverse_spec (c : ℚ) (hc : c ≠ 0) (p : ℚ[X]) :
    c • inverse c p + (inverse c p).derivative = p :=
  inverseAux_spec c hc _ p (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _))

@[simp] theorem inverse_zero (c : ℚ) : inverse c 0 = 0 := by
  simp [inverse, inverseAux]

private theorem homogeneous_zero_aux (c : ℚ) (hc : c ≠ 0) (n : ℕ)
    (p : ℚ[X]) (hn : Polynomial.derivative^[n] p = 0)
    (hp : c • p + p.derivative = 0) : p = 0 := by
  induction n generalizing p with
  | zero => exact hn
  | succ n ih =>
      have hd : c • p.derivative + p.derivative.derivative = 0 := by
        simpa using congrArg Polynomial.derivative hp
      have hn' : Polynomial.derivative^[n] p.derivative = 0 := by
        simpa only [Function.iterate_succ_apply] using hn
      have hz := ih p.derivative hn' hd
      have hcp : c • p = 0 := by simpa [hz] using hp
      exact (smul_eq_zero.mp hcp).resolve_left hc

/-- Nonzero `c` makes the polynomial differential equation injective. -/
theorem inverse_unique (c : ℚ) (hc : c ≠ 0) (p q : ℚ[X])
    (hq : c • q + q.derivative = p) : q = inverse c p := by
  apply sub_eq_zero.mp
  apply homogeneous_zero_aux c hc ((q - inverse c p).natDegree + 1)
    (q - inverse c p) (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _))
  calc
    _ = (c • q + q.derivative) - (c • inverse c p + (inverse c p).derivative) := by
      simp only [smul_sub, Polynomial.derivative_sub]
      abel
    _ = 0 := by rw [hq, inverse_spec c hc p, sub_self]

theorem inverse_add (c : ℚ) (p q : ℚ[X]) : inverse c (p + q) = inverse c p + inverse c q := by
  by_cases hc : c = 0
  · simp [hc, inverse, inverseAux]
  symm
  apply inverse_unique c hc
  calc
    _ = (c • inverse c p + (inverse c p).derivative) +
        (c • inverse c q + (inverse c q).derivative) := by
      simp only [smul_add, Polynomial.derivative_add]
      abel
    _ = p + q := by rw [inverse_spec c hc p, inverse_spec c hc q]

theorem inverse_smul (c a : ℚ) (p : ℚ[X]) : inverse c (a • p) = a • inverse c p := by
  by_cases hc : c = 0
  · simp [hc, inverse, inverseAux]
  symm
  apply inverse_unique c hc
  calc
    _ = a • (c • inverse c p + (inverse c p).derivative) := by
      simp [smul_add, smul_smul, mul_comm]
    _ = a • p := by rw [inverse_spec c hc p]

/-- Formal physical-time derivative of each exponential-polynomial term. -/
noncomputable def deriv (ν : ℚ) (P : ExpPoly) : ExpPoly :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.onFinset P.coeff.support
    (fun k => (P.coeff k).derivative - (ν * k) • P.coeff k) fun k hk => by
      rw [Finsupp.mem_support_iff]
      intro hz
      exact hk (by simp [hz])

@[simp] theorem deriv_coeff (ν : ℚ) (P : ExpPoly) (k : ℕ) :
    (deriv ν P).coeff k = (P.coeff k).derivative - (ν * k) • P.coeff k := rfl

@[simp] theorem deriv_zero (ν : ℚ) : deriv ν 0 = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp

theorem deriv_add (ν : ℚ) (P Q : ExpPoly) : deriv ν (P + Q) = deriv ν P + deriv ν Q := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro k
  simp only [deriv_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    Polynomial.derivative_add, smul_add]
  abel

theorem deriv_smul (ν a : ℚ) (P : ExpPoly) : deriv ν (a • P) = a • deriv ν P := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro k
  simp [smul_sub, smul_smul, mul_comm]

theorem deriv_sub (ν : ℚ) (P Q : ExpPoly) : deriv ν (P - Q) = deriv ν P - deriv ν Q := by
  rw [sub_eq_add_neg, ← neg_one_smul ℚ Q, deriv_add, deriv_smul]
  simp [sub_eq_add_neg]

@[simp] theorem deriv_single (ν : ℚ) (k : ℕ) (p : ℚ[X]) :
    deriv ν (AddMonoidAlgebra.single k p) =
      AddMonoidAlgebra.single k (p.derivative - (ν * k) • p) := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro j
  by_cases h : k = j <;> simp [h]

/-- Duhamel on one exponential index, splitting on the full rational resonance. -/
noncomputable def duhamelTerm (ν : ℚ) (μ k : ℕ) (p : ℚ[X]) : ExpPoly :=
  let c : ℚ := ν * ((μ : ℚ) - (k : ℚ))
  if c = 0 then AddMonoidAlgebra.single k (integrate p)
  else AddMonoidAlgebra.single k (inverse c p) -
    AddMonoidAlgebra.single μ (Polynomial.C ((inverse c p).eval 0))

@[simp] theorem duhamelTerm_zero (ν : ℚ) (μ k : ℕ) : duhamelTerm ν μ k 0 = 0 := by
  simp [duhamelTerm, integrate]

/-- Exact modewise Duhamel integration with target heat index `μ`. -/
noncomputable def duhamel (ν : ℚ) (μ : ℕ) (P : ExpPoly) : ExpPoly :=
  P.coeff.sum (duhamelTerm ν μ)

@[simp] theorem duhamel_single (ν : ℚ) (μ k : ℕ) (p : ℚ[X]) :
    duhamel ν μ (AddMonoidAlgebra.single k p) = duhamelTerm ν μ k p := by
  simp [duhamel]

theorem duhamelTerm_add (ν : ℚ) (μ k : ℕ) (p q : ℚ[X]) :
    duhamelTerm ν μ k (p + q) = duhamelTerm ν μ k p + duhamelTerm ν μ k q := by
  unfold duhamelTerm
  dsimp only
  split_ifs <;> simp only [integrate_add, inverse_add, Polynomial.eval_add, map_add,
    AddMonoidAlgebra.single_add]
  abel

theorem duhamelTerm_smul (ν a : ℚ) (μ k : ℕ) (p : ℚ[X]) :
    duhamelTerm ν μ k (a • p) = a • duhamelTerm ν μ k p := by
  unfold duhamelTerm
  dsimp only
  split_ifs <;> simp only [integrate_smul, inverse_smul, smul_sub,
    AddMonoidAlgebra.smul_single, Polynomial.eval_smul, Polynomial.smul_C]

@[simp] theorem duhamel_zero (ν : ℚ) (μ : ℕ) : duhamel ν μ 0 = 0 := by
  simp [duhamel]

theorem duhamel_add (ν : ℚ) (μ : ℕ) (P Q : ExpPoly) :
    duhamel ν μ (P + Q) = duhamel ν μ P + duhamel ν μ Q := by
  unfold duhamel
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intros; exact duhamelTerm_zero _ _ _
  · intros; exact duhamelTerm_add _ _ _ _ _

theorem duhamel_smul (ν a : ℚ) (μ : ℕ) (P : ExpPoly) :
    duhamel ν μ (a • P) = a • duhamel ν μ P := by
  unfold duhamel
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index']
  · simp only [duhamelTerm_smul, Finsupp.sum, Finset.smul_sum]
  · exact fun k => duhamelTerm_zero ν μ k

/-- The termwise integration-by-parts formula solves the forced heat equation. -/
theorem deriv_duhamelTerm (ν : ℚ) (μ k : ℕ) (p : ℚ[X]) :
    deriv ν (duhamelTerm ν μ k p) + (ν * μ) • duhamelTerm ν μ k p =
      AddMonoidAlgebra.single k p := by
  unfold duhamelTerm
  dsimp only
  split_ifs with hc
  · have h : ν * (μ : ℚ) = ν * (k : ℚ) := by
      exact sub_eq_zero.mp (by simpa [mul_sub] using hc)
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro j
    by_cases hk : k = j
    · subst j
      simp [h]
    · simp [hk]
  · let c : ℚ := ν * ((μ : ℚ) - (k : ℚ))
    let q := inverse c p
    have hi : c • q + q.derivative = p := inverse_spec c hc p
    have hq : q.derivative - (ν * k) • q + (ν * μ) • q = p := by
      calc
        _ = c • q + q.derivative := by
          dsimp only [c]
          rw [mul_sub, sub_smul]
          abel
        _ = p := hi
    change deriv ν (AddMonoidAlgebra.single k q -
        AddMonoidAlgebra.single μ (C (q.eval 0))) +
        (ν * μ) • (AddMonoidAlgebra.single k q -
        AddMonoidAlgebra.single μ (C (q.eval 0))) = _
    calc
      _ = AddMonoidAlgebra.single k
          (q.derivative - (ν * k) • q + (ν * μ) • q) := by
        simp only [deriv_sub, deriv_single, Polynomial.derivative_C,
          smul_sub, AddMonoidAlgebra.smul_single, AddMonoidAlgebra.single_add,
          AddMonoidAlgebra.single_sub, AddMonoidAlgebra.single_zero]
        abel
      _ = _ := congrArg (AddMonoidAlgebra.single k) hq

/-- Differentiation commutes with finite sums of exact terms. -/
theorem deriv_sum {ι : Type*} (ν : ℚ) (s : Finset ι) (f : ι → ExpPoly) :
    deriv ν (∑ i ∈ s, f i) = ∑ i ∈ s, deriv ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, deriv_add, ih]

/-- Exact Duhamel integration solves the forced heat equation. -/
theorem deriv_duhamel (ν : ℚ) (μ : ℕ) (P : ExpPoly) :
    deriv ν (duhamel ν μ P) + (ν * μ) • duhamel ν μ P = P := by
  unfold duhamel
  simp only [Finsupp.sum, deriv_sum, Finset.smul_sum, ← Finset.sum_add_distrib,
    deriv_duhamelTerm]
  exact AddMonoidAlgebra.sum_coeff_single P

private theorem aeval_at_zero (p : ℚ[X]) :
    Polynomial.aeval (0 : ℝ) p = (p.eval 0 : ℚ) := by
  simp [Polynomial.aeval_def, Polynomial.eval₂_at_zero, ← Polynomial.coeff_zero_eq_eval_zero]

/-- Each Duhamel term has zero initial value, including either resonance. -/
@[simp] theorem eval_duhamelTerm_zero (ν : ℚ) (μ k : ℕ) (p : ℚ[X]) :
    eval ν 0 (duhamelTerm ν μ k p) = 0 := by
  unfold duhamelTerm
  dsimp only
  split_ifs <;> simp [aeval_at_zero]

/-- Duhamel's zero initial value survives exact finite summation. -/
@[simp] theorem eval_duhamel_zero (ν : ℚ) (μ : ℕ) (P : ExpPoly) :
    eval ν 0 (duhamel ν μ P) = 0 := by
  simp [duhamel, Finsupp.sum]

/-- The formal time derivative agrees with the real derivative of a term. -/
theorem hasDerivAt_single (ν : ℚ) (k : ℕ) (p : ℚ[X]) (t : ℝ) :
    HasDerivAt (fun s => eval ν s (AddMonoidAlgebra.single k p))
      (eval ν t (deriv ν (AddMonoidAlgebra.single k p))) t := by
  have he := (((hasDerivAt_id t).const_mul ((ν : ℝ) * k)).neg).exp
  have h := (p.hasDerivAt_aeval t).mul he
  simp only [eval_single, deriv_single, map_sub, map_smul]
  convert h using 1 <;> first | rfl | (simp [Algebra.smul_def]; ring)

/-- Every exact exponential polynomial has the advertised physical derivative. -/
theorem hasDerivAt (ν : ℚ) (P : ExpPoly) (t : ℝ) :
    HasDerivAt (fun s => eval ν s P) (eval ν t (deriv ν P)) t := by
  have h := HasDerivAt.fun_sum (u := P.coeff.support)
    (fun k _ => hasDerivAt_single ν k (P.coeff k) t)
  have hs : ∑ k ∈ P.coeff.support, AddMonoidAlgebra.single k (P.coeff k) = P :=
    AddMonoidAlgebra.sum_coeff_single P
  simpa only [← map_sum, ← deriv_sum, hs] using h

/-- Evaluation is continuous for every physical time. -/
theorem continuous_eval (ν : ℚ) (P : ExpPoly) : Continuous (fun t => eval ν t P) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt ν P t).continuousAt)

/-- The derivative of the exact integral has the expected forced-heat form. -/
theorem hasDerivAt_duhamel (ν : ℚ) (μ : ℕ) (P : ExpPoly) (t : ℝ) :
    HasDerivAt (fun s => eval ν s (duhamel ν μ P))
      (eval ν t P - ((ν : ℝ) * μ) * eval ν t (duhamel ν μ P)) t := by
  have h := congrArg (eval ν t) (deriv_duhamel ν μ P)
  simp [Algebra.smul_def] at h
  convert hasDerivAt ν (duhamel ν μ P) t using 1
  linarith

/-- Exact coefficients evaluate to the usual heat-kernel Duhamel integral. -/
theorem eval_duhamel (ν : ℚ) (μ : ℕ) (P : ExpPoly) (t : ℝ) :
    eval ν t (duhamel ν μ P) =
      ∫ s in (0 : ℝ)..t, Real.exp (-((ν : ℝ) * μ * (t - s))) * eval ν s P := by
  let a : ℝ := (ν : ℝ) * μ
  have hd (s : ℝ) : HasDerivAt
      (fun x => Real.exp (a * x) * eval ν x (duhamel ν μ P))
      (Real.exp (a * s) * eval ν s P) s := by
    have h := (((hasDerivAt_id s).const_mul a).exp).mul
      (hasDerivAt_duhamel ν μ P s)
    convert h using 1 <;> first | rfl | (dsimp [a]; ring)
  have hc : Continuous (fun s => Real.exp (a * s) * eval ν s P) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (continuous_eval ν P)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hc.intervalIntegrable 0 t)
  simp only [mul_zero, Real.exp_zero, eval_duhamel_zero, mul_zero, sub_zero] at hi
  have hfactor (s : ℝ) :
      Real.exp (-(a * (t - s))) * eval ν s P =
        Real.exp (-(a * t)) * (Real.exp (a * s) * eval ν s P) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  change _ = ∫ s in (0 : ℝ)..t, Real.exp (-(a * (t - s))) * eval ν s P
  simp_rw [hfactor]
  rw [intervalIntegral.integral_const_mul, hi, ← mul_assoc, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_mul]

/-- At zero viscosity the heat kernel is one, including unequal rate indices. -/
theorem eval_duhamel_zero_viscosity (μ : ℕ) (P : ExpPoly) (t : ℝ) :
    eval 0 t (duhamel 0 μ P) = ∫ s in (0 : ℝ)..t, eval 0 s P := by
  simpa using eval_duhamel 0 μ P t

end ExpPoly
end Gimle.Asgard.Streams
