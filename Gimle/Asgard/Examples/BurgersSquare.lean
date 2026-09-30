import Gimle.Asgard.Streams.Burgers

/-! # Burgers from the profile `x²`

`D_t u = −u·D_x u + ν·D_x² u` with `ν = 1/10` from `u(0, x) = x²`, on axes
`[t, x]`. The first Picard iterates are computed as polynomials and the
stream's low coefficients read off them:

  `u = x² + t (1/5 − 2x³) + t² (−4x/5 + 5x⁴) + …`

The iterate of order `n` is right up to `t`-degree `n` and wrong beyond it
(its `t³` term is not the stream's), which is exactly what `Causal` says. The
full series is expected to diverge; nothing about convergence is claimed
here. Affine data `x` gives the first iterate `x − t x` of the rational
solution `x/(1+t)`; nothing beyond the first iterate is proved. -/
namespace Gimle.Asgard.Examples.BurgersSquare

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Burgers

local notation "T" => (MvPolynomial.X 0 : Poly 2)
local notation "X" => (MvPolynomial.X 1 : Poly 2)

/-- The viscosity of this example. -/
def ν : ℚ := 1 / 10

/-- Coefficients at `n 0 = 0` of `T * q` vanish. -/
theorem coeff_T_mul_slice (q : Poly 2) (n : Index 2) (zero : n 0 = 0) :
    MvPolynomial.coeff n (T * q) = 0 := by
  rw [MvPolynomial.coeff_X_mul']
  simp [zero]

theorem coeff_T_pow_mul_slice (k : ℕ) (q : Poly 2) (n : Index 2) (zero : n 0 = 0) :
    MvPolynomial.coeff n (T ^ (k + 1) * q) = 0 := by
  rw [pow_succ', mul_assoc, coeff_T_mul_slice _ _ zero]

/-- The constants of the iterates, as multiples of `ν`. -/
theorem C_fifth : (MvPolynomial.C (1 / 5) : Poly 2) = MvPolynomial.C ν * 2 := by
  rw [ν, show (1 / 5 : ℚ) = 1 / 10 * 2 by norm_num, MvPolynomial.C_mul, map_ofNat]

theorem C_neg_four_fifths : (MvPolynomial.C (-4 / 5) : Poly 2) = MvPolynomial.C ν * (-8) := by
  rw [ν, show (-4 / 5 : ℚ) = 1 / 10 * (-8) by norm_num, MvPolynomial.C_mul, map_neg, map_ofNat]

theorem C_two_fifths : (MvPolynomial.C (2 / 5) : Poly 2) = MvPolynomial.C ν * 4 := by
  rw [ν, show (2 / 5 : ℚ) = 1 / 10 * 4 by norm_num, MvPolynomial.C_mul, map_ofNat]

/-- Polynomial identities among the iterates are settled by evaluating both
sides as real fields, where the rational constants are plain numbers. -/
theorem iterate_identity {p q : Poly 2} (h : ∀ y : Fin 2 → ℝ, field p y = field q y) : p = q :=
  field_injective h

/-- First iterate: `x² + t(1/5 − 2x³)`. -/
theorem picard_one :
    picard ν (X ^ 2) 1 = X ^ 2 + T * (MvPolynomial.C (1 / 5) - 2 * X ^ 3) := by
  rw [picard, picard]
  apply integralPoly_eq
  · rw [C_fifth]
    simp only [rhsPoly, map_sub, map_add, Derivation.leibniz_pow, Derivation.leibniz,
      MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, pderiv_ofNat]
    simp
    ring
  · intro n zero
    rw [MvPolynomial.coeff_add, coeff_T_mul_slice _ _ zero, add_zero]

/-- Second iterate: right to `t²`; its `t³` term is an artefact of the iteration. -/
theorem picard_two :
    picard ν (X ^ 2) 2 = X ^ 2 + T * (MvPolynomial.C (1 / 5) - 2 * X ^ 3) +
      T ^ 2 * (MvPolynomial.C (-4 / 5) * X + 5 * X ^ 4) +
      T ^ 3 * (MvPolynomial.C (2 / 5) * X ^ 2 - 4 * X ^ 5) := by
  rw [picard, picard_one]
  apply integralPoly_eq
  · rw [C_fifth, C_neg_four_fifths, C_two_fifths]
    simp only [rhsPoly, map_sub, map_add, Derivation.leibniz_pow, Derivation.leibniz,
      MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, pderiv_ofNat]
    simp
    ring
  · intro n zero
    simp only [MvPolynomial.coeff_add, coeff_T_mul_slice _ _ zero,
      coeff_T_pow_mul_slice _ _ _ zero, add_zero]

/-- Third iterate: right to `t³` (`16x²/5 − 14x⁵`); the terms from `t⁴` on are
artefacts of the iteration. Proved by evaluating both sides as real fields. -/
theorem picard_three :
    picard ν (X ^ 2) 3 = X ^ 2 + T * (MvPolynomial.C (1 / 5) - 2 * X ^ 3) +
      T ^ 2 * (MvPolynomial.C (-4 / 5) * X + 5 * X ^ 4) +
      T ^ 3 * (MvPolynomial.C (16 / 5) * X ^ 2 - 14 * X ^ 5) +
      T ^ 4 * (MvPolynomial.C (3 / 50) - 5 * X ^ 3 + MvPolynomial.C (49 / 2) * X ^ 6) +
      T ^ 5 * (MvPolynomial.C (-4 / 25) * X + MvPolynomial.C (28 / 5) * X ^ 4 +
        MvPolynomial.C (-164 / 5) * X ^ 7) +
      T ^ 6 * (MvPolynomial.C (4 / 25) * X ^ 2 + MvPolynomial.C (-26 / 5) * X ^ 5 + 30 * X ^ 8) +
      T ^ 7 * (MvPolynomial.C (-8 / 175) * X ^ 3 + MvPolynomial.C (8 / 5) * X ^ 6 +
        MvPolynomial.C (-80 / 7) * X ^ 9) := by
  rw [picard, picard_two]
  apply integralPoly_eq
  · simp only [rhsPoly, map_sub, map_add, Derivation.leibniz_pow, Derivation.leibniz,
      MvPolynomial.pderiv_X, MvPolynomial.pderiv_C, pderiv_ofNat]
    apply iterate_identity
    intro y
    simp [ν]
    ring
  · intro n zero
    simp only [MvPolynomial.coeff_add, coeff_T_mul_slice _ _ zero,
      coeff_T_pow_mul_slice _ _ _ zero, add_zero]

/-- The stream's coefficient of `t` is `1/5`: the viscous term alone, since
`u₀·D_x u₀ = 2x³` has no constant part. -/
theorem coeff_t : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1) = 1 / 5 := by
  rw [stream_ogf_coeff, Finsupp.single_eq_same, picard_one]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C,
    Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply]

/-- The coefficient of `t x³` is `−2`: the nonlinearity alone. -/
theorem coeff_t_x3 :
    stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1 + Finsupp.single 1 3) = -2 := by
  have idx : (Finsupp.single 0 1 + Finsupp.single 1 3 : Index 2) 0 = 1 := by simp
  rw [stream_ogf_coeff, idx, picard_one]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_pow, MvPolynomial.coeff_C,
    Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply]

/-- The coefficient of `t² x` is `−4/5`. -/
theorem coeff_t2_x :
    stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 2 + Finsupp.single 1 1) = -4 / 5 := by
  have idx : (Finsupp.single 0 2 + Finsupp.single 1 1 : Index 2) 0 = 2 := by simp
  rw [stream_ogf_coeff, idx, picard_two]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X, MvPolynomial.coeff_C, pow_succ,
    mul_assoc, Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply, Finsupp.tsub_apply]

/-- The coefficient of `t² x⁴` is `5`. -/
theorem coeff_t2_x4 :
    stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 2 + Finsupp.single 1 4) = 5 := by
  have idx : (Finsupp.single 0 2 + Finsupp.single 1 4 : Index 2) 0 = 2 := by simp
  rw [stream_ogf_coeff, idx, picard_two]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X, MvPolynomial.coeff_C, pow_succ,
    mul_assoc, Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply, Finsupp.tsub_apply]

/-- At `t³`: the coefficients of `x²` and `x⁵` are `16/5` and `−14`. -/
theorem coeff_t3_x2 :
    stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 3 + Finsupp.single 1 2) = 16 / 5 := by
  have idx : (Finsupp.single 0 3 + Finsupp.single 1 2 : Index 2) 0 = 3 := by simp
  rw [stream_ogf_coeff, idx, picard_three]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X, MvPolynomial.coeff_C, pow_succ,
    mul_assoc, Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply, Finsupp.tsub_apply]

theorem coeff_t3_x5 :
    stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 3 + Finsupp.single 1 5) = -14 := by
  have idx : (Finsupp.single 0 3 + Finsupp.single 1 5 : Index 2) 0 = 3 := by simp
  rw [stream_ogf_coeff, idx, picard_three]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X, MvPolynomial.coeff_C, pow_succ,
    mul_assoc, Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply, Finsupp.tsub_apply]

/-- Without viscosity the first iterate is `x² − 2t x³`, and the `t`-coefficient
`1/5` above is indeed the viscous term's alone. -/
theorem picard_one_inviscid : picard 0 (X ^ 2) 1 = X ^ 2 - T * (2 * X ^ 3) := by
  rw [picard, picard]
  apply integralPoly_eq
  · simp only [rhsPoly, map_sub, Derivation.leibniz_pow, Derivation.leibniz,
      MvPolynomial.pderiv_X, pderiv_ofNat]
    simp
    ring
  · intro n zero
    rw [MvPolynomial.coeff_sub, coeff_T_mul_slice _ _ zero, sub_zero]

theorem coeff_t_inviscid : stream .ogf 0 (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1) = 0 := by
  rw [stream_ogf_coeff, Finsupp.single_eq_same, picard_one_inviscid]
  simp [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_pow, Finsupp.ext_iff,
    Fin.forall_fin_two, Finsupp.single_apply]

/-- Affine data: the first iterate of `x` is `x − t x`, the start of `x/(1+t)`;
the viscous term vanishes identically. -/
theorem picard_affine_one : picard ν X 1 = X - T * X := by
  rw [picard, picard]
  apply integralPoly_eq
  · simp only [rhsPoly, map_sub, Derivation.leibniz, MvPolynomial.pderiv_X]
    simp
  · intro n zero
    rw [MvPolynomial.coeff_sub, coeff_T_mul_slice _ _ zero, sub_zero]

/-- The circuit reconstructs this stream and nothing else from `x²`. -/
theorem unique (a unused v : Stream 2)
    (rel : (circuit .ogf ν).Rel ![a, ofPoly .ogf (X ^ 2), unused] ![v, a]) :
    a = stream .ogf ν (ofPoly .ogf (X ^ 2)) :=
  candidate_stream .ogf ν _ a unused v rel

#print axioms coeff_t
#print axioms coeff_t2_x4
#print axioms coeff_t3_x5
#print axioms unique
end Gimle.Asgard.Examples.BurgersSquare
