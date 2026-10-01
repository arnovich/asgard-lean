import Gimle.Asgard.Streams.Tail
import Gimle.Asgard.Streams.Majorant

/-! # The analytic field of a product and an inverse

`analyticField` is a `tsum` of decoded coefficients; `Tail.lean` makes it
converge where a majorant is proved. This module says what the field of a
product, a scalar multiple, the unit and an inverse of streams *is* at a point
where both factors are majorized:

* `analyticField_mul`: the field of `a * b` is the product of the fields, on
  a box strictly inside both majorants — Mathlib's Cauchy product over
  `Finsupp.antidiagonal`, from absolute convergence;
* `analyticField_C_mul`, `analyticField_one`;
* `analyticField_inv`: for a stream with nonzero constant term, the field of
  `φ⁻¹` is the inverse of the field of `φ`, the corollary of `φ⁻¹ * φ = 1`,
  given majorants of both; in particular the field of `φ` does not vanish
  there. (With constant term `0`, Mathlib's `φ⁻¹` is `0`, trivially
  majorized, and the identity fails.)

Everything is about the OGF reading: the decoded coefficient of an OGF stream
is the coefficient itself (`decode .ogf a = a`, definitionally). -/
namespace Gimle.Asgard.Streams

open MvPowerSeries

variable {d : Nat}

/-- The series term of an OGF stream is its coefficient times the monomial. -/
theorem seriesTerm_ogf (a : Stream d) (x : Fin d → ℝ) (α : Index d) :
    seriesTerm .ogf a x α = ((coeff α a : ℚ) : ℝ) * ∏ i, x i ^ α i := rfl

/-- Monomials multiply by adding indices. -/
theorem prod_pow_add (x : Fin d → ℝ) (α β : Index d) :
    (∏ i, x i ^ (α + β) i) = (∏ i, x i ^ α i) * ∏ i, x i ^ β i := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]

/-- **The field of a product is the product of the fields**, wherever both
factors are majorized: the Cauchy product of two absolutely convergent series
over multi-indices, regrouped along antidiagonals. -/
theorem analyticField_mul {a b : Stream d} {ma mb : Majorant d} {box : Box d}
    (ha : Majorizes .ogf a ma) (hb : Majorizes .ogf b mb)
    (ia : ∀ i, box.radius i < ma.radius i) (ib : ∀ i, box.radius i < mb.radius i)
    {x : Fin d → ℝ} (hx : box.Mem x) :
    analyticField .ogf (a * b) x = analyticField .ogf a x * analyticField .ogf b x := by
  have sa := summable_norm_seriesTerm ha ia hx
  have sb := summable_norm_seriesTerm hb ib hx
  unfold analyticField
  rw [sa.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal sb.of_norm
    (summable_mul_of_summable_norm sa sb)]
  congr 1
  funext n
  rw [seriesTerm_ogf, coeff_mul, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [seriesTerm_ogf, seriesTerm_ogf, ← hp, prod_pow_add, Rat.cast_mul]
  ring

/-- Scaling the stream scales the field. -/
theorem analyticField_C_mul (q : ℚ) (a : Stream d) (x : Fin d → ℝ) :
    analyticField .ogf (C q * a) x = q * analyticField .ogf a x := by
  unfold analyticField
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [seriesTerm_ogf, seriesTerm_ogf, coeff_C_mul, Rat.cast_mul, mul_assoc]

/-- The field of the unit stream is `1`. -/
theorem analyticField_one (x : Fin d → ℝ) : analyticField .ogf (1 : Stream d) x = 1 := by
  unfold analyticField
  rw [tsum_eq_single 0]
  · rw [seriesTerm_ogf, coeff_one, if_pos rfl]
    simp
  · intro n hn
    rw [seriesTerm_ogf, coeff_one, if_neg hn]
    simp

/-- **The field of an inverse is the inverse of the field**, for a stream with
nonzero constant term, wherever both the stream and its inverse are majorized;
the field of the stream is then nonzero. -/
theorem analyticField_inv {φ : Stream d} {m m' : Majorant d} {box : Box d}
    (hc : constantCoeff φ ≠ 0) (hφ : Majorizes .ogf φ m) (hinv : Majorizes .ogf φ⁻¹ m')
    (i : ∀ i, box.radius i < m.radius i) (i' : ∀ i, box.radius i < m'.radius i)
    {x : Fin d → ℝ} (hx : box.Mem x) :
    analyticField .ogf φ⁻¹ x = (analyticField .ogf φ x)⁻¹ ∧ analyticField .ogf φ x ≠ 0 := by
  have one : analyticField .ogf φ⁻¹ x * analyticField .ogf φ x = 1 := by
    rw [← analyticField_mul hinv hφ i' i hx, MvPowerSeries.inv_mul_cancel φ hc,
      analyticField_one]
  exact ⟨eq_inv_of_mul_eq_one_left one, right_ne_zero_of_mul_eq_one one⟩

end Gimle.Asgard.Streams
