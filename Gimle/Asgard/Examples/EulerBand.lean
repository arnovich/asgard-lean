import Gimle.Asgard.Streams.EulerRadius
import Gimle.Asgard.Streams.Gevrey
import Gimle.Asgard.Streams.EulerSolution
import Gimle.Asgard.Examples.EulerThreeMode

/-! # A certified radius, truncation and band for the three-mode Euler stream

The Euler stream of `Examples/EulerThreeMode` starts from
`ω₀ = cos x + cos(x + y) + cos(2x + y)`: three modes of size at most `K = 3`
and ℓ¹ norm `L = 3`. `EulerRadius.euler_l1_geometric` gives

  `l1 ω_n ≤ 9 · 648ⁿ`,

so the `t`-series of the stream's field converges for `|t| < 1/648`
(`hasSum_field`), and on `|t| ≤ 1/6480` that analytic field is within `1/100`
of the finite sum through `t²` (`truncation`) and within `1/50` of the field
of the initial vorticity, `cos x + cos(x + y) + cos(2x + y)` (`band`): the two
coefficients the window needs beyond `ω₀` have ℓ¹ norms `8/5` and `223/260`,
read off the kernel-computed tables.

The analytic field is a classical solution of the vorticity equation on
`|t| < 1/648` (`classical`, an `NS.IsClassicalSolution`; `vorticity_equation`,
`laplacian_streamFunction` and `initial` project it): `ΔΨ = ω`, `u = ∇⊥Ψ`,
`∂_t ω + u·∇ω = 0` at every point, the partial derivatives continuous. Nothing
about the real equation stays on paper; what is not stated is higher
regularity, the velocity form and uniqueness. The reading of `field` as the
real exponential sum names the coefficients (true for even data, which every
coefficient here is by `coeff_isEven`). The radius
is small — the constants of the induction are not sharp, and the device is
pessimistic by nature; evidence about the true radius belongs to the notebook
that shows the computed norms, not here. For the viscous stream (`ν = 1/10`)
only Gevrey-1 growth in `t` is certified, `l1 ω_n ≤ 3 · (99/10)ⁿ · n!`
(`viscous_gevrey`); nothing here claims a radius for it. -/
namespace Gimle.Asgard.Examples.EulerBand

open Gimle.Asgard.Streams.Torus Gimle.Asgard.Streams.TrigStream Gimle.Asgard.Streams.NS
  Gimle.Asgard.Examples.EulerThreeMode Real

/-- The three modes have size at most `3`. -/
theorem start_sizeLE : SizeLE 3 ω₀ := by
  rw [ω₀_eq_table]
  exact Table.sizeLE_toTrig (by decide)

/-- The start has ℓ¹ norm at most `3` (six coefficients `1/2`; the bound is tight). -/
theorem start_l1 : l1 ω₀ ≤ 3 := by
  rw [ω₀_eq_table]
  exact (Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))

/-- The field of the start: `cos x + cos(x + y) + cos(2x + y)`. -/
theorem field_start (x : ℝ × ℝ) :
    field ω₀ x = cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2) := by
  simp only [ω₀, field_add, field_cosine]
  push_cast
  ring_nf

/-- **The geometric bound.** `l1 ω_n ≤ 9 · 648ⁿ` for the Euler stream. -/
theorem euler_l1 (n : ℕ) : l1 (stream .ogf 0 start n) ≤ 9 * 648 ^ n := by
  have h := euler_l1_geometric start (K := 3) (by norm_num) start_sizeLE start_l1 n
  norm_num at h ⊢
  exact h

theorem geometric : GeometricBound (stream .ogf 0 start) 9 648 := by
  have h := euler_geometricBound start (K := 3) (by norm_num) start_sizeLE start_l1
  norm_num at h
  exact h

/-- **Convergence.** The `t`-series of the field converges for `|t| < 1/648`. -/
theorem hasSum_field {t : ℝ} (x : ℝ × ℝ) (ht : |t| < 1 / 648) :
    HasSum (seriesTerm (stream .ogf 0 start) t x) (analyticField (stream .ogf 0 start) t x) :=
  hasSum_analyticField geometric (by norm_num) (by linarith) le_rfl

/-- **Certified truncation.** On `|t| ≤ 1/6480` the analytic field is within
`1/100` of the finite sum through `t²`. -/
theorem truncation : TruncationBound (stream .ogf 0 start) (1 / 6480) 3 (1 / 100) := by
  have h := truncationBound geometric (by norm_num) (by norm_num : (648 : ℝ) * (1 / 6480) < 1) 3
  refine h.mono (le_of_eq ?_)
  norm_num

/-- The ℓ¹ norms of the next two coefficients, from the kernel-computed tables. -/
theorem l1_one : l1 (stream .ogf 0 start 1) ≤ 8 / 5 := by
  rw [stream_eq_table 0 startTable start start_eq_table]
  exact (Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))

theorem l1_two : l1 (stream .ogf 0 start 2) ≤ 223 / 260 := by
  rw [stream_eq_table 0 startTable start start_eq_table]
  exact (Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel))

/-- **A band around the initial vorticity.** On `|t| ≤ 1/6480` the analytic
field stays within `1/50` of `cos x + cos(x + y) + cos(2x + y)`. -/
theorem band {t : ℝ} (x : ℝ × ℝ) (ht : |t| ≤ 1 / 6480) :
    |analyticField (stream .ogf 0 start) t x - (cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2))| ≤
      1 / 50 := by
  have h := abs_analyticField_sub_field_le (x := x) geometric (by norm_num)
    (by norm_num : (648 : ℝ) * (1 / 6480) < 1) ht (N := 3) (by norm_num)
  rw [stream_slice] at h
  have e : field (start 0) x = cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2) := field_start x
  rw [e] at h
  refine h.trans ?_
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ]
  have h1 : (l1 (stream .ogf 0 start 1) : ℝ) ≤ 8 / 5 := by
    have := (Rat.cast_le (K := ℝ)).mpr l1_one
    push_cast at this
    exact this
  have h2 : (l1 (stream .ogf 0 start 2) : ℝ) ≤ 223 / 260 := by
    have := (Rat.cast_le (K := ℝ)).mpr l1_two
    push_cast at this
    exact this
  linarith [h1, h2]

/-- **Gevrey-1 in `t` for the viscous stream**, `ν = 1/10`: `l1 ω_n ≤ 3 · (99/10)ⁿ · n!`. -/
theorem viscous_gevrey (n : ℕ) :
    (l1 (stream .ogf ν start n) : ℝ) ≤ 3 * (99 / 10) ^ n * n.factorial := by
  have h := gevrey_one ν start (by norm_num [ν]) start_sizeLE start_l1 n
  norm_num [ν] at h ⊢
  exact h

/-! ## The field is a classical solution

On `|t| < 1/648` the analytic field of the three-mode Euler stream is a classical
solution of the vorticity equation (`NS.euler_classical`): its stream function
`Ψ` has `ΔΨ = ω`, the velocity `∇⊥Ψ` is divergence-free, and `∂_t ω + u·∇ω = 0`
pointwise, every derivative the sum of the termwise derivatives and continuous
in `(t, x)`. -/

/-- The three-mode field is a classical solution at every `(t, x)` with `|t| < 1/648`. -/
theorem classical {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    IsClassicalSolution (stream .ogf 0 start) t x :=
  euler_classical start ω₀_meanZero ω₀_isEven start_sizeLE geometric (by norm_num) ht x

/-- `∂_t ω + u·∇ω = 0` for the three-mode start, on `|t| < 1/648`. -/
theorem vorticity_equation {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesDt (stream .ogf 0 start) t x +
      (-seriesD₂ (psi (stream .ogf 0 start)) t x * seriesD₁ (stream .ogf 0 start) t x +
        seriesD₁ (psi (stream .ogf 0 start)) t x * seriesD₂ (stream .ogf 0 start) t x) = 0 :=
  (classical ht x).equation

/-- `ΔΨ = ω` for the three-mode start, on `|t| < 1/648`. -/
theorem laplacian_streamFunction {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesD₁₁ (psi (stream .ogf 0 start)) t x + seriesD₂₂ (psi (stream .ogf 0 start)) t x =
      analyticField (stream .ogf 0 start) t x :=
  (classical ht x).laplacian

/-- At `t = 0` the field is the start's, `cos x + cos(x + y) + cos(2x + y)`. -/
theorem initial (x : ℝ × ℝ) :
    analyticField (stream .ogf 0 start) 0 x = cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2) := by
  rw [analyticField_zero]
  exact field_start x

#print axioms start_sizeLE
#print axioms start_l1
#print axioms euler_l1
#print axioms geometric
#print axioms hasSum_field
#print axioms truncation
#print axioms l1_one
#print axioms l1_two
#print axioms band
#print axioms viscous_gevrey
#print axioms classical
#print axioms vorticity_equation
#print axioms laplacian_streamFunction
#print axioms initial

end Gimle.Asgard.Examples.EulerBand
