import Gimle.Asgard.Examples.EulerBand

/-! Coverage for the Euler radius (task 066).

Pinned here: the three estimates behind the induction (the coupling costs at
most one derivative, the transport bound, Nagumo) on concrete inputs; the
induction's two sums at small `n`; the Euler recursion against the computed
coefficients; the geometric bound, convergence, truncation and band of the
three-mode example; hostile checks — a wrong table norm refuted by the kernel,
a size bound the start violates, the created mode `(3, 2)` present and within
the size growth, and the arithmetic facts behind "nothing is claimed beyond the
radius"; Gevrey-1 for the viscous stream; and a transitive standard-axiom audit
of every root theorem and example claim. -/

namespace Gimle.Asgard.Tests.EulerRadius

open Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.TrigStream
open Gimle.Asgard.Streams.NS
open Gimle.Asgard.Examples.EulerThreeMode
open Gimle.Asgard.Examples.EulerBand
open Real

/-! ### The estimates -/

/-- `|(p × q)/|p|²| ≤ |q|₁`: at `p = (1, 0)`, `q = (0, 1)` the coupling is `1 = |q|₁`. -/
example : |coupling (1, 0) (0, 1)| ≤ (size (0, 1) : ℚ) := abs_coupling_le _ _
example : coupling (1, 0) (0, 1) = 1 := by simp [coupling, cross, lam]
example : size ((0, 1) : Wave) = 1 := rfl
example : size ((2, 1) : Wave) = 3 := rfl
example : size ((-3, -2) : Wave) = 5 := rfl

/-- Lagrange: `(p × q)² ≤ |p|²|q|²`. -/
example (p q : Wave) : cross p q ^ 2 ≤ lam p * lam q := cross_sq_le p q

/-- The transport costs at most one derivative. -/
example {σ : ℝ} (hσ : 0 ≤ σ) (P Q : TrigPoly) :
    wnorm σ (transport P Q) ≤ wnorm σ P * dnorm σ Q := wnorm_transport_le hσ P Q

/-- Nagumo: `2y ≤ e^y`, and a derivative is paid for by a loss of radius. -/
example : (2 : ℝ) * 1 ≤ exp 1 := two_mul_le_exp zero_le_one
example {σ σ' : ℝ} (h : σ < σ') (Q : TrigPoly) :
    dnorm σ Q ≤ wnorm σ' Q / (2 * (σ' - σ)) := dnorm_le_wnorm_div h Q

/-- At `σ = 0` the weighted norm is the ℓ¹ norm; the ℓ¹ norm of the start is at most `3`. -/
example : wnorm 0 ω₀ = l1 ω₀ := wnorm_zero ω₀
example : l1 ω₀ ≤ 3 := start_l1

/-! ### The two sums -/

example : ∑ m ∈ Finset.range (0 + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 2 - 1 / (((0 : ℕ) : ℝ) + 1) :=
  sum_inv_sq_le 0
example : ∑ m ∈ Finset.range 3, (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * (((2 - m : ℕ) : ℝ) + 1) ^ 2) ≤
    8 / ((2 : ℝ) + 2) ^ 2 := convolution_sum_le 2

/-- The convolution sum at `n = 2` is `1/9 + 1/16 + 1/9 = 41/144`, below `8/16`. -/
example : ∑ m ∈ Finset.range 3, (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * (((2 - m : ℕ) : ℝ) + 1) ^ 2) =
    41 / 144 := by
  simp [Finset.sum_range_succ]
  norm_num

example : (((0 : ℕ) : ℝ) + 2) / (((0 : ℕ) : ℝ) + 1) ^ 1 ≤ 3 := by
  have := ratio_pow_le_three 0 1 le_rfl
  simpa using this

/-! ### The recursion -/

/-- The Euler recursion at `n = 0` is the transport of the start by itself. -/
example : stream .ogf 0 start 1 = -((1 : ℚ)⁻¹ • transport ω₀ ω₀) := by
  have h := euler_succ start 0
  simpa [stream_slice, start] using h

/-- The abstract bound is consistent with the computed coefficient: the `t¹`
coefficient has ℓ¹ norm at most `8/5 ≤ 9 · 648`. -/
example : l1 (stream .ogf 0 start 1) ≤ 9 * 648 ^ 1 := euler_l1 1
example : (8 / 5 : ℚ) ≤ 9 * 648 ^ 1 := by norm_num

/-! ### The three-mode example -/

example : GeometricBound (stream .ogf 0 start) 9 648 := geometric

example {t : ℝ} (x : ℝ × ℝ) (ht : |t| < 1 / 648) :
    HasSum (seriesTerm (stream .ogf 0 start) t x) (analyticField (stream .ogf 0 start) t x) :=
  hasSum_field x ht

example : TruncationBound (stream .ogf 0 start) (1 / 6480) 3 (1 / 100) := truncation

/-- The rational tail bound at the example's data is exactly `1/100`. -/
example : tailBound 9 648 (1 / 6480) 3 = 1 / 100 := by norm_num [tailBound]

example {t : ℝ} (x : ℝ × ℝ) (ht : |t| ≤ 1 / 6480) :
    |analyticField (stream .ogf 0 start) t x -
      (cos x.1 + cos (x.1 + x.2) + cos (2 * x.1 + x.2))| ≤ 1 / 50 := band x ht

/-- The field of the start at the origin is `3`. -/
example : field ω₀ (0, 0) = 3 := by
  rw [field_start]; norm_num

/-! ### Hostile -/

/-- A wrong table norm is refuted by the kernel: the `t¹` coefficient's table
does not sum to `3/2`. -/
example : Table.absSum ((picard 0 startTable 1).get 1) ≠ 3 / 2 := by decide +kernel

/-- The start violates the size bound `2`: `(2, 1)` has size `3`. -/
example : ¬ SizeLE 2 ω₀ := by
  intro h
  have mem : ((2, 1) : Wave) ∈ ω₀.support := by
    rw [ω₀_eq_table, Finsupp.mem_support_iff, Table.toTrig_apply]
    decide +kernel
  exact absurd (h (2, 1) mem) (by decide)

/-- The created mode `(3, 2)` is present at `t¹` and within the size growth
`(n + 1) K = 6`. -/
example : ((3, 2) : Wave) ∈ (stream .ogf 0 start 1).support := by
  rw [Finsupp.mem_support_iff, euler_t_3x2y]; norm_num
example : size ((3, 2) : Wave) ≤ (1 + 1) * 3 :=
  sizeLE_stream 0 start start_sizeLE 1 (3, 2) (by rw [Finsupp.mem_support_iff, euler_t_3x2y]; norm_num)

/-- `Table.absSum` is only a bound: a table with cancelling duplicates sums to `2`
while its polynomial is zero. -/
example : Table.absSum [((1, 0), 1), ((1, 0), -1)] = 2 := by decide +kernel
example : Table.toTrig [((1, 0), 1), ((1, 0), -1)] = 0 := by
  simp [Table.toTrig]

/-- Beyond the certified radius the geometric tail does not sum: at `r = 1/648`
the ratio `ρ r` is `1`, and the truncation theorem's hypothesis fails. -/
example : ¬ ((648 : ℝ) * (1 / 648) < 1) := by norm_num

/-- A tighter error at the same window fails the arithmetic: the certified
error at `N = 3` is exactly `1/100`; `1/200` is not below it. -/
example : ¬ (tailBound 9 648 (1 / 6480) 3 ≤ 1 / 200) := by norm_num [tailBound]

/-! ### Viscosity -/

example (n : ℕ) : (l1 (stream .ogf ν start n) : ℝ) ≤ 3 * (99 / 10) ^ n * n.factorial :=
  viscous_gevrey n
example (n : ℕ) : SizeLE ((n + 1) * 3) (stream .ogf ν start n) := sizeLE_stream ν start start_sizeLE n

/-! ### Axioms -/

/--
info: 'Gimle.Asgard.Streams.Torus.abs_coupling_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.abs_coupling_le
/--
info: 'Gimle.Asgard.Streams.Torus.wnorm_transport_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.wnorm_transport_le
/--
info: 'Gimle.Asgard.Streams.Torus.dnorm_le_wnorm_div'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.dnorm_le_wnorm_div
/--
info: 'Gimle.Asgard.Streams.Torus.sizeLE_transport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.sizeLE_transport
/--
info: 'Gimle.Asgard.Streams.NS.stream_succ_ogf'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_succ_ogf
/--
info: 'Gimle.Asgard.Streams.NS.euler_succ'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_succ
/--
info: 'Gimle.Asgard.Streams.NS.convolution_sum_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.convolution_sum_le
/--
info: 'Gimle.Asgard.Streams.NS.euler_wnorm_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_wnorm_bound
/--
info: 'Gimle.Asgard.Streams.NS.euler_l1_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_l1_bound
/--
info: 'Gimle.Asgard.Streams.NS.euler_l1_geometric'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_l1_geometric
/--
info: 'Gimle.Asgard.Streams.NS.euler_geometricBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_geometricBound
/--
info: 'Gimle.Asgard.Streams.Torus.abs_field_le_l1'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.abs_field_le_l1
/--
info: 'Gimle.Asgard.Streams.Torus.field_cosine'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.field_cosine
/--
info: 'Gimle.Asgard.Streams.Torus.Table.l1_le_absSum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.Table.l1_le_absSum
/--
info: 'Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.Table.sizeLE_toTrig
/--
info: 'Gimle.Asgard.Streams.TrigStream.hasSum_analyticField'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.hasSum_analyticField
/--
info: 'Gimle.Asgard.Streams.TrigStream.abs_analyticField_sub_windowField_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.abs_analyticField_sub_windowField_le
/--
info: 'Gimle.Asgard.Streams.TrigStream.truncationBound_rat'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.truncationBound_rat
/--
info: 'Gimle.Asgard.Streams.TrigStream.abs_analyticField_sub_field_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.abs_analyticField_sub_field_le
/--
info: 'Gimle.Asgard.Streams.TrigStream.abs_analyticField_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.abs_analyticField_le
/--
info: 'Gimle.Asgard.Streams.NS.sizeLE_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.sizeLE_stream
/--
info: 'Gimle.Asgard.Streams.NS.gevrey_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.gevrey_one
/--
info: 'Gimle.Asgard.Examples.EulerBand.start_sizeLE'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.start_sizeLE
/--
info: 'Gimle.Asgard.Examples.EulerBand.start_l1'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.start_l1
/--
info: 'Gimle.Asgard.Examples.EulerBand.euler_l1'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.euler_l1
/--
info: 'Gimle.Asgard.Examples.EulerBand.geometric'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.geometric
/--
info: 'Gimle.Asgard.Examples.EulerBand.hasSum_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.hasSum_field
/--
info: 'Gimle.Asgard.Examples.EulerBand.truncation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.truncation
/--
info: 'Gimle.Asgard.Examples.EulerBand.l1_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.l1_one
/--
info: 'Gimle.Asgard.Examples.EulerBand.l1_two'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.l1_two
/--
info: 'Gimle.Asgard.Examples.EulerBand.band'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.band
/--
info: 'Gimle.Asgard.Examples.EulerBand.viscous_gevrey'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.viscous_gevrey

end Gimle.Asgard.Tests.EulerRadius
