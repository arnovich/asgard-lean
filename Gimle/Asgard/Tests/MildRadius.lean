import Gimle.Asgard.Examples.MildBand

/-! Boundary and output-binding regressions for both physical mild bounds. -/
namespace Gimle.Asgard.Tests.MildRadius

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus Gimle.Asgard.Streams.Mild

-- Both exceptional Fourier branches are total and give zero coupling.
example (q : Wave) : coupling 0 q ^ 2 ≤ (lam (0 + q) : ℚ) / lam 0 := coupling_sq_le 0 q
example (p : Wave) : coupling p (-p) = 0 := coupling_neg_self p

-- The heat absorption estimate includes zero horizon/radius without dividing by zero.
example (p q : Wave) : |(coupling p q : ℝ)| * min 0 (1 / ((1 : ℝ) * lam (p + q))) ≤ 0 :=
  coupling_heat_min_le p q (by norm_num) le_rfl le_rfl (by norm_num)

-- The sharper tail matters: the coarse L θ^N/(1-θ) would be 3/8.
example : catalanTail 3 (1 / 24) 4 = 21 / 1024 := Examples.MildBand.tail_constant
example : catalanTail 3 (1 / 24) 4 < 3 * (1 / 2) ^ 4 / (1 - 1 / 2) := by
  rw [Examples.MildBand.tail_constant]; norm_num

-- Actual related circuit outputs inherit the bound, for every boundary with
-- the correct initial slice. Higher boundary noise is unconstrained.
example (boundary : Stream) (hb : boundary 0 = embed Examples.EulerThreeMode.ω₀)
    (output : Mild.Point 1) (hout : (mildCircuit (1 / 10)).Rel ![boundary] output) :
    MildTruncationBound (1 / 10) (output 0) (1 / 5760) 4 (21 / 1024) := by
  rw [(mildCircuit_rel_iff _ _ _).mp hout]
  have h := wild_catalan_truncation (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    boundary Examples.EulerThreeMode.ω₀ hb Examples.EulerBand.start_l1 (by norm_num) 4
  simpa only [Matrix.cons_val_zero, Examples.MildBand.tail_constant, Rat.cast_div, Rat.cast_ofNat] using h

-- Bound two covers Euler itself and positive viscosity with the same constants.
example : MildTruncationBound 0 (Examples.MildBand.ω 0) (1 / 1296) 4 (9 / 8) := by
  have h := Examples.MildBand.euler_truncation (ν := 0) (T := 1 / 1296)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

example : MildTruncationBound (1 / 10) (Examples.MildBand.ω (1 / 10)) (1 / 1296) 4 (9 / 8) := by
  have h := Examples.MildBand.euler_truncation (ν := 1 / 10) (T := 1 / 1296)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

-- An exact-zero start has no finite time restriction, also at ν = 0.
example (T ν : ℚ) (hT : 0 ≤ T) (hν : 0 ≤ ν) (boundary : Stream)
    (hb : boundary 0 = embed 0) : MildTruncationBound ν (wild ν boundary) T 4 0 := by
  have h := wild_euler_truncation hν hT boundary 0 hb (K := 1) (by norm_num)
    (by simp [Torus.SizeLE]) (L := 0) (by simp [Torus.l1]) (by norm_num) 4
  simpa [eulerTail] using h

-- The strict geometric endpoint is a real requirement, not an off-by-one window convention.
example : ¬ (4 * (1 / 12 : ℚ) * 3 < 1) := by norm_num
example : ¬ (72 * (3 : ℚ) * 3 * (1 / 648) < 1) := by norm_num
example : 1 / 648 < (1 : ℚ) * (1 / 24) ^ 2 :=
  (Examples.MildBand.bound_crossing 1).mpr (by norm_num)

#print axioms wild_wnorm_bound
#print axioms wild_catalan
#print axioms wild_euler_band
#print axioms wild_catalan_band
end Gimle.Asgard.Tests.MildRadius
