import Gimle.Asgard.Examples.MildBand

/-! Regressions for classical realization and dissipation of actual mild
circuit outputs, including degenerate data and forward-time boundaries. -/
namespace Gimle.Asgard.Tests.MildClassical
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus Gimle.Asgard.Streams.Mild
open Set

-- Positive viscosity: both physical bounds give full classical solutions.
example : IsMildClassicalSolution (1 / 10) (Examples.MildBand.ω (1 / 10))
    Examples.EulerThreeMode.ω₀ (1 / 5760) := Examples.MildBand.classical
example : HasDissipation (1 / 10) (Examples.MildBand.ω (1 / 10)) (1 / 5760) :=
  Examples.MildBand.dissipation
example : IsMildClassicalSolution (1 / 10) (Examples.MildBand.ω (1 / 10))
    Examples.EulerThreeMode.ω₀ (1 / 1296) :=
  (Examples.MildBand.euler_classical_dissipation (by norm_num) (by norm_num) (by norm_num)).1

-- The inviscid endpoint has zero derivative for both infinite quadratic sums.
example {t : ℝ} (ht : t ∈ Ioo 0 (1 / 1296)) :
    HasDerivAt (fun s => enstrophy (fourierCoeff 0 (Examples.MildBand.ω 0) s)) 0 t := by
  have h := (Examples.MildBand.euler_classical_dissipation (ν := 0) (T := 1 / 1296)
    (by norm_num) (by norm_num) (by norm_num)).2
  simpa using h.enstrophy_deriv t ht
example {t : ℝ} (ht : t ∈ Ioo 0 (1 / 1296)) :
    HasDerivAt (fun s => energy (fourierCoeff 0 (Examples.MildBand.ω 0) s)) 0 t := by
  have h := (Examples.MildBand.euler_classical_dissipation (ν := 0) (T := 1 / 1296)
    (by norm_num) (by norm_num) (by norm_num)).2
  simpa using h.energy_deriv t ht

-- The initial derivative is one-sided and the value is the supplied field.
example (x : ℝ × ℝ) :
    HasDerivWithinAt (fun t => analyticField (1 / 10) (Examples.MildBand.ω (1 / 10)) t x)
      (seriesDt (1 / 10) (Examples.MildBand.ω (1 / 10)) 0 x) (Ici 0) 0 :=
  Examples.MildBand.classical.right_derivT (by norm_num) x
example (x : ℝ × ℝ) : analyticField (1 / 10) (Examples.MildBand.ω (1 / 10)) 0 x =
    RealPoly.field (realEmbed Examples.EulerThreeMode.ω₀) x := Examples.MildBand.classical.initial x

-- The upper endpoint is included in continuity and nonincrease.
example : enstrophy (fourierCoeff (1 / 10) (Examples.MildBand.ω (1 / 10)) (1 / 5760)) ≤
    enstrophy (fourierCoeff (1 / 10) (Examples.MildBand.ω (1 / 10)) 0) :=
  Examples.MildBand.dissipation.enstrophy_le_initial ⟨by norm_num, le_rfl⟩
example : energy (fourierCoeff (1 / 10) (Examples.MildBand.ω (1 / 10)) (1 / 5760)) ≤
    energy (fourierCoeff (1 / 10) (Examples.MildBand.ω (1 / 10)) 0) :=
  Examples.MildBand.dissipation.energy_le_initial ⟨by norm_num, le_rfl⟩

-- Both conclusions follow for every related circuit output. Higher boundary
-- slices are deliberately unconstrained.
example (boundary : Stream) (hb : boundary 0 = embed Examples.EulerThreeMode.ω₀)
    (output : Mild.Point 1) (hout : (mildCircuit (1 / 10)).Rel ![boundary] output) :
    IsMildClassicalSolution (1 / 10) (output 0) Examples.EulerThreeMode.ω₀ (1 / 5760) ∧
      HasDissipation (1 / 10) (output 0) (1 / 5760) := by
  rw [(mildCircuit_rel_iff _ _ _).mp hout]
  have hg := wild_geometric (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    boundary Examples.EulerThreeMode.ω₀ hb Examples.EulerBand.start_l1
  exact ⟨mild_classical (by norm_num) boundary Examples.EulerThreeMode.ω₀ hb
      Examples.EulerThreeMode.ω₀_meanZero Examples.EulerThreeMode.ω₀_isEven
      Examples.EulerBand.start_sizeLE (by norm_num) hg (by norm_num) (by norm_num),
    mild_dissipation (by norm_num) boundary Examples.EulerThreeMode.ω₀ hb
      Examples.EulerThreeMode.ω₀_meanZero Examples.EulerThreeMode.ω₀_isEven
      Examples.EulerBand.start_sizeLE (by norm_num) hg (by norm_num) (by norm_num)⟩

-- Zero data work at every finite nonnegative horizon, even when ν=0. The
-- supplied geometric ratio is exactly zero, exercising its internal padding.
example (ν : ℚ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T) (boundary : Stream)
    (hb : boundary 0 = embed 0) :
    IsMildClassicalSolution ν (wild ν boundary) 0 T ∧ HasDissipation ν (wild ν boundary) T := by
  have hg := wild_euler_geometric hν boundary 0 hb (K := 1) (by norm_num)
    (by simp [Torus.SizeLE]) (L := 0) (by simp [Torus.l1]) T
  have hg' : GeometricBound ν (wild ν boundary) T 0 0 := by simpa using hg
  exact ⟨mild_classical hν boundary 0 hb (by simp [Torus.MeanZero])
      (by simp [Torus.IsEven]) (K := 1) (by simp [Torus.SizeLE]) hT hg' le_rfl (by norm_num),
    mild_dissipation hν boundary 0 hb (by simp [Torus.MeanZero])
      (by simp [Torus.IsEven]) (K := 1) (by simp [Torus.SizeLE]) hT hg' le_rfl (by norm_num)⟩

-- A zero-length interval is supported without claiming a two-sided time derivative.
example : IsMildClassicalSolution 0 (Examples.MildBand.ω 0) Examples.EulerThreeMode.ω₀ 0 :=
  (Examples.MildBand.euler_classical_dissipation (by norm_num) le_rfl (by norm_num)).1
example : ¬ (0 : ℝ) ∈ Ioo 0 (1 / 5760) := by simp
example : ¬ (1 / 5760 : ℝ) ∈ Ioo 0 (1 / 5760) := by simp

-- The finite algebraic cancellation also covers nonsymmetric polynomials.
example (W : RealPoly) : RealPoly.pairing (fun _ => 1) W (RealPoly.transport W W) = 0 :=
  RealPoly.enstrophy_flux_zero W
example (W : RealPoly) : RealPoly.pairing (fun k => (lam k : ℝ)⁻¹) W (RealPoly.transport W W) = 0 :=
  RealPoly.energy_flux_zero W

#print axioms mild_classical
#print axioms mild_dissipation
#print axioms ModeControl.hasDerivAt_square
#print axioms fourierDt_eq
end Gimle.Asgard.Tests.MildClassical
