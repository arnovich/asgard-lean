import Gimle.Asgard.Streams.FourierFlux
import Gimle.Asgard.Streams.MildFourierSeries

/-! Absolute Fourier exchanges and nonlinear cancellation for infinite real
coefficient sequences with one summable spatial derivative. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

/-- The inverse Laplacian spectral weight is between zero and one. -/
theorem inv_lam_abs_le_one (k : Wave) : |(lam k : ℝ)⁻¹| ≤ 1 := by
  by_cases hk : k = 0
  · simp [hk]
  · have hl : (1 : ℝ) ≤ lam k := by exact_mod_cast (show (1 : ℤ) ≤ lam k from lam_pos hk)
    rw [abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact inv_le_one_of_one_le₀ hl

/-- Every coefficient of an absolutely summable sequence is bounded by its mass. -/
theorem abs_le_mass {W : Wave → ℝ} (hW : Summable (fun k => |W k|)) (k : Wave) :
    |W k| ≤ ∑' j, |W j| := hW.le_tsum k (fun _ _ => abs_nonneg _)

/-- Infinite transport, with the output-mode constraint kept explicit. -/
noncomputable def fourierTransport (W V : Wave → ℝ) (k : Wave) : ℝ :=
  ∑' p, ∑' q, if p + q = k then (coupling p q : ℝ) * W p * V q else 0

/-- Weighted transport paired with the opposite Fourier coefficient. -/
noncomputable def fourierFlux (w W : Wave → ℝ) : ℝ :=
  ∑' p, ∑' q, w (p + q) * W (-(p + q)) * (coupling p q : ℝ) * W p * W q

/-- An absolute summable product dominates all closed triads. -/
theorem summable_norm_triad {w W : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) * |W k|)) :
    Summable (fun z : Wave × Wave × Wave => ‖RealPoly.triad w W z.1 z.2.1 z.2.2‖) := by
  have hd0 : ∀ k, 0 ≤ (size k : ℝ) * |W k| := fun k => by positivity
  have hh := hW.mul_of_nonneg (hD.mul_of_nonneg hW hd0 (fun _ => abs_nonneg _))
    (fun _ => abs_nonneg _) (fun z => mul_nonneg (hd0 z.1) (abs_nonneg _))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_) hh
  rw [Real.norm_eq_abs]
  unfold RealPoly.triad
  split_ifs
  · simp only [abs_mul]
    have hc : |(coupling z.1 z.2.1 : ℝ)| ≤ size z.2.1 := by exact_mod_cast abs_coupling_le z.1 z.2.1
    calc |w z.2.2| * |(coupling z.1 z.2.1 : ℝ)| * |W z.1| * |W z.2.1| * |W z.2.2|
        ≤ 1 * (size z.2.1 : ℝ) * |W z.1| * |W z.2.1| * |W z.2.2| := by gcongr; exact hw _
        _ = _ := by ring
  · simp only [abs_zero]
    positivity

/-- The constrained third-mode sum equals the opposite-mode pairing. -/
theorem tsum_triad (w W : Wave → ℝ) (hw : ∀ k, w (-k) = w k) (p q : Wave) :
    (∑' r, RealPoly.triad w W p q r) =
      w (p + q) * W (-(p + q)) * (coupling p q : ℝ) * W p * W q := by
  rw [tsum_eq_single (-(p + q))]
  · simp only [RealPoly.triad, add_neg_cancel, ite_true, hw]
    ring
  · intro r hr
    simp only [RealPoly.triad]
    rw [if_neg (fun h => hr (eq_neg_of_add_eq_zero_right h))]

/-- The double flux is an absolutely convergent triple sum. -/
theorem fourierFlux_eq_triad {w W : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    (he : ∀ k, w (-k) = w k) (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) * |W k|)) :
    fourierFlux w W = ∑' z : Wave × Wave × Wave, RealPoly.triad w W z.1 z.2.1 z.2.2 := by
  have hs := (summable_norm_triad hw hW hD).of_norm
  rw [hs.tsum_prod]
  simp_rw [(fun p => (hs.prod_factor p).tsum_prod), tsum_triad w W he]
  rfl

/-- Enstrophy transport flux vanishes after the absolutely justified Fourier exchange. -/
theorem fourier_enstrophy_flux_zero {W : Wave → ℝ} (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) * |W k|)) : fourierFlux (fun _ => 1) W = 0 := by
  rw [fourierFlux_eq_triad (fun _ => by norm_num) (fun _ => rfl) hW hD]
  let e : (Wave × Wave × Wave) ≃ (Wave × Wave × Wave) :=
    ⟨fun z => (z.1, z.2.2, z.2.1), fun z => (z.1, z.2.2, z.2.1), fun _ => rfl, fun _ => rfl⟩
  have he := e.tsum_eq (fun z : Wave × Wave × Wave => RealPoly.triad (fun _ => 1) W z.1 z.2.1 z.2.2)
  change (∑' z : Wave × Wave × Wave, RealPoly.triad (fun _ => 1) W z.1 z.2.2 z.2.1) = _ at he
  have hn := tsum_congr (L := SummationFilter.unconditional _) (fun z : Wave × Wave × Wave => RealPoly.triad_enstrophy_swap W z.1 z.2.1 z.2.2)
  rw [tsum_neg] at hn
  linarith

/-- Energy transport flux vanishes by exchanging the first and third modes. -/
theorem fourier_energy_flux_zero {W : Wave → ℝ} (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) * |W k|)) :
    fourierFlux (fun k => (lam k : ℝ)⁻¹) W = 0 := by
  rw [fourierFlux_eq_triad inv_lam_abs_le_one (fun k => by rw [lam_neg]) hW hD]
  let e : (Wave × Wave × Wave) ≃ (Wave × Wave × Wave) :=
    ⟨fun z => (z.2.2, z.2.1, z.1), fun z => (z.2.2, z.2.1, z.1), fun _ => rfl, fun _ => rfl⟩
  have he := e.tsum_eq (fun z : Wave × Wave × Wave => RealPoly.triad (fun k => (lam k : ℝ)⁻¹) W z.1 z.2.1 z.2.2)
  change (∑' z : Wave × Wave × Wave, RealPoly.triad (fun k => (lam k : ℝ)⁻¹) W z.2.2 z.2.1 z.1) = _ at he
  have hn := tsum_congr (L := SummationFilter.unconditional _) (fun z : Wave × Wave × Wave => RealPoly.triad_energy_swap W z.1 z.2.1 z.2.2)
  rw [tsum_neg] at hn
  linarith

#print axioms fourier_enstrophy_flux_zero
#print axioms fourier_energy_flux_zero
end Gimle.Asgard.Streams.Mild
