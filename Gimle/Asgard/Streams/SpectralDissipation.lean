import Gimle.Asgard.Streams.FourierPairing
import Gimle.Asgard.Streams.MildModeCalculus

/-! Enstrophy and energy dissipation for the infinite Fourier equation.
The square sums are differentiated under their own uniform mode envelopes. -/
namespace Gimle.Asgard.Streams.Mild
open Torus Real Set

/-- The full enstrophy square sum in exponential Fourier coordinates. -/
noncomputable def enstrophy (W : Wave → ℝ) : ℝ := ∑' k, (W k) ^ 2

/-- Kinetic energy, with the zero mean mode assigned zero inverse weight. -/
noncomputable def energy (W : Wave → ℝ) : ℝ := ∑' k, (lam k : ℝ)⁻¹ * (W k) ^ 2

/-- The viscous enstrophy dissipation sum. -/
noncomputable def palinstrophy (W : Wave → ℝ) : ℝ := ∑' k, (lam k : ℝ) * (W k) ^ 2

theorem lam_nonneg_real (k : Wave) : (0 : ℝ) ≤ lam k := by unfold lam; positivity

/-- Two summable spatial derivatives make the viscous square sum summable. -/
theorem summable_palinstrophy {W : Wave → ℝ} (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) ^ 2 * |W k|)) :
    Summable (fun k => (lam k : ℝ) * (W k) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (lam_nonneg_real k) (sq_nonneg _))
    (fun k => ?_) (hD.mul_left (∑' j, |W j|))
  have hl : (lam k : ℝ) ≤ (size k : ℝ) ^ 2 := by exact_mod_cast lam_le_size_sq k
  have hb := abs_le_mass hW k
  calc (lam k : ℝ) * (W k) ^ 2 = (lam k : ℝ) * |W k| * |W k| := by rw [← sq_abs]; ring
       _ ≤ (size k : ℝ) ^ 2 * (∑' j, |W j|) * |W k| := by gcongr
       _ = _ := by ring

/-- Bounded spectral weights preserve the summability of viscous squares. -/
theorem summable_weighted_viscous {w W : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    (hW : Summable (fun k => |W k|)) (hD : Summable (fun k => (size k : ℝ) ^ 2 * |W k|)) :
    Summable (fun k => w k * (lam k : ℝ) * (W k) ^ 2) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (summable_palinstrophy hW hD)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (lam_nonneg_real k), abs_of_nonneg (sq_nonneg (W k))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hw k) (lam_nonneg_real k)) (sq_nonneg (W k))

/-- Sum the coefficient equation against a bounded spectral weight with zero nonlinear flux. -/
theorem weighted_dissipation_sum {ν : ℝ} {W V w : Wave → ℝ}
    (hPDE : ∀ k, V k = -ν * (lam k : ℝ) * W k - fourierTransport W W k)
    (hflux : HasSum (fun k => w k * W k * fourierTransport W W k) 0)
    (hw : ∀ k, |w k| ≤ 1) (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) ^ 2 * |W k|)) :
    (∑' k, w k * (2 * W k * V k)) = -2 * ν * ∑' k, w k * (lam k : ℝ) * (W k) ^ 2 := by
  have hs := ((summable_weighted_viscous hw hW hD).hasSum.mul_left (-2 * ν)).sub (hflux.mul_left 2)
  have he (k : Wave) : w k * (2 * W k * V k) =
      -2 * ν * (w k * (lam k : ℝ) * (W k) ^ 2) - 2 * (w k * W k * fourierTransport W W k) := by
    rw [hPDE k]; ring
  simpa only [mul_zero, sub_zero, ← he] using hs.tsum_eq

/-- Cancel the inverse Laplacian at every mode of a mean-zero sequence. -/
theorem inverse_viscous_eq {W : Wave → ℝ} (h0 : W 0 = 0) (k : Wave) :
    (lam k : ℝ)⁻¹ * (lam k : ℝ) * (W k) ^ 2 = (W k) ^ 2 := by
  by_cases hk : k = 0
  · simp [hk, h0]
  · have hl : (lam k : ℝ) ≠ 0 := by exact_mod_cast (lam_pos hk).ne'
    rw [inv_mul_cancel₀ hl, one_mul]

variable {f f' : ℝ → Wave → ℝ} {T ν : ℝ} (hc : ModeControl f f' T)
  (he : ∀ t ∈ Icc 0 T, ∀ k, f t (-k) = f t k)
  (h0 : ∀ t ∈ Icc 0 T, f t 0 = 0)
  (hs : ∀ t ∈ Icc 0 T, ∀ d : ℕ, Summable (fun k => (size k : ℝ) ^ d * |f t k|))
  (hPDE : ∀ t ∈ Ioo 0 T, ∀ k, f' t k = -ν * (lam k : ℝ) * f t k - fourierTransport (f t) (f t) k)

include hc he hs hPDE
/-- Enstrophy loses precisely twice viscosity times palinstrophy. -/
theorem hasDerivAt_enstrophy {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => enstrophy (f s)) (-2 * ν * palinstrophy (f t)) t := by
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have hW : Summable (fun k => |f t k|) := by simpa using hs t ht' 0
  have hD : Summable (fun k => (size k : ℝ) * |f t k|) := by simpa using hs t ht' 1
  have hd := hc.hasDerivAt_square (w := fun _ => 1) (fun _ => by norm_num) ht
  have hf := hasSum_enstrophy_transport (he t ht') hW hD
  have hf' : HasSum (fun k => (1 : ℝ) * f t k * fourierTransport (f t) (f t) k) 0 := by simpa using hf
  rw [weighted_dissipation_sum (hPDE t ht) hf' (fun _ => by norm_num) hW (hs t ht' 2)] at hd
  simpa only [one_mul, enstrophy, palinstrophy] using hd

include h0 in
/-- Energy loses precisely twice viscosity times enstrophy. -/
theorem hasDerivAt_energy {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => energy (f s)) (-2 * ν * enstrophy (f t)) t := by
  have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have hW : Summable (fun k => |f t k|) := by simpa using hs t ht' 0
  have hD : Summable (fun k => (size k : ℝ) * |f t k|) := by simpa using hs t ht' 1
  have hd := hc.hasDerivAt_square inv_lam_abs_le_one ht
  rw [weighted_dissipation_sum (hPDE t ht) (hasSum_energy_transport (he t ht') hW hD)
    inv_lam_abs_le_one hW (hs t ht' 2)] at hd
  simpa only [inverse_viscous_eq (h0 t ht'), energy, enstrophy] using hd

/-- Nonnegative viscosity makes enstrophy nonincreasing on the closed interval. -/
theorem antitoneOn_enstrophy (hν : 0 ≤ ν) : AntitoneOn (fun t => enstrophy (f t)) (Icc 0 T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (by simpa only [one_mul, enstrophy] using hc.continuousOn_square (w := fun _ => 1) (fun _ => by norm_num))
  · intro t ht
    exact (hasDerivAt_enstrophy hc he hs hPDE (by simpa using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_enstrophy hc he hs hPDE (by simpa using ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (tsum_nonneg (fun k => mul_nonneg (lam_nonneg_real k) (sq_nonneg _)))

include h0 in
/-- Nonnegative viscosity makes energy nonincreasing on the closed interval. -/
theorem antitoneOn_energy (hν : 0 ≤ ν) : AntitoneOn (fun t => energy (f t)) (Icc 0 T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (hc.continuousOn_square inv_lam_abs_le_one)
  · intro t ht
    exact (hasDerivAt_energy hc he h0 hs hPDE (by simpa using ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    change _root_.deriv (fun s => energy (f s)) t ≤ 0
    rw [(hasDerivAt_energy hc he h0 hs hPDE (by simpa using ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (tsum_nonneg (fun _ => sq_nonneg _))

#print axioms hasDerivAt_enstrophy
#print axioms hasDerivAt_energy
#print axioms antitoneOn_enstrophy
#print axioms antitoneOn_energy
end Gimle.Asgard.Streams.Mild
