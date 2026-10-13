import Gimle.Asgard.Streams.FourierSequence

/-! Pairing the infinite Fourier transport against a summable coefficient
sequence. Absolute triad convergence justifies the mode exchanges. -/
namespace Gimle.Asgard.Streams.Mild
open Torus Real

/-- Pairing transport is summable and has precisely the absolutely convergent flux sum. -/
theorem hasSum_fourierPairing {w W : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    (he : ∀ k, w (-k) = w k) (hW : Summable (fun k => |W k|))
    (hD : Summable (fun k => (size k : ℝ) * |W k|)) :
    HasSum (fun k => w k * W (-k) * fourierTransport W W k) (fourierFlux w W) := by
  let e : (Wave × Wave × Wave) ≃ (Wave × Wave × Wave) :=
    ⟨fun z => (z.2.1, z.2.2, -z.1), fun z => (-z.2.2, z.1, z.2.1),
      fun z => by simp, fun z => by simp⟩
  have hs : Summable (fun z : Wave × Wave × Wave => RealPoly.triad w W z.2.1 z.2.2 (-z.1)) :=
    (e.summable_iff (f := fun z : Wave × Wave × Wave => RealPoly.triad w W z.1 z.2.1 z.2.2)).mpr
      (summable_norm_triad hw hW hD).of_norm
  have hm (k : Wave) : (∑' p, ∑' q, RealPoly.triad w W p q (-k)) =
      w k * W (-k) * fourierTransport W W k := by
    rw [fourierTransport, ← tsum_mul_left]
    apply tsum_congr
    intro p
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    have hc : p + q + -k = 0 ↔ p + q = k := by simp only [← sub_eq_add_neg, sub_eq_zero]
    simp only [RealPoly.triad, hc, he]
    split_ifs <;> ring
  have ht (k : Wave) : (∑' z : Wave × Wave, RealPoly.triad w W z.1 z.2 (-k)) =
      w k * W (-k) * fourierTransport W W k := by
    rw [(hs.prod_factor k).tsum_prod, hm]
  have hh := hs.hasSum.prod_fiberwise (fun k =>
    ((hs.prod_factor k).hasSum_iff.mpr (ht k)))
  have heq : (∑' z : Wave × Wave × Wave, RealPoly.triad w W z.2.1 z.2.2 (-z.1)) =
      ∑' z : Wave × Wave × Wave, RealPoly.triad w W z.1 z.2.1 z.2.2 :=
    e.tsum_eq (fun z => RealPoly.triad w W z.1 z.2.1 z.2.2)
  rw [heq, ← fourierFlux_eq_triad hw he hW hD] at hh
  exact hh

/-- The enstrophy pairing of an even summable coefficient sequence vanishes. -/
theorem hasSum_enstrophy_transport {W : Wave → ℝ} (he : ∀ k, W (-k) = W k)
    (hW : Summable (fun k => |W k|)) (hD : Summable (fun k => (size k : ℝ) * |W k|)) :
    HasSum (fun k => W k * fourierTransport W W k) 0 := by
  have h := hasSum_fourierPairing (w := fun _ => 1) (fun _ => by norm_num) (fun _ => rfl) hW hD
  simpa only [one_mul, he, fourier_enstrophy_flux_zero hW hD] using h

/-- The energy pairing of an even summable coefficient sequence vanishes. -/
theorem hasSum_energy_transport {W : Wave → ℝ} (he : ∀ k, W (-k) = W k)
    (hW : Summable (fun k => |W k|)) (hD : Summable (fun k => (size k : ℝ) * |W k|)) :
    HasSum (fun k => (lam k : ℝ)⁻¹ * W k * fourierTransport W W k) 0 := by
  have h := hasSum_fourierPairing inv_lam_abs_le_one (fun k => by rw [lam_neg]) hW hD
  simpa only [he, fourier_energy_flux_zero hW hD] using h

#print axioms hasSum_fourierPairing
end Gimle.Asgard.Streams.Mild
