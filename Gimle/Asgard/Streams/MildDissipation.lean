import Gimle.Asgard.Streams.MildFourierPDE
import Gimle.Asgard.Streams.SpectralDissipation

/-! Both dissipation identities for the actual mild circuit stream, on the
closed interval certified by either physical bound. -/
namespace Gimle.Asgard.Streams.Mild
open Torus Real Set

/-- Infinite energy and enstrophy identities, including closed-interval control. -/
structure HasDissipation (ν : ℚ) (ω : Stream) (T : ℝ) : Prop where
  summable : ∀ t ∈ Icc 0 T, ∀ d : ℕ,
    Summable (fun k => (size k : ℝ) ^ d * |fourierCoeff ν ω t k|)
  enstrophy_continuous : ContinuousOn (fun t => enstrophy (fourierCoeff ν ω t)) (Icc 0 T)
  energy_continuous : ContinuousOn (fun t => energy (fourierCoeff ν ω t)) (Icc 0 T)
  enstrophy_deriv : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => enstrophy (fourierCoeff ν ω s))
      (-2 * (ν : ℝ) * palinstrophy (fourierCoeff ν ω t)) t
  energy_deriv : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => energy (fourierCoeff ν ω s))
      (-2 * (ν : ℝ) * enstrophy (fourierCoeff ν ω t)) t
  enstrophy_antitone : AntitoneOn (fun t => enstrophy (fourierCoeff ν ω t)) (Icc 0 T)
  energy_antitone : AntitoneOn (fun t => energy (fourierCoeff ν ω t)) (Icc 0 T)

/-- Either geometric convergence bound supplies the two dissipation identities.
The internal positive ratio also covers exact zero data and zero viscosity. -/
theorem mild_dissipation {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly)
    (hb : b 0 = embed P) (hb0 : Torus.MeanZero P) (hbe : Torus.IsEven P)
    {K : ℕ} (hK : Torus.SizeLE K P) {T M q : ℝ} (hT : 0 ≤ T)
    (h : GeometricBound ν (wild ν b) T M q) (hq : 0 ≤ q) (hq1 : q < 1) :
    HasDissipation ν (wild ν b) T := by
  have hK' : SizeLE K (b 0) := by rw [hb]; exact sizeLE_embed hK
  have hz : MeanZero (b 0) := by rw [hb]; exact meanZero_embed hb0
  have he : IsEven (b 0) := by rw [hb]; exact isEven_embed hbe
  have hv : (0 : ℝ) ≤ ν := by exact_mod_cast hν
  have hM : 0 ≤ M := by
    have hh := (RealPoly.l1_nonneg (eval ν 0 (wild ν b 0))).trans (h 0 ⟨le_rfl, hT⟩ 0)
    simpa using hh
  let q' := (q + 1) / 2
  have hq' : 0 < q' := by dsimp [q']; linarith
  have hq1' : q' < 1 := by dsimp [q']; linarith
  have hqq : q ≤ q' := by dsimp [q']; linarith
  have h' : GeometricBound ν (wild ν b) T M q' := by
    intro t ht n
    exact (h t ht n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqq n) hM)
  have hKn := wild_sizeLE ν b K hK'
  have hD : 0 ≤ (ν : ℝ) * K ^ 2 * M + (K : ℝ) * M ^ 2 / q' := by positivity
  let hc : ModeControl (fourierCoeff ν (wild ν b)) (fourierDt ν (wild ν b)) T :=
    modeControl_of_bounds hKn hM hD hq'.le hq1' h'
      (fun t ht n => wild_deriv_l1_le hν b P hb hK' h' hq' hM ht n)
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) (d : ℕ) :
      Summable (fun k => (size k : ℝ) ^ d * |fourierCoeff ν (wild ν b) t k|) :=
    summable_weighted_coeff hKn hM hq'.le hq1' (h' t ht) d
  have he' (t : ℝ) (_ht : t ∈ Icc 0 T) (k : Wave) := fourierCoeff_even (ν := ν) b he t k
  have hz' (t : ℝ) (_ht : t ∈ Icc 0 T) := fourierCoeff_meanZero (ν := ν) b hz t
  have hp (t : ℝ) (ht : t ∈ Ioo 0 T) (k : Wave) :=
    fourierDt_eq hν b P hb hK' h' hq' hq1' hM ⟨ht.1.le, ht.2.le⟩ k
  refine ⟨hs, ?_, hc.continuousOn_square inv_lam_abs_le_one,
    fun _ ht => hasDerivAt_enstrophy hc he' hs hp ht,
    fun _ ht => hasDerivAt_energy hc he' hz' hs hp ht,
    antitoneOn_enstrophy hc he' hs hp hv, antitoneOn_energy hc he' hz' hs hp hv⟩
  simpa only [one_mul, enstrophy] using hc.continuousOn_square (w := fun _ => 1) (fun _ => by norm_num)

/-- Enstrophy is bounded by its initial value throughout the certified interval. -/
theorem HasDissipation.enstrophy_le_initial {ν : ℚ} {ω : Stream} {T t : ℝ}
    (h : HasDissipation ν ω T) (ht : t ∈ Icc 0 T) :
    enstrophy (fourierCoeff ν ω t) ≤ enstrophy (fourierCoeff ν ω 0) :=
  h.enstrophy_antitone ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

/-- Energy is bounded by its initial value throughout the certified interval. -/
theorem HasDissipation.energy_le_initial {ν : ℚ} {ω : Stream} {T t : ℝ}
    (h : HasDissipation ν ω T) (ht : t ∈ Icc 0 T) :
    energy (fourierCoeff ν ω t) ≤ energy (fourierCoeff ν ω 0) :=
  h.energy_antitone ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

#print axioms mild_dissipation
end Gimle.Asgard.Streams.Mild
