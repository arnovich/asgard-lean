import Gimle.Asgard.Streams.MildFourierSeries

/-! Differentiating spectral quadratic quantities under summable, uniform
mode envelopes. The bounds concern evaluated physical coefficients. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Set

/-- Uniform mode control sufficient to differentiate a spectral square sum. -/
structure ModeControl (f f' : ℝ → Wave → ℝ) (T : ℝ) where
  valueBound : Wave → ℝ
  derivBound : Wave → ℝ
  value_nonneg : ∀ k, 0 ≤ valueBound k
  deriv_nonneg : ∀ k, 0 ≤ derivBound k
  value_summable : Summable valueBound
  deriv_summable : Summable derivBound
  value_le : ∀ t ∈ Icc 0 T, ∀ k, |f t k| ≤ valueBound k
  deriv_le : ∀ t ∈ Icc 0 T, ∀ k, |f' t k| ≤ derivBound k
  continuous : ∀ k, ContinuousOn (fun t => f t k) (Icc 0 T)
  hasDeriv : ∀ t ∈ Ioo 0 T, ∀ k, HasDerivAt (fun s => f s k) (f' t k) t

/-- Evaluated mild coefficients possess uniform summable mode control. -/
noncomputable def modeControl_of_bounds {ν : ℚ} {ω : Stream} {K : ℕ} {T C D q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ t ∈ Icc 0 T, ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (hd : ∀ t ∈ Icc 0 T, ∀ n, RealPoly.l1 (eval ν t (deriv ν (ω n))) ≤
      D * (((n : ℝ) + 1) ^ 2 * q ^ n)) :
    ModeControl (fourierCoeff ν ω) (fourierDt ν ω) T := by
  let a : ℕ → ℝ := fun n => C * q ^ n
  let d : ℕ → ℝ := fun n => D * (((n : ℝ) + 1) ^ 2 * q ^ n)
  let δω : Stream := fun n => deriv ν (ω n)
  have ha : ∀ n, 0 ≤ a n := fun _ => by dsimp [a]; positivity
  have hd' : ∀ n, 0 ≤ d n := fun _ => by dsimp [d]; positivity
  have hKd (n : ℕ) : SizeLE ((n + 1) * K) (δω n) :=
    fun k hk => hK n k (support_deriv_subset ν (ω n) hk)
  have sa : Summable (fun n => ((ω n).support.card : ℝ) * a n) := by
    simpa [a] using summable_support_geometric ω hK hC hq hq1 0
  have sd := summable_support_geometric δω hKd hD hq hq1 2
  refine ⟨modeEnvelope ω a, modeEnvelope δω d, modeEnvelope_nonneg ω ha,
    modeEnvelope_nonneg δω hd', summable_modeEnvelope ω ha sa,
    summable_modeEnvelope δω hd' sd, ?_, ?_, ?_, ?_⟩
  · exact fun t ht k => abs_fourierCoeff_le ha sa (h t ht) k
  · exact fun t ht k => abs_fourierCoeff_le hd' sd (hd t ht) k
  · intro k
    exact continuousOn_tsum (fun n => (ExpPoly.continuous_eval ν (ω n k)).continuousOn)
      (summable_envelope_degree ω ha sa k) (fun n t ht => by
        rw [Real.norm_eq_abs]; exact abs_eval_le_envelope (h t ht n) k)
  · intro t ht k
    exact hasDerivAt_tsum_of_isPreconnected (summable_envelope_degree δω hd' sd k)
      isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
      (fun n s _ => ExpPoly.hasDerivAt ν (ω n k) s)
      (fun n s hs => by
        rw [Real.norm_eq_abs]; exact abs_eval_le_envelope (hd s ⟨hs.1.le, hs.2.le⟩ n) k)
      (y₀ := t) ht (summable_norm_coeff ha sa (h t ⟨ht.1.le, ht.2.le⟩) k).of_norm ht

namespace ModeControl
variable {f f' : ℝ → Wave → ℝ} {T : ℝ} (h : ModeControl f f' T)
include h

/-- The total envelope bounds every mode. -/
theorem value_le_total (k : Wave) : h.valueBound k ≤ ∑' j, h.valueBound j :=
  h.value_summable.le_tsum k (fun j _ => h.value_nonneg j)

/-- The quadratic value series has a uniform summable envelope. -/
theorem abs_square_le {w : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (k : Wave) :
    |w k * (f t k) ^ 2| ≤ (∑' j, h.valueBound j) * h.valueBound k := by
  rw [abs_mul, abs_pow]
  have hv := h.value_nonneg k
  calc |w k| * |f t k| ^ 2 ≤ 1 * (h.valueBound k) ^ 2 := by
         gcongr; exact hw k; exact h.value_le t ht k
       _ ≤ (∑' j, h.valueBound j) * h.valueBound k := by
         nlinarith [mul_le_mul_of_nonneg_right (h.value_le_total k) (h.value_nonneg k)]

/-- The differentiated square series has its own summable envelope. -/
theorem abs_square_deriv_le {w : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) (k : Wave) :
    |w k * (2 * f t k * f' t k)| ≤ (2 * ∑' j, h.valueBound j) * h.derivBound k := by
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hv := h.value_nonneg k
  have hd := h.deriv_nonneg k
  calc |w k| * (2 * |f t k| * |f' t k|)
       ≤ 1 * (2 * h.valueBound k * h.derivBound k) := by
          gcongr; exact hw k; exact h.value_le t ht k; exact h.deriv_le t ht k
       _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_right (h.value_le_total k) (h.deriv_nonneg k)]

/-- Absolute convergence of each spectral square sum. -/
theorem summable_norm_square {w : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Summable (fun k => ‖w k * (f t k) ^ 2‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
    rw [Real.norm_eq_abs]; exact h.abs_square_le hw ht k)
    (h.value_summable.mul_left _)

/-- Absolute convergence of the differentiated spectral square sum. -/
theorem summable_norm_square_deriv {w : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Summable (fun k => ‖w k * (2 * f t k * f' t k)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
    rw [Real.norm_eq_abs]; exact h.abs_square_deriv_le hw ht k)
    (h.deriv_summable.mul_left _)

/-- Closed-interval continuity of a spectral square sum. -/
theorem continuousOn_square {w : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1) :
    ContinuousOn (fun t => ∑' k, w k * (f t k) ^ 2) (Icc 0 T) :=
  continuousOn_tsum (fun k => ((h.continuous k).pow 2).const_mul (w k))
    (h.value_summable.mul_left _) (fun k t ht => by
      rw [Real.norm_eq_abs]; exact h.abs_square_le hw ht k)

/-- Differentiate the sum over Fourier modes, using its own uniform majorant. -/
theorem hasDerivAt_square {w : Wave → ℝ} (hw : ∀ k, |w k| ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => ∑' k, w k * (f s k) ^ 2)
      (∑' k, w k * (2 * f t k * f' t k)) t := by
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun k s => w k * (f s k) ^ 2)
    (g' := fun k s => w k * (2 * f s k * f' s k))
    (h.deriv_summable.mul_left (2 * ∑' j, h.valueBound j))
    isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun k s hs => ?_) (fun k s hs => ?_) (y₀ := t) ht
    (h.summable_norm_square hw ⟨ht.1.le, ht.2.le⟩).of_norm ht
  · simpa using ((h.hasDeriv s hs k).pow 2).const_mul (w k)
  · rw [Real.norm_eq_abs]
    exact h.abs_square_deriv_le hw ⟨hs.1.le, hs.2.le⟩ k

end ModeControl
#print axioms modeControl_of_bounds
#print axioms ModeControl.hasDerivAt_square
end Gimle.Asgard.Streams.Mild
