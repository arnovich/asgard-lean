import Gimle.Asgard.Streams.MildEvaluation
import Gimle.Asgard.Streams.TrigNorm

/-! Heat-kernel estimates for physical evaluation of exact mild terms.
The output zero mode is handled without division by its heat rate. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Set

/-- The derivative loss belongs to the output mode, with totalized division
also covering the zero input mode. -/
theorem coupling_sq_le (p q : Wave) :
    coupling p q ^ 2 ≤ (lam (p + q) : ℚ) / lam p := by
  by_cases hp : p = 0
  · subst p; simp [coupling]
  have hl : (0 : ℚ) < lam p := by exact_mod_cast lam_pos hp
  have hc : cross p (p + q) = cross p q := by simp [cross]; ring
  have h := cross_sq_le p (p + q)
  rw [hc] at h
  have h' : (cross p q : ℚ) ^ 2 ≤ (lam p : ℚ) * lam (p + q) := by exact_mod_cast h
  rw [coupling, div_pow, div_le_div_iff₀ (sq_pos_of_pos hl) hl]
  nlinarith [mul_le_mul_of_nonneg_right h' hl.le]

/-- A square-free heat absorption estimate. -/
theorem coupling_heat_min_le (p q : Wave) {ν T r : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hr : 0 ≤ r) (hTr : T ≤ ν * r ^ 2) :
    |(coupling p q : ℝ)| * min T (1 / (ν * lam (p + q))) ≤ r := by
  by_cases hp : p = 0
  · subst p; simpa [coupling] using hr
  by_cases hk : p + q = 0
  · have hq : q = -p := eq_neg_of_add_eq_zero_right hk
    subst q; simpa using hr
  have hl : (0 : ℝ) < lam (p + q) := by exact_mod_cast lam_pos hk
  have hp1 : (1 : ℝ) ≤ lam p := by exact_mod_cast lam_pos hp
  have hc : (coupling p q : ℝ) ^ 2 ≤ (lam (p + q) : ℝ) / lam p := by
    exact_mod_cast coupling_sq_le p q
  have hc' : (coupling p q : ℝ) ^ 2 ≤ lam (p + q) :=
    hc.trans (div_le_self hl.le hp1)
  let z := min T (1 / (ν * lam (p + q)))
  have hz : 0 ≤ z := le_min hT (by positivity)
  have hzT : z ≤ T := min_le_left _ _
  have hza : z * (ν * lam (p + q)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hzz : ν * lam (p + q) * z ^ 2 ≤ T := by
    nlinarith [mul_le_mul_of_nonneg_right hza hz]
  have habs : |(coupling p q : ℝ)| ^ 2 = (coupling p q : ℝ) ^ 2 := sq_abs _
  have hczz := mul_le_mul_of_nonneg_right hc' (sq_nonneg z)
  have hfinal : (|(coupling p q : ℝ)| * z) ^ 2 ≤ r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hczz hν.le
    apply (mul_le_mul_iff_right₀ hν).mp
    calc ν * (|(coupling p q : ℝ)| * z) ^ 2
        = ν * ((coupling p q : ℝ) ^ 2 * z ^ 2) := by rw [mul_pow, habs]
      _ ≤ ν * (lam (p + q) * z ^ 2) := this
      _ ≤ ν * r ^ 2 := by nlinarith
  exact le_of_sq_le_sq hfinal hr

/-- Nonnegative viscosity makes the heat kernel a contraction forward in time. -/
theorem heat_kernel_le_one {a t s : ℝ} (ha : 0 ≤ a) (hst : s ≤ t) :
    exp (-(a * (t - s))) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)

/-- A continuous scalar forcing is bounded by its absolute time integral. -/
theorem abs_heat_integral_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    {f : ℝ → ℝ} (hf : Continuous f) :
    |∫ s in (0 : ℝ)..t, exp (-(a * (t - s))) * f s| ≤
      ∫ s in (0 : ℝ)..t, |f s| := by
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  apply intervalIntegral.integral_mono_on ht
    (((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id)).neg).mul hf).abs.intervalIntegrable 0 t)
    (hf.abs.intervalIntegrable 0 t)
  intro s hs
  dsimp only [Pi.mul_apply, Function.comp_apply, Pi.neg_apply, Pi.sub_apply, id_eq]
  rw [abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (heat_kernel_le_one ha hs.2)

/-- A uniform forcing bound gives the linear-in-time Duhamel bound. -/
theorem abs_heat_integral_le_time {a t A : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    {f : ℝ → ℝ} (hf : Continuous f) (hA : ∀ s ∈ Icc 0 t, |f s| ≤ A) :
    |∫ s in (0 : ℝ)..t, exp (-(a * (t - s))) * f s| ≤ t * A := by
  refine (abs_heat_integral_le ha ht hf).trans ?_
  calc (∫ s in (0 : ℝ)..t, |f s|) ≤ ∫ _ in (0 : ℝ)..t, A :=
      intervalIntegral.integral_mono_on ht (hf.abs.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) hA
    _ = t * A := by simp

/-- The integral of a positive-rate heat kernel. -/
theorem integral_heat_kernel {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, exp (-(a * (t - s)))) = (1 - exp (-(a * t))) / a := by
  have hd (s : ℝ) : HasDerivAt (fun s => exp (-(a * (t - s))) / a)
      (exp (-(a * (t - s)))) s := by
    have h := ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul a).neg.exp).div_const a
    convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id)).neg).intervalIntegrable 0 t)
  simpa [sub_div] using hi

/-- A positive heat rate absorbs the time integral uniformly. -/
theorem abs_heat_integral_le_rate {a t A : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    {f : ℝ → ℝ} (hf : Continuous f) (hA : ∀ s ∈ Icc 0 t, |f s| ≤ A) :
    |∫ s in (0 : ℝ)..t, exp (-(a * (t - s))) * f s| ≤ A / a := by
  have hA0 : 0 ≤ A := (abs_nonneg (f 0)).trans (hA 0 ⟨le_rfl, ht⟩)
  have hc : Continuous (fun s => exp (-(a * (t - s)))) := by fun_prop
  calc |∫ s in (0 : ℝ)..t, exp (-(a * (t - s))) * f s|
      ≤ ∫ s in (0 : ℝ)..t, |exp (-(a * (t - s))) * f s| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ s in (0 : ℝ)..t, exp (-(a * (t - s))) * A := by
        apply intervalIntegral.integral_mono_on ht
          ((hc.mul hf).abs.intervalIntegrable 0 t)
          ((hc.mul continuous_const).intervalIntegrable 0 t)
        intro s hs
        dsimp only [Pi.mul_apply]
        rw [abs_mul, abs_of_pos (exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hA s hs) (exp_pos _).le
    _ = (1 - exp (-(a * t))) / a * A := by
        rw [intervalIntegral.integral_mul_const, integral_heat_kernel ha]
    _ ≤ A / a := by
        have := mul_nonneg (exp_pos (-(a * t))).le hA0
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha]
        nlinarith

/-- Physical Duhamel evaluation is bounded by the integral of physical forcing. -/
theorem eval_duhamel_abs_le {ν : ℚ} (hν : 0 ≤ ν) (μ : ℕ) (P : ExpPoly)
    {t : ℝ} (ht : 0 ≤ t) :
    |ExpPoly.eval ν t (ExpPoly.duhamel ν μ P)| ≤
      ∫ s in (0 : ℝ)..t, |ExpPoly.eval ν s P| := by
  rw [ExpPoly.eval_duhamel]
  exact abs_heat_integral_le (mul_nonneg (by exact_mod_cast hν) (Nat.cast_nonneg _))
    ht (ExpPoly.continuous_eval ν P)

#print axioms coupling_sq_le
#print axioms coupling_heat_min_le
#print axioms eval_duhamel_abs_le
end Gimle.Asgard.Streams.Mild
