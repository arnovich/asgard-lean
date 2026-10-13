import Gimle.Asgard.Streams.RealTrigNorm
import Gimle.Asgard.Streams.MildHeatBounds

/-! Weighted norms of physically evaluated mild coefficients and their
heat/Duhamel estimates. All time integrals are forward from zero. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Set

/-- The physical weighted Fourier norm. -/
noncomputable def mwnorm (σ : ℝ) (ν : ℚ) (P : MildPoly) (t : ℝ) : ℝ :=
  RealPoly.wnorm σ (eval ν t P)

/-- The physical norm of one spatial derivative. -/
noncomputable def mdnorm (σ : ℝ) (ν : ℚ) (P : MildPoly) (t : ℝ) : ℝ :=
  RealPoly.dnorm σ (eval ν t P)

/-- Evaluation cannot create a Fourier mode. -/
theorem support_eval_subset (ν : ℚ) (t : ℝ) (P : MildPoly) :
    (eval ν t P).support ⊆ P.support := by
  intro k hk
  rw [Finsupp.mem_support_iff] at hk ⊢
  intro hz
  exact hk (by simp [hz])

theorem mwnorm_eq_sum (σ : ℝ) (ν : ℚ) (P : MildPoly) (t : ℝ) :
    mwnorm σ ν P t = ∑ k ∈ P.support, |ExpPoly.eval ν t (P k)| * exp (σ * size k) :=
  RealPoly.wnorm_eq_sum σ (support_eval_subset ν t P)

theorem mwnorm_nonneg (σ : ℝ) (ν : ℚ) (P : MildPoly) (t : ℝ) : 0 ≤ mwnorm σ ν P t :=
  RealPoly.wnorm_nonneg _ _

theorem mdnorm_nonneg (σ : ℝ) (ν : ℚ) (P : MildPoly) (t : ℝ) : 0 ≤ mdnorm σ ν P t :=
  RealPoly.dnorm_nonneg _ _

theorem continuous_mwnorm (σ : ℝ) (ν : ℚ) (P : MildPoly) : Continuous (mwnorm σ ν P) := by
  simp only [funext (mwnorm_eq_sum σ ν P)]
  exact continuous_finsetSum _ (fun k _ => (ExpPoly.continuous_eval ν (P k)).abs.mul continuous_const)

theorem mwnorm_neg (σ : ℝ) (ν : ℚ) (P : MildPoly) (t : ℝ) :
    mwnorm σ ν (-P) t = mwnorm σ ν P t := by
  rw [mwnorm_eq_sum, mwnorm_eq_sum]
  simp only [Finsupp.support_neg, Finsupp.neg_apply, map_neg, abs_neg]

theorem mwnorm_sum_le {ι : Type*} (σ : ℝ) (ν : ℚ) (s : Finset ι)
    (f : ι → MildPoly) (t : ℝ) :
    mwnorm σ ν (∑ i ∈ s, f i) t ≤ ∑ i ∈ s, mwnorm σ ν (f i) t := by
  simpa only [mwnorm, map_sum] using RealPoly.wnorm_sum_le σ s (fun i => eval ν t (f i))

theorem mwnorm_mono {σ σ' : ℝ} (h : σ ≤ σ') (ν : ℚ) (P : MildPoly) (t : ℝ) :
    mwnorm σ ν P t ≤ mwnorm σ' ν P t := RealPoly.wnorm_mono h _

theorem mwnorm_transport_le {σ : ℝ} (hσ : 0 ≤ σ) (ν : ℚ) (P Q : MildPoly) (t : ℝ) :
    mwnorm σ ν (transport P Q) t ≤ mwnorm σ ν P t * mdnorm σ ν Q t := by
  simpa only [mwnorm, mdnorm, eval_transport] using
    RealPoly.wnorm_transport_le hσ (eval ν t P) (eval ν t Q)

theorem mdnorm_le_mwnorm_div {σ σ' : ℝ} (h : σ < σ') (ν : ℚ) (P : MildPoly) (t : ℝ) :
    mdnorm σ ν P t ≤ mwnorm σ' ν P t / (2 * (σ' - σ)) :=
  RealPoly.dnorm_le_wnorm_div h _

/-- Heat evolution contracts every weighted norm at forward physical times. -/
theorem mwnorm_heat_embed_le (σ : ℝ) {ν : ℚ} (hν : 0 ≤ ν) (P : TrigPoly)
    {t : ℝ} (ht : 0 ≤ t) : mwnorm σ ν (heat (embed P)) t ≤ Torus.wnorm σ P := by
  have hs : (eval ν t (heat (embed P))).support ⊆ P.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro hz
    exact hk (by simp [hz])
  rw [mwnorm, RealPoly.wnorm_eq_sum σ hs, Torus.wnorm_eq_sum σ subset_rfl]
  apply Finset.sum_le_sum
  intro k _
  simp only [eval_apply, heat_apply, map_mul, ExpPoly.eval_single, map_one,
    one_mul, embed_apply, AlgHom.commutes]
  rw [abs_mul, abs_of_pos (exp_pos _)]
  have he : exp (-((ν : ℝ) * heatRate k * t)) ≤ 1 :=
    exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg
      (mul_nonneg (by exact_mod_cast hν) (Nat.cast_nonneg _)) ht))
  calc exp (-((ν : ℝ) * heatRate k * t)) * |(P k : ℝ)| * exp (σ * size k)
      ≤ 1 * |(P k : ℝ)| * exp (σ * size k) := by gcongr
    _ = _ := by ring

/-- The weighted Duhamel norm is bounded by the time integral of the forcing norm. -/
theorem mwnorm_duhamel_le (σ : ℝ) {ν : ℚ} (hν : 0 ≤ ν) (P : MildPoly)
    {t : ℝ} (ht : 0 ≤ t) :
    mwnorm σ ν (duhamel ν P) t ≤ ∫ s in (0 : ℝ)..t, mwnorm σ ν P s := by
  have hs : (eval ν t (duhamel ν P)).support ⊆ P.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro hz
    exact hk (by simp [hz])
  rw [mwnorm, RealPoly.wnorm_eq_sum σ hs]
  simp_rw [mwnorm_eq_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_le_sum
    intro k _
    rw [intervalIntegral.integral_mul_const]
    exact mul_le_mul_of_nonneg_right (eval_duhamel_abs_le hν (heatRate k) (P k) ht) (exp_pos _).le
  · intro k _
    exact ((ExpPoly.continuous_eval ν (P k)).abs.mul continuous_const).intervalIntegrable 0 t

#print axioms mwnorm_heat_embed_le
#print axioms mwnorm_duhamel_le
#print axioms mwnorm_transport_le
end Gimle.Asgard.Streams.Mild
