import Gimle.Asgard.Streams.MildTimeDerivatives

/-! The convergent physical mild series satisfies the vorticity PDE and the
stream-function Laplacian. These identities refer to the actual Wild output. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

/-- Cauchy multiplication of physical interaction series. -/
theorem tsum_mul_tsum_interaction {a b : ℕ → ℝ}
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    (∑' n, a n) * (∑' n, b n) = ∑' n, ∑ m ∈ Finset.range (n + 1), a m * b (n - m) := by
  simpa using TrigStream.tsum_mul_tsum_pow (t := 1) (by simpa using ha) (by simpa using hb)

/-- Absolute convergence makes the physical Cauchy series summable. -/
theorem summable_cauchy_interaction {a b : ℕ → ℝ}
    (ha : Summable (fun n => ‖a n‖)) (hb : Summable (fun n => ‖b n‖)) :
    Summable (fun n => ∑ m ∈ Finset.range (n + 1), a m * b (n - m)) := by
  simpa using TrigStream.summable_cauchy_pow (t := 1) (by simpa using ha) (by simpa using hb)

/-- The real field is linear under subtraction. -/
theorem RealPoly.field_sub (P Q : RealPoly) (x : ℝ × ℝ) :
    RealPoly.field (P - Q) x = RealPoly.field P x - RealPoly.field Q x := by
  rw [sub_eq_add_neg, RealPoly.field_add, RealPoly.field_neg, sub_eq_add_neg]

variable {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P)
  {K : ℕ} (hK : SizeLE K (b 0)) {T M q : ℝ}
  (h : GeometricBound ν (wild ν b) T M q) (hq : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)

local notation "ω" => wild ν b

include hν hb hK h hq hq1 hM

/-- Summing the exact physical term equations yields the viscous vorticity identity. -/
theorem seriesDt_eq (hbe : IsEven (b 0)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : ℝ × ℝ) :
    seriesDt ν ω t x = (ν : ℝ) * (seriesD₁₁ ν ω t x + seriesD₂₂ ν ω t x) -
      (seriesD₁ ν (psi ω) t x * seriesD₂ ν ω t x - seriesD₂ ν (psi ω) t x * seriesD₁ ν ω t x) := by
  have hKn := wild_sizeLE ν b K hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  have s1 := summable_norm_spatial hψ hKψ ht hq.le hq1 (k := 1)
    (fun _ _ y hs => by simpa using RealPoly.abs_fieldD₁_le hs y) x
  have s2 := summable_norm_spatial h hKn ht hq.le hq1 (k := 1)
    (fun _ _ y hs => by simpa using RealPoly.abs_fieldD₂_le hs y) x
  have s3 := summable_norm_spatial hψ hKψ ht hq.le hq1 (k := 1)
    (fun _ _ y hs => by simpa using RealPoly.abs_fieldD₂_le hs y) x
  have s4 := summable_norm_spatial h hKn ht hq.le hq1 (k := 1)
    (fun _ _ y hs => by simpa using RealPoly.abs_fieldD₁_le hs y) x
  have sl1 := (summable_norm_spatial h hKn ht hq.le hq1
    (fun _ _ y hs => RealPoly.abs_fieldD₁₁_le hs y) x).of_norm
  have sl2 := (summable_norm_spatial h hKn ht hq.le hq1
    (fun _ _ y hs => RealPoly.abs_fieldD₂₂_le hs y) x).of_norm
  let L := fun n => RealPoly.field (RealPoly.laplacian (eval ν t (ω n))) x
  let C := fun n => ∑ m ∈ Finset.range (n + 1),
    RealPoly.field (RealPoly.transport (eval ν t (ω m)) (eval ν t (ω (n - m)))) x
  have hL (n : ℕ) : L n = RealPoly.fieldD₁₁ (eval ν t (ω n)) x +
      RealPoly.fieldD₂₂ (eval ν t (ω n)) x := RealPoly.field_laplacian _ _
  have hC (n : ℕ) : C n =
      (∑ m ∈ Finset.range (n + 1), RealPoly.fieldD₁ (eval ν t (psi ω m)) x *
        RealPoly.fieldD₂ (eval ν t (ω (n - m))) x) -
      ∑ m ∈ Finset.range (n + 1), RealPoly.fieldD₂ (eval ν t (psi ω m)) x *
        RealPoly.fieldD₁ (eval ν t (ω (n - m))) x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [RealPoly.field_transport _ (isEven_eval ν t (wild_isEven ν b hbe (n - m))) x]
    simp only [psi, eval_laplacianInv]
  have sL : Summable L := (sl1.add sl2).congr (fun n => (hL n).symm)
  have sC : Summable C := ((summable_cauchy_interaction s1 s2).sub
    (summable_cauchy_interaction s3 s4)).congr (fun n => (hC n).symm)
  have he0 : RealPoly.field (eval ν t (deriv ν (ω 0))) x = (ν : ℝ) * L 0 := by
    rw [eval_deriv_wild_zero ν b P hb, RealPoly.field_smul]
  have hes (n : ℕ) : RealPoly.field (eval ν t (deriv ν (ω (n + 1)))) x =
      (ν : ℝ) * L (n + 1) - C n := by
    rw [eval_deriv_wild_succ, RealPoly.field_sub, RealPoly.field_smul, RealPoly.field_finset_sum]
  have sd := (summable_norm_time hν b P hb hK h hq hq1 hM ht x).of_norm
  have he : seriesDt ν ω t x = (ν : ℝ) * (∑' n, L n) - ∑' n, C n := by
    rw [seriesDt, sd.tsum_eq_zero_add, he0]
    simp_rw [hes]
    have ss0 : Summable (fun n => L (n + 1)) := (summable_nat_add_iff 1).mpr sL
    have ss : Summable (fun n => (ν : ℝ) * L (n + 1)) := ss0.mul_left _
    rw [ss.tsum_sub sC,
      tsum_mul_left, sL.tsum_eq_zero_add]
    ring
  rw [he]
  have hls : (∑' n, L n) = seriesD₁₁ ν ω t x + seriesD₂₂ ν ω t x := by
    simp_rw [hL]
    exact sl1.tsum_add sl2
  have hcs : (∑' n, C n) = seriesD₁ ν (psi ω) t x * seriesD₂ ν ω t x -
      seriesD₂ ν (psi ω) t x * seriesD₁ ν ω t x := by
    simp_rw [hC]
    rw [(summable_cauchy_interaction s1 s2).tsum_sub (summable_cauchy_interaction s3 s4),
      ← tsum_mul_tsum_interaction s1 s2, ← tsum_mul_tsum_interaction s3 s4]
    rfl
  rw [hls, hcs]

omit hν hb hM in
/-- The stream function's Laplacian recovers the mean-zero vorticity field. -/
theorem series_laplacian_psi (hb0 : MeanZero (b 0)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : ℝ × ℝ) :
    seriesD₁₁ ν (psi ω) t x + seriesD₂₂ ν (psi ω) t x = analyticField ν ω t x := by
  have hKn := wild_sizeLE ν b K hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  have s1 := (summable_norm_spatial hψ hKψ ht hq.le hq1
    (fun _ _ y hs => RealPoly.abs_fieldD₁₁_le hs y) x).of_norm
  have s2 := (summable_norm_spatial hψ hKψ ht hq.le hq1
    (fun _ _ y hs => RealPoly.abs_fieldD₂₂_le hs y) x).of_norm
  rw [seriesD₁₁, seriesD₂₂, ← s1.tsum_add s2, analyticField]
  apply tsum_congr
  intro n
  simp only [seriesTerm, psi, eval_laplacianInv]
  rw [← RealPoly.field_laplacian,
    RealPoly.laplacian_laplacianInv (meanZero_eval ν t (wild_meanZero ν b hb0 n))]

#print axioms seriesDt_eq
#print axioms series_laplacian_psi
end Gimle.Asgard.Streams.Mild
