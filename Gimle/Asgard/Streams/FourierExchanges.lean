import Gimle.Asgard.Streams.FourierSequence

/-! Absolute exchanges between interaction degree and Fourier mode. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

/-- Flatten four independently summable indices. -/
theorem tsum_four {A B C D : Type*} {F : A → B → C → D → ℝ}
    (h : Summable (fun z : (A × B) × C × D => F z.1.1 z.1.2 z.2.1 z.2.2)) :
    (∑' z : (A × B) × C × D, F z.1.1 z.1.2 z.2.1 z.2.2) =
      ∑' a, ∑' b, ∑' c, ∑' d, F a b c d := by
  rw [h.tsum_prod, h.prod.tsum_prod]
  exact tsum_congr (fun a => tsum_congr (fun b => (h.prod_factor (a, b)).tsum_prod))

/-- A geometric physical stream is absolutely summable jointly in degree and weighted mode. -/
theorem summable_degree_mode_weighted {ν : ℚ} {ω : Stream} {K : ℕ} {t C q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (d : ℕ) : Summable (fun z : ℕ × Wave => (size z.2 : ℝ) ^ d * |ExpPoly.eval ν t (ω z.1 z.2)|) := by
  let a : ℕ → ℝ := fun n => C * (K : ℝ) ^ d * (((n : ℝ) + 1) ^ d * q ^ n)
  have ha : ∀ n, 0 ≤ a n := fun n => by dsimp [a]; positivity
  have hs := summable_support_geometric ω hK (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg K) d)) hq hq1 d
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    (summable_degree_mode_envelope ω ha hs)
  split_ifs with hk
  · have hk' : (size z.2 : ℝ) ≤ ((z.1 : ℝ) + 1) * K := by exact_mod_cast hK z.1 z.2 hk
    have hc := (RealPoly.abs_apply_le_l1 (eval ν t (ω z.1)) z.2).trans (h z.1)
    calc (size z.2 : ℝ) ^ d * |ExpPoly.eval ν t (ω z.1 z.2)|
        ≤ (((z.1 : ℝ) + 1) * K) ^ d * (C * q ^ z.1) := by gcongr; exact hc
        _ = a z.1 := by dsimp [a]; rw [mul_pow]; ring
  · rw [eval_apply_eq_zero hk, abs_zero, mul_zero]

/-- A finite polynomial's Fourier transport agrees with the infinite formula. -/
theorem fourierTransport_finite (P Q : RealPoly) (k : Wave) :
    fourierTransport P Q k = RealPoly.transport P Q k := by
  rw [fourierTransport, RealPoly.transport_apply, tsum_eq_sum (s := P.support)]
  · apply Finset.sum_congr rfl
    intro p _
    exact tsum_eq_sum (fun q hq => by rw [Finsupp.notMem_support_iff.mp hq]; split_ifs <;> simp)
  · intro p hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp

/-- The transport summand before summing degree or mode. -/
noncomputable def transportTerm (ν : ℚ) (ω : Stream) (t : ℝ) (k : Wave)
    (n : ℕ) (p : Wave) (m : ℕ) (q : Wave) : ℝ :=
  if p + q = k then (coupling p q : ℝ) * ExpPoly.eval ν t (ω n p) * ExpPoly.eval ν t (ω m q) else 0

/-- All four transport indices are absolutely summable. -/
theorem summable_norm_transportTerm {ν : ℚ} {ω : Stream} {K : ℕ} {t C q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (k : Wave) : Summable (fun z : (ℕ × Wave) × ℕ × Wave =>
      ‖transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2‖) := by
  have sa : Summable (fun z : ℕ × Wave => |ExpPoly.eval ν t (ω z.1 z.2)|) := by
    simpa using summable_degree_mode_weighted hK hC hq hq1 h 0
  have sb : Summable (fun z : ℕ × Wave => (size z.2 : ℝ) * |ExpPoly.eval ν t (ω z.1 z.2)|) := by
    simpa using summable_degree_mode_weighted hK hC hq hq1 h 1
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    (sa.mul_of_nonneg sb (fun _ => abs_nonneg _) (fun z => by positivity))
  rw [Real.norm_eq_abs]
  unfold transportTerm
  split_ifs
  · simp only [abs_mul]
    have hc : |(coupling z.1.2 z.2.2 : ℝ)| ≤ size z.2.2 := by exact_mod_cast abs_coupling_le z.1.2 z.2.2
    calc |(coupling z.1.2 z.2.2 : ℝ)| * |ExpPoly.eval ν t (ω z.1.1 z.1.2)| * |ExpPoly.eval ν t (ω z.2.1 z.2.2)|
        ≤ (size z.2.2 : ℝ) * |ExpPoly.eval ν t (ω z.1.1 z.1.2)| * |ExpPoly.eval ν t (ω z.2.1 z.2.2)| := by gcongr
        _ = _ := by ring
  · simp only [abs_zero]
    positivity

/-- Infinite Fourier transport commutes with the convergent degree expansion. -/
theorem fourierTransport_coeff {ν : ℚ} {ω : Stream} {K : ℕ} {t C q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (k : Wave) : fourierTransport (fourierCoeff ν ω t) (fourierCoeff ν ω t) k =
      ∑' n, ∑' m, RealPoly.transport (eval ν t (ω n)) (eval ν t (ω m)) k := by
  have hs := (summable_norm_transportTerm hK hC hq hq1 h k).of_norm
  have he (p r : Wave) :
      (if p + r = k then (coupling p r : ℝ) * fourierCoeff ν ω t p * fourierCoeff ν ω t r else 0) =
        ∑' n, ∑' m, transportTerm ν ω t k n p m r := by
    unfold transportTerm
    split_ifs
    · change (coupling p r : ℝ) * (∑' n, ExpPoly.eval ν t (ω n p)) * (∑' m, ExpPoly.eval ν t (ω m r)) = _
      conv_lhs => lhs; rw [← tsum_mul_left]
      rw [← tsum_mul_right]
      exact tsum_congr (fun n => (tsum_mul_left).symm)
    · simp
  simp_rw [fourierTransport, he]
  let ea := Equiv.prodProdProdComm ℕ ℕ Wave Wave
  let eb : (Wave × Wave) × ℕ × ℕ ≃ (ℕ × Wave) × ℕ × Wave :=
    ⟨fun z => ((z.2.1, z.1.1), z.2.2, z.1.2),
      fun z => ((z.1.2, z.2.2), z.1.1, z.2.1), fun _ => rfl, fun _ => rfl⟩
  have hsa : Summable (fun z : (ℕ × ℕ) × Wave × Wave => transportTerm ν ω t k z.1.1 z.2.1 z.1.2 z.2.2) := (ea.summable_iff (f := fun z : (ℕ × Wave) × ℕ × Wave => transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2)).mpr hs
  have hsb : Summable (fun z : (Wave × Wave) × ℕ × ℕ => transportTerm ν ω t k z.2.1 z.1.1 z.2.2 z.1.2) := (eb.summable_iff (f := fun z : (ℕ × Wave) × ℕ × Wave => transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2)).mpr hs
  calc (∑' p, ∑' r, ∑' n, ∑' m, transportTerm ν ω t k n p m r)
      = ∑' z : (Wave × Wave) × ℕ × ℕ, transportTerm ν ω t k z.2.1 z.1.1 z.2.2 z.1.2 :=
        by
          exact (tsum_four (F := fun p r n m => transportTerm ν ω t k n p m r) hsb).symm
    _ = ∑' z : (ℕ × Wave) × ℕ × Wave, transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2 := by
      exact eb.tsum_eq (fun z => transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2)
    _ = ∑' z : (ℕ × ℕ) × Wave × Wave, transportTerm ν ω t k z.1.1 z.2.1 z.1.2 z.2.2 := by
      exact (ea.tsum_eq (fun z => transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2)).symm
    _ = ∑' n, ∑' m, ∑' p, ∑' r, transportTerm ν ω t k n p m r := by
      exact tsum_four (F := fun n m p r => transportTerm ν ω t k n p m r) hsa
    _ = _ := by
      apply tsum_congr
      intro n
      apply tsum_congr
      intro m
      exact fourierTransport_finite (eval ν t (ω n)) (eval ν t (ω m)) k

/-- A finite physical polynomial is also its sum over all Fourier modes. -/
theorem RealPoly.field_eq_tsum (P : RealPoly) (x : ℝ × ℝ) :
    RealPoly.field P x = ∑' k, P k * cos (phase k x) := by
  rw [tsum_eq_sum (s := P.support)]
  · rfl
  · intro k hk
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul]

/-- The summed degree coefficients reconstruct the same classical field.
Absolute degree-mode summability justifies exchanging the two expansions. -/
theorem analyticField_eq_fourier {ν : ℚ} {ω : Stream} {K : ℕ} {t C q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (x : ℝ × ℝ) : analyticField ν ω t x = ∑' k, fourierCoeff ν ω t k * cos (phase k x) := by
  have sa : Summable (fun z : ℕ × Wave => |ExpPoly.eval ν t (ω z.1 z.2)|) := by
    simpa using summable_degree_mode_weighted hK hC hq hq1 h 0
  have sn : Summable (fun z : ℕ × Wave => ‖ExpPoly.eval ν t (ω z.1 z.2) * cos (phase z.2 x)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)) sa
  have hs := sn.of_norm
  simp only [analyticField, seriesTerm, RealPoly.field_eq_tsum]
  change (∑' n, ∑' k, ExpPoly.eval ν t (ω n k) * cos (phase k x)) = _
  rw [← hs.tsum_comm (f := fun n k => ExpPoly.eval ν t (ω n k) * cos (phase k x))]
  exact tsum_congr (fun k => tsum_mul_right)

#print axioms analyticField_eq_fourier
#print axioms fourierTransport_coeff
end Gimle.Asgard.Streams.Mild
