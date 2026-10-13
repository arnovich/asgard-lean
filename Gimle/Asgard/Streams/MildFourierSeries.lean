import Gimle.Asgard.Streams.MildSolution

/-! Uniform summable mode envelopes for physical Fourier coefficients and
their time derivatives. These justify the modewise energy exchanges. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

/-- A single real Fourier coefficient is bounded by the total absolute mass. -/
theorem RealPoly.abs_apply_le_l1 (P : RealPoly) (k : Wave) : |P k| ≤ RealPoly.l1 P := by
  by_cases hk : k ∈ P.support
  · exact Finset.single_le_sum (fun j _ => abs_nonneg (P j)) hk
  · rw [Finsupp.notMem_support_iff.mp hk, abs_zero]
    exact RealPoly.l1_nonneg _

/-- A support of ℓ¹ radius `K` fits in an integer square of side `2K+1`. -/
theorem support_card_le {P : MildPoly} {K : ℕ} (hK : SizeLE K P) :
    P.support.card ≤ (2 * K + 1) ^ 2 := by
  let box := Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K
  have hs : P.support ⊆ box := by
    intro k hk
    have h := hK k hk
    have h1 : k.1.natAbs ≤ K := (Nat.le_add_right _ _).trans h
    have h2 : k.2.natAbs ≤ K := (Nat.le_add_left _ _).trans h
    have hc1 : |k.1| ≤ (K : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr h1)
    have hc2 : |k.2| ≤ (K : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr h2)
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hc1), Finset.mem_Icc.mpr (abs_le.mp hc2)⟩
  refine (Finset.card_le_card hs).trans_eq ?_
  simp only [box, Finset.card_product, Int.card_Icc]
  have he : (K : ℤ) + 1 - -(K : ℤ) = (2 * K + 1 : ℕ) := by push_cast; ring
  rw [he]
  simp only [Int.toNat_natCast, sq]

/-- Time differentiation cannot create Fourier modes. -/
theorem support_deriv_subset (ν : ℚ) (P : MildPoly) : (deriv ν P).support ⊆ P.support :=
  Finsupp.support_mapRange

/-- A fixed Fourier coefficient of the interaction sum. -/
noncomputable def fourierCoeff (ν : ℚ) (ω : Stream) (t : ℝ) (k : Wave) : ℝ :=
  ∑' n, ExpPoly.eval ν t (ω n k)

/-- Its physical derivative series. -/
noncomputable def fourierDt (ν : ℚ) (ω : Stream) (t : ℝ) (k : Wave) : ℝ :=
  ∑' n, ExpPoly.eval ν t (deriv ν (ω n) k)

/-- A mode envelope built from physical degree bounds and finite supports. -/
noncomputable def modeEnvelope (ω : Stream) (a : ℕ → ℝ) (k : Wave) : ℝ :=
  ∑' n, if k ∈ (ω n).support then a n else 0

/-- Each fixed degree envelope has a finite sum over all modes. -/
theorem hasSum_degree_envelope (P : MildPoly) (a : ℝ) :
    HasSum (fun k => if k ∈ P.support then a else 0) (P.support.card * a) := by
  have h : HasSum (fun k => if k ∈ P.support then a else 0)
      (∑ k ∈ P.support, if k ∈ P.support then a else 0) := hasSum_sum_of_ne_finset_zero (s := P.support) (f := fun k => if k ∈ P.support then a else 0)
    (fun k hk => if_neg hk)
  simpa only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul] using h

/-- Summable degree masses give a summable double-index mode envelope. -/
theorem summable_degree_mode_envelope (ω : Stream) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n => ((ω n).support.card : ℝ) * a n)) :
    Summable (fun p : ℕ × Wave => if p.2 ∈ (ω p.1).support then a p.1 else 0) := by
  apply (summable_prod_of_nonneg (fun p : ℕ × Wave => by split_ifs; exact ha p.1; exact le_rfl)).mpr
  exact ⟨fun n => (hasSum_degree_envelope (ω n) (a n)).summable,
    by simpa only [(fun n => (hasSum_degree_envelope (ω n) (a n)).tsum_eq)] using hs⟩

/-- The modewise envelope is summable, so it can dominate later nonlinear sums. -/
theorem summable_modeEnvelope (ω : Stream) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n => ((ω n).support.card : ℝ) * a n)) :
    Summable (modeEnvelope ω a) := by
  exact (summable_degree_mode_envelope ω ha hs).prod_symm.prod

/-- Finite support growth times polynomial-geometric physical bounds is summable. -/
theorem summable_support_geometric (ω : Stream) {K : ℕ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) {C q : ℝ} (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (d : ℕ) :
    Summable (fun n => ((ω n).support.card : ℝ) * (C * (((n : ℝ) + 1) ^ d * q ^ n))) := by
  have hb (n : ℕ) : ((ω n).support.card : ℝ) ≤ (2 * (K : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    have h : ((ω n).support.card : ℝ) ≤ (2 * ((n + 1) * K : ℕ) + 1 : ℕ) ^ 2 := by
      exact_mod_cast support_card_le (hK n)
    push_cast at h
    refine h.trans ?_
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hb := mul_self_le_mul_self (show (0 : ℝ) ≤ 2 * (n + 1) * K + 1 by positivity)
      (show 2 * ((n : ℝ) + 1) * K + 1 ≤ (2 * K + 1) * (n + 1) by nlinarith)
    nlinarith only [hb]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((TrigStream.summable_succ_pow_mul_geometric (2 + d) hq hq1).mul_left ((2 * (K : ℝ) + 1) ^ 2 * C))
  have h := mul_le_mul_of_nonneg_right (hb n) (show 0 ≤ C * (((n : ℝ) + 1) ^ d * q ^ n) by positivity)
  calc _ ≤ _ := h
       _ = _ := by rw [pow_add]; ring

/-- A physical coefficient is zero outside its carrier support. -/
theorem eval_apply_eq_zero {P : MildPoly} {k : Wave} (hk : k ∉ P.support) (ν : ℚ) (t : ℝ) :
    ExpPoly.eval ν t (P k) = 0 := by rw [Finsupp.notMem_support_iff.mp hk, map_zero]

/-- Pointwise domination by the supported degree envelope. -/
theorem abs_eval_le_envelope {ν : ℚ} {P : MildPoly} {t a : ℝ}
    (h : RealPoly.l1 (eval ν t P) ≤ a) (k : Wave) :
    |ExpPoly.eval ν t (P k)| ≤ if k ∈ P.support then a else 0 := by
  split_ifs with hk
  · exact (RealPoly.abs_apply_le_l1 (eval ν t P) k).trans h
  · rw [eval_apply_eq_zero hk, abs_zero]

/-- Every individual degree envelope is summable in degree. -/
theorem summable_envelope_degree (ω : Stream) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n => ((ω n).support.card : ℝ) * a n)) (k : Wave) :
    Summable (fun n => if k ∈ (ω n).support then a n else 0) :=
  (summable_degree_mode_envelope ω ha hs).prod_symm.prod_factor k

/-- Physical Fourier coefficients are absolutely summable in interaction degree. -/
theorem summable_norm_coeff {ν : ℚ} {ω : Stream} {t : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n => ((ω n).support.card : ℝ) * a n))
    (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ a n) (k : Wave) :
    Summable (fun n => ‖ExpPoly.eval ν t (ω n k)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]; exact abs_eval_le_envelope (h n) k)
    (summable_envelope_degree ω ha hs k)

/-- The uniform mode envelope bounds the actual summed Fourier coefficient. -/
theorem abs_fourierCoeff_le {ν : ℚ} {ω : Stream} {t : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n => ((ω n).support.card : ℝ) * a n))
    (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ a n) (k : Wave) :
    |fourierCoeff ν ω t k| ≤ modeEnvelope ω a k := by
  have hc := summable_norm_coeff ha hs h k
  refine (norm_tsum_le_tsum_norm hc).trans ?_
  exact hc.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact abs_eval_le_envelope (h n) k)
    (summable_envelope_degree ω ha hs k)

/-- Mode envelopes are nonnegative. -/
theorem modeEnvelope_nonneg (ω : Stream) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k : Wave) :
    0 ≤ modeEnvelope ω a k := tsum_nonneg (fun n => by split_ifs; exact ha n; exact le_rfl)

/-- Every polynomial spatial weight of a geometric physical stream is summable. -/
theorem summable_weighted_coeff {ν : ℚ} {ω : Stream} {K : ℕ} {t C q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (d : ℕ) : Summable (fun k => (size k : ℝ) ^ d * |fourierCoeff ν ω t k|) := by
  let a : ℕ → ℝ := fun n => C * q ^ n
  let c : ℕ → ℝ := fun n => C * (K : ℝ) ^ d * (((n : ℝ) + 1) ^ d * q ^ n)
  have ha : ∀ n, 0 ≤ a n := fun n => by dsimp [a]; positivity
  have hc : ∀ n, 0 ≤ c n := fun n => by dsimp [c]; positivity
  have hs : Summable (fun n => ((ω n).support.card : ℝ) * a n) := by
    simpa [a] using summable_support_geometric ω hK hC hq hq1 0
  have hcs := summable_support_geometric ω hK (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg K) d)) hq hq1 d
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_modeEnvelope ω hc hcs)
  refine (mul_le_mul_of_nonneg_left (abs_fourierCoeff_le ha hs h k) (by positivity)).trans ?_
  rw [modeEnvelope, ← tsum_mul_left]
  apply ((summable_envelope_degree ω ha hs k).mul_left _).tsum_le_tsum _
    (summable_envelope_degree ω hc hcs k)
  intro n
  split_ifs with hk
  · have hk' : (size k : ℝ) ≤ ((n : ℝ) + 1) * K := by exact_mod_cast hK n k hk
    calc (size k : ℝ) ^ d * a n ≤ (((n : ℝ) + 1) * K) ^ d * a n := by gcongr
         _ = c n := by dsimp [a, c]; rw [mul_pow]; ring
  · simp

#print axioms support_card_le
#print axioms summable_modeEnvelope
#print axioms summable_weighted_coeff
end Gimle.Asgard.Streams.Mild
