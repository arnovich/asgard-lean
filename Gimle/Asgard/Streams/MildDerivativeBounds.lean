import Gimle.Asgard.Streams.MildCalculus
import Gimle.Asgard.Streams.MildRadius

/-! Uniform physical-time derivative bounds from either certified geometric
bound. Polynomial losses in interaction degree remain summable. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

/-- Rational scaling evaluates as real scaling. -/
theorem eval_smul_real (ν a : ℚ) (t : ℝ) (P : MildPoly) :
    eval ν t (a • P) = (a : ℝ) • eval ν t P := by
  apply Finsupp.ext
  intro k
  simp [Algebra.smul_def]

/-- The exact positive-degree PDE after physical evaluation. -/
theorem eval_deriv_wild_succ (ν : ℚ) (b : Stream) (n : ℕ) (t : ℝ) :
    eval ν t (deriv ν (wild ν b (n + 1))) =
      (ν : ℝ) • RealPoly.laplacian (eval ν t (wild ν b (n + 1))) -
        ∑ m ∈ Finset.range (n + 1),
          RealPoly.transport (eval ν t (wild ν b m)) (eval ν t (wild ν b (n - m))) := by
  rw [deriv_wild_succ]
  simp_rw [← eval_transport]
  apply Finsupp.ext
  intro k
  simp [Algebra.smul_def]

/-- The zero-degree PDE after physical evaluation of constant initial data. -/
theorem eval_deriv_wild_zero (ν : ℚ) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) (t : ℝ) :
    eval ν t (deriv ν (wild ν b 0)) = (ν : ℝ) • RealPoly.laplacian (eval ν t (wild ν b 0)) := by
  rw [deriv_wild_zero ν b P hb, eval_smul_real, eval_laplacian]

/-- A uniform geometric coefficient bound also bounds the differentiated terms. -/
theorem wild_deriv_l1_le {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly)
    (hb : b 0 = embed P) {K : ℕ} (hK : SizeLE K (b 0)) {T M q : ℝ}
    (h : GeometricBound ν (wild ν b) T M q) (hq : 0 < q) (hM : 0 ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (n : ℕ) :
    RealPoly.l1 (eval ν t (deriv ν (wild ν b n))) ≤
      ((ν : ℝ) * K ^ 2 * M + (K : ℝ) * M ^ 2 / q) * (((n : ℝ) + 1) ^ 2 * q ^ n) := by
  have hv : (0 : ℝ) ≤ ν := by exact_mod_cast hν
  have hs (n : ℕ) : RealPoly.SizeLE ((n + 1) * K) (eval ν t (wild ν b n)) :=
    sizeLE_eval ν t (wild_sizeLE ν b K hK n)
  have hlap (n : ℕ) : RealPoly.l1 (RealPoly.laplacian (eval ν t (wild ν b n))) ≤
      (((n : ℝ) + 1) * K) ^ 2 * (M * q ^ n) := by
    refine (RealPoly.l1_laplacian_le (hs n)).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (h t ht n) (by positivity)
  cases n with
  | zero =>
      rw [eval_deriv_wild_zero ν b P hb, RealPoly.l1_smul, abs_of_nonneg hv]
      have hh := mul_le_mul_of_nonneg_left (hlap 0) hv
      simp only [Nat.cast_zero, zero_add, pow_zero, mul_one, one_mul, one_pow] at hh ⊢
      nlinarith [show 0 ≤ (K : ℝ) * M ^ 2 / q by positivity]
  | succ n =>
      have hc : RealPoly.l1 (∑ m ∈ Finset.range (n + 1),
          RealPoly.transport (eval ν t (wild ν b m)) (eval ν t (wild ν b (n - m)))) ≤
          ((n : ℝ) + 1) ^ 2 * K * M ^ 2 * q ^ n := by
        refine (RealPoly.l1_sum_le _ _).trans ?_
        calc (∑ m ∈ Finset.range (n + 1), RealPoly.l1
              (RealPoly.transport (eval ν t (wild ν b m)) (eval ν t (wild ν b (n - m)))))
            ≤ ∑ _m ∈ Finset.range (n + 1), ((n : ℝ) + 1) * K * M ^ 2 * q ^ n := by
              apply Finset.sum_le_sum
              intro m hm
              have hmle : m ≤ n := by have := Finset.mem_range.mp hm; omega
              have hsize : (((n - m : ℕ) : ℝ) + 1) * K ≤ ((n : ℝ) + 1) * K := by
                gcongr; exact_mod_cast Nat.sub_le n m
              refine (RealPoly.l1_transport_le _ (hs (n - m))).trans ?_
              have hp : q ^ m * q ^ (n - m) = q ^ n := by rw [← pow_add, Nat.add_sub_cancel' hmle]
              calc (((n - m + 1) * K : ℕ) : ℝ) * RealPoly.l1 (eval ν t (wild ν b m)) *
                    RealPoly.l1 (eval ν t (wild ν b (n - m)))
                  ≤ (((n - m : ℕ) : ℝ) + 1) * K * (M * q ^ m) * (M * q ^ (n - m)) := by
                      push_cast
                      exact mul_le_mul (mul_le_mul_of_nonneg_left (h t ht m) (by positivity))
                        (h t ht (n - m)) (RealPoly.l1_nonneg _) (by positivity)
                _ ≤ ((n : ℝ) + 1) * K * (M * q ^ m) * (M * q ^ (n - m)) := by gcongr
                _ = _ := by rw [← hp]; ring
          _ = _ := by simp; ring
      rw [eval_deriv_wild_succ]
      refine (RealPoly.l1_sub_le _ _).trans ?_
      rw [RealPoly.l1_smul, abs_of_nonneg hv]
      refine (add_le_add (mul_le_mul_of_nonneg_left (hlap (n + 1)) hv) hc).trans ?_
      have hp : q ^ (n + 1) / q = q ^ n := by rw [pow_succ]; field_simp
      have hn : ((n : ℝ) + 1) ^ 2 ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by push_cast; nlinarith [Nat.cast_nonneg n (α := ℝ)]
      have hc' := mul_le_mul_of_nonneg_right hn (show 0 ≤ (K : ℝ) * M ^ 2 * q ^ n by positivity)
      have he : ((ν : ℝ) * K ^ 2 * M + (K : ℝ) * M ^ 2 / q) *
          ((((n + 1 : ℕ) : ℝ) + 1) ^ 2 * q ^ (n + 1)) =
          (ν : ℝ) * ((((n + 1 : ℕ) : ℝ) + 1) * K) ^ 2 * (M * q ^ (n + 1)) +
          ((((n + 1 : ℕ) : ℝ) + 1) ^ 2) * K * M ^ 2 * q ^ n := by
        rw [← hp]; ring
      rw [he]
      nlinarith [hc']

#print axioms wild_deriv_l1_le
end Gimle.Asgard.Streams.Mild
