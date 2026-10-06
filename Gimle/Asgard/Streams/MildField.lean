import Gimle.Asgard.Streams.MildNorm
import Mathlib.Analysis.SpecificLimits.Normed

/-! Fields and certified interaction windows for mild streams. A physical
term already depends on time; no additional Taylor power multiplies it. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

namespace RealPoly

/-- The cosine field of a finite real Fourier polynomial. -/
noncomputable def field (P : RealPoly) (x : ℝ × ℝ) : ℝ :=
  P.sum fun k a => a * cos (k.1 * x.1 + k.2 * x.2)

theorem abs_field_le_l1 (P : RealPoly) (x : ℝ × ℝ) : |field P x| ≤ l1 P := by
  rw [field, Finsupp.sum, l1_eq_sum subset_rfl]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

end RealPoly

/-- One physically evaluated interaction term. -/
noncomputable def seriesTerm (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) (n : ℕ) : ℝ :=
  RealPoly.field (eval ν t (ω n)) x

/-- The infinite interaction series, when the following bounds certify convergence. -/
noncomputable def analyticField (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, seriesTerm ν ω t x n

/-- The window of interaction degrees strictly below `N`. -/
noncomputable def windowField (ν : ℚ) (N : ℕ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, seriesTerm ν ω t x n

/-- Absolute convergence and a bound on the interaction window on `[0,T]`. -/
def MildTruncationBound (ν : ℚ) (ω : Stream) (T : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ x : ℝ × ℝ,
    Summable (fun n => ‖seriesTerm ν ω t x n‖) ∧
    |analyticField ν ω t x - windowField ν N ω t x| ≤ ε

/-- A field band on the same closed physical time interval. -/
def MildBandBound (ν : ℚ) (ω : Stream) (T B : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ x : ℝ × ℝ, |analyticField ν ω t x| ≤ B

theorem MildTruncationBound.mono {ν : ℚ} {ω : Stream} {T ε ε' : ℝ} {N : ℕ}
    (h : MildTruncationBound ν ω T N ε) (hle : ε ≤ ε') : MildTruncationBound ν ω T N ε' := by
  intro t ht x
  exact ⟨(h t ht x).1, (h t ht x).2.trans hle⟩

/-- A geometric tail estimate requires only the bounds from the selected
window onward, so sharper finite prefixes and Catalan tails can be retained. -/
theorem geometric_tail {f : ℕ → ℝ} {M q : ℝ} {N : ℕ}
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, N ≤ n → |f n| ≤ M * q ^ n) :
    Summable (fun n => ‖f n‖) ∧
      |(∑' n, f n) - ∑ n ∈ Finset.range N, f n| ≤ M * q ^ N / (1 - q) := by
  have htail : ∀ n, ‖f (n + N)‖ ≤ M * q ^ N * q ^ n := by
    intro n
    rw [Real.norm_eq_abs]
    refine (h (n + N) (by omega)).trans_eq ?_
    rw [pow_add]; ring
  have hg : HasSum (fun n : ℕ => M * q ^ N * q ^ n) (M * q ^ N * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq hq1).mul_left _
  have hs : Summable (fun n => ‖f (n + N)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail hg.summable
  have hsall : Summable (fun n => ‖f n‖) := (summable_nat_add_iff N).mp hs
  refine ⟨hsall, ?_⟩
  have split := hsall.of_norm.sum_add_tsum_nat_add N
  have he : (∑' n, f n) - ∑ n ∈ Finset.range N, f n = ∑' n, f (n + N) := by
    rw [← split]; ring
  rw [he, div_eq_mul_inv]
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hg htail

/-- A shifted geometric tail, allowing the sharper bound at `N`. -/
theorem geometric_tail_shifted {f : ℕ → ℝ} {A q : ℝ} {N : ℕ}
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, |f (n + N)| ≤ A * q ^ n) :
    Summable (fun n => ‖f n‖) ∧
      |(∑' n, f n) - ∑ n ∈ Finset.range N, f n| ≤ A / (1 - q) := by
  have hg := (hasSum_geometric_of_lt_one hq hq1).mul_left A
  have hb : ∀ n, ‖f (n + N)‖ ≤ A * q ^ n := by simpa only [Real.norm_eq_abs] using h
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg (f (n + N))) hb hg.summable
  have hsall : Summable (fun n => ‖f n‖) := (summable_nat_add_iff N).mp hs
  refine ⟨hsall, ?_⟩
  have split := hsall.of_norm.sum_add_tsum_nat_add N
  have he : (∑' n, f n) - ∑ n ∈ Finset.range N, f n = ∑' n, f (n + N) := by
    rw [← split]; ring
  rw [he, div_eq_mul_inv]
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hg hb

/-- A finite window's physical ℓ¹ bounds plus its certified tail give a band. -/
theorem band_of_truncation {ν : ℚ} {ω : Stream} {T ε : ℝ} {N : ℕ}
    (h : MildTruncationBound ν ω T N ε) (a : ℕ → ℝ)
    (ha : ∀ t ∈ Set.Icc 0 T, ∀ n ∈ Finset.range N, RealPoly.l1 (eval ν t (ω n)) ≤ a n) :
    MildBandBound ν ω T ((∑ n ∈ Finset.range N, a n) + ε) := by
  intro t ht x
  have hw : |windowField ν N ω t x| ≤ ∑ n ∈ Finset.range N, a n :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n hn =>
      (RealPoly.abs_field_le_l1 _ x).trans (ha t ht n hn)))
  have htri := abs_add_le (analyticField ν ω t x - windowField ν N ω t x) (windowField ν N ω t x)
  have hb := (h t ht x).2
  rw [sub_add_cancel] at htri
  linarith

#print axioms geometric_tail
#print axioms geometric_tail_shifted
#print axioms band_of_truncation
end Gimle.Asgard.Streams.Mild
