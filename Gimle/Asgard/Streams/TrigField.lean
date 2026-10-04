import Gimle.Asgard.Streams.TrigNorm
import Gimle.Asgard.Streams.TrigStream

/-! # The field of a trigonometric stream, and a one-axis certified truncation

`field P x = Σ_k P_k cos(k·x)` is the real function an even trigonometric
polynomial describes in the exponential reading: for even `P` the sine parts
of `Σ P_k e^{ik·x}` cancel in pairs, and for a non-even `P` this is its real
part. That reading is on paper (no complex exponential is formed here); what
Lean proves about `field` holds for every `P`, and `EulerSolution` proves its
partial derivatives and the Jacobian identity that ties `transport` to
`u·∇q` as real functions. It is bounded by
the ℓ¹ norm (`abs_field_le_l1`, from `|cos| ≤ 1`). A stream `ω` with a
geometric bound on its ℓ¹ norms, `l1 ω_n ≤ M ρⁿ` (`GeometricBound`), has an
analytic field `Σ_n field ω_n (x) tⁿ` on `|t| < 1/ρ`, and on `|t| ≤ r` with
`ρ r < 1` it is within `M (ρr)^N / (1 − ρr)` of the finite sum through
`t`-degree `N − 1` (`abs_analyticField_sub_windowField_le`; the predicate
`TruncationBound`, with the rational `tailBound`) — the one-axis tail. A band
follows from the window's ℓ¹ spread plus that error
(`abs_analyticField_sub_field_le`, `abs_analyticField_le`), with no inverse
table and no closed form. Which streams have a geometric bound is the business
of `EulerRadius`; that the analytic field of the Euler stream is a classical
solution of the vorticity equation on `|t| < 1/ρ` is `EulerSolution`'s
`NS.euler_classical`. -/
namespace Gimle.Asgard.Streams.Torus

open Real

/-- `Σ_k P_k cos(k·x)`: for an even polynomial, the real function it describes;
in general the real part. -/
noncomputable def field (P : TrigPoly) (x : ℝ × ℝ) : ℝ :=
  P.sum fun k a => (a : ℝ) * cos (k.1 * x.1 + k.2 * x.2)

theorem field_add (P Q : TrigPoly) (x : ℝ × ℝ) : field (P + Q) x = field P x + field Q x := by
  unfold field
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]

theorem field_single (k : Wave) (a : ℚ) (x : ℝ × ℝ) :
    field (Finsupp.single k a) x = a * cos (k.1 * x.1 + k.2 * x.2) := by
  unfold field
  rw [Finsupp.sum_single_index (by simp)]

/-- `cos(k·x)` is the field of `cosine k`. -/
theorem field_cosine (k : Wave) (x : ℝ × ℝ) : field (cosine k) x = cos (k.1 * x.1 + k.2 * x.2) := by
  rw [cosine, field_add, field_single, field_single]
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  rw [show -(k.1 : ℝ) * x.1 + -(k.2 : ℝ) * x.2 = -((k.1 : ℝ) * x.1 + k.2 * x.2) by ring, cos_neg]
  push_cast
  ring

/-- The field is bounded by the ℓ¹ norm. -/
theorem abs_field_le_l1 (P : TrigPoly) (x : ℝ × ℝ) : |field P x| ≤ l1 P := by
  rw [field, Finsupp.sum, l1_eq_sum subset_rfl]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)


end Gimle.Asgard.Streams.Torus

namespace Gimle.Asgard.Streams.TrigStream

open Torus Real

/-- The `n`-th term of the field's `t`-series at `(t, x)`. -/
noncomputable def seriesTerm (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) (n : ℕ) : ℝ :=
  field (ω n) x * t ^ n

/-- The analytic field `Σ_n field ω_n (x) tⁿ` (zero where the series does not
converge). -/
noncomputable def analyticField (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, seriesTerm ω t x n

/-- The window: the finite sum through `t`-degree `N − 1`. -/
noncomputable def windowField (N : ℕ) (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, seriesTerm ω t x n

/-- A geometric bound on the ℓ¹ norms of the coefficients. -/
def GeometricBound (ω : TrigStream) (M ρ : ℝ) : Prop := ∀ n, (l1 (ω n) : ℝ) ≤ M * ρ ^ n

variable {ω : TrigStream} {M ρ r t : ℝ} {x : ℝ × ℝ}

theorem abs_seriesTerm_le (h : GeometricBound ω M ρ) (ht : |t| ≤ r) (n : ℕ) :
    |seriesTerm ω t x n| ≤ M * (ρ * r) ^ n := by
  have hr : 0 ≤ r := (abs_nonneg t).trans ht
  rw [seriesTerm, abs_mul, abs_pow, mul_pow]
  have h1 : |field (ω n) x| ≤ M * ρ ^ n := (abs_field_le_l1 _ _).trans (h n)
  have h2 : |t| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg _) ht n
  calc |field (ω n) x| * |t| ^ n ≤ M * ρ ^ n * r ^ n :=
        mul_le_mul h1 h2 (by positivity) ((abs_nonneg _).trans h1)
    _ = M * (ρ ^ n * r ^ n) := by ring

theorem summable_norm_seriesTerm (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ) (hr : ρ * r < 1)
    (ht : |t| ≤ r) : Summable fun n => ‖seriesTerm ω t x n‖ := by
  have hr0 : 0 ≤ r := (abs_nonneg t).trans ht
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (by positivity) hr).mul_left M)
  rw [Real.norm_eq_abs]
  exact abs_seriesTerm_le h ht n

theorem hasSum_analyticField (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ) (hr : ρ * r < 1)
    (ht : |t| ≤ r) : HasSum (seriesTerm ω t x) (analyticField ω t x) :=
  (summable_norm_seriesTerm h hρ hr ht).of_norm.hasSum

/-- **One-axis certified truncation.** On `|t| ≤ r` with `ρr < 1`, the analytic
field is within `M (ρr)^N / (1 − ρr)` of the window of `t`-degree `< N`. -/
theorem abs_analyticField_sub_windowField_le (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ)
    (hr : ρ * r < 1) (ht : |t| ≤ r) (N : ℕ) :
    |analyticField ω t x - windowField N ω t x| ≤ M * (ρ * r) ^ N / (1 - ρ * r) := by
  have hr0 : 0 ≤ r := (abs_nonneg t).trans ht
  have hM : 0 ≤ M := by
    have := h 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (by exact_mod_cast l1_nonneg (ω 0)) this
  have summ := (summable_norm_seriesTerm (x := x) h hρ hr ht).of_norm
  have split := summ.sum_add_tsum_nat_add N
  have tail : analyticField ω t x - windowField N ω t x = ∑' n, seriesTerm ω t x (n + N) := by
    rw [analyticField, windowField, ← split]; ring
  rw [tail]
  have geom : HasSum (fun n : ℕ => M * (ρ * r) ^ N * (ρ * r) ^ n)
      (M * (ρ * r) ^ N * (1 - ρ * r)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hr).mul_left _
  have bound : ∀ n, ‖seriesTerm ω t x (n + N)‖ ≤ M * (ρ * r) ^ N * (ρ * r) ^ n := by
    intro n
    rw [Real.norm_eq_abs]
    refine (abs_seriesTerm_le h ht (n + N)).trans (le_of_eq ?_)
    rw [pow_add]; ring
  have := tsum_of_norm_bounded geom bound
  rw [Real.norm_eq_abs] at this
  rw [div_eq_mul_inv]
  exact this

/-- `TruncationBound ω r N ε`: on `|t| ≤ r` the analytic field is within `ε` of
the window through `t`-degree `N − 1`, at every point. -/
def TruncationBound (ω : TrigStream) (r : ℝ) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ r → |analyticField ω t x - windowField N ω t x| ≤ ε

theorem TruncationBound.mono {ω : TrigStream} {r : ℝ} {N : ℕ} {ε ε' : ℝ}
    (h : TruncationBound ω r N ε) (le : ε ≤ ε') : TruncationBound ω r N ε' :=
  fun t x ht => (h t x ht).trans le

/-- The one-axis tail bound `M (ρr)^N / (1 − ρr)`, a rational for rational data. -/
def tailBound (M ρ r : ℚ) (N : ℕ) : ℚ := M * (ρ * r) ^ N / (1 - ρ * r)

theorem truncationBound (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ) (hr : ρ * r < 1) (N : ℕ) :
    TruncationBound ω r N (M * (ρ * r) ^ N / (1 - ρ * r)) :=
  fun _ _ ht => abs_analyticField_sub_windowField_le h hρ hr ht N

/-- With rational data the error is the rational `tailBound`, which the kernel
evaluates. -/
theorem truncationBound_rat {M ρ r : ℚ} (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ)
    (hr : ρ * r < 1) (N : ℕ) : TruncationBound ω r N (tailBound M ρ r N) := by
  have hρ' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hr' : (ρ : ℝ) * r < 1 := by exact_mod_cast hr
  intro t x ht
  have := abs_analyticField_sub_windowField_le (x := x) h hρ' hr' ht N
  rw [tailBound]
  push_cast
  exact this

/-- The window of positive length is within the ℓ¹ spread of its `t⁰` term. -/
theorem abs_windowField_sub_le (ht : |t| ≤ r) {N : ℕ} (hN : 0 < N) :
    |windowField N ω t x - field (ω 0) x| ≤
      ∑ n ∈ Finset.Ico 1 N, (l1 (ω n) : ℝ) * r ^ n := by
  have hr0 : 0 ≤ r := (abs_nonneg t).trans ht
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [windowField, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp only [seriesTerm, pow_zero, mul_one, add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul (abs_field_le_l1 _ _) (pow_le_pow_left₀ (abs_nonneg _) ht n)
    (by positivity) (by exact_mod_cast l1_nonneg _)

/-- **A band around the initial profile.** On `|t| ≤ r`, the field stays within
the window's spread plus the certified error of its `t = 0` value. -/
theorem abs_analyticField_sub_field_le (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ) (hr : ρ * r < 1)
    (ht : |t| ≤ r) {N : ℕ} (hN : 0 < N) :
    |analyticField ω t x - field (ω 0) x| ≤
      (∑ n ∈ Finset.Ico 1 N, (l1 (ω n) : ℝ) * r ^ n) + M * (ρ * r) ^ N / (1 - ρ * r) := by
  calc |analyticField ω t x - field (ω 0) x|
      = |(analyticField ω t x - windowField N ω t x) + (windowField N ω t x - field (ω 0) x)| := by
        ring_nf
    _ ≤ |analyticField ω t x - windowField N ω t x| + |windowField N ω t x - field (ω 0) x| :=
        abs_add_le _ _
    _ ≤ M * (ρ * r) ^ N / (1 - ρ * r) + ∑ n ∈ Finset.Ico 1 N, (l1 (ω n) : ℝ) * r ^ n :=
        add_le_add (abs_analyticField_sub_windowField_le h hρ hr ht N) (abs_windowField_sub_le ht hN)
    _ = _ := add_comm _ _

/-- **A band on the field.** `|F(t, x)| ≤ Σ_{n<N} l1 ω_n rⁿ + M (ρr)^N/(1 − ρr)`. -/
theorem abs_analyticField_le (h : GeometricBound ω M ρ) (hρ : 0 ≤ ρ) (hr : ρ * r < 1)
    (ht : |t| ≤ r) (N : ℕ) :
    |analyticField ω t x| ≤
      (∑ n ∈ Finset.range N, (l1 (ω n) : ℝ) * r ^ n) + M * (ρ * r) ^ N / (1 - ρ * r) := by
  have hr0 : 0 ≤ r := (abs_nonneg t).trans ht
  have window : |windowField N ω t x| ≤ ∑ n ∈ Finset.range N, (l1 (ω n) : ℝ) * r ^ n := by
    rw [windowField]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [seriesTerm, abs_mul, abs_pow]
    exact mul_le_mul (abs_field_le_l1 _ _) (pow_le_pow_left₀ (abs_nonneg _) ht n)
      (by positivity) (by exact_mod_cast l1_nonneg _)
  calc |analyticField ω t x|
      = |(analyticField ω t x - windowField N ω t x) + windowField N ω t x| := by ring_nf
    _ ≤ |analyticField ω t x - windowField N ω t x| + |windowField N ω t x| := abs_add_le _ _
    _ ≤ M * (ρ * r) ^ N / (1 - ρ * r) + ∑ n ∈ Finset.range N, (l1 (ω n) : ℝ) * r ^ n :=
        add_le_add (abs_analyticField_sub_windowField_le h hρ hr ht N) window
    _ = _ := add_comm _ _

#print axioms abs_field_le_l1
#print axioms field_cosine
#print axioms hasSum_analyticField
#print axioms abs_analyticField_sub_windowField_le
#print axioms truncationBound_rat
#print axioms abs_analyticField_sub_field_le
#print axioms abs_analyticField_le
end Gimle.Asgard.Streams.TrigStream
