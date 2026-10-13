import Gimle.Asgard.Streams.Tail

/-! # Certified truncation of the two-axis geometric stream

Axes `[t, x]`, OGF coefficients `a_(m,n) = 1`, majorant `M = R_t = R_x = 1`,
box `|t|, |x| ≤ 1/2`. Then `q_t = q_x = 1/2` and at window `(N, N)`

`ε = 1 · (2 · 2^(−N)) · (2 · 2) = 8 · 2^(−N)`   (`error_eq`).

The certified field is the exact geometric sum `1 / ((1 − t)(1 − x))`
(`analyticField_ones`), the window field is the product of two finite geometric
sums (`windowField_ones`), and at the corner `(1/2, 1/2)` the true error is
`8 · 2^(−N) − 4 · 4^(−N)` (`corner_error`): the union bound overcounts exactly
the doubly omitted corner block. The same series stored as EGF has raw
coefficients `m!·n!` yet carries the same certificate, because majorants are
stated on decoded coefficients. -/
namespace Gimle.Asgard.Examples.GeometricTail

open Gimle.Asgard.Streams

/-- `a_(m,n) = 1` for every `m, n`. -/
def ones : Stream 2 := fun _ => 1

/-- `M = 1`, `R_t = R_x = 1`. -/
def unit : Majorant 2 := ⟨1, fun _ => 1, by norm_num, fun _ => by norm_num⟩

/-- `|t|, |x| ≤ 1/2`. -/
def half : Box 2 := ⟨fun _ => 1 / 2, fun _ => by norm_num⟩

/-- Every coefficient, not only a prefix: `|1| ≤ 1 · ∏ 1^(−α_i)`. -/
theorem ones_majorized : Majorizes .ogf ones unit := by
  intro α
  simp [ones, unit, decode]

/-- The certificate: exact data and the full-stream proof. -/
def certificate : TailCertificate .ogf ones :=
  ⟨unit, half, fun _ => by norm_num [half, unit], ones_majorized⟩

/-- The error at window `(N, N)` is `8 · 2^(−N)`. -/
theorem error_eq (N : ℕ) : certificate.error ![N, N] = 8 * (1 / 2) ^ N := by
  simp only [TailCertificate.error, tailBound, ratio, certificate, unit, half,
    Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  ring

/-- **Worked bound**: uniformly on the box, `|F − W_N| ≤ 8 · 2^(−N)`. -/
theorem bound (N : ℕ) : TruncationBound .ogf ones half ![N, N] (8 * (1 / 2) ^ N) :=
  error_eq N ▸ certificate.truncationBound ![N, N]

/-- At window `(10, 10)` the certified error is `1/128`, by kernel evaluation. -/
theorem error_ten : certificate.error ![10, 10] = 1 / 128 := by
  decide +kernel

/-! ## Agreement with the exact geometric sum -/

private theorem abs_lt_one {x : Fin 2 → ℝ} (hx : half.Mem x) (i : Fin 2) : |x i| < 1 := by
  have := hx i
  simp only [half] at this
  push_cast at this
  linarith

theorem seriesTerm_ones (x : Fin 2 → ℝ) (α : Index 2) :
    seriesTerm .ogf ones x α = ∏ i, x i ^ α i := by
  simp [seriesTerm, ones, decode]

/-- On the box the certified field is `1 / ((1 − t)(1 − x))`. -/
theorem analyticField_ones {x : Fin 2 → ℝ} (hx : half.Mem x) :
    analyticField .ogf ones x = ((1 - x 0) * (1 - x 1))⁻¹ := by
  have norms : ∀ i, Summable fun k => ‖x i ^ k‖ := fun i => by
    simp only [norm_pow, Real.norm_eq_abs]
    exact summable_geometric_of_lt_one (abs_nonneg _) (abs_lt_one hx i)
  have h := hasSum_index_prod (fun i k => x i ^ k) (fun i => (1 - x i)⁻¹) norms
    (fun i => hasSum_geometric_of_abs_lt_one (abs_lt_one hx i))
  rw [← (certificate.hasSum hx).tsum_eq, funext (seriesTerm_ones x), h.tsum_eq,
    Fin.prod_univ_two, mul_inv]

/-- The window field is the product of two finite geometric sums. -/
theorem windowField_ones (N : ℕ) (x : Fin 2 → ℝ) :
    windowField .ogf ![N, N] ones x =
      (∑ m ∈ Finset.range N, x 0 ^ m) * ∑ n ∈ Finset.range N, x 1 ^ n := by
  have prod := Finset.prod_univ_sum (fun i : Fin 2 => Finset.range (![N, N] i))
    (fun i k => x i ^ k)
  rw [Fin.prod_univ_two] at prod
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at prod
  rw [prod, windowField, window, Finset.sum_map]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [seriesTerm_ones]
  rfl

/-- At the corner `(1/2, 1/2)`: `F − W_N = 8·2^(−N) − 4·4^(−N)`, within the
certified `8·2^(−N)`, which overcounts exactly the corner block `4·4^(−N)`. -/
theorem corner_error (N : ℕ) :
    analyticField .ogf ones ![1 / 2, 1 / 2] - windowField .ogf ![N, N] ones ![1 / 2, 1 / 2] =
      8 * (1 / 2) ^ N - 4 * (1 / 4) ^ N := by
  have hx : half.Mem ![1 / 2, 1 / 2] := by
    intro i
    fin_cases i <;> norm_num [half]
  rw [analyticField_ones hx, windowField_ones]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1),
    show (1 / 4 : ℝ) ^ N = ((1 / 2) ^ N) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  ring

/-! ## The same series stored as EGF -/

/-- EGF raw coefficients `m!·n!`. Read as OGF they would violate the unit
majorant; the certificate reads decoded coefficients, which are all `1`. -/
noncomputable def egfOnes : Stream 2 := encode .egf ones

theorem egfOnes_apply (α : Index 2) : egfOnes α = factorial α := by
  simp [egfOnes, encode, ones]

theorem egf_decode : decode .ogf ones = decode .egf egfOnes := by
  rw [egfOnes, decode_encode]
  rfl

/-- The certificate transports: same majorant, box and error. -/
noncomputable def egfCertificate : TailCertificate .egf egfOnes :=
  certificate.transport egf_decode

theorem egf_bound (N : ℕ) : TruncationBound .egf egfOnes half ![N, N] (8 * (1 / 2) ^ N) := by
  have e : egfCertificate.error ![N, N] = 8 * (1 / 2) ^ N := error_eq N
  exact e ▸ egfCertificate.truncationBound ![N, N]

theorem egf_field : analyticField .egf egfOnes = analyticField .ogf ones :=
  analyticField_encode .egf ones

end Gimle.Asgard.Examples.GeometricTail
