import Gimle.Asgard.Streams.AnalyticHeat
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Heat evolution of the profile `e^x`, with a certified truncation

The profile `e^x` has raw EGF coefficients `g_j = 1`, so its heat stream has
raw EGF coefficients `u_(n,k) = 1` (`stream_egf`): the output is `e^(x+t)`. The
certified profile bound is `|1| ≤ 1 · 1^(−j)` (`M = ρ = 1`), so the heat
majorant is `M = 1` with radii `[1, 1]` on `[t, x]`.

On the box `|t| ≤ 1/4`, `|x| ≤ 1/2` at the window `(8, 16)` (`t`-degree `< 8`,
`x`-degree `< 16`), with `q_t = 1/4`, `q_x = 1/2`:

`ε = 1 · (4^(−8) + 2^(−16)) · (4/3) · 2 = 1/12288`   (`error_eq`, by `decide +kernel`).

The analytic field is `exp (x + t)` at every real point (`analyticField_eq`), so
on the box `|exp (x + t) − W| ≤ 1/12288`, where `W` is the window field, the
real field of the window polynomial (`exp_bound`). The majorant drops the
factorials, so this bound is conservative. -/
namespace Gimle.Asgard.Examples.ExpHeat

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.AnalyticHeat

/-- Raw EGF coefficients of `e^x`: every derivative at `0` is `1`. -/
def g : ℕ → ℚ := fun _ => 1

/-- Every raw EGF coefficient of the heat stream is `1`: the EGF of `e^(x+t)`. -/
theorem stream_egf (α : Index 2) : stream .egf g α = 1 := stream_egf_apply g α

/-- The certified profile bound, for **every** `j`: `|1| ≤ 1 · 1^(−j)`. -/
theorem profileBound : ProfileBound g 1 1 := by
  intro j
  simp [g]

/-- The heat majorant `M = 1`, radii `[1², 1]`. -/
def majorant : Majorant 2 := heatMajorant 1 1 (by norm_num) (by norm_num)

/-- `|t| ≤ 1/4`, `|x| ≤ 1/2`. -/
def box : Box 2 := ⟨![1 / 4, 1 / 2], fun i => by fin_cases i <;> norm_num⟩

/-- The window `t`-degree `< 8`, `x`-degree `< 16`. -/
def window : Fin 2 → ℕ := ![8, 16]

/-- The box is strictly inside the radii, checked by the kernel. -/
theorem inside : ∀ i, box.radius i < majorant.radius i := by
  decide +kernel

/-- The certificate, in either basis. -/
noncomputable def certificate (basis : Basis) : TailCertificate basis (stream basis g) :=
  AnalyticHeat.certificate basis (by norm_num) (by norm_num) profileBound box inside

/-- The certified error at the window. -/
def error : ℚ := tailBound majorant box window

/-- `ε = 1/12288`, computed exactly by the kernel. -/
theorem error_eq : error = 1 / 12288 := by
  decide +kernel

theorem certificate_error (basis : Basis) : (certificate basis).error window = error := rfl

/-- **Certified bound**: uniformly on the box, `|F − W| ≤ 1/12288`. -/
theorem bound (basis : Basis) : TruncationBound basis (stream basis g) box window (1 / 12288) :=
  error_eq ▸ (certificate basis).truncationBound window

/-! ## The analytic field is `exp (x + t)` -/

private theorem seriesTerm_eq (basis : Basis) (y : Fin 2 → ℝ) (α : Index 2) :
    seriesTerm basis (stream basis g) y α =
      ∏ i, y i ^ α i / ((α i).factorial : ℝ) := by
  rw [seriesTerm, decode_stream, Fin.prod_univ_two, Fin.prod_univ_two]
  change ((1 / factorial α : ℚ) : ℝ) * _ = _
  simp only [factorial, Fin.prod_univ_two]
  push_cast
  field_simp

private theorem hasSum_exp (r : ℝ) : HasSum (fun k => r ^ k / (k.factorial : ℝ)) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

/-- At every real point `(t, x)` the heat series converges to `exp (x + t)`. -/
theorem hasSum_field (basis : Basis) (y : Fin 2 → ℝ) :
    HasSum (seriesTerm basis (stream basis g) y) (Real.exp (y 1 + y 0)) := by
  have h := hasSum_index_prod (fun i k => y i ^ k / (k.factorial : ℝ)) (fun i => Real.exp (y i))
    (fun i => by
      simpa [norm_div, norm_pow, Real.norm_eq_abs] using Real.summable_pow_div_factorial |y i|)
    (fun i => hasSum_exp (y i))
  rw [Fin.prod_univ_two, ← Real.exp_add, add_comm] at h
  exact (funext (seriesTerm_eq basis y)) ▸ h

/-- **The analytic field is `exp (x + t)`**, everywhere, hence on the box. -/
theorem analyticField_eq (basis : Basis) (y : Fin 2 → ℝ) :
    analyticField basis (stream basis g) y = Real.exp (y 1 + y 0) :=
  (hasSum_field basis y).tsum_eq

/-- **Worked result**: on `|t| ≤ 1/4`, `|x| ≤ 1/2`, the window field at `(8, 16)`
is within `1/12288` of `exp (x + t)`. -/
theorem exp_bound (basis : Basis) (y : Fin 2 → ℝ) (hy : box.Mem y) :
    |Real.exp (y 1 + y 0) - windowField basis window (stream basis g) y| ≤ 1 / 12288 := by
  have h := bound basis y hy
  rw [analyticField_eq] at h
  push_cast at h
  exact h

end Gimle.Asgard.Examples.ExpHeat
