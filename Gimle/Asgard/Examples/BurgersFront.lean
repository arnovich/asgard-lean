import Gimle.Asgard.Streams.ColeHopf

/-! # The viscous Burgers front, certified

`φ(0, x) = 1 + e^(−x)` with `ν = 1/2` gives, through Cole–Hopf, the front
`u = 1/(1 + e^(x − t/2))`: a step from `1` on the left to `0` on the right,
moving right at speed `1/2`. Its formal Burgers stream is `ColeHopf.front`,
and this file checks every side condition of `front_truncation` by kernel
computation: the profile fits `ρ = 1`; the inverse is majorized at radii
`(2/3, 1/2)` because `(M_rest/|c|)·(∏(1 − r_i/R_i)⁻¹ − 1) = (1/2)·(3 − 1) = 1`;
the product halves the radii to `(1/3, 1/4)`; on the box `|t| ≤ 1/6`,
`|x| ≤ 1/8` at window `16 × 16` the certified error is exactly `1/16384`.

The bound is a proof, not a measurement: the true error on that box is far
smaller. The last section identifies the analytic field on the box with the
classical front `1/(1 + e^(x − t/2))` (`front_field_eq`), and proves the band
`2/5 ≤ u ≤ 3/5` there for every stream the circuit reconstructs from the
front's slice, while `u ≤ 27/50` fails at the corner `(1/6, −1/8)`. -/
namespace Gimle.Asgard.Examples.BurgersFront

open Gimle.Asgard.Streams Gimle.Asgard.Streams.ColeHopf
open Gimle.Asgard.Streams.AnalyticHeat (expSumFits)
open MvPowerSeries (constantCoeff)

/-- `1 + e^(−x)` as `[(c, a)]` pairs. -/
def terms : List (ℚ × ℚ) := [(1, 0), (1, -1)]

/-- The viscosity. -/
def ν : ℚ := 1 / 2

/-- The profile radius. -/
def ρ : ℚ := 1

/-- The radii for the inverse. -/
def r : Fin 2 → ℚ := ![2 / 3, 1 / 2]

/-- The box `|t| ≤ 1/6`, `|x| ≤ 1/8`. -/
def box : Box 2 := ⟨![1 / 6, 1 / 8], fun i => by fin_cases i <;> norm_num⟩

/-- The window `16 × 16`. -/
def N : Fin 2 → ℕ := ![16, 16]

/-! Every side condition of `front_truncation`, decided by the kernel. -/

theorem hν : 0 < ν := by norm_num [ν]
theorem hρ : 0 < ρ := by norm_num [ρ]
theorem c0 : constantTerm terms ≠ 0 := by decide +kernel
theorem fits : expSumFits terms ρ = true := by decide +kernel
theorem hr : ∀ i, 0 < r i := by decide +kernel
theorem inside : ∀ i, r i < heatRadii ν ρ i := by decide +kernel
theorem small : smallEnough ν ρ terms r := by decide +kernel
theorem boxInside : ∀ i, box.radius i < r i / 2 := by decide +kernel

/-- The front's value at the origin is `1/2`: `u(0, 0) = 1/(1 + e⁰)`. -/
theorem constantCoeff_front_eq : constantCoeff (front ν terms) = 1 / 2 := by
  rw [constantCoeff_front]
  decide +kernel

/-- The front's majorant bound is `1/2`, at radii `(1/3, 1/4)`. -/
theorem frontBound_eq : frontBound ν terms = 1 / 2 := by decide +kernel

/-- The certified truncation error at window `16 × 16`. -/
theorem error_eq : tailBound (frontMajorant ν terms r hr) box N = 1 / 16384 := by decide +kernel

/-- **The root claim.** Whatever the Burgers circuit at `ν = 1/2` reconstructs
from the front's `t = 0` slice differs from its `16 × 16` window by at most
`1/16384` everywhere on the box. -/
theorem bound :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        TruncationBound .ogf a box N (1 / 16384) :=
  front_truncation hν hρ terms c0 fits hr inside small box boxInside N (le_of_eq error_eq)

/-! ## The analytic field is the closed form `1/(1 + e^(x − t/2))` -/

/-- On the certified box the front's analytic field is `1/(1 + e^(x − t/2))`:
the Cole–Hopf quotient of the classical heat fields, `−2ν · (−e^(t/2 − x)) /
(1 + e^(t/2 − x))` at `ν = 1/2`. -/
theorem front_field_eq {x : Fin 2 → ℝ} (hx : box.Mem x) :
    analyticField .ogf (front ν terms) x = 1 / (1 + Real.exp (x 1 - x 0 / 2)) := by
  obtain ⟨_, eq⟩ := analyticField_front hν hρ terms c0 fits hr inside small box boxInside hx
  rw [eq]
  have shift : Real.exp (x 1 - x 0 / 2) = (Real.exp (x 0 / 2 - x 1))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have num : expSumField ν (shifted terms) x = -Real.exp (x 0 / 2 - x 1) := by
    simp only [expSumField, shifted, terms, ν, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    push_cast
    ring_nf
  have den : expSumField ν terms x = 1 + Real.exp (x 0 / 2 - x 1) := by
    simp only [expSumField, terms, ν, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
    rw [Real.exp_zero]
  rw [num, den, shift]
  have pos := Real.exp_pos (x 0 / 2 - x 1)
  simp only [ν]
  push_cast
  field_simp
  ring

/-- The box is `|x − t/2| ≤ 5/24`. -/
private theorem shift_bound {x : Fin 2 → ℝ} (hx : box.Mem x) : |x 1 - x 0 / 2| ≤ 5 / 24 := by
  have h0 := hx 0
  have h1 := hx 1
  simp only [box, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  push_cast at h0 h1
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- **The band.** On the box, `2/5 ≤ u ≤ 3/5`, from `s + 1 ≤ e^s` alone:
`e^s ≥ 19/24` and `e^(−s) ≥ 19/24` for `|s| ≤ 5/24`. -/
theorem front_band {x : Fin 2 → ℝ} (hx : box.Mem x) :
    2 / 5 ≤ analyticField .ogf (front ν terms) x ∧ analyticField .ogf (front ν terms) x ≤ 3 / 5 := by
  rw [front_field_eq hx]
  have hs := shift_bound hx
  rw [abs_le] at hs
  set s := x 1 - x 0 / 2 with hs_def
  have up := Real.add_one_le_exp s
  have low := Real.add_one_le_exp (-s)
  rw [Real.exp_neg] at low
  have pos := Real.exp_pos s
  have cancel : Real.exp s * (Real.exp s)⁻¹ = 1 := mul_inv_cancel₀ pos.ne'
  have inv_pos : 0 < (Real.exp s)⁻¹ := inv_pos.mpr pos
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left low pos.le]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- The corner `(t, x) = (1/6, −1/8)` lies in the box. -/
theorem corner_mem : box.Mem ![1 / 6, -1 / 8] := by
  intro i
  fin_cases i <;> norm_num [box]

/-- At the corner the front exceeds `27/50`: `u = 1/(1 + e^(−5/24))` and
`e^(−5/24) ≤ 24/29`. -/
theorem front_corner_gt : 27 / 50 < analyticField .ogf (front ν terms) ![1 / 6, -1 / 8] := by
  rw [front_field_eq corner_mem]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have arg : (-1 / 8 : ℝ) - 1 / 6 / 2 = -(5 / 24) := by norm_num
  rw [arg, Real.exp_neg]
  have low := Real.add_one_le_exp (5 / 24 : ℝ)
  have pos := Real.exp_pos (5 / 24 : ℝ)
  rw [lt_div_iff₀ (by positivity)]
  have : (Real.exp (5 / 24))⁻¹ ≤ 24 / 29 := by
    rw [inv_le_comm₀ pos (by norm_num)]
    linarith
  linarith

/-- **The band, for every reconstruction.** Whatever the Burgers circuit at
`ν = 1/2` reconstructs from the front's `t = 0` slice has its analytic field
in `[2/5, 3/5]` everywhere on the box. -/
theorem band :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, box.Mem x →
          2 / 5 ≤ analyticField .ogf a x ∧ analyticField .ogf a x ≤ 3 / 5 := by
  intro a unused v rel x hx
  have hc : constantCoeff (expSumHeat ν terms) ≠ 0 := by
    rw [constantCoeff_expSumHeat]; exact c0
  simp only [front] at rel
  rw [candidate_quotient ν _ hc (heatSeries_pde ν _) a unused v rel]
  exact front_band hx

/-- **Refuted.** `u ≤ 27/50` on the box is false: the front itself is a
reconstruction, and at the corner it exceeds `27/50`. -/
theorem not_below :
    ¬ ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, box.Mem x → analyticField .ogf a x ≤ 27 / 50 := by
  intro h
  have := h (front ν terms) 0 _ (circuit_front ν terms c0 0) _ corner_mem
  linarith [front_corner_gt]

#print axioms constantCoeff_front_eq
#print axioms bound
#print axioms front_field_eq
#print axioms band
#print axioms not_below
end Gimle.Asgard.Examples.BurgersFront
