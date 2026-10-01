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

/-! ## The same band from a checked window, with no closed form

What a decider can do: the window of `φ⁻¹` below `16 × 16` is a table of
rationals computed outside Lean and checked here by `WindowIdentity`
(`decide +kernel`); the front's window follows, its spread over the box is a
rational sum, and `front_band_of_window` turns the certified truncation error
into a band on the analytic field — without `front_field_eq`, for any stream
with a certificate. The band it proves is a little wider than the truth
(`[0.4477, 0.5523]` against `[0.448, 0.552]`), which is the price of a bound
the kernel computes; `[2/5, 3/5]` is well inside it, and the corner
`(1/6, −1/8)` still refutes `27/50`. -/

open Gimle.Asgard.Streams.Lowering

def inverseTable : List (List ℚ) := [
  [1 / 2, 1 / 4, 0, -1 / 48, 0, 1 / 480, 0, -17 / 80640, 0, 31 / 1451520, 0, -691 / 319334400, 0, 5461 / 24908083200, 0, -929569 / 41845579776000],
  [-1 / 8, 0, 1 / 32, 0, -1 / 192, 0, 17 / 23040, 0, -31 / 322560, 0, 691 / 58060800, 0, -5461 / 3832012800, 0, 929569 / 5579410636800, 0],
  [0, -1 / 64, 0, 1 / 192, 0, -17 / 15360, 0, 31 / 161280, 0, -691 / 23224320, 0, 5461 / 1277337600, 0, -929569 / 1594117324800, 0, 3202291 / 41845579776000],
  [1 / 384, 0, -1 / 384, 0, 17 / 18432, 0, -31 / 138240, 0, 691 / 15482880, 0, -5461 / 696729600, 0, 929569 / 735746457600, 0, -3202291 / 16738231910400, 0],
  [0, 1 / 1536, 0, -17 / 36864, 0, 31 / 184320, 0, -691 / 15482880, 0, 5461 / 557383680, 0, -929569 / 490497638400, 0, 3202291 / 9564703948800, 0, -221930581 / 4017175658496000],
  [-1 / 15360, 0, 17 / 122880, 0, -31 / 368640, 0, 691 / 22118400, 0, -5461 / 619315200, 0, 929569 / 445906944000, 0, -3202291 / 7357464576000, 0, 221930581 / 2678117105664000, 0],
  [0, -17 / 737280, 0, 31 / 1105920, 0, -691 / 44236800, 0, 5461 / 928972800, 0, -929569 / 535088332800, 0, 3202291 / 7357464576000, 0, -221930581 / 2295528947712000, 0, 4722116521 / 241030539509760000],
  [17 / 10321920, 0, -31 / 5160960, 0, 691 / 123863040, 0, -5461 / 1857945600, 0, 929569 / 832359628800, 0, -3202291 / 9364045824000, 0, 221930581 / 2472108097536000, 0, -4722116521 / 224961836875776000, 0],
  [0, 31 / 41287680, 0, -691 / 495452160, 0, 5461 / 4954521600, 0, -929569 / 1664719257600, 0, 3202291 / 14982473318400, 0, -221930581 / 3296144130048000, 0, 4722116521 / 257099242143744000, 0, -968383680827 / 215963363400744960000],
  [-31 / 743178240, 0, 691 / 2972712960, 0, -5461 / 17836277760, 0, 929569 / 4280706662400, 0, -3202291 / 29964946636800, 0, 221930581 / 5393690394624000, 0, -4722116521 / 355983566045184000, 0, 968383680827 / 259156036080893952000, 0],
  [0, -691 / 29727129600, 0, 5461 / 89181388800, 0, -929569 / 14269022208000, 0, 3202291 / 74912366592000, 0, -221930581 / 10787380789248000, 0, 4722116521 / 593305943408640000, 0, -968383680827 / 370222908686991360000, 0, 14717667114151 / 19436702706067046400000],
  [691 / 653996851200, 0, -5461 / 653996851200, 0, 929569 / 62783697715200, 0, -3202291 / 235438866432000, 0, 221930581 / 26369153040384000, 0, -4722116521 / 1186611886817280000, 0, 968383680827 / 626531076239523840000, 0, -14717667114151 / 28507163968898334720000, 0],
  [0, 5461 / 7847962214400, 0, -929569 / 376702186291200, 0, 3202291 / 941755465728000, 0, -221930581 / 79107459121152000, 0, 4722116521 / 2847868528361472000, 0, -968383680827 / 1253062152479047680000, 0, 14717667114151 / 48869423946682859520000, 0, -2093660879252671 / 20525158057606800998400000],
  [-5461 / 204047017574400, 0, 929569 / 3264752281190400, 0, -3202291 / 4897128421785600, 0, 221930581 / 293827705307136000, 0, -4722116521 / 8227175748599808000, 0, 968383680827 / 2961783269495930880000, 0, -14717667114151 / 97738847893365719040000, 0, 2093660879252671 / 35576940633185121730560000, 0],
  [0, -929569 / 45706531936665600, 0, 3202291 / 34279898952499200, 0, -221930581 / 1371195958099968000, 0, 4722116521 / 28795115120099328000, 0, -968383680827 / 8292993154588606464000, 0, 14717667114151 / 228057311751186677760000, 0, -2093660879252671 / 71153881266370243461120000, 0, 86125672563201181 / 7471157532968875563417600000],
  [929569 / 1371195958099968000, 0, -3202291 / 342798989524992000, 0, 221930581 / 8227175748599808000, 0, -4722116521 / 123407636228997120000, 0, 968383680827 / 27643310515295354880000, 0, -14717667114151 / 621974486594145484800000, 0, 2093660879252671 / 164201264460854407987200000, 0, -86125672563201181 / 14942315065937751126835200000, 0]]

/-- The window of `φ⁻¹` as a function of degree vectors. -/
def Q (k : Degrees 2) : ℚ := (inverseTable.getD (k 0) []).getD (k 1) 0

theorem windowIdentity : WindowIdentity ν terms N Q := by decide +kernel

theorem positiveWindow : ∀ i, 0 < N i := by decide +kernel

/-- The band the window gives: its constant term, spread and the error. -/
theorem band_window_low :
    (2 / 5 : ℚ) ≤ frontWindow ν terms Q 0 - windowSpread ν terms Q box N - 1 / 16384 := by
  decide +kernel

theorem band_window_high :
    frontWindow ν terms Q 0 + windowSpread ν terms Q box N + 1 / 16384 ≤ 3 / 5 := by
  decide +kernel

/-- **The band, from the window alone.** -/
theorem band_of_window :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, box.Mem x →
          2 / 5 ≤ analyticField .ogf a x ∧ analyticField .ogf a x ≤ 3 / 5 := by
  intro a unused v rel x hx
  have h := front_band_of_window hν hρ terms c0 fits hr inside small box boxInside N
    positiveWindow (le_of_eq error_eq) windowIdentity band_window_low band_window_high
    a unused v rel x hx
  push_cast at h
  exact h

/-- The corner lies in the box, as rationals. -/
theorem corner_in_box : ∀ i, |(![1 / 6, -1 / 8] : Fin 2 → ℚ) i| ≤ box.radius i := by
  decide +kernel

/-- The window at the corner exceeds `27/50` by more than the error. -/
theorem corner_window_above :
    (27 / 50 : ℚ) < frontValue ν terms Q N ![1 / 6, -1 / 8] - 1 / 16384 := by
  decide +kernel

/-- **The refutation, from the window alone.** -/
theorem not_below_of_window :
    ¬ ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, box.Mem x → analyticField .ogf a x ≤ 27 / 50 := by
  intro h
  refine front_above_of_window hν hρ terms c0 fits hr inside small box boxInside N
    positiveWindow (le_of_eq error_eq) windowIdentity ![1 / 6, -1 / 8] corner_in_box
    corner_window_above fun a unused v rel x hx => ?_
  have := h a unused v rel x hx
  push_cast
  exact this

#print axioms constantCoeff_front_eq
#print axioms bound
#print axioms front_field_eq
#print axioms band
#print axioms not_below
#print axioms band_of_window
#print axioms not_below_of_window
end Gimle.Asgard.Examples.BurgersFront
