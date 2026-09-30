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
smaller. Nothing here identifies the analytic field with `1/(1 + e^(x − t/2))`;
that is a separate statement. -/
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

#print axioms constantCoeff_front_eq
#print axioms bound
end Gimle.Asgard.Examples.BurgersFront
