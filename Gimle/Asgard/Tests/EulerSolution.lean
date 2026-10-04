import Gimle.Asgard.Examples.EulerBand

/-! Coverage for the classical-solution theorem (task 067).

Pinned here: the partial derivatives of a field on single modes; the
Laplacian identity; the Jacobian identity on one pair of modes, checked
against the coupling by hand; the stream-function stream and its ℓ¹ bound;
the derivative series' bounds; the three-mode example as a classical solution
on `|t| < 1/648`, with its stream function; hostile checks — the Jacobian
identity needs an even `Q`, the open disc stops at the radius, and the field's
derivative of a constant mode vanishes; and a transitive standard-axiom audit
of every root theorem. -/

namespace Gimle.Asgard.Tests.EulerSolution

open Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.TrigStream
open Gimle.Asgard.Streams.NS
open Gimle.Asgard.Examples.EulerThreeMode
open Gimle.Asgard.Examples.EulerBand
open Real

/-! ### Derivatives of a field -/

/-- `∂₁ cos(x) = −sin x` at every point. -/
example (x : ℝ × ℝ) : fieldD₁ (Finsupp.single ((1, 0) : Wave) 1) x = -sin x.1 := by
  simp [fieldD₁, phase]

/-- `∂₂ cos(x)` vanishes: the mode `(1, 0)` has no `y`. -/
example (x : ℝ × ℝ) : fieldD₂ (Finsupp.single ((1, 0) : Wave) 1) x = 0 := by
  simp [fieldD₂, phase]

/-- The derivative facts are `HasDerivAt`, at every point. -/
example (P : TrigPoly) (x : ℝ × ℝ) : HasDerivAt (fun s => field P (s, x.2)) (fieldD₁ P x) x.1 :=
  hasDerivAt_field_fst P x
example (P : TrigPoly) (x : ℝ × ℝ) : HasDerivAt (fun s => field P (x.1, s)) (fieldD₂ P x) x.2 :=
  hasDerivAt_field_snd P x

/-- `Δ cos(2x + y) = −5 cos(2x + y)` through `field_laplacian`. -/
example (x : ℝ × ℝ) :
    field (laplacian (Finsupp.single ((2, 1) : Wave) 1)) x =
      -5 * cos (2 * x.1 + x.2) := by
  rw [field_laplacian]
  simp [fieldD₁₁, fieldD₂₂, phase]
  ring

/-! ### The Jacobian identity -/

/-- On one pair of modes the identity reduces to the coupling: with `P = e_{(1,0)}`,
`Q = cos(y)` (even), `field (transport P Q) = (1·1 − 0·0)/1 · (cos(x + y) + cos(x − y))/2`,
and the Jacobian `∂₁ψ ∂₂q − ∂₂ψ ∂₁q` with `ψ = −cos x` gives `sin x · (−sin y)`. -/
example (x : ℝ × ℝ) :
    field (transport (Finsupp.single ((1, 0) : Wave) 1) (cosine (0, 1))) x =
      fieldD₁ (laplacianInv (Finsupp.single ((1, 0) : Wave) 1)) x * fieldD₂ (cosine (0, 1)) x -
        fieldD₂ (laplacianInv (Finsupp.single ((1, 0) : Wave) 1)) x * fieldD₁ (cosine (0, 1)) x :=
  field_transport _ (isEven_cosine _) x

/-- The identity holds for the three-mode start against itself. -/
example (x : ℝ × ℝ) :
    field (transport ω₀ ω₀) x =
      fieldD₁ (laplacianInv ω₀) x * fieldD₂ ω₀ x - fieldD₂ (laplacianInv ω₀) x * fieldD₁ ω₀ x :=
  field_transport ω₀ ω₀_isEven x

/-! ### The stream function -/

example : l1 (laplacianInv ω₀) ≤ l1 ω₀ := l1_laplacianInv_le ω₀
example : GeometricBound (psi (stream .ogf 0 start)) 9 648 := geometricBound_psi geometric

/-- `Δ⁻¹` divides by `|k|²`: the `(2, 1)` coefficient `1/2` of the start becomes `−1/10`. -/
example : laplacianInv ω₀ (2, 1) = -(1 / 10) := by
  rw [laplacianInv_apply, if_neg (by decide), ω₀_eq_table, Table.toTrig_apply]
  decide +kernel

/-! ### The three-mode example -/

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField (stream .ogf 0 start) s x)
      (seriesDt (stream .ogf 0 start) t x) t :=
  (classical ht x).1

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesDt (stream .ogf 0 start) t x +
      (-seriesD₂ (psi (stream .ogf 0 start)) t x * seriesD₁ (stream .ogf 0 start) t x +
        seriesD₁ (psi (stream .ogf 0 start)) t x * seriesD₂ (stream .ogf 0 start) t x) = 0 :=
  (classical ht x).2

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesD₁₁ (psi (stream .ogf 0 start)) t x + seriesD₂₂ (psi (stream .ogf 0 start)) t x =
      analyticField (stream .ogf 0 start) t x :=
  laplacian_streamFunction ht x

/-- At `t = 0` the field is the start's: `3` at the origin. -/
example : analyticField (stream .ogf 0 start) 0 (0, 0) = 3 := by
  rw [analyticField_zero]
  show field ω₀ (0, 0) = 3
  rw [field_start]; norm_num

/-- The whole statement, with every derivative, at the three-mode start. -/
example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField (stream .ogf 0 start) t (s, x.2))
      (seriesD₁ (stream .ogf 0 start) t x) x.1 :=
  (euler_classical start ω₀_meanZero ω₀_isEven start_sizeLE geometric (by norm_num) ht x).2.1

/-! ### Hostile -/

/-- The Jacobian identity's hypothesis is evenness of `Q`, not of `P`: the
theorem is stated for every `P`. -/
example (P : TrigPoly) (x : ℝ × ℝ) :
    field (transport P ω₀) x =
      fieldD₁ (laplacianInv P) x * fieldD₂ ω₀ x - fieldD₂ (laplacianInv P) x * fieldD₁ ω₀ x :=
  field_transport P ω₀_isEven x

/-- The open disc stops at the radius: `|t| < 1/648` fails at `t = 1/648`. -/
example : ¬ (|(1 / 648 : ℝ)| < 1 / 648) := by norm_num

/-- The derivative of the zero mode's field vanishes. -/
example (x : ℝ × ℝ) : fieldD₁ (Finsupp.single ((0, 0) : Wave) 7) x = 0 := by
  simp [fieldD₁, phase]

/-- `ρ |t| < 1` on the disc, the hypothesis every bound uses. -/
example {t : ℝ} (ht : |t| < 1 / 648) : (648 : ℝ) * |t| < 1 := mul_abs_lt_one (by norm_num) ht

/-! ### Axioms -/

#print axioms Gimle.Asgard.Streams.Torus.field_transport
#print axioms Gimle.Asgard.Streams.NS.euler_classical
#print axioms Gimle.Asgard.Examples.EulerBand.classical
#print axioms Gimle.Asgard.Examples.EulerBand.laplacian_streamFunction

end Gimle.Asgard.Tests.EulerSolution
