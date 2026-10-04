import Gimle.Asgard.Examples.EulerBand

/-! Coverage for the classical-solution theorem (task 067).

Pinned here: the partial derivatives of a field on single modes; the Laplacian
identity; the Jacobian identity on one pair of modes, evaluated numerically at
a point where a flipped sign would show, and on the three-mode start against
itself; the stream-function stream and its ℓ¹ bound; the summability lemmas
behind the derivative series; the three-mode example as a classical solution
on `|t| < 1/648`, with its stream function, its derivatives and its initial
value; hostile checks — the Jacobian identity fails for an odd `Q`, the open
disc stops at the radius, and the derivative of a constant mode vanishes; and
a transitive standard-axiom check of every root theorem that fails on any
other axiom. -/

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
example (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (x.1, s)) (fieldD₁₂ P x) x.2 := hasDerivAt_fieldD₁_snd P x

/-- `Δ cos(2x + y) = −5 cos(2x + y)` through `field_laplacian`. -/
example (x : ℝ × ℝ) :
    field (laplacian (Finsupp.single ((2, 1) : Wave) 1)) x = -5 * cos (2 * x.1 + x.2) := by
  rw [field_laplacian]
  simp [fieldD₁₁, fieldD₂₂, phase]
  ring

/-- The fields and their derivatives are continuous. -/
example (P : TrigPoly) : Continuous (field P) := continuous_field P
example (P : TrigPoly) : Continuous (fieldD₁₂ P) := continuous_fieldD₁₂ P

/-! ### The Jacobian identity -/

/-- On one pair of modes the identity reduces to the coupling: with `P = e_{(1,0)}` and
`Q = cos y` (even), `transport P Q = ½(e_{(1,1)} − e_{(1,−1)})`, whose field is
`(cos(x + y) − cos(x − y))/2 = −sin x sin y`, and the Jacobian with `ψ = −cos x` is
`sin x · (−sin y) − 0`. -/
example (x : ℝ × ℝ) :
    field (transport (Finsupp.single ((1, 0) : Wave) 1) (cosine (0, 1))) x =
      fieldD₁ (laplacianInv (Finsupp.single ((1, 0) : Wave) 1)) x * fieldD₂ (cosine (0, 1)) x -
        fieldD₂ (laplacianInv (Finsupp.single ((1, 0) : Wave) 1)) x * fieldD₁ (cosine (0, 1)) x :=
  field_transport _ (isEven_cosine _) x

/-- The transport field of that pair is `(cos(x + y) − cos(x − y))/2`. -/
example (x : ℝ × ℝ) :
    field (transport (Finsupp.single ((1, 0) : Wave) 1) (cosine (0, 1))) x =
      (cos (x.1 + x.2) - cos (x.1 - x.2)) / 2 := by
  rw [cosine, transport_add_right, transport_single_single, transport_single_single, field_add,
    field_single, field_single]
  simp only [coupling, cross, lam, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring_nf

/-- At `(π/2, π/2)` the transport field of `P = e_{(1,0)}`, `Q = cos y` is
`−sin x sin y = −1`; a flipped coupling would give `+1`. -/
example :
    field (transport (Finsupp.single ((1, 0) : Wave) 1) (cosine (0, 1))) (π / 2, π / 2) = -1 := by
  rw [cosine, transport_add_right, transport_single_single, transport_single_single, field_add,
    field_single, field_single]
  simp only [coupling, cross, lam]
  norm_num [show (π : ℝ) / 2 + π / 2 = π by ring, cos_pi]

/-- …and the Jacobian side, computed directly from `ψ = −cos x` and `q = cos y`, is
`sin(π/2) · (−sin(π/2)) − 0 = −1` too; a sign error in `laplacianInv` or in a
derivative field would show here. -/
example :
    fieldD₁ (laplacianInv (Finsupp.single ((1, 0) : Wave) 1)) (π / 2, π / 2) *
        fieldD₂ (cosine (0, 1)) (π / 2, π / 2) -
      fieldD₂ (laplacianInv (Finsupp.single ((1, 0) : Wave) 1)) (π / 2, π / 2) *
        fieldD₁ (cosine (0, 1)) (π / 2, π / 2) = -1 := by
  have hψ : laplacianInv (Finsupp.single ((1, 0) : Wave) 1) =
      Finsupp.single ((1, 0) : Wave) (-1) := by
    ext k
    rw [laplacianInv_apply]
    by_cases hk : k = (1, 0)
    · subst hk; simp [lam]
    · simp [Finsupp.single_apply, Ne.symm hk, hk]
  rw [hψ, cosine, fieldD₁, fieldD₂, fieldD₁, fieldD₂]
  simp only [Finset.sum_singleton, Finsupp.single_apply, phase]
  norm_num [Finsupp.support_add_eq, Finsupp.support_single, Finsupp.single_apply,
    sin_pi_div_two, cos_pi_div_two]

/-- The identity holds for the three-mode start against itself. -/
example (x : ℝ × ℝ) :
    field (transport ω₀ ω₀) x =
      fieldD₁ (laplacianInv ω₀) x * fieldD₂ ω₀ x - fieldD₂ (laplacianInv ω₀) x * fieldD₁ ω₀ x :=
  field_transport ω₀ ω₀_isEven x

/-! ### The stream function -/

example : l1 (laplacianInv ω₀) ≤ l1 ω₀ := l1_laplacianInv_le ω₀
example : GeometricBound (psi (stream .ogf 0 start)) 9 648 := geometricBound_psi geometric
example : SizeLE 3 (laplacianInv ω₀) := sizeLE_laplacianInv start_sizeLE

/-- `Δ⁻¹` divides by `|k|²`: the `(2, 1)` coefficient `1/2` of the start becomes `−1/10`. -/
example : laplacianInv ω₀ (2, 1) = -(1 / 10) := by
  rw [laplacianInv_apply, if_neg (by decide), ω₀_eq_table, Table.toTrig_apply]
  decide +kernel

/-! ### Summability -/

example : Summable fun n : ℕ => (n : ℝ) * (1 / 2) ^ (n - 1) :=
  summable_mul_pow_pred (by norm_num) (by norm_num)
example : Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * (1 / 10) ^ n :=
  summable_succ_pow_mul_geometric 2 (by norm_num) (by norm_num)
example : Summable fun n : ℕ => ((n : ℝ) + 1) ^ 3 * (0 : ℝ) ^ n :=
  summable_succ_pow_mul_geometric 3 le_rfl zero_lt_one
example {t : ℝ} (ht : |t| < 1 / 648) : (648 : ℝ) * |t| < 1 := mul_abs_lt_one (by norm_num) ht

/-! ### The three-mode example -/

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    IsClassicalSolution (stream .ogf 0 start) t x := classical ht x

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField (stream .ogf 0 start) s x)
      (seriesDt (stream .ogf 0 start) t x) t :=
  (classical ht x).derivT

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField (stream .ogf 0 start) t (s, x.2))
      (seriesD₁ (stream .ogf 0 start) t x) x.1 :=
  (classical ht x).derivX₁

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesDt (stream .ogf 0 start) p.1 p.2) (t, x) :=
  (classical ht x).continuous_derivT

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesDt (stream .ogf 0 start) t x +
      (-seriesD₂ (psi (stream .ogf 0 start)) t x * seriesD₁ (stream .ogf 0 start) t x +
        seriesD₁ (psi (stream .ogf 0 start)) t x * seriesD₂ (stream .ogf 0 start) t x) = 0 :=
  vorticity_equation ht x

example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesD₁₁ (psi (stream .ogf 0 start)) t x + seriesD₂₂ (psi (stream .ogf 0 start)) t x =
      analyticField (stream .ogf 0 start) t x :=
  laplacian_streamFunction ht x

/-- The vorticity equation in its `seriesDt_eq` form, at the example's constants. -/
example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    seriesDt (stream .ogf 0 start) t x =
      -(seriesD₁ (psi (stream .ogf 0 start)) t x * seriesD₂ (stream .ogf 0 start) t x -
        seriesD₂ (psi (stream .ogf 0 start)) t x * seriesD₁ (stream .ogf 0 start) t x) :=
  seriesDt_eq start ω₀_isEven start_sizeLE geometric (by norm_num) ht x

/-- At `t = 0` the field is the start's: `3` at the origin. -/
example : analyticField (stream .ogf 0 start) 0 (0, 0) = 3 := by
  rw [initial]; norm_num

/-- The mixed derivatives of the stream function agree, which is `div u = 0`. -/
example {t : ℝ} (ht : |t| < 1 / 648) (x : ℝ × ℝ) :
    HasDerivAt (fun s => -seriesD₂ (psi (stream .ogf 0 start)) t (s, x.2))
      (-seriesD₁₂ (psi (stream .ogf 0 start)) t x) x.1 ∧
    HasDerivAt (fun s => seriesD₁ (psi (stream .ogf 0 start)) t (x.1, s))
      (seriesD₁₂ (psi (stream .ogf 0 start)) t x) x.2 :=
  ⟨(classical ht x).psi_derivX₂X₁.neg, (classical ht x).psi_derivX₁X₂⟩

/-! ### Hostile -/

/-- The Jacobian identity needs `Q` even: for the odd `Q = e_{(0,1)} − e_{(0,−1)}` the
field `Σ Q_k cos(k·x)` vanishes identically, so the Jacobian side is `0`, while the
transport side is `cos(x + y) + cos(x − y)`, which is `2 cos x cos y`. -/
example (x : ℝ × ℝ) :
    field (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1) x = 0 := by
  rw [sub_eq_add_neg, ← Finsupp.single_neg, field_add, field_single, field_single]
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, zero_add]
  rw [show -(1 : ℝ) * x.2 = -x.2 by ring, cos_neg]
  push_cast
  ring

/-- Its derivative fields vanish too (the derivatives of the zero function), so the
Jacobian side is `0` for every `P`… -/
example (x : ℝ × ℝ) :
    fieldD₁ (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1) x = 0 ∧
    fieldD₂ (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1) x = 0 := by
  have h0 : ∀ y : ℝ × ℝ,
      field (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1) y = 0 := by
    intro y
    rw [sub_eq_add_neg, ← Finsupp.single_neg, field_add, field_single, field_single]
    simp only [Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, zero_add]
    rw [show -(1 : ℝ) * y.2 = -y.2 by ring, cos_neg]
    push_cast
    ring
  have h1 := hasDerivAt_field_fst
    (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1) x
  have h2 := hasDerivAt_field_snd
    (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1) x
  simp only [h0] at h1 h2
  exact ⟨h1.unique (hasDerivAt_const _ _), h2.unique (hasDerivAt_const _ _)⟩

/-- …while at the origin the transport side is `2`: the identity fails for odd `Q`. -/
example :
    field (transport (Finsupp.single ((1, 0) : Wave) 1)
      (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1)) (0, 0) = 2 := by
  rw [sub_eq_add_neg, ← Finsupp.single_neg, transport_add_right, transport_single_single,
    transport_single_single, field_add, field_single, field_single]
  simp only [coupling, cross, lam, Prod.fst_add, Prod.snd_add]
  norm_num
example (x : ℝ × ℝ) :
    field (transport (Finsupp.single ((1, 0) : Wave) 1)
      (Finsupp.single ((0, 1) : Wave) 1 - Finsupp.single ((0, -1) : Wave) 1)) x =
      cos (x.1 + x.2) + cos (x.1 - x.2) := by
  rw [sub_eq_add_neg, ← Finsupp.single_neg, transport_add_right, transport_single_single,
    transport_single_single, field_add, field_single, field_single]
  simp only [coupling, cross, lam, Prod.fst_add, Prod.snd_add]
  push_cast
  ring_nf

/-- The theorem is stated for every `P`; only `Q` must be even. -/
example (P : TrigPoly) (x : ℝ × ℝ) :
    field (transport P ω₀) x =
      fieldD₁ (laplacianInv P) x * fieldD₂ ω₀ x - fieldD₂ (laplacianInv P) x * fieldD₁ ω₀ x :=
  field_transport P ω₀_isEven x

/-- The open disc stops at the radius: `|t| < 1/648` fails at `t = 1/648`. -/
example : ¬ (|(1 / 648 : ℝ)| < 1 / 648) := by norm_num

/-- The derivative of the zero mode's field vanishes. -/
example (x : ℝ × ℝ) : fieldD₁ (Finsupp.single ((0, 0) : Wave) 7) x = 0 := by
  simp [fieldD₁, phase]

/-! ### Axioms -/

/--
info: 'Gimle.Asgard.Streams.Torus.field_transport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.field_transport
/--
info: 'Gimle.Asgard.Streams.Torus.field_laplacian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.field_laplacian
/--
info: 'Gimle.Asgard.Streams.TrigStream.hasDerivAt_analyticField_t'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Gimle.Asgard.Streams.TrigStream.hasDerivAt_analyticField_t
/--
info: 'Gimle.Asgard.Streams.TrigStream.continuousAt_analyticField'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Gimle.Asgard.Streams.TrigStream.continuousAt_analyticField
/--
info: 'Gimle.Asgard.Streams.NS.seriesDt_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.seriesDt_eq
/--
info: 'Gimle.Asgard.Streams.NS.seriesD₁₁_psi_add_seriesD₂₂_psi'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Gimle.Asgard.Streams.NS.seriesD₁₁_psi_add_seriesD₂₂_psi
/--
info: 'Gimle.Asgard.Streams.NS.analyticField_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.analyticField_zero
/--
info: 'Gimle.Asgard.Streams.NS.euler_classical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.euler_classical
/--
info: 'Gimle.Asgard.Examples.EulerBand.classical'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.classical
/--
info: 'Gimle.Asgard.Examples.EulerBand.vorticity_equation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Gimle.Asgard.Examples.EulerBand.vorticity_equation
/--
info: 'Gimle.Asgard.Examples.EulerBand.laplacian_streamFunction'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Gimle.Asgard.Examples.EulerBand.laplacian_streamFunction
/--
info: 'Gimle.Asgard.Examples.EulerBand.initial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerBand.initial

end Gimle.Asgard.Tests.EulerSolution
