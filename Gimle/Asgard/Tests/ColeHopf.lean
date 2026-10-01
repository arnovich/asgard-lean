import Gimle.Asgard.Examples.BurgersFront

/-! Coverage for the majorant calculus and the Cole–Hopf front (task 061).

Pinned here: the ordinary derivative is a derivation that commutes across
axes; the inverse's majorant condition is exactly what limits the radii (the
front's `r = (2/3, 1/2)` is tight, and `(1, 1/2)` fails); a profile that does
not fit `ρ` is refused; a box on the halved radii is refused; the certified
error of the front and its majorant bound; the front's value at the origin,
the one boundary coefficient read off the opaque slice; a zero constant term
makes `smallEnough` trivially true, which is why `c0` is a separate
hypothesis; the analytic field of the front on the box is the classical front
and the band holds there while a tighter bound fails at a corner (task 062);
and a transitive standard-axiom audit of the root theorems and every example
claim. -/

namespace Gimle.Asgard.Tests.ColeHopf

open Gimle.Asgard.Streams Gimle.Asgard.Streams.ColeHopf Gimle.Asgard.Examples.BurgersFront
open MvPowerSeries (constantCoeff)
open Gimle.Asgard.Streams.AnalyticHeat (expSumFits)
/-! ### The derivative as a derivation -/

example {d : Nat} (i : Fin d) (a b : Stream d) : ogfD i (a * b) = ogfD i a * b + a * ogfD i b := ogfD_mul i a b

example {d : Nat} (i j : Fin d) (a : Stream d) : ogfD i (ogfD j a) = ogfD j (ogfD i a) := ogfD_comm i j a

/-! ### The front's side conditions, and what fails -/

example : frontBound ν terms = 1 / 2 := frontBound_eq
example : tailBound (frontMajorant ν terms r hr) box N = 1 / 16384 := error_eq

/-- The inverse's condition is tight at `r = (2/3, 1/2)`: with `r = (1, 1/2)` the
ratio tail is `(1/2)·(4 − 1) = 3/2 > 1`. -/
example : ¬ smallEnough ν ρ terms ![1, 1 / 2] := by
  unfold smallEnough; decide +kernel

/-- `1 + e^(−x)` does not fit `ρ = 2` (`|−1| · 2 > 1`). -/
example : expSumFits terms 2 = false := by decide +kernel

/-- A box reaching the halved radius `1/3` in `t` is rejected. -/
example : ¬ ∀ i, (⟨![1 / 3, 1 / 8], fun i => by fin_cases i <;> norm_num⟩ : Box 2).radius i < r i / 2 := by
  decide +kernel

/-- The front starts at `1/2` at the origin. -/
example : constantCoeff (front ν terms) = 1 / 2 := constantCoeff_front_eq

/-- The root's hypothesis is satisfiable: the circuit relates the front to its slice. -/
example (unused : Stream 2) :
    (Burgers.circuit .ogf ν).Rel ![front ν terms, zeroSlice (front ν terms), unused]
      ![Burgers.rhs .ogf ν (front ν terms), front ν terms] :=
  circuit_front ν terms c0 unused

/-- A profile with zero constant term has no inverse to speak of: `smallEnough`
is then trivially true (`x / 0 = 0`), so `front_truncation` demands `c0`
separately. -/
example : constantTerm [((1 : ℚ), (1 : ℚ)), (-1, 0)] = 0 := by decide +kernel
example : smallEnough ν ρ [((1 : ℚ), (1 : ℚ)), (-1, 0)] ![1, 1] := by decide +kernel

/-- A box strictly between the halved and the unhalved radii is rejected: the
product really costs a factor two. -/
example : ¬ ∀ i,
    (⟨![1 / 2, 1 / 8], fun i => by fin_cases i <;> norm_num⟩ : Box 2).radius i < r i / 2 := by
  decide +kernel

/-- An `ε` below the certified bound is not reached by this route. -/
example : ¬ tailBound (frontMajorant ν terms r hr) box N ≤ 1 / 20000 := by decide +kernel

/-- A finer window certifies a smaller error. -/
example : tailBound (frontMajorant ν terms r hr) box ![20, 20] = 1 / 262144 := by decide +kernel

/-! ### The analytic field (062) -/

/-- The field of the unit stream, of a scaled stream, and the product rule's shape. -/
example (x : Fin 2 → ℝ) : analyticField .ogf (1 : Stream 2) x = 1 := analyticField_one x

example (q : ℚ) (a : Stream 2) (x : Fin 2 → ℝ) :
    analyticField .ogf (MvPowerSeries.C q * a) x = q * analyticField .ogf a x :=
  analyticField_C_mul q a x

/-- The heat stream of `1 + e^(−x)` at `ν = 1/2` sums to `1 + e^(t/2 − x)` everywhere. -/
example (x : Fin 2 → ℝ) :
    analyticField .ogf (expSumHeat ν terms) x = expSumField ν terms x :=
  analyticField_heatSeries_expSum ν terms x

/-- On the box the front is the classical front. -/
example {x : Fin 2 → ℝ} (hx : box.Mem x) :
    analyticField .ogf (front ν terms) x = 1 / (1 + Real.exp (x 1 - x 0 / 2)) :=
  front_field_eq hx

/-- The band's two numbers are not sharp: the corner value is above `27/50`. -/
example : 27 / 50 < analyticField .ogf (front ν terms) ![1 / 6, -1 / 8] := front_corner_gt

/-- A point just outside the box is not covered by the identification. -/
example : ¬ box.Mem ![1 / 6, 1 / 4] := by
  intro h
  have := h 1
  norm_num [box] at this

/-- `band` is stated over every reconstruction, `not_below` is its refutation
at a tighter bound: the two are about the same root hypothesis. -/
example : ∀ a unused v : Stream 2,
    (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
      ∀ x : Fin 2 → ℝ, box.Mem x → 2 / 5 ≤ analyticField .ogf a x ∧ analyticField .ogf a x ≤ 3 / 5 :=
  band

example : ¬ ∀ a unused v : Stream 2,
    (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
      ∀ x : Fin 2 → ℝ, box.Mem x → analyticField .ogf a x ≤ 27 / 50 :=
  not_below

/-! ### Axioms -/

/--
info: 'Gimle.Asgard.Streams.analyticField_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.analyticField_mul
/--
info: 'Gimle.Asgard.Streams.analyticField_inv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.analyticField_inv
/--
info: 'Gimle.Asgard.Streams.ColeHopf.analyticField_heatSeries_expSum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.analyticField_heatSeries_expSum
/--
info: 'Gimle.Asgard.Streams.ColeHopf.analyticField_front'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.analyticField_front
/--
info: 'Gimle.Asgard.Examples.BurgersFront.front_field_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.front_field_eq
/--
info: 'Gimle.Asgard.Examples.BurgersFront.band'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.band
/--
info: 'Gimle.Asgard.Examples.BurgersFront.not_below'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.not_below

/--
info: 'Gimle.Asgard.Streams.ogfD_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ogfD_mul
/--
info: 'Gimle.Asgard.Streams.ogfD_inv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ogfD_inv
/--
info: 'Gimle.Asgard.Streams.majorizes_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.majorizes_mul
/--
info: 'Gimle.Asgard.Streams.majorizes_inv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.majorizes_inv
/--
info: 'Gimle.Asgard.Streams.ColeHopf.heatSeries_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.heatSeries_pde
/--
info: 'Gimle.Asgard.Streams.ColeHopf.quotient_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.quotient_pde
/--
info: 'Gimle.Asgard.Streams.ColeHopf.candidate_quotient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.candidate_quotient
/--
info: 'Gimle.Asgard.Streams.ColeHopf.majorizes_front'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.majorizes_front
/--
info: 'Gimle.Asgard.Streams.ColeHopf.front_truncation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.front_truncation
/--
info: 'Gimle.Asgard.Examples.BurgersFront.bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.bound
/--
info: 'Gimle.Asgard.Examples.BurgersFront.error_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.error_eq
/--
info: 'Gimle.Asgard.Streams.ogfD_comm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ogfD_comm
/--
info: 'Gimle.Asgard.Streams.majorizes_mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.majorizes_mono
/--
info: 'Gimle.Asgard.Streams.majorizes_C_mul'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.majorizes_C_mul
/--
info: 'Gimle.Asgard.Streams.ColeHopf.quotient_eq_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.quotient_eq_stream
/--
info: 'Gimle.Asgard.Streams.ColeHopf.constantCoeff_front'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.constantCoeff_front
/--
info: 'Gimle.Asgard.Streams.ColeHopf.circuit_front'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ColeHopf.circuit_front
/--
info: 'Gimle.Asgard.Examples.BurgersFront.constantCoeff_front_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersFront.constantCoeff_front_eq

end Gimle.Asgard.Tests.ColeHopf
