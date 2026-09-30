import Gimle.Asgard.Examples.BurgersFront

/-! Coverage for the majorant calculus and the Cole–Hopf front (task 061).

Pinned here: the ordinary derivative is a derivation that commutes across
axes; the inverse's majorant condition is exactly what limits the radii (the
front's `r = (2/3, 1/2)` is tight, and `(1, 1/2)` fails); a profile that does
not fit `ρ` is refused; a box on the halved radii is refused; the certified
error of the front and its majorant bound; the front's value at the origin,
the one boundary coefficient read off the opaque slice; a zero constant term
makes `smallEnough` trivially true, which is why `c0` is a separate
hypothesis; and a transitive standard-axiom audit of the root theorems and
every example claim. -/

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

/-! ### Axioms -/

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
