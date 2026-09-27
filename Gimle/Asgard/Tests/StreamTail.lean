import Gimle.Asgard.Examples.GeometricTail

/-! Coverage for certified analytic truncation (task 025).

Pinned here: a finite prefix never certifies a majorant, and a stream equal to
the geometric one on the whole window `(N, N)` but with a large tail diverges on
the certified box, so it has no certificate; boundary radii `r = R` are rejected
by the contract and the series really diverges there; zero radius and zero axes;
the sup-norm combination of output ports; the EGF/OGF transport; and a
transitive standard-axiom audit of every public theorem. -/

namespace Gimle.Asgard.Tests.StreamTail

open Gimle.Asgard.Streams
open Gimle.Asgard.Examples.GeometricTail

/-! ### Full-stream evidence versus finitely many coefficients -/

/-- Any finite observation of the geometric stream is also an observation of a
stream that violates the unit majorant. -/
example (S : Finset (Index 2)) :
    ∃ a : Stream 2, (∀ α ∈ S, a α = ones α) ∧ ¬ Majorizes .ogf a unit :=
  prefix_cannot_certify .ogf ones S unit

/-- Equal to `ones` on the window `(N, N)`, then `4^m` along `x`-degree 0. -/
def hostile (N : ℕ) : Stream 2 := fun α => if α 1 = 0 ∧ N ≤ α 0 then 4 ^ α 0 else 1

theorem hostile_prefix (N : ℕ) : truncate ![N, N] (hostile N) = truncate ![N, N] ones := by
  funext α
  simp only [truncate]
  split_ifs with inside
  · have : ¬ (α 1 = 0 ∧ N ≤ α 0) := fun h => by
      have := inside 0
      simp only [Matrix.cons_val_zero] at this
      omega
    simp [hostile, ones, this]
  · rfl

/-- Every observable window quantity coincides… -/
theorem hostile_windowField (N : ℕ) (x : Fin 2 → ℝ) :
    windowField .ogf ![N, N] (hostile N) x = windowField .ogf ![N, N] ones x := by
  rw [← analyticField_truncate, ← analyticField_truncate, hostile_prefix]

private theorem single_zero_apply_one (m : ℕ) : (Finsupp.single (0 : Fin 2) m) 1 = 0 := by
  simp

/-- …but at `(1/2, 0)`, inside the geometric certificate's box, the series of the
hostile stream diverges: its terms along `x`-degree 0 are `2^m`. -/
theorem hostile_diverges (N : ℕ) : ¬ Summable (seriesTerm .ogf (hostile N) ![1 / 2, 0]) := by
  intro summable
  have along := (summable.comp_injective (Finsupp.single_injective (0 : Fin 2))).tendsto_atTop_zero
  have big : ∀ m, N ≤ m →
      (seriesTerm .ogf (hostile N) ![1 / 2, 0] ∘ Finsupp.single (0 : Fin 2)) m = 2 ^ m := by
    intro m hm
    simp only [Function.comp_apply, seriesTerm, decode, hostile, single_zero_apply_one,
      Finsupp.single_eq_same, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      pow_zero, mul_one, true_and, if_pos hm]
    push_cast
    rw [← mul_pow]
    norm_num
  have tends : Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    along.congr' (Filter.eventually_atTop.mpr ⟨N, fun m hm => big m hm⟩)
  have := tends.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨m, hm⟩ := (this.and (Filter.eventually_ge_atTop 0)).exists
  have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  linarith [hm.1]

/-- So no certificate of any majorant covers that point: the finite window
agreement and the geometric radius estimate certify nothing about this stream. -/
theorem hostile_uncertifiable (N : ℕ) (c : TailCertificate .ogf (hostile N)) :
    ¬ c.box.Mem ![1 / 2, 0] :=
  fun mem => hostile_diverges N (c.summable_norm mem).of_norm

theorem hostile_not_majorized (N : ℕ) : ¬ Majorizes .ogf (hostile N) unit := by
  intro maj
  apply hostile_uncertifiable N ⟨unit, half, certificate.inside, maj⟩
  intro i
  fin_cases i <;> norm_num [half]

/-- Raw EGF coefficients read as OGF violate the unit majorant (`(2,0)` has
`2! = 2`), even though the decoded series is the certified geometric one. -/
example : ¬ Majorizes .ogf egfOnes unit := by
  intro maj
  have := maj (Finsupp.single 0 2)
  change |egfOnes (Finsupp.single 0 2)| ≤ _ at this
  rw [egfOnes_apply] at this
  simp [unit, factorial, Fin.prod_univ_two] at this

/-! ### Boundary radii are rejected -/

/-- A box on the majorant's boundary cannot enter a certificate. -/
example (b : Box 2) (h : b.radius 0 = 1) : ¬ ∀ i, b.radius i < unit.radius i := by
  intro inside
  have := inside 0
  simp [h, unit] at this

/-- And the rejection is necessary: at `r = R = 1` the geometric series diverges
at the corner `(1, 1)`. -/
example : ¬ Summable (seriesTerm .ogf ones ![1, 1]) := by
  intro summable
  have along := (summable.comp_injective (Finsupp.single_injective (0 : Fin 2))).tendsto_atTop_zero
  have one : (seriesTerm .ogf ones ![1, 1] ∘ Finsupp.single (0 : Fin 2)) = fun _ => 1 := by
    funext m
    simp [seriesTerm, ones, decode]
  rw [one] at along
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds along)

/-! ### Zero radius and zero axes -/

/-- A zero-radius box: positive windows are exact. -/
def point : Box 2 := ⟨fun _ => 0, fun _ => le_rfl⟩

example (N : ℕ) (pos : 0 < N) : tailBound unit point ![N, N] = 0 :=
  tailBound_radius_zero unit point (fun _ => rfl) _ (fun i => by fin_cases i <;> exact pos)

/-- …the only point is the origin, where the field is the constant coefficient… -/
example (x : Fin 2 → ℝ) (hx : point.Mem x) : analyticField .ogf ones x = 1 := by
  rw [Box.mem_of_radius_zero (fun _ => rfl) hx, analyticField_zero]
  simp [ones, decode]

/-- …while the empty window `N = 0` keeps the whole `M` on each axis. -/
example : tailBound unit point ![0, 0] = 2 := by
  decide +kernel

/-- With no axes the stream is a single constant and truncation is exact. -/
def scalar : Stream 0 := fun _ => 5

example (m : Majorant 0) (b : Box 0) (N : Fin 0 → ℕ) : tailBound m b N = 0 :=
  tailBound_axes_zero m b N

example (N : Fin 0 → ℕ) (x : Fin 0 → ℝ) :
    analyticField .ogf scalar x = windowField .ogf N scalar x := by
  have whole : truncate N scalar = scalar := by
    funext α
    exact truncate_inside N scalar α (fun i => i.elim0)
  rw [← analyticField_truncate, whole]

/-! ### Output ports combine in the sup norm -/

/-- Two ports on a shared box, each with its own certified bound: the vector
error in the sup norm is at most the common `8 · 2^(−N)`. -/
example (N : ℕ) (x : Fin 2 → ℝ) (hx : half.Mem x) :
    ‖fun j => analyticField .ogf (![ones, ones] j) x - windowField .ogf ![N, N] (![ones, ones] j) x‖
      ≤ 8 * (1 / 2) ^ N := by
  refine truncationBound_ports (ε := fun _ => 8 * (1 / 2) ^ N) (fun j => ?_) (by positivity)
    (fun _ => by push_cast; exact le_rfl) hx
  fin_cases j <;> exact bound N

/-! ### Transport through the bound -/

/-- The window field lower-bounds the analytic one up to `ε`. -/
example (N : ℕ) : windowField .ogf ![N, N] ones ![1 / 2, 1 / 2] - 8 * (1 / 2) ^ N ≤
    analyticField .ogf ones ![1 / 2, 1 / 2] := by
  have hx : half.Mem ![1 / 2, 1 / 2] := by
    intro i
    fin_cases i <;> norm_num [half]
  have := (bound N).lower hx le_rfl
  push_cast at this
  exact this

/-- The truncated stream is a polynomial stream whose field is the window field. -/
example (N : ℕ) (x : Fin 2 → ℝ) :
    Realizes .egf (truncate ![N, N] egfOnes) (windowPoly .egf ![N, N] egfOnes) ∧
      field (windowPoly .egf ![N, N] egfOnes) x = windowField .ogf ![N, N] ones x := by
  refine ⟨truncate_realizes .egf _ _, ?_⟩
  rw [field_windowPoly, egfOnes, windowField_encode]

/-! ### Transitive axiom audit -/

/--
info: 'Gimle.Asgard.Streams.hasSum_index_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.hasSum_index_prod
/--
info: 'Gimle.Asgard.Streams.summable_norm_seriesTerm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.summable_norm_seriesTerm
/--
info: 'Gimle.Asgard.Streams.hasSum_analyticField'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.hasSum_analyticField
/--
info: 'Gimle.Asgard.Streams.abs_analyticField_sub_windowField_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.abs_analyticField_sub_windowField_le
/--
info: 'Gimle.Asgard.Streams.TailCertificate.truncationBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TailCertificate.truncationBound
/--
info: 'Gimle.Asgard.Streams.TailCertificate.hasSum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TailCertificate.hasSum
/--
info: 'Gimle.Asgard.Streams.truncationBound_ports'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.truncationBound_ports
/--
info: 'Gimle.Asgard.Streams.truncationBound_iff_of_decode'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.truncationBound_iff_of_decode
/--
info: 'Gimle.Asgard.Streams.analyticField_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.analyticField_zero
/--
info: 'Gimle.Asgard.Streams.tailBound_radius_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.tailBound_radius_zero
/--
info: 'Gimle.Asgard.Streams.truncate_realizes'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.truncate_realizes
/--
info: 'Gimle.Asgard.Streams.field_windowPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.field_windowPoly
/--
info: 'Gimle.Asgard.Streams.analyticField_truncate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.analyticField_truncate
/--
info: 'Gimle.Asgard.Streams.prefix_cannot_certify'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.prefix_cannot_certify
/--
info: 'Gimle.Asgard.Examples.GeometricTail.bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.GeometricTail.bound
/--
info: 'Gimle.Asgard.Examples.GeometricTail.error_ten'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.GeometricTail.error_ten
/--
info: 'Gimle.Asgard.Examples.GeometricTail.analyticField_ones'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.GeometricTail.analyticField_ones
/--
info: 'Gimle.Asgard.Examples.GeometricTail.corner_error'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.GeometricTail.corner_error
/--
info: 'Gimle.Asgard.Examples.GeometricTail.egf_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.GeometricTail.egf_bound
/--
info: 'Gimle.Asgard.Tests.StreamTail.hostile_uncertifiable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Tests.StreamTail.hostile_uncertifiable
/--
info: 'Gimle.Asgard.Tests.StreamTail.hostile_not_majorized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Tests.StreamTail.hostile_not_majorized

end Gimle.Asgard.Tests.StreamTail
