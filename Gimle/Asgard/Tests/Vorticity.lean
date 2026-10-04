import Gimle.Asgard.Examples.EulerThreeMode
import Gimle.Asgard.Streams.Burgers

/-! Coverage for the formal vorticity stream (task 065).

Pinned here: the causal lemma is now stated for an abstract axis and the
stream version is literally its instance; the trigonometric `t`-axis is
another; the vorticity right-hand side is causal in both bases and the stream
is the unique formal solution from any start; the transport is mean zero,
even on even inputs, not symmetric, and agrees with the restated cosine
coupling of the Galerkin family at kept and discarded modes alike; the
three-mode coefficients are the hand values and a wrong
value is refuted by the same kernel computation; and a transitive
standard-axiom audit of every root theorem and example claim. -/

namespace Gimle.Asgard.Tests.Vorticity

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.NS
open Gimle.Asgard.Examples.EulerThreeMode

/-! ### The generic lemma and its instances -/

/-- The stream solution is the abstract one on the stream axis, definitionally. -/
example {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d) (b : Stream d) :
    Causal.solution basis axis F b = (Causal.streamAxis basis axis).solution F b := rfl

/-- Causality along a stream axis is causality for the abstract axis. -/
example (basis : Basis) (ν : ℚ) :
    (Causal.streamAxis basis 0).IsCausal (Burgers.rhs basis ν) := Burgers.rhs_causal basis ν

/-- The Burgers stream is the abstract solution on the `t`-axis of `Stream 2`. -/
example (basis : Basis) (ν : ℚ) (b : Stream 2) :
    Burgers.stream basis ν b = (Causal.streamAxis basis 0).solution (Burgers.rhs basis ν) b := rfl

/-- The vorticity stream is the abstract solution on the trigonometric `t`-axis. -/
example (basis : Basis) (ν : ℚ) (b : TrigStream) :
    stream basis ν b = (TrigStream.trigAxis basis).solution (rhs basis ν) b := rfl

/-- `D_t` is not causal on trigonometric streams either. -/
example : ¬ (TrigStream.trigAxis .ogf).IsCausal (TrigStream.derivative .ogf) := by
  intro causal
  have agree : TrigStream.AgreeBelow 0 (fun _ => 0) (fun n => if n = 1 then cosine (1, 0) else 0) := by
    intro n hn
    rw [Nat.le_zero.mp hn]
    simp
  have := causal 0 _ _ agree 0 le_rfl
  simp [TrigStream.derivative, cosine] at this
  have := congrArg (fun P : TrigPoly => P (1, 0)) this
  simp at this

/-! ### The equation -/

example (basis : Basis) (ν : ℚ) : (TrigStream.trigAxis basis).IsCausal (rhs basis ν) :=
  rhs_causal basis ν

example (basis : Basis) (ν : ℚ) (b : TrigStream) :
    TrigStream.derivative basis (stream basis ν b) = rhs basis ν (stream basis ν b) ∧
      stream basis ν b 0 = b 0 :=
  ⟨stream_pde basis ν b, stream_slice basis ν b⟩

example (basis : Basis) (ν : ℚ) (a b : TrigStream)
    (ha : TrigStream.derivative basis a = rhs basis ν a)
    (hb : TrigStream.derivative basis b = rhs basis ν b) (slice : a 0 = b 0) : a = b :=
  formal_unique basis ν a b ha hb slice

/-- Positive `t`-degrees of the boundary do not reach the stream. -/
example (basis : Basis) (ν : ℚ) (P Q : TrigPoly) :
    stream basis ν (fun n => if n = 0 then P else Q) = stream basis ν (fun _ => P) :=
  stream_congr_slice basis ν _ _ (by simp)

/-- The OGF right-hand side at `t¹` is the two cross terms with the start. -/
example (ν : ℚ) (ω : TrigStream) :
    rhs .ogf ν ω 1 = ν • laplacian (ω 1) - (transport (ω 0) (ω 1) + transport (ω 1) (ω 0)) := by
  simp [rhs, TrigStream.convolve_ogf_apply, Finset.sum_range_succ]

/-! ### The transport -/

example (P Q : TrigPoly) : MeanZero (transport P Q) := meanZero_transport P Q

example {P Q : TrigPoly} (hP : IsEven P) (hQ : IsEven Q) : IsEven (transport P Q) :=
  isEven_transport hP hQ

/-- On single modes the coupling is `(p × q)/|p|²`: `cos x` transporting
`cos y` lands on `(1, 1)` with `1 · (1/2)(1/2)`. -/
example : transport (cosine (1, 0)) (cosine (0, 1)) (1, 1) = 1 / 4 := by
  have h : cosine (1, 0) = Table.toTrig [((1, 0), 1 / 2), ((-1, 0), 1 / 2)] := by
    simp [cosine, Table.toTrig]
  have h' : cosine (0, 1) = Table.toTrig [((0, 1), 1 / 2), ((0, -1), 1 / 2)] := by
    simp [cosine, Table.toTrig]
  rw [h, h', ← Table.toTrig_transport, Table.toTrig_apply]
  decide +kernel

/-- **The transport is not symmetric**: the other order lands with `−1/4`. -/
example : transport (cosine (0, 1)) (cosine (1, 0)) (1, 1) = -1 / 4 := by
  have h : cosine (1, 0) = Table.toTrig [((1, 0), 1 / 2), ((-1, 0), 1 / 2)] := by
    simp [cosine, Table.toTrig]
  have h' : cosine (0, 1) = Table.toTrig [((0, 1), 1 / 2), ((0, -1), 1 / 2)] := by
    simp [cosine, Table.toTrig]
  rw [h, h', ← Table.toTrig_transport, Table.toTrig_apply]
  decide +kernel

/-- The restated cosine coupling at the `T3` triad: `cos x` and `cos(x + y)`
feed `cos(2x + y)` with `c((1,0), (1,1), (2,1)) = −1/2`. -/
example : cosineCoupling (1, 0) (1, 1) (2, 1) = -1 / 2 := by
  simp [cosineCoupling, S, cross, lam]
  norm_num

/-- The two bases checked against each other on the `T3` start: the transport
of `ω₀` by itself is `1/8` at the kept mode `(2, 1)` and `−1/8` at the
discarded mode `(0, 1)`, and `rhs = −transport` gives `euler_t_2xy`,
`euler_t_y`; the family's `−1/4 · a₁₀ a₁₁` is `2 · (−1/8)` on `a = 2P`. -/
example : transport ω₀ ω₀ (2, 1) = 1 / 8 := by
  rw [ω₀_eq_table, ← Table.toTrig_transport, Table.toTrig_apply]
  decide +kernel
example : transport ω₀ ω₀ (0, 1) = -1 / 8 := by
  rw [ω₀_eq_table, ← Table.toTrig_transport, Table.toTrig_apply]
  decide +kernel

/-- The agreement lemma applies to the `T3` start at a discarded mode. -/
example : transport ω₀ ω₀ (0, 1) =
    -2 * ∑ p ∈ {(1, 0), (1, 1), (2, 1)}, ∑ q ∈ {(1, 0), (1, 1), (2, 1)},
      cosineCoupling p q (0, 1) * ω₀ p * ω₀ q := by
  refine transport_eq_cosine _ (by decide) (by decide) ω₀_isEven ω₀_isEven ?_ ?_ (by decide)
  all_goals
    intro p hp
    rw [ω₀_eq_table, Table.toTrig_apply] at hp
    by_contra h
    push Not at h
    apply hp
    -- a mode outside `±H` has zero coefficient in the start
    simp only [startTable, Table.coeff, Finset.mem_insert, Finset.mem_singleton, not_or] at h ⊢
    obtain ⟨p1, p2⟩ := p
    simp only [Prod.neg_mk, Prod.ext_iff] at h ⊢
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num

/-- `Δ⁻¹` inverts `Δ` on a mean-zero polynomial. -/
example : laplacian (laplacianInv ω₀) = ω₀ := laplacian_laplacianInv ω₀_meanZero

/-- `Δ` on `cos(2x + y)` is `−5 cos(2x + y)`. -/
example : laplacian (cosine (2, 1)) = (-5 : ℚ) • cosine (2, 1) := by
  rw [cosine, laplacian_add, laplacian_single, laplacian_single, smul_add, Finsupp.smul_single,
    Finsupp.smul_single, lam_neg]
  norm_num [lam]

/-! ### Coefficients from three modes -/

example : stream .ogf 0 start 1 (1, 0) = -3 / 40 := euler_t_x
example : stream .ogf 0 start 1 (0, 1) = 1 / 8 := euler_t_y
example : stream .ogf 0 start 2 (2, 2) = 11 / 130 := euler_t2_2x2y
example : stream .ogf 0 start 3 (1, 0) = 27 / 32000 := euler_t3_x
example : stream .ogf ν start 1 (2, 1) = -3 / 8 := viscous_t_2xy
example : stream .ogf ν start 2 (1, 1) = -7 / 65 := viscous_t2_xy

/-- The start is the `t⁰` coefficient. -/
example : stream .ogf 0 start 0 = ω₀ := stream_slice .ogf 0 start

/-- The `t⁰` coefficient of `e^{i x}` is `1/2`, read through the table. -/
example : stream .ogf 0 start 0 (1, 0) = 1 / 2 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- Mean zero at every degree, by the invariant and by the computation. -/
example (n : ℕ) : stream .ogf 0 start n 0 = 0 := coeff_meanZero 0 n
example : stream .ogf 0 start 2 (0, 0) = 0 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- Even at every degree: the computed coefficients at `±(3, 2)` agree. -/
example : stream .ogf 0 start 1 (-(3, 2)) = stream .ogf 0 start 1 (3, 2) := coeff_isEven 0 1 (3, 2)

/-- A wrong coefficient is refuted by the same computation. -/
example : stream .ogf 0 start 1 (1, 0) ≠ -1 / 8 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- Viscosity changes the `(2, 1)` coefficient at `t¹` and not the `(0, 1)` one. -/
example : stream .ogf ν start 1 (2, 1) ≠ stream .ogf 0 start 1 (2, 1) := by
  rw [viscous_t_2xy, euler_t_2xy]; norm_num
example : stream .ogf ν start 1 (0, 1) = stream .ogf 0 start 1 (0, 1) := by
  rw [viscous_t_y, euler_t_y]

/-! ### Axioms -/

/--
info: 'Gimle.Asgard.Streams.Causal.Axis.solution_reconstructs' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.Axis.solution_reconstructs
/--
info: 'Gimle.Asgard.Streams.Causal.Axis.formal_unique' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.Axis.formal_unique
/--
info: 'Gimle.Asgard.Streams.Causal.Axis.eq_solution' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.Axis.eq_solution
/--
info: 'Gimle.Asgard.Streams.Causal.solution_reconstructs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.solution_reconstructs
/--
info: 'Gimle.Asgard.Streams.Causal.formal_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.formal_unique
/--
info: 'Gimle.Asgard.Streams.Torus.laplacian_laplacianInv'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.laplacian_laplacianInv
/--
info: 'Gimle.Asgard.Streams.Torus.transport_single_single'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.transport_single_single
/--
info: 'Gimle.Asgard.Streams.Torus.meanZero_transport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.meanZero_transport
/--
info: 'Gimle.Asgard.Streams.Torus.isEven_transport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.isEven_transport
/--
info: 'Gimle.Asgard.Streams.Torus.transport_eq_cosine'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.transport_eq_cosine
/--
info: 'Gimle.Asgard.Streams.TrigStream.derivative_integral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.derivative_integral
/--
info: 'Gimle.Asgard.Streams.TrigStream.integral_derivative'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.integral_derivative
/--
info: 'Gimle.Asgard.Streams.TrigStream.convolve_causal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.TrigStream.convolve_causal
/--
info: 'Gimle.Asgard.Streams.NS.rhs_causal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.rhs_causal
/--
info: 'Gimle.Asgard.Streams.NS.stream_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_pde
/--
info: 'Gimle.Asgard.Streams.NS.stream_reconstructs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_reconstructs
/--
info: 'Gimle.Asgard.Streams.NS.formal_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.formal_unique
/--
info: 'Gimle.Asgard.Streams.NS.eq_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.eq_stream
/--
info: 'Gimle.Asgard.Streams.NS.stream_congr_slice'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_congr_slice
/--
info: 'Gimle.Asgard.Streams.NS.stream_meanZero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_meanZero
/--
info: 'Gimle.Asgard.Streams.NS.stream_isEven'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_isEven
/--
info: 'Gimle.Asgard.Streams.Torus.Table.toTrig_transport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.Table.toTrig_transport
/--
info: 'Gimle.Asgard.Streams.NS.stream_eq_table'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_eq_table
/--
info: 'Gimle.Asgard.Streams.NS.stream_coeff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_coeff
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t_x'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t_x
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t_y'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t_y
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t2_2x2y'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t2_2x2y
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t3_x'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t3_x
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.viscous_t_2xy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.viscous_t_2xy
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.viscous_t2_xy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.viscous_t2_xy
/--
info: 'Gimle.Asgard.Streams.Causal.Axis.solution_pde' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.Axis.solution_pde
/--
info: 'Gimle.Asgard.Streams.Causal.Axis.solution_congr_slice' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.Axis.solution_congr_slice
/--
info: 'Gimle.Asgard.Streams.Causal.Axis.glue_unique' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.Axis.glue_unique
/--
info: 'Gimle.Asgard.Streams.Torus.laplacianInv_laplacian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.laplacianInv_laplacian
/--
info: 'Gimle.Asgard.Streams.Torus.transport_eq_jacobian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Torus.transport_eq_jacobian
/--
info: 'Gimle.Asgard.Streams.NS.rhs_eq_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.rhs_eq_family
/--
info: 'Gimle.Asgard.Streams.NS.stream_slice'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.stream_slice
/--
info: 'Gimle.Asgard.Streams.NS.reconstructs_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.reconstructs_iff
/--
info: 'Gimle.Asgard.Streams.NS.toTrig_picard'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.NS.toTrig_picard
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t_xy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t_xy
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t_2xy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t_2xy
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t_3x2y'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t_3x2y
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t_2x2y'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t_2x2y
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.euler_t2_xy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.euler_t2_xy
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.viscous_t_y'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.viscous_t_y
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.viscous_t2_2x2y'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.viscous_t2_2x2y
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.coeff_meanZero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.coeff_meanZero
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.coeff_isEven'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.coeff_isEven
/--
info: 'Gimle.Asgard.Examples.EulerThreeMode.unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.EulerThreeMode.unique

end Gimle.Asgard.Tests.Vorticity
