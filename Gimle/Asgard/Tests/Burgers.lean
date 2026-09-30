import Gimle.Asgard.Examples.BurgersSquare
import Gimle.Asgard.Examples.PolynomialHeat

/-! Coverage for the formal Burgers stream (task 060).

Pinned here: the right-hand side is causal along `t` while `D_t` itself is
not, so a causal equation has exactly one formal solution from any boundary
and only the boundary's `t = 0` slice enters; the Picard construction
reproduces the closed-form heat stream; the circuit reconstructs only the
constructed stream and refuses the heat stream; the low coefficients from
`x²` at `ν = 1/10` are the hand values in both bases, including one where
only the viscous term contributes (zero without viscosity) and one where only
the nonlinearity does; and a transitive standard-axiom audit of the root
theorems and every example claim. -/

namespace Gimle.Asgard.Tests.Burgers

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Burgers
open Gimle.Asgard.Examples.BurgersSquare

local notation "X" => (MvPolynomial.X 1 : Poly 2)

local notation "T" => (MvPolynomial.X 0 : Poly 2)

/-! ### Causality and uniqueness -/

example (basis : Basis) (ν : ℚ) : Causal.IsCausal (0 : Fin 2) (rhs basis ν) := rhs_causal basis ν

/-- `D_t` reads a higher `t`-degree than it writes: it is not causal along `t`,
which is why `derivative_causal` asks for another axis. -/
example : ¬ Causal.IsCausal (0 : Fin 2) (derivative .ogf 0) := by
  intro causal
  have agree : Causal.AgreeBelow (0 : Fin 2) 0 (0 : Stream 2) (MvPowerSeries.X 0) := by
    intro m hm
    have zero : m 0 = 0 := Nat.le_zero.mp hm
    change (0 : ℚ) = MvPowerSeries.coeff m (MvPowerSeries.X 0)
    rw [MvPowerSeries.coeff_X, if_neg]
    intro same
    have := congrArg (fun q : Index 2 => q 0) same
    simp [zero] at this
  have := causal 0 _ _ agree 0 le_rfl
  simp [derivative] at this
  change (0 : ℚ) = MvPowerSeries.coeff (Finsupp.single 0 1) (MvPowerSeries.X 0) at this
  simp [MvPowerSeries.coeff_X] at this

/-- The Picard construction reproduces the closed-form heat stream: the
general lemma agrees with the special case built independently. -/
example (basis : Basis) (p : Heat.Profile) :
    Heat.stream basis p = Causal.solution basis 0
      (fun u => derivative basis 1 (derivative basis 1 u)) (Heat.boundary basis p) :=
  Causal.eq_solution
    (fun _ _ _ h => Causal.derivative_causal basis (by decide)
      (Causal.derivative_causal basis (by decide) h)) _
    (Heat.stream_pde basis p) (Heat.stream_boundary basis p)

/-- Positive `t`-degrees of the boundary argument do not reach the stream. -/
example (basis : Basis) (ν : ℚ) (g : Poly 2) :
    stream basis ν (ofPoly basis (X ^ 2 + T * g)) = stream basis ν (ofPoly basis (X ^ 2)) := by
  apply stream_congr_slice
  intro m zero
  cases basis <;> simp only [ofPoly_ogf_apply, ofPoly_egf_apply, MvPolynomial.coeff_add,
    coeff_T_mul_slice _ _ zero, add_zero]

/-- Two solutions with the same profile agree, in either basis and for any `ν`. -/
example (basis : Basis) (ν : ℚ) (a b : Stream 2)
    (ha : derivative basis 0 a = rhs basis ν a) (hb : derivative basis 0 b = rhs basis ν b)
    (slice : ∀ m : Index 2, m 0 = 0 → a m = b m) : a = b :=
  formal_unique basis ν a b ha hb slice

/-- The constructed stream solves the equation and carries the slice. -/
example (basis : Basis) (ν : ℚ) (b : Stream 2) :
    derivative basis 0 (stream basis ν b) = rhs basis ν (stream basis ν b) ∧
      ∀ m : Index 2, m 0 = 0 → stream basis ν b m = b m :=
  ⟨stream_pde basis ν b, stream_slice basis ν b⟩

/-- The circuit accepts the constructed stream … -/
example (basis : Basis) (ν : ℚ) (b unused : Stream 2) :
    (circuit basis ν).Rel ![stream basis ν b, b, unused]
      ![rhs basis ν (stream basis ν b), stream basis ν b] :=
  circuit_solution basis ν b unused

/-- … and nothing else. -/
example (basis : Basis) (ν : ℚ) (b a unused v : Stream 2)
    (rel : (circuit basis ν).Rel ![a, b, unused] ![v, a]) : a = stream basis ν b :=
  candidate_stream basis ν b a unused v rel

/-! ### Coefficients from `x²` -/

example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1) = 1 / 5 := coeff_t

example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1 + Finsupp.single 1 3) = -2 :=
  coeff_t_x3

example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 2 + Finsupp.single 1 1) = -4 / 5 :=
  coeff_t2_x

example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 2 + Finsupp.single 1 4) = 5 :=
  coeff_t2_x4

example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 3 + Finsupp.single 1 2) = 16 / 5 :=
  coeff_t3_x2

/-- Without viscosity the `t`-coefficient vanishes: `1/5` is the viscous term's. -/
example : stream .ogf 0 (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1) = 0 := coeff_t_inviscid

/-- The EGF raw coefficient carries the factorials: `1!·3!·(−2) = −12`. -/
example : stream .egf ν (ofPoly .egf (X ^ 2)) (Finsupp.single 0 1 + Finsupp.single 1 3) = -12 := by
  have idx : (Finsupp.single 0 1 + Finsupp.single 1 3 : Index 2) 0 = 1 := by simp
  rw [stream_ofPoly_apply, idx, picard_one, ofPoly_egf_apply]
  simp [factorial, Fin.prod_univ_two, MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X_pow,
    MvPolynomial.coeff_C, Finsupp.ext_iff, Fin.forall_fin_two, Finsupp.single_apply]
  norm_num

/-- The slice is the profile: the coefficient of `x²` at `t⁰` is `1`. -/
example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 1 2) = 1 := by
  rw [stream_slice _ _ _ _ (by simp), ofPoly_ogf_apply, MvPolynomial.coeff_X_pow]
  simp

/-- A wrong coefficient is refuted by the same computation. -/
example : stream .ogf ν (ofPoly .ogf (X ^ 2)) (Finsupp.single 0 1) ≠ 0 := by
  rw [coeff_t]; norm_num

/-! ### Hostile: the heat stream from `x²` is not the Burgers stream -/

/-- The circuit refuses the heat stream as a Burgers solution from `x²`. -/
example (unused v : Stream 2) :
    ¬ (circuit .ogf ν).Rel ![Heat.stream .ogf (Polynomial.X ^ 2), ofPoly .ogf (X ^ 2), unused]
      ![v, Heat.stream .ogf (Polynomial.X ^ 2)] := by
  intro rel
  have same := candidate_stream .ogf ν _ _ unused v rel
  have := congrFun same (Finsupp.single 0 1)
  rw [coeff_t, Heat.stream, Gimle.Asgard.Examples.PolynomialHeat.square, ofPoly_ogf_apply] at this
  simp [MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X, Finsupp.ext_iff, Fin.forall_fin_two,
    Finsupp.single_apply] at this
  norm_num at this

/-- `x² + 2t` solves heat, not Burgers: its `t`-coefficient is `2`, not `1/5`. -/
example : Heat.stream .ogf (_root_.Polynomial.X ^ 2) ≠ stream .ogf ν (ofPoly .ogf (X ^ 2)) := by
  intro same
  have := congrFun same (Finsupp.single 0 1)
  rw [coeff_t, Heat.stream, Gimle.Asgard.Examples.PolynomialHeat.square, ofPoly_ogf_apply] at this
  simp [MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X, Finsupp.ext_iff, Fin.forall_fin_two,
    Finsupp.single_apply] at this
  norm_num at this

/-! ### Axioms -/

/--
info: 'Gimle.Asgard.Streams.Causal.solution_reconstructs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.solution_reconstructs
/--
info: 'Gimle.Asgard.Streams.Causal.solution_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.solution_pde
/--
info: 'Gimle.Asgard.Streams.Causal.formal_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.formal_unique
/--
info: 'Gimle.Asgard.Streams.Causal.eq_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.eq_solution
/--
info: 'Gimle.Asgard.Streams.Causal.solution_congr_slice'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.solution_congr_slice
/--
info: 'Gimle.Asgard.Streams.Causal.reconstructs_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Causal.reconstructs_iff
/--
info: 'Gimle.Asgard.Streams.Burgers.rhs_causal'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.rhs_causal
/--
info: 'Gimle.Asgard.Streams.Burgers.stream_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.stream_pde
/--
info: 'Gimle.Asgard.Streams.Burgers.stream_reconstructs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.stream_reconstructs
/--
info: 'Gimle.Asgard.Streams.Burgers.formal_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.formal_unique
/--
info: 'Gimle.Asgard.Streams.Burgers.eq_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.eq_stream
/--
info: 'Gimle.Asgard.Streams.Burgers.stream_congr_slice'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.stream_congr_slice
/--
info: 'Gimle.Asgard.Streams.Burgers.circuit_rel_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.circuit_rel_iff
/--
info: 'Gimle.Asgard.Streams.Burgers.circuit_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.circuit_solution
/--
info: 'Gimle.Asgard.Streams.Burgers.candidate_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.candidate_stream
/--
info: 'Gimle.Asgard.Streams.Burgers.rhs_ofPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.rhs_ofPoly
/--
info: 'Gimle.Asgard.Streams.Burgers.approx_ofPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.approx_ofPoly
/--
info: 'Gimle.Asgard.Streams.Burgers.stream_ogf_coeff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.stream_ogf_coeff
/--
info: 'Gimle.Asgard.Streams.Burgers.integralPoly_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Burgers.integralPoly_eq
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.picard_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.picard_one
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.picard_two'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.picard_two
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.picard_three'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.picard_three
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t_x3'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t_x3
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t2_x'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t2_x
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t2_x4'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t2_x4
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t3_x2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t3_x2
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t3_x5'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t3_x5
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.coeff_t_inviscid'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.coeff_t_inviscid
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.picard_affine_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.picard_affine_one
/--
info: 'Gimle.Asgard.Examples.BurgersSquare.unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.BurgersSquare.unique

end Gimle.Asgard.Tests.Burgers
