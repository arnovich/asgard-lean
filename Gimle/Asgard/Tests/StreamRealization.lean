import Gimle.Asgard.Examples.PolynomialHeat

/-! Coverage for finite polynomial streams, their real fields and polynomial
heat evolution (task 024).

Pinned here: OGF/EGF coefficients of an embedded polynomial on both axes; a
mixed circuit whose realized output is read off its polynomial semantics; the
substitution side condition on realized inputs; the analytic meaning of a
selected-axis derivative and of an integral carrying a nonconstant boundary;
and a transitive standard-axiom audit of every public theorem. -/

namespace Gimle.Asgard.Tests.StreamRealization

open Gimle.Asgard.Streams

local notation "T" => (MvPolynomial.X 0 : Poly 2)
local notation "X" => (MvPolynomial.X 1 : Poly 2)

/-! ### Embedding and factorial conversion -/

/-- `t·x²`: OGF coefficient 1 at `(1,2)`, EGF coefficient `1!·2! = 2`. -/
example : ofPoly .ogf (T * X ^ 2) (Finsupp.single 0 1 + Finsupp.single 1 2) = 1 ∧
    ofPoly .egf (T * X ^ 2) (Finsupp.single 0 1 + Finsupp.single 1 2) = 2 := by
  have mono : T * X ^ 2 = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1 := by
    rw [MvPolynomial.X_pow_eq_monomial]
    show MvPolynomial.monomial (Finsupp.single 0 1) 1 * _ = _
    rw [MvPolynomial.monomial_mul, one_mul]
  rw [ofPoly_ogf_apply, ofPoly_egf_apply, mono, MvPolynomial.coeff_monomial, if_pos rfl]
  simp [factorial, Fin.prod_univ_two]

/-- The evaluated field is the finite sum of decoded coefficients (EGF too). -/
example (p : Poly 2) (x : Fin 2 → ℝ) : field p x = ∑ n ∈ p.support,
    ((decode .egf (ofPoly .egf p) n : ℚ) : ℝ) * ∏ i, x i ^ n i := field_eq_sum .egf p x

/-! ### Circuits over realized inputs -/

/-- `t · ∫_x u` with boundary `1`, in EGF, read off its polynomial semantics. -/
def mixed : Expr .egf 2 1 :=
  .binary .product (.axisVariable 0) (.binary (.integral 1) (.input 0) (.constant 1))

example (p : Poly 2) : mixed.compile.Rel ![ofPoly .egf p]
    ![ofPoly .egf (T * integralPoly 1 p (MvPolynomial.C 1))] := by
  have h := (Circuit.rel_ofPoly (basis := .egf) mixed.compile ![p]
    ![ofPoly .egf (T * integralPoly 1 p (MvPolynomial.C 1))]).mpr
  have input : (fun j => ofPoly .egf ((![p] : Fin 1 → Poly 2) j)) = ![ofPoly .egf p] := by
    funext j; fin_cases j; rfl
  rw [input] at h
  apply h
  refine ⟨by simp [mixed, Expr.compile, Circuit.PolyDefined, Circuit.pair, Binary.PolyDomain],
    ?_⟩
  funext j; fin_cases j
  rfl

/-- Substitution on realized inputs keeps its strict zero-constant domain. -/
example : ¬ (Binary.seriesCompose (0 : Fin 2)).Domain .ogf (ofPoly .ogf T)
    (ofPoly .ogf (1 + X)) := by
  rw [Binary.domain_ofPoly]
  simp [Binary.PolyDomain]

/-! ### Analytic meaning -/

/-- `∂_t (t²x) = 2tx`, as the real derivative of the evaluated field. -/
example (t x : ℝ) : deriv (fun s => field (T ^ 2 * X) (Function.update ![t, x] 0 s)) t =
    2 * t * x := by
  have h := deriv_field (T ^ 2 * X) 0 ![t, x]
  simp only [Matrix.cons_val_zero] at h
  rw [h]
  simp [MvPolynomial.pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring

/-- Integrating `0` along `t` keeps the nonconstant boundary `x`, evaluated at `t = 0`. -/
example (t x : ℝ) : field (integralPoly 0 0 X) ![t, x] = x := by
  rw [field_integralPoly]
  simp

/-! ### Transitive axiom audit -/

/--
info: 'Gimle.Asgard.Streams.ofPoly_injective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.ofPoly_injective
/--
info: 'Gimle.Asgard.Streams.finiteSupport_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.finiteSupport_iff
/--
info: 'Gimle.Asgard.Streams.field_eq_sum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.field_eq_sum
/--
info: 'Gimle.Asgard.Streams.field_injective'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.field_injective
/--
info: 'Gimle.Asgard.Streams.derivative_ofPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.derivative_ofPoly
/--
info: 'Gimle.Asgard.Streams.integral_ofPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.integral_ofPoly
/--
info: 'Gimle.Asgard.Streams.seriesCompose_ofPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.seriesCompose_ofPoly
/--
info: 'Gimle.Asgard.Streams.hasDerivAt_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.hasDerivAt_field
/--
info: 'Gimle.Asgard.Streams.field_integralPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.field_integralPoly
/--
info: 'Gimle.Asgard.Streams.field_composePoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.field_composePoly
/--
info: 'Gimle.Asgard.Streams.slice_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.slice_iff
/--
info: 'Gimle.Asgard.Streams.Circuit.rel_ofPoly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Circuit.rel_ofPoly
/--
info: 'Gimle.Asgard.Streams.Heat.solution_eq_sum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.solution_eq_sum
/--
info: 'Gimle.Asgard.Streams.Heat.solution_of_natDegree_le_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.solution_of_natDegree_le_one
/--
info: 'Gimle.Asgard.Streams.Heat.pde_poly'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.pde_poly
/--
info: 'Gimle.Asgard.Streams.Heat.coeff_solution_slice'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.coeff_solution_slice
/--
info: 'Gimle.Asgard.Streams.Heat.field_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.field_solution
/--
info: 'Gimle.Asgard.Streams.Heat.solution_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.solution_pde
/--
info: 'Gimle.Asgard.Streams.Heat.solution_initial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.solution_initial
/--
info: 'Gimle.Asgard.Streams.Heat.circuit_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.circuit_solution
/--
info: 'Gimle.Asgard.Streams.Heat.reconstructs_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.reconstructs_iff
/--
info: 'Gimle.Asgard.Streams.Heat.formal_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.formal_unique
/--
info: 'Gimle.Asgard.Streams.Heat.poly_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.poly_unique
/--
info: 'Gimle.Asgard.Streams.Heat.field_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.field_unique
/--
info: 'Gimle.Asgard.Streams.Heat.candidate_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.Heat.candidate_stream
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.square'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.square
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.quartic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.quartic
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.affine'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.affine
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.zero_profile'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.zero_profile
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.square_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.square_field
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.square_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.square_unique
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.original_heat'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.original_heat
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.original_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.original_solution
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.egf_coefficients'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.egf_coefficients
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.egf_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.egf_solution
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.transported'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.transported
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.changed_boundary'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.changed_boundary
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.changed_coefficient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.changed_coefficient
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.same_prefix'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.same_prefix
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.tail_infinite'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.tail_infinite
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.tailed_not_realized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.tailed_not_realized
/--
info: 'Gimle.Asgard.Examples.PolynomialHeat.tailed_not_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.PolynomialHeat.tailed_not_solution

end Gimle.Asgard.Tests.StreamRealization
