import Gimle.Asgard.Streams.Causal
import Gimle.Asgard.Streams.Heat

/-! # The formal Burgers stream

`D_t u = −u·D_x u + ν·D_x² u` on axes `[t, x]`, for a rational viscosity `ν`.
The right-hand side is causal along `t` (a Cauchy product and spatial
derivatives), so `Causal` gives one formal solution for every boundary
stream, and the derivative/integration circuit built from the same
right-hand side reconstructs exactly that solution.

Nothing here is about convergence. For a polynomial profile of degree at
least two the series is expected to diverge when `ν ≠ 0` (a classical
Cole–Hopf argument, checked numerically, proved nowhere in this library; the
convergent Cole–Hopf quotient is `Streams.ColeHopf`); the
coefficients are exact and unique regardless, and that is all this module
claims. `rhs` is the right-hand side as a function on streams and `rhsExpr`
the same expression for the compiler. -/
namespace Gimle.Asgard.Streams.Burgers

open Causal

/-- `−u·D_x u + ν·D_x² u`, with the scalars as constant streams so that the
same expression compiles to a circuit. -/
noncomputable def rhs (basis : Basis) (ν : ℚ) (u : Stream 2) : Stream 2 :=
  product basis (constant basis ν) (derivative basis 1 (derivative basis 1 u)) +
    product basis (constant basis (-1)) (product basis u (derivative basis 1 u))

/-- The right-hand side reads no higher `t`-degree than it writes. -/
theorem rhs_causal (basis : Basis) (ν : ℚ) : IsCausal (0 : Fin 2) (rhs basis ν) := by
  intro k a b h
  have ne : (1 : Fin 2) ≠ 0 := by decide
  unfold rhs
  exact add_causal
    (product_causal basis (AgreeBelow.refl _ _ _)
      (derivative_causal basis ne (derivative_causal basis ne h)))
    (product_causal basis (AgreeBelow.refl _ _ _)
      (product_causal basis h (derivative_causal basis ne h)))

/-- The formal Burgers stream from a boundary stream: its `t = 0` slice is
the profile, and positive `t`-degrees of the argument do not matter
(`stream_congr_slice`). -/
noncomputable def stream (basis : Basis) (ν : ℚ) (boundary : Stream 2) : Stream 2 :=
  Causal.solution basis 0 (rhs basis ν) boundary

/-- The stream satisfies the equation on every coefficient. -/
theorem stream_pde (basis : Basis) (ν : ℚ) (boundary : Stream 2) :
    derivative basis 0 (stream basis ν boundary) = rhs basis ν (stream basis ν boundary) :=
  Causal.solution_pde (rhs_causal basis ν)

/-- On `t = 0` the stream is the boundary. -/
theorem stream_slice (basis : Basis) (ν : ℚ) (boundary : Stream 2) (m : Index 2)
    (zero : m 0 = 0) : stream basis ν boundary m = boundary m :=
  Causal.solution_slice m zero

/-- Integrating the stream's own right-hand side from the boundary returns it. -/
theorem stream_reconstructs (basis : Basis) (ν : ℚ) (boundary : Stream 2) :
    integral basis 0 (rhs basis ν (stream basis ν boundary)) boundary = stream basis ν boundary :=
  Causal.solution_reconstructs (rhs_causal basis ν)

/-- **Uniqueness** among all formal streams, for every profile. -/
theorem formal_unique (basis : Basis) (ν : ℚ) (a b : Stream 2)
    (ha : derivative basis 0 a = rhs basis ν a) (hb : derivative basis 0 b = rhs basis ν b)
    (slice : ∀ m : Index 2, m 0 = 0 → a m = b m) : a = b :=
  Causal.formal_unique (rhs_causal basis ν) a b ha hb slice

/-- Every solution with the given profile is the constructed stream. -/
theorem eq_stream (basis : Basis) (ν : ℚ) (boundary a : Stream 2)
    (ha : derivative basis 0 a = rhs basis ν a)
    (slice : ∀ m : Index 2, m 0 = 0 → a m = boundary m) : a = stream basis ν boundary :=
  Causal.eq_solution (rhs_causal basis ν) a ha slice

/-- Only the boundary's `t = 0` slice enters the stream. -/
theorem stream_congr_slice (basis : Basis) (ν : ℚ) (boundary boundary' : Stream 2)
    (slice : ∀ m : Index 2, m 0 = 0 → boundary m = boundary' m) :
    stream basis ν boundary = stream basis ν boundary' :=
  Causal.solution_congr_slice (rhs_causal basis ν) boundary' slice

/-! ## The circuit -/

/-- The right-hand side as a circuit expression; inputs are `[u, boundary, unused]`. -/
def rhsExpr (basis : Basis) (ν : ℚ) : Expr basis 2 3 :=
  .binary .add
    (.binary .product (.constant ν) (.unary (.derivative 1) (.unary (.derivative 1) (.input 0))))
    (.binary .product (.constant (-1))
      (.binary .product (.input 0) (.unary (.derivative 1) (.input 0))))

/-- Integrate the right-hand side along `t` with the full boundary profile. -/
def rebuilt (basis : Basis) (ν : ℚ) : Expr basis 2 3 :=
  .binary (.integral 0) (rhsExpr basis ν) (.input 1)

/-- The Burgers circuit, returning `[rhs u, I_t(rhs u, boundary)]`. -/
def circuit (basis : Basis) (ν : ℚ) : Streams.Circuit basis 2 3 2 :=
  (rhsExpr basis ν).compile.pair (rebuilt basis ν).compile

/-- The expression computes `rhs` of the first input. -/
theorem rhsExpr_value (basis : Basis) (ν : ℚ) (x : StreamPoint 2 3) :
    (rhsExpr basis ν).value x = rhs basis ν (x 0) := by
  simp [rhsExpr, rhs, Expr.value, Unary.value, Binary.value]

/-- The circuit is total and returns `[rhs u, I_t(rhs u, boundary)]`. -/
theorem circuit_rel_iff (basis : Basis) (ν : ℚ) (a b unused : Stream 2) (y : StreamPoint 2 2) :
    (circuit basis ν).Rel ![a, b, unused] y ↔
      y = ![rhs basis ν a, integral basis 0 (rhs basis ν a) b] := by
  rw [Streams.Circuit.rel_iff]
  have defined : (circuit basis ν).Defined ![a, b, unused] := by
    simp [circuit, Streams.Circuit.pair_defined, Expr.compile_defined, rhsExpr, rebuilt,
      Expr.Defined, Binary.Domain]
  simp only [defined, true_and]
  simp [circuit, Streams.Circuit.pair_value, Expr.compile_value, rebuilt, Expr.value,
    Binary.value, rhsExpr_value]

/-- Reconstruction by integration is exactly the equation plus the slice. -/
theorem reconstructs_iff (basis : Basis) (ν : ℚ) (a b : Stream 2) :
    integral basis 0 (rhs basis ν a) b = a ↔
      derivative basis 0 a = rhs basis ν a ∧ ∀ m : Index 2, m 0 = 0 → a m = b m :=
  Causal.reconstructs_iff basis 0 (rhs basis ν) a b

/-- **Constructed family:** the circuit returns `[rhs u, u]` on
`[u, boundary, unused]` for the constructed stream, any boundary, either basis. -/
theorem circuit_solution (basis : Basis) (ν : ℚ) (boundary unused : Stream 2) :
    (circuit basis ν).Rel ![stream basis ν boundary, boundary, unused]
      ![rhs basis ν (stream basis ν boundary), stream basis ν boundary] := by
  rw [circuit_rel_iff, stream_reconstructs]

/-- **Supplied candidate stream:** any stream the circuit reconstructs from the
boundary is the constructed stream. -/
theorem candidate_stream (basis : Basis) (ν : ℚ) (boundary a unused v : Stream 2)
    (rel : (circuit basis ν).Rel ![a, boundary, unused] ![v, a]) :
    a = stream basis ν boundary := by
  rw [circuit_rel_iff] at rel
  have reconstructed := congrFun rel 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at reconstructed
  obtain ⟨pde, slice⟩ := (reconstructs_iff basis ν a _).mp reconstructed.symm
  exact eq_stream basis ν boundary a pde slice

/-! ## Polynomial profiles: the Picard iterates are polynomials

Products, spatial derivatives and `t`-integrals of polynomials are
polynomials, so from a polynomial boundary every iterate is `ofPoly` of an
explicit polynomial, and the coefficient of the stream at `t`-degree `n` is a
coefficient of the `n`-th iterate. The stream itself is not polynomial. -/

/-- The right-hand side on bivariate polynomials. -/
noncomputable def rhsPoly (ν : ℚ) (q : Poly 2) : Poly 2 :=
  MvPolynomial.C ν * MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 q) -
    q * MvPolynomial.pderiv 1 q

/-- The right-hand side of a polynomial stream is a polynomial stream. -/
theorem rhs_ofPoly (basis : Basis) (ν : ℚ) (q : Poly 2) :
    rhs basis ν (ofPoly basis q) = ofPoly basis (rhsPoly ν q) := by
  rw [rhs, rhsPoly, constant_eq_ofPoly, constant_eq_ofPoly, derivative_ofPoly, derivative_ofPoly,
    product_ofPoly, product_ofPoly, product_ofPoly, ofPoly_add, sub_eq_add_neg]
  congr 2
  rw [MvPolynomial.C_neg, MvPolynomial.C_1, neg_one_mul]

/-- The Picard iterates of a polynomial boundary, as polynomials. -/
noncomputable def picard (ν : ℚ) (b : Poly 2) : ℕ → Poly 2
  | 0 => b
  | n + 1 => integralPoly 0 (rhsPoly ν (picard ν b n)) b

/-- Every Picard iterate of a polynomial boundary is a polynomial stream. -/
theorem approx_ofPoly (basis : Basis) (ν : ℚ) (b : Poly 2) (n : ℕ) :
    Causal.approx basis 0 (rhs basis ν) (ofPoly basis b) n = ofPoly basis (picard ν b n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Causal.approx_succ, ih, rhs_ofPoly, integral_ofPoly, picard]

/-- **Coefficients.** At `t`-degree `n` the stream reads the `n`-th iterate. -/
theorem stream_ofPoly_apply (basis : Basis) (ν : ℚ) (b : Poly 2) (m : Index 2) :
    stream basis ν (ofPoly basis b) m = ofPoly basis (picard ν b (m 0)) m := by
  rw [stream, Causal.solution_apply, approx_ofPoly]

/-- The OGF coefficient at `t`-degree `n` is a coefficient of the `n`-th iterate. -/
theorem stream_ogf_coeff (ν : ℚ) (b : Poly 2) (m : Index 2) :
    stream .ogf ν (ofPoly .ogf b) m = MvPolynomial.coeff m (picard ν b (m 0)) := by
  rw [stream_ofPoly_apply, ofPoly_ogf_apply]

/-- A polynomial with the right `t`-derivative and the right zero slice is the
integral: the way to evaluate `integralPoly` by exhibiting its value. -/
theorem integralPoly_eq (p b r : Poly 2) (der : MvPolynomial.pderiv 0 r = p)
    (slice : ∀ n : Index 2, n 0 = 0 → MvPolynomial.coeff n r = MvPolynomial.coeff n b) :
    integralPoly 0 p b = r := by
  apply ofPoly_injective .ogf
  rw [← integral_ofPoly, ← der, ← derivative_ofPoly]
  calc integral .ogf 0 (derivative .ogf 0 (ofPoly .ogf r)) (ofPoly .ogf b) =
      integral .ogf 0 (derivative .ogf 0 (ofPoly .ogf r)) (ofPoly .ogf r) := by
        funext n
        by_cases zero : n 0 = 0
        · rw [integral_boundary _ _ _ _ _ zero, integral_boundary _ _ _ _ _ zero,
            ofPoly_ogf_apply, ofPoly_ogf_apply, slice n zero]
        · simp [integral, zero]
    _ = ofPoly .ogf r := integral_derivative .ogf 0 _

#print axioms stream_reconstructs
#print axioms formal_unique
#print axioms circuit_solution
#print axioms candidate_stream
#print axioms stream_congr_slice
#print axioms stream_ogf_coeff
#print axioms integralPoly_eq
end Gimle.Asgard.Streams.Burgers
