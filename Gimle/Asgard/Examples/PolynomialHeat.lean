import Gimle.Asgard.Streams.Heat
import Gimle.Asgard.Examples.FormalHeat

/-! # Polynomial heat fixtures

Worked instances of `Streams.Heat` on axes `[t, x]`:

* `p = x²` gives `x² + 2t`; `p = x⁴` gives `x⁴ + 12tx² + 12t²`; affine
  profiles are stationary.
* The hand-written `FormalHeat.heat` stream is the constructed OGF stream for
  `x²`, and `FormalHeat.circuit` is literally `Heat.circuit .ogf`, so the
  general theorem is stated about the original circuit.
* Both bases, axis transport, and three invalidations: a changed boundary, a
  changed coefficient, and a same-prefix/different-tail stream that no finite
  window can certify as polynomial. -/
namespace Gimle.Asgard.Examples.PolynomialHeat

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Heat

local notation "T" => (MvPolynomial.X 0 : Poly 2)
local notation "X" => (MvPolynomial.X 1 : Poly 2)

/-! ## Regressions -/

theorem square : solution (_root_.Polynomial.X ^ 2) = X ^ 2 + 2 * T := by
  rw [solution, cutoff, _root_.Polynomial.natDegree_X_pow]
  simp [Finset.sum_range_succ, term, lift]
  ring

theorem quartic : solution (_root_.Polynomial.X ^ 4) =
    X ^ 4 + 12 * T * X ^ 2 + 12 * T ^ 2 := by
  rw [solution, cutoff, _root_.Polynomial.natDegree_X_pow]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, term, lift,
    _root_.Polynomial.iterate_derivative_X_pow_eq_natCast_mul]
  apply field_injective
  intro y
  simp [Nat.descFactorial_succ, Nat.factorial_succ, map_ofNat]
  ring

theorem affine (a b : ℚ) :
    solution (_root_.Polynomial.C a * _root_.Polynomial.X + _root_.Polynomial.C b) =
      MvPolynomial.C a * X + MvPolynomial.C b := by
  rw [solution_of_natDegree_le_one _ (_root_.Polynomial.natDegree_linear_le)]
  simp [lift]

theorem zero_profile : solution 0 = 0 := by
  rw [solution_of_natDegree_le_one _ (by simp)]
  simp [lift]

/-- The evaluated field of the `x²` solution is `x² + 2t`. -/
theorem square_field (t x : ℝ) :
    field (solution (_root_.Polynomial.X ^ 2)) ![t, x] = x ^ 2 + 2 * t := by
  rw [square]
  simp


/-- A polynomial field satisfying the heat equation with profile `x²` is `x² + 2t`. -/
theorem square_unique (q : Poly 2)
    (pde : ∀ t x : ℝ, deriv (fun s => field q ![s, x]) t =
      deriv (fun y => deriv (fun z => field q ![t, z]) y) x)
    (initial : ∀ x : ℝ, field q ![0, x] = x ^ 2) : q = X ^ 2 + 2 * T := by
  rw [← square]
  exact field_unique _ q pde (fun x => by simpa using initial x)

/-! ## The original circuit and fixture -/

private theorem single_eq_iff (i : Fin 2) (k : ℕ) (n : Index 2) :
    Finsupp.single i k = n ↔ n 0 = Finsupp.single i k 0 ∧ n 1 = Finsupp.single i k 1 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩, fun ⟨a, b⟩ => ⟨a.symm, b.symm⟩⟩

private theorem coeff_ofNat_mul (k : ℕ) [k.AtLeastTwo] (n : Index 2) (p : Poly 2) :
    MvPolynomial.coeff n ((ofNat(k) : Poly 2) * p) = ofNat(k) * MvPolynomial.coeff n p := by
  rw [← map_ofNat MvPolynomial.C k, MvPolynomial.coeff_C_mul]

/-- The general heat circuit at OGF is literally the original fixture circuit. -/
theorem original_circuit : FormalHeat.circuit = Heat.circuit .ogf := rfl

theorem original_boundary : FormalHeat.boundary = boundary .ogf (_root_.Polynomial.X ^ 2) := by
  funext n
  rw [boundary, ofPoly_ogf_apply]
  simp only [lift, map_pow, _root_.Polynomial.aeval_X, MvPolynomial.coeff_X_pow, single_eq_iff,
    FormalHeat.boundary]
  simp

/-- The hand-written stream `x² + 2t` is the constructed one: derived from its
own circuit theorem by uniqueness, not by recomputing coefficients. -/
theorem original_heat : FormalHeat.heat = stream .ogf (_root_.Polynomial.X ^ 2) := by
  apply candidate_stream .ogf _ _ 0 FormalHeat.two
  rw [← original_circuit, ← original_boundary]
  exact FormalHeat.circuit_behavior 0

/-- The general theorem, stated about the original circuit. -/
theorem original_solution (unused : Stream 2) :
    FormalHeat.circuit.Rel ![stream .ogf (_root_.Polynomial.X ^ 2),
        boundary .ogf (_root_.Polynomial.X ^ 2), unused]
      ![derivative .ogf 1 (derivative .ogf 1 (stream .ogf (_root_.Polynomial.X ^ 2))),
        stream .ogf (_root_.Polynomial.X ^ 2)] :=
  circuit_solution .ogf _ unused

/-! ## Both bases and axis transport -/

/-- EGF raw coefficients carry the factorials: `x²` at `(0,2)` is `2!·1`, `2t`
at `(1,0)` is `1!·2`. -/
theorem egf_coefficients :
    stream .egf (_root_.Polynomial.X ^ 2) (Finsupp.single 1 2) = 2 ∧
      stream .egf (_root_.Polynomial.X ^ 2) (Finsupp.single 0 1) = 2 ∧
      stream .ogf (_root_.Polynomial.X ^ 2) (Finsupp.single 1 2) = 1 := by
  simp only [stream, ofPoly_egf_apply, ofPoly_ogf_apply, square, factorial, Fin.prod_univ_two]
  simp [MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X, coeff_ofNat_mul, single_eq_iff]

theorem egf_solution (unused : Stream 2) :
    (Heat.circuit .egf).Rel ![stream .egf (_root_.Polynomial.X ^ 4),
        boundary .egf (_root_.Polynomial.X ^ 4), unused]
      ![derivative .egf 1 (derivative .egf 1 (stream .egf (_root_.Polynomial.X ^ 4))),
        stream .egf (_root_.Polynomial.X ^ 4)] :=
  circuit_solution .egf _ unused

/-- The named source resolves to the same right-hand side in both bases. -/
theorem resolves_both (basis : Basis) :
    FormalHeat.context.resolve basis FormalHeat.namedRhs = some (Heat.rhs basis) := by
  cases basis <;> decide

/-- Swapping the axes to `[x, t]` moves the equation to `D_1 u = D_0² u`. -/
theorem transported (basis : Basis) (p : Profile) :
    derivative basis 1 (reindex (Equiv.swap 0 1) (stream basis p)) =
      derivative basis 0 (derivative basis 0 (reindex (Equiv.swap 0 1) (stream basis p))) := by
  have h := congrArg (reindex (Equiv.swap (0 : Fin 2) 1)) (stream_pde basis p)
  rw [reindex_derivative, reindex_derivative, reindex_derivative] at h
  simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using h

/-! ## Invalidations -/

/-- The `x²` stream with the `x⁴` boundary is not reconstructed by the circuit. -/
theorem changed_boundary (basis : Basis) (unused v : Stream 2) :
    ¬ (Heat.circuit basis).Rel ![stream basis (_root_.Polynomial.X ^ 2),
        boundary basis (_root_.Polynomial.X ^ 4), unused]
      ![v, stream basis (_root_.Polynomial.X ^ 2)] := by
  intro rel
  have h := ofPoly_injective basis (candidate_stream basis _ _ _ _ rel)
  rw [square, quartic] at h
  have c := congrArg (fun q => field q ![0, 2]) h
  norm_num at c

/-- Changing the `t` coefficient of `x² + 2t` to 3 breaks the correspondence. -/
theorem changed_coefficient (basis : Basis) (unused v : Stream 2) :
    ¬ (Heat.circuit basis).Rel ![ofPoly basis (X ^ 2 + 3 * T),
        boundary basis (_root_.Polynomial.X ^ 2), unused] ![v, ofPoly basis (X ^ 2 + 3 * T)] := by
  intro rel
  have h := ofPoly_injective basis (candidate_stream basis _ _ _ _ rel)
  rw [square] at h
  have c := congrArg (fun q => field q ![1, 0]) h
  norm_num at c

/-! ## Same prefix, different tail -/

/-- A tail of ones along `t = 0`, from `x`-degree 5 on: infinitely supported. -/
def tail : Stream 2 := fun n => if n 0 = 0 ∧ 5 ≤ n 1 then 1 else 0

/-- `x² + 2t` plus that tail. -/
noncomputable def tailed : Stream 2 := stream .ogf (_root_.Polynomial.X ^ 2) + tail

/-- On the window `degree < (5,5)` the tailed stream is indistinguishable… -/
theorem same_prefix :
    truncate ![5, 5] tailed = truncate ![5, 5] (stream .ogf (_root_.Polynomial.X ^ 2)) := by
  funext n
  simp only [truncate]
  split_ifs with inside
  · have : tail n = 0 := by
      have := inside 1
      simp only [tail]
      rw [if_neg (by simp at this; omega)]
    change stream .ogf _ n + tail n = _
    rw [this, add_zero]
  · rfl

theorem tail_infinite : ¬ FiniteSupport tail := by
  rintro ⟨s, hs⟩
  have mem := hs (Finsupp.single 1 (s.sup (fun n => n 1) + 5)) (by simp [tail])
  have := Finset.le_sup (f := fun n : Index 2 => n 1) mem
  simp only [Finsupp.single_eq_same] at this
  omega

/-- …but no polynomial realizes it: finite support fails for the whole stream,
so neither `finiteSupport_iff` nor any field theorem applies. -/
theorem tailed_not_realized : ¬ ∃ q, Realizes .ogf tailed q := by
  intro realized
  apply tail_infinite
  obtain ⟨s₁, h₁⟩ := (finiteSupport_iff .ogf tailed).mpr realized
  obtain ⟨s₂, h₂⟩ := (finiteSupport_iff .ogf (stream .ogf (_root_.Polynomial.X ^ 2))).mpr ⟨_, rfl⟩
  refine ⟨s₁ ∪ s₂, fun n ne => ?_⟩
  by_contra outside
  simp only [Finset.mem_union, not_or] at outside
  have a : tailed n = 0 := by by_contra h; exact outside.1 (h₁ n h)
  have b : stream .ogf (_root_.Polynomial.X ^ 2) n = 0 := by
    by_contra h; exact outside.2 (h₂ n h)
  apply ne
  have : tailed n = stream .ogf (_root_.Polynomial.X ^ 2) n + tail n := rfl
  rw [a, b, zero_add] at this
  exact this.symm

/-- The heat circuit with the `x²` profile does not reconstruct the tailed stream. -/
theorem tailed_not_solution (unused v : Stream 2) :
    ¬ (Heat.circuit .ogf).Rel ![tailed, boundary .ogf (_root_.Polynomial.X ^ 2), unused]
      ![v, tailed] := by
  intro rel
  have h := candidate_stream .ogf _ _ _ _ rel
  exact tailed_not_realized ⟨_, h⟩

end Gimle.Asgard.Examples.PolynomialHeat
