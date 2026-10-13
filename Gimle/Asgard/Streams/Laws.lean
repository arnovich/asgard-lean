import Gimle.Asgard.Streams.Compiler

namespace Gimle.Asgard.Streams

/-- Increasing one degree multiplies the multi-factorial by that successor. -/
theorem factorial_update {d : Nat} (n : Index d) (axis : Fin d) :
    factorial (n.update axis (n axis + 1)) = (n axis + 1 : ℚ) * factorial n := by
  unfold factorial
  calc
    (∏ i, (↑((n.update axis (n axis + 1)) i).factorial : ℚ)) =
        ∏ i, (if i = axis then (n axis + 1 : ℚ) else 1) * (n i).factorial := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases same : i = axis <;> simp [Finsupp.update_apply, same, Nat.factorial_succ]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- EGF differentiation agrees with ordinary formal differentiation after the
explicit factorial encoding. This checks the interpretation, not only D/I cancellation. -/
theorem derivative_encode {d : Nat} (basis : Basis) (axis : Fin d) (a : Stream d) :
    derivative basis axis (encode basis a) = encode basis (derivative .ogf axis a) := by
  cases basis with
  | ogf => rfl
  | egf =>
      funext n
      dsimp [derivative, encode]
      rw [factorial_update]
      ring


/-- Integration and its entire boundary profile use the same basis conversion. -/
theorem integral_encode {d : Nat} (basis : Basis) (axis : Fin d) (a boundary : Stream d) :
    integral basis axis (encode basis a) (encode basis boundary) =
      encode basis (integral .ogf axis a boundary) := by
  cases basis with
  | ogf => rfl
  | egf =>
      funext n
      by_cases zero : n axis = 0
      · simp [integral, encode, zero]
      · have pos : 0 < n axis := Nat.pos_of_ne_zero zero
        have cast : (↑(n axis - 1) : ℚ) + 1 = ↑(n axis) := by
          exact_mod_cast Nat.sub_add_cancel pos
        have step : factorial n = (n axis : ℚ) * factorial (n.update axis (n axis - 1)) := by
          simpa [Nat.sub_add_cancel pos, cast] using factorial_update (n.update axis (n axis - 1)) axis
        simp [integral, encode, zero, step]
        have nonzero : (n axis : ℚ) ≠ 0 := by exact_mod_cast zero
        field_simp


theorem substitution_valid {d : Nat} (basis : Basis) (axis : Fin d) (inner : Stream d)
    (valid : CanCompose basis inner) :
    MvPowerSeries.HasSubst (substitution axis (decode basis inner)) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  by_cases same : i = axis
  · simpa [substitution, same, CanCompose] using valid
  · simp [substitution, same]

theorem compose_variable {d : Nat} (basis : Basis) (axis : Fin d) (inner : Stream d)
    (valid : CanCompose basis inner) :
    seriesCompose basis axis (axisVariable basis axis) inner = inner := by
  simp [seriesCompose, axisVariable, MvPowerSeries.subst_X (substitution_valid basis axis inner valid),
    substitution]

theorem compose_other_variable {d : Nat} (basis : Basis) (axis other : Fin d)
    (inner : Stream d) (valid : CanCompose basis inner) (different : other ≠ axis) :
    seriesCompose basis axis (axisVariable basis other) inner = axisVariable basis other := by
  simp [seriesCompose, axisVariable, MvPowerSeries.subst_X (substitution_valid basis axis inner valid),
    substitution, different]

theorem compose_identity {d : Nat} (basis : Basis) (axis : Fin d) (outer : Stream d) :
    seriesCompose basis axis outer (axisVariable basis axis) = outer := by
  have identity : substitution axis (MvPowerSeries.X axis) = (MvPowerSeries.X : Fin d → Stream d) := by
    funext i
    by_cases same : i = axis <;> simp [substitution, same]
  simp [seriesCompose, axisVariable, identity, MvPowerSeries.subst_self]

theorem compose_product {d : Nat} (basis : Basis) (axis : Fin d) (a b inner : Stream d)
    (valid : CanCompose basis inner) :
    seriesCompose basis axis (product basis a b) inner =
      product basis (seriesCompose basis axis a inner) (seriesCompose basis axis b inner) := by
  simp [seriesCompose, product, MvPowerSeries.subst_mul (substitution_valid basis axis inner valid)]

/-- The exact EGF coefficient formula scales every coordinate's factorial.
Each antidiagonal pair splits the multi-index componentwise. -/
theorem egf_product_coefficient {d : Nat} (a b : Stream d) (n : Index d) :
    product .egf a b n = factorial n *
      ∑ p ∈ Finset.antidiagonal n, (a p.1 / factorial p.1) * (b p.2 / factorial p.2) := by
  change factorial n * MvPowerSeries.coeff n (decode .egf a * decode .egf b) = _
  rw [MvPowerSeries.coeff_mul]
  rfl

/-- A circuit rewrite must preserve the full partial relation. -/
def Circuit.Equivalent {basis : Basis} {d n m : Nat}
    (a b : Circuit basis d n m) : Prop := ∀ x y, a.Rel x y ↔ b.Rel x y

theorem Expr.rewrite {basis : Basis} {d n : Nat} (a b : Expr basis d n)
    (domains : ∀ x, a.Defined x ↔ b.Defined x)
    (values : ∀ x, a.Defined x → a.value x = b.value x) : Circuit.Equivalent a.compile b.compile := by
  intro x y
  rw [Expr.compile_rel, Expr.compile_rel]
  constructor
  · rintro ⟨ha, hy⟩
    exact ⟨(domains x).mp ha, by rw [← values x ha]; exact hy⟩
  · rintro ⟨hb, hy⟩
    have ha := (domains x).mpr hb
    exact ⟨ha, by rw [values x ha]; exact hy⟩

/-- D(I(a,b))=a only drops b when its expression is defined. For arbitrary
input wires this is unconditional; no invalid substituted child is erased. -/
theorem derivative_integral_circuit (basis : Basis) (d : Nat) (axis : Fin d) :
    Circuit.Equivalent
      (Expr.unary (.derivative axis) (.binary (.integral axis) (.input 0) (.input 1)) :
        Expr basis d 2).compile
      (Expr.input 0).compile := by
  apply Expr.rewrite
  · intro x; simp [Expr.Defined, Binary.Domain]
  · intro x _; exact derivative_integral basis axis (x 0) (x 1)

#print axioms derivative_encode
#print axioms integral_encode
#print axioms substitution_valid
#print axioms compose_variable
#print axioms compose_identity
#print axioms compose_product
#print axioms egf_product_coefficient
#print axioms derivative_integral_circuit
end Gimle.Asgard.Streams
