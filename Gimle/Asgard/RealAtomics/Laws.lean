import Gimle.Asgard.RealAtomics.Compiler

/-! Rewrite laws compare partial operational relations, retaining any domain
premises. They never equate circuits solely by their auxiliary totalized values. -/
namespace Gimle.Asgard.RealAtomics

def Circuit.EquivalentOn {k n m : Nat} (region : Point k → Point n → Prop)
    (left right : Circuit k n m) : Prop :=
  ∀ axes x, region axes x → ∀ y, left.Rel axes x y ↔ right.Rel axes x y

theorem Expr.rewrite {k n : Nat} (a b : Expr k n) (region : Point k → Point n → Prop)
    (domains : ∀ axes x, region axes x → (a.Defined axes x ↔ b.Defined axes x))
    (values : ∀ axes x, region axes x → a.Defined axes x → a.value axes x = b.value axes x) :
    Circuit.EquivalentOn region a.compile b.compile := by
  intro axes x hx y
  rw [Expr.compile_rel, Expr.compile_rel]
  constructor
  · rintro ⟨ha, hy⟩
    exact ⟨(domains axes x hx).mp ha, by rw [← values axes x hx ha]; exact hy⟩
  · rintro ⟨hb, hy⟩
    have ha := (domains axes x hx).mpr hb
    exact ⟨ha, by rw [values axes x hx ha]; exact hy⟩

theorem log_exp {k : Nat} : Circuit.EquivalentOn (fun _ _ => True)
    (Expr.unary .log (.unary .exp (.input 0)) : Expr k 1).compile
    (Expr.input 0).compile := by
  apply Expr.rewrite
  · intros
    simp [Expr.Defined, Expr.value, Unary.Domain, Unary.value, Real.exp_pos]
  · intros
    simp [Expr.value, Unary.value, Real.log_exp]

theorem exp_log {k : Nat} : Circuit.EquivalentOn (fun _ x => 0 < x 0)
    (Expr.unary .exp (.unary .log (.input 0)) : Expr k 1).compile
    (Expr.input 0).compile := by
  apply Expr.rewrite
  · intro axes x hx
    simp [Expr.Defined, Expr.value, Unary.Domain, hx]
  · intro axes x hx _
    simpa [Expr.value, Unary.value] using Real.exp_log hx

theorem sqrt_square {k : Nat} : Circuit.EquivalentOn (fun _ _ => True)
    (Expr.unary .sqrt (.unary (.naturalPower 2) (.input 0)) : Expr k 1).compile
    (Expr.unary .abs (.input 0)).compile := by
  apply Expr.rewrite
  · intros
    simp [Expr.Defined, Expr.value, Unary.Domain, Unary.value, sq_nonneg]
  · intros
    simp [Expr.value, Unary.value, Real.sqrt_sq_eq_abs]

theorem square_sqrt {k : Nat} : Circuit.EquivalentOn (fun _ x => 0 ≤ x 0)
    (Expr.unary (.naturalPower 2) (.unary .sqrt (.input 0)) : Expr k 1).compile
    (Expr.input 0).compile := by
  apply Expr.rewrite
  · intro axes x hx
    simp [Expr.Defined, Expr.value, Unary.Domain, hx]
  · intro axes x hx _
    simpa [Expr.value, Unary.value] using Real.sq_sqrt hx

theorem division_self {k : Nat} : Circuit.EquivalentOn (fun _ x => x 0 ≠ 0)
    (Expr.binary .division (.input 0) (.input 0) : Expr k 1).compile
    (Expr.constant 1).compile := by
  apply Expr.rewrite
  · intro axes x hx
    simp [Expr.Defined, Expr.value, Binary.Domain, hx]
  · intro axes x hx _
    simp [Expr.value, Binary.value, hx]

theorem rational_power_zero {k : Nat} : Circuit.EquivalentOn (fun _ x => 0 < x 0)
    (Expr.unary (.rationalPower 0) (.input 0) : Expr k 1).compile
    (Expr.constant 1).compile := by
  apply Expr.rewrite
  · intro axes x hx
    simp [Expr.Defined, Expr.value, Unary.Domain, hx]
  · intros
    simp [Expr.value, Unary.value]

/-- Real power and exp(log(base)*exponent) have the same positive-base domain,
so this is an equality of partial relations even without an external region. -/
theorem real_power_exp_log {k : Nat} : Circuit.EquivalentOn (fun _ _ => True)
    (Expr.binary .realPower (.input 0) (.input 1) : Expr k 2).compile
    (Expr.unary .exp (.binary .mul (.unary .log (.input 0)) (.input 1))).compile := by
  apply Expr.rewrite
  · intros
    simp [Expr.Defined, Expr.value, Unary.Domain, Binary.Domain]
  · intro axes x _ hd
    have positive : 0 < x 0 := by simpa [Expr.Defined, Expr.value, Binary.Domain] using hd
    simpa [Expr.value, Unary.value, Binary.value] using Real.rpow_def_of_pos positive (x 1)

#print axioms Expr.rewrite
#print axioms sqrt_square
#print axioms square_sqrt
#print axioms log_exp
#print axioms exp_log
#print axioms division_self
#print axioms rational_power_zero
#print axioms real_power_exp_log
end Gimle.Asgard.RealAtomics
