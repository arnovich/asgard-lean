import Gimle.Asgard.Streams.Torus

/-! # Norms on trigonometric polynomials

The ℓ¹ norm `l1 P = Σ |P_k|` of the coefficients, a rational, and the weighted
norms `wnorm σ P = Σ |P_k| e^{σ|k|}` with `|k| = |k₁| + |k₂|` (`size`), the
scale of Banach spaces in which the Cauchy–Kowalevski induction for the Euler
stream closes. `dnorm σ P = Σ |P_k| |k| e^{σ|k|}` is the norm of one
derivative. Three estimates carry the induction:

* the transport costs at most one derivative, `|(p × q)/|p|²| ≤ |q|₁`
  (`abs_coupling_le`, from Lagrange's identity `(p × q)² ≤ |p|²|q|²`), so
  `wnorm σ (transport P Q) ≤ wnorm σ P · dnorm σ Q` for `σ ≥ 0`
  (`wnorm_transport_le`);
* Nagumo: a derivative is paid for by a loss of radius,
  `dnorm σ Q ≤ wnorm σ' Q / (2(σ' − σ))` for `σ < σ'` (`dnorm_le_wnorm_div`),
  from `2y ≤ e^y`; the sharp constant is `1/e`, and `1/2` keeps every constant
  rational;
* the ℓ¹ norm is below every weighted norm with `σ ≥ 0` and the weighted norm
  is below `l1 P · e^{σK}` when every mode has size at most `K`.

`SizeLE` and `size` live in `Torus`. Nothing here is a function on the torus;
`TrigField` evaluates. -/
namespace Gimle.Asgard.Streams.Torus

open Real

/-- `|k|² ≤ (|k₁| + |k₂|)²`. -/
theorem lam_le_size_sq (k : Wave) : lam k ≤ (size k : ℤ) ^ 2 := by
  simp only [lam, size]
  push_cast
  nlinarith [abs_nonneg k.1, abs_nonneg k.2, sq_abs k.1, sq_abs k.2]

/-- Lagrange's identity, as the inequality `(p × q)² ≤ |p|² |q|²`. -/
theorem cross_sq_le (p q : Wave) : cross p q ^ 2 ≤ lam p * lam q := by
  have identity : cross p q ^ 2 + (p.1 * q.1 + p.2 * q.2) ^ 2 = lam p * lam q := by
    simp only [cross, lam]; ring
  nlinarith [sq_nonneg (p.1 * q.1 + p.2 * q.2)]

/-- The transport costs at most one derivative: `|(p × q)/|p|²| ≤ |q₁| + |q₂|`. -/
theorem abs_coupling_le (p q : Wave) : |coupling p q| ≤ (size q : ℚ) := by
  by_cases hp : p = 0
  · subst hp
    simp [coupling]
  · have lpos : (0 : ℤ) < lam p := lam_pos hp
    have hcross : |cross p q| ≤ lam p * size q := by
      apply abs_le_of_sq_le_sq _ (by positivity)
      calc cross p q ^ 2 ≤ lam p * lam q := cross_sq_le p q
        _ ≤ lam p * (size q : ℤ) ^ 2 := by
            exact mul_le_mul_of_nonneg_left (lam_le_size_sq q) lpos.le
        _ ≤ (lam p) ^ 2 * (size q : ℤ) ^ 2 := by
            have : lam p ≤ lam p ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_right this (by positivity)
        _ = (lam p * size q) ^ 2 := by ring
    have lposq : (0 : ℚ) < lam p := by exact_mod_cast lpos
    rw [coupling, abs_div, abs_of_pos lposq, div_le_iff₀ lposq]
    have h : ((|cross p q| : ℤ) : ℚ) ≤ ((lam p * size q : ℤ) : ℚ) := by exact_mod_cast hcross
    push_cast at h
    linarith

/-! ## The norms -/

/-- The ℓ¹ norm of the coefficients. -/
def l1 (P : TrigPoly) : ℚ := P.sum fun _ a => |a|

/-- The weighted norm `Σ |P_k| e^{σ|k|}`. -/
noncomputable def wnorm (σ : ℝ) (P : TrigPoly) : ℝ :=
  P.sum fun k a => |(a : ℝ)| * exp (σ * size k)

/-- The norm of one derivative, `Σ |P_k| |k| e^{σ|k|}`. -/
noncomputable def dnorm (σ : ℝ) (P : TrigPoly) : ℝ :=
  P.sum fun k a => |(a : ℝ)| * size k * exp (σ * size k)

theorem wnorm_eq_sum (σ : ℝ) {P : TrigPoly} {s : Finset Wave} (hs : P.support ⊆ s) :
    wnorm σ P = ∑ k ∈ s, |(P k : ℝ)| * exp (σ * size k) :=
  Finsupp.sum_of_support_subset P hs _ fun k _ => by simp

theorem dnorm_eq_sum (σ : ℝ) {P : TrigPoly} {s : Finset Wave} (hs : P.support ⊆ s) :
    dnorm σ P = ∑ k ∈ s, |(P k : ℝ)| * size k * exp (σ * size k) :=
  Finsupp.sum_of_support_subset P hs _ fun k _ => by simp

theorem l1_eq_sum {P : TrigPoly} {s : Finset Wave} (hs : P.support ⊆ s) :
    l1 P = ∑ k ∈ s, |P k| :=
  Finsupp.sum_of_support_subset P hs _ fun k _ => by simp

theorem l1_nonneg (P : TrigPoly) : 0 ≤ l1 P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem wnorm_nonneg (σ : ℝ) (P : TrigPoly) : 0 ≤ wnorm σ P :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem dnorm_nonneg (σ : ℝ) (P : TrigPoly) : 0 ≤ dnorm σ P :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The ℓ¹ norm is subadditive. -/
theorem l1_add_le (P Q : TrigPoly) : l1 (P + Q) ≤ l1 P + l1 Q := by
  rw [l1_eq_sum (Finsupp.support_add (g₁ := P) (g₂ := Q)),
    l1_eq_sum (Finset.subset_union_left (s₂ := Q.support)),
    l1_eq_sum (Finset.subset_union_right (s₁ := P.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by rw [Finsupp.add_apply]; exact abs_add_le _ _

theorem l1_single_le (k : Wave) (a : ℚ) : l1 (Finsupp.single k a) ≤ |a| := by
  rw [l1_eq_sum Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]

theorem l1_smul (c : ℚ) (P : TrigPoly) : l1 (c • P) = |c| * l1 P := by
  rw [l1_eq_sum (Finsupp.support_smul (b := c) (g := P)), l1_eq_sum subset_rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Finsupp.smul_apply, smul_eq_mul, abs_mul]

theorem l1_neg (P : TrigPoly) : l1 (-P) = l1 P := by
  rw [l1_eq_sum (by simp : (-P).support ⊆ P.support), l1_eq_sum subset_rfl]
  simp

theorem l1_sub_le (P Q : TrigPoly) : l1 (P - Q) ≤ l1 P + l1 Q := by
  have h := l1_add_le P (-Q)
  rw [l1_neg, ← sub_eq_add_neg] at h
  exact h

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → TrigPoly) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (l1_add_le _ _).trans (add_le_add le_rfl ih)

/-- At `σ = 0` the weighted norm is the ℓ¹ norm. -/
theorem wnorm_zero (P : TrigPoly) : wnorm 0 P = l1 P := by
  rw [wnorm_eq_sum 0 subset_rfl, l1_eq_sum subset_rfl]
  push_cast
  simp

/-- The ℓ¹ norm is below every weighted norm with `σ ≥ 0`. -/
theorem l1_le_wnorm {σ : ℝ} (hσ : 0 ≤ σ) (P : TrigPoly) : (l1 P : ℝ) ≤ wnorm σ P := by
  rw [wnorm_eq_sum σ subset_rfl, l1_eq_sum subset_rfl]
  push_cast
  refine Finset.sum_le_sum fun k _ => ?_
  have one_le : 1 ≤ exp (σ * size k) := one_le_exp (by positivity)
  calc |(P k : ℝ)| = |(P k : ℝ)| * 1 := (mul_one _).symm
    _ ≤ |(P k : ℝ)| * exp (σ * size k) := mul_le_mul_of_nonneg_left one_le (abs_nonneg _)

/-- The weighted norm grows with `σ`. -/
theorem wnorm_mono {σ σ' : ℝ} (h : σ ≤ σ') (P : TrigPoly) : wnorm σ P ≤ wnorm σ' P := by
  rw [wnorm_eq_sum σ subset_rfl, wnorm_eq_sum σ' subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [(size k).cast_nonneg (α := ℝ)]))
    (abs_nonneg _)

/-- Modes of size at most `K` give `wnorm σ P ≤ l1 P · e^{σK}` for `σ ≥ 0`. -/
theorem wnorm_le_l1_mul_exp {σ : ℝ} (hσ : 0 ≤ σ) {P : TrigPoly} {K : ℕ} (hK : SizeLE K P) :
    wnorm σ P ≤ l1 P * exp (σ * K) := by
  rw [wnorm_eq_sum σ subset_rfl, l1_eq_sum subset_rfl]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (abs_nonneg _)
  have : (size k : ℝ) ≤ K := by exact_mod_cast hK k hk
  nlinarith

theorem wnorm_single (σ : ℝ) (k : Wave) (a : ℚ) :
    wnorm σ (Finsupp.single k a) = |(a : ℝ)| * exp (σ * size k) := by
  rw [wnorm_eq_sum σ Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]

theorem wnorm_add_le (σ : ℝ) (P Q : TrigPoly) : wnorm σ (P + Q) ≤ wnorm σ P + wnorm σ Q := by
  rw [wnorm_eq_sum σ (Finsupp.support_add (g₁ := P) (g₂ := Q)),
    wnorm_eq_sum σ (Finset.subset_union_left (s₂ := Q.support)),
    wnorm_eq_sum σ (Finset.subset_union_right (s₁ := P.support)), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← add_mul, Finsupp.add_apply]
  push_cast
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (exp_pos _).le

theorem wnorm_smul (σ : ℝ) (c : ℚ) (P : TrigPoly) : wnorm σ (c • P) = |(c : ℝ)| * wnorm σ P := by
  rw [wnorm_eq_sum σ (Finsupp.support_smul (b := c) (g := P)), wnorm_eq_sum σ subset_rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  push_cast
  rw [abs_mul]
  ring

theorem wnorm_neg (σ : ℝ) (P : TrigPoly) : wnorm σ (-P) = wnorm σ P := by
  rw [wnorm_eq_sum σ (by simp : (-P).support ⊆ P.support), wnorm_eq_sum σ subset_rfl]
  simp

theorem wnorm_sum_le {ι : Type*} (σ : ℝ) (s : Finset ι) (f : ι → TrigPoly) :
    wnorm σ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, wnorm σ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (wnorm_add_le σ _ _).trans (add_le_add le_rfl ih)

/-! ## The transport costs one derivative -/

/-- `wnorm σ (transport P Q) ≤ wnorm σ P · dnorm σ Q` for `σ ≥ 0`: each pair
`(p, q)` lands at `p + q`, with `e^{σ|p+q|} ≤ e^{σ|p|} e^{σ|q|}` and the
coupling below `|q|`. -/
theorem wnorm_transport_le {σ : ℝ} (hσ : 0 ≤ σ) (P Q : TrigPoly) :
    wnorm σ (transport P Q) ≤ wnorm σ P * dnorm σ Q := by
  rw [transport_eq_sum, Finsupp.sum]
  refine (wnorm_sum_le σ _ _).trans ?_
  rw [wnorm_eq_sum (P := P) σ subset_rfl, dnorm_eq_sum σ subset_rfl, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [wnorm_smul, Finsupp.sum]
  refine (mul_le_mul_of_nonneg_left (wnorm_sum_le σ _ _) (abs_nonneg _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [wnorm_smul, wnorm_single]
  have coupling_le : |(coupling p q : ℝ)| ≤ (size q : ℝ) := by exact_mod_cast abs_coupling_le p q
  have exp_le : exp (σ * size (p + q)) ≤ exp (σ * size p) * exp (σ * size q) := by
    rw [← exp_add, ← mul_add]
    refine exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hσ)
    exact_mod_cast size_add_le p q
  calc |(P p : ℝ)| * (|(Q q : ℝ)| * (|(coupling p q : ℝ)| * exp (σ * size (p + q))))
      ≤ |(P p : ℝ)| * (|(Q q : ℝ)| * ((size q : ℝ) * (exp (σ * size p) * exp (σ * size q)))) := by
        gcongr
    _ = |(P p : ℝ)| * exp (σ * size p) * (|(Q q : ℝ)| * size q * exp (σ * size q)) := by ring

/-! ## Nagumo: a derivative for a loss of radius -/

/-- `2y ≤ e^y` for `y ≥ 0`, from `1 + y + y²/2 ≤ e^y`. -/
theorem two_mul_le_exp {y : ℝ} (hy : 0 ≤ y) : 2 * y ≤ exp y := by
  have := quadratic_le_exp_of_nonneg hy
  nlinarith [sq_nonneg (y - 1)]

/-- `x e^{σx} ≤ e^{σ'x} / (2(σ' − σ))` for `x ≥ 0` and `σ < σ'`. -/
theorem nagumo {σ σ' x : ℝ} (h : σ < σ') (hx : 0 ≤ x) :
    x * exp (σ * x) ≤ exp (σ' * x) / (2 * (σ' - σ)) := by
  have d_pos : 0 < σ' - σ := sub_pos.mpr h
  rw [le_div_iff₀ (by positivity)]
  have key : 2 * ((σ' - σ) * x) ≤ exp ((σ' - σ) * x) := two_mul_le_exp (by positivity)
  calc x * exp (σ * x) * (2 * (σ' - σ)) = exp (σ * x) * (2 * ((σ' - σ) * x)) := by ring
    _ ≤ exp (σ * x) * exp ((σ' - σ) * x) := mul_le_mul_of_nonneg_left key (exp_pos _).le
    _ = exp (σ' * x) := by rw [← exp_add]; ring_nf

/-- The derivative norm at `σ` is paid for at `σ' > σ`: `dnorm σ Q ≤ wnorm σ' Q / (2(σ' − σ))`. -/
theorem dnorm_le_wnorm_div {σ σ' : ℝ} (h : σ < σ') (Q : TrigPoly) :
    dnorm σ Q ≤ wnorm σ' Q / (2 * (σ' - σ)) := by
  rw [dnorm_eq_sum σ subset_rfl, wnorm_eq_sum σ' subset_rfl, Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (nagumo h (Nat.cast_nonneg _)) (abs_nonneg _)

#print axioms abs_coupling_le
#print axioms wnorm_transport_le
#print axioms dnorm_le_wnorm_div
end Gimle.Asgard.Streams.Torus
