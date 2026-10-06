import Gimle.Asgard.Streams.MildEvaluation
import Gimle.Asgard.Streams.TrigNorm

/-! Weighted norms on real Fourier coefficients. These estimates apply after
physical evaluation of the exponential-polynomial carrier. In particular,
no estimate takes absolute values of the redundant carrier coefficients. -/
namespace Gimle.Asgard.Streams.Mild.RealPoly

open Torus Real

/-! ## The norms -/

/-- The ℓ¹ norm of the coefficients. -/
noncomputable def l1 (P : RealPoly) : ℝ := P.sum fun _ a => |a|

/-- The weighted norm `Σ |P_k| e^{σ|k|}`. -/
noncomputable def wnorm (σ : ℝ) (P : RealPoly) : ℝ :=
  P.sum fun k a => |(a : ℝ)| * exp (σ * size k)

/-- The norm of one derivative, `Σ |P_k| |k| e^{σ|k|}`. -/
noncomputable def dnorm (σ : ℝ) (P : RealPoly) : ℝ :=
  P.sum fun k a => |(a : ℝ)| * size k * exp (σ * size k)

theorem wnorm_eq_sum (σ : ℝ) {P : RealPoly} {s : Finset Wave} (hs : P.support ⊆ s) :
    wnorm σ P = ∑ k ∈ s, |(P k : ℝ)| * exp (σ * size k) :=
  Finsupp.sum_of_support_subset P hs _ fun k _ => by simp

theorem dnorm_eq_sum (σ : ℝ) {P : RealPoly} {s : Finset Wave} (hs : P.support ⊆ s) :
    dnorm σ P = ∑ k ∈ s, |(P k : ℝ)| * size k * exp (σ * size k) :=
  Finsupp.sum_of_support_subset P hs _ fun k _ => by simp

theorem l1_eq_sum {P : RealPoly} {s : Finset Wave} (hs : P.support ⊆ s) :
    l1 P = ∑ k ∈ s, |P k| :=
  Finsupp.sum_of_support_subset P hs _ fun k _ => by simp

theorem l1_nonneg (P : RealPoly) : 0 ≤ l1 P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem wnorm_nonneg (σ : ℝ) (P : RealPoly) : 0 ≤ wnorm σ P :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem dnorm_nonneg (σ : ℝ) (P : RealPoly) : 0 ≤ dnorm σ P :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The ℓ¹ norm is subadditive. -/
theorem l1_add_le (P Q : RealPoly) : l1 (P + Q) ≤ l1 P + l1 Q := by
  rw [l1_eq_sum (Finsupp.support_add (g₁ := P) (g₂ := Q)),
    l1_eq_sum (Finset.subset_union_left (s₂ := Q.support)),
    l1_eq_sum (Finset.subset_union_right (s₁ := P.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by rw [Finsupp.add_apply]; exact abs_add_le _ _

theorem l1_single_le (k : Wave) (a : ℝ) : l1 (Finsupp.single k a) ≤ |a| := by
  rw [l1_eq_sum Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]

theorem l1_smul (c : ℝ) (P : RealPoly) : l1 (c • P) = |c| * l1 P := by
  rw [l1_eq_sum (Finsupp.support_smul (b := c) (g := P)), l1_eq_sum subset_rfl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Finsupp.smul_apply, smul_eq_mul, abs_mul]

theorem l1_neg (P : RealPoly) : l1 (-P) = l1 P := by
  rw [l1_eq_sum (by simp : (-P).support ⊆ P.support), l1_eq_sum subset_rfl]
  simp

theorem l1_sub_le (P Q : RealPoly) : l1 (P - Q) ≤ l1 P + l1 Q := by
  have h := l1_add_le P (-Q)
  rw [l1_neg, ← sub_eq_add_neg] at h
  exact h

theorem l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → RealPoly) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (l1_add_le _ _).trans (add_le_add le_rfl ih)

/-- At `σ = 0` the weighted norm is the ℓ¹ norm. -/
theorem wnorm_zero (P : RealPoly) : wnorm 0 P = l1 P := by
  rw [wnorm_eq_sum 0 subset_rfl, l1_eq_sum subset_rfl]
  simp

/-- The ℓ¹ norm is below every weighted norm with `σ ≥ 0`. -/
theorem l1_le_wnorm {σ : ℝ} (hσ : 0 ≤ σ) (P : RealPoly) : (l1 P : ℝ) ≤ wnorm σ P := by
  rw [wnorm_eq_sum σ subset_rfl, l1_eq_sum subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  have one_le : 1 ≤ exp (σ * size k) := one_le_exp (by positivity)
  calc |(P k : ℝ)| = |(P k : ℝ)| * 1 := (mul_one _).symm
    _ ≤ |(P k : ℝ)| * exp (σ * size k) := mul_le_mul_of_nonneg_left one_le (abs_nonneg _)

/-- The weighted norm grows with `σ`. -/
theorem wnorm_mono {σ σ' : ℝ} (h : σ ≤ σ') (P : RealPoly) : wnorm σ P ≤ wnorm σ' P := by
  rw [wnorm_eq_sum σ subset_rfl, wnorm_eq_sum σ' subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [(size k).cast_nonneg (α := ℝ)]))
    (abs_nonneg _)

/-- Modes of size at most `K` give `wnorm σ P ≤ l1 P · e^{σK}` for `σ ≥ 0`. -/
theorem wnorm_le_l1_mul_exp {σ : ℝ} (hσ : 0 ≤ σ) {P : RealPoly} {K : ℕ} (hK : ∀ k ∈ P.support, size k ≤ K) :
    wnorm σ P ≤ l1 P * exp (σ * K) := by
  rw [wnorm_eq_sum σ subset_rfl, l1_eq_sum subset_rfl]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (abs_nonneg _)
  have : (size k : ℝ) ≤ K := by exact_mod_cast hK k hk
  nlinarith

theorem wnorm_single (σ : ℝ) (k : Wave) (a : ℝ) :
    wnorm σ (Finsupp.single k a) = |(a : ℝ)| * exp (σ * size k) := by
  rw [wnorm_eq_sum σ Finsupp.support_single_subset, Finset.sum_singleton, Finsupp.single_eq_same]

theorem wnorm_add_le (σ : ℝ) (P Q : RealPoly) : wnorm σ (P + Q) ≤ wnorm σ P + wnorm σ Q := by
  rw [wnorm_eq_sum σ (Finsupp.support_add (g₁ := P) (g₂ := Q)),
    wnorm_eq_sum σ (Finset.subset_union_left (s₂ := Q.support)),
    wnorm_eq_sum σ (Finset.subset_union_right (s₁ := P.support)), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← add_mul, Finsupp.add_apply]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (exp_pos _).le

theorem wnorm_smul (σ : ℝ) (c : ℝ) (P : RealPoly) : wnorm σ (c • P) = |(c : ℝ)| * wnorm σ P := by
  rw [wnorm_eq_sum σ (Finsupp.support_smul (b := c) (g := P)), wnorm_eq_sum σ subset_rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  rw [abs_mul]
  ring

theorem wnorm_neg (σ : ℝ) (P : RealPoly) : wnorm σ (-P) = wnorm σ P := by
  rw [wnorm_eq_sum σ (by simp : (-P).support ⊆ P.support), wnorm_eq_sum σ subset_rfl]
  simp

theorem wnorm_sum_le {ι : Type*} (σ : ℝ) (s : Finset ι) (f : ι → RealPoly) :
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
theorem wnorm_transport_le {σ : ℝ} (hσ : 0 ≤ σ) (P Q : RealPoly) :
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

/-- The derivative norm at `σ` is paid for at `σ' > σ`: `dnorm σ Q ≤ wnorm σ' Q / (2(σ' − σ))`. -/
theorem dnorm_le_wnorm_div {σ σ' : ℝ} (h : σ < σ') (Q : RealPoly) :
    dnorm σ Q ≤ wnorm σ' Q / (2 * (σ' - σ)) := by
  rw [dnorm_eq_sum σ subset_rfl, wnorm_eq_sum σ' subset_rfl, Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (nagumo h (Nat.cast_nonneg _)) (abs_nonneg _)

#print axioms wnorm_transport_le
#print axioms dnorm_le_wnorm_div
end Gimle.Asgard.Streams.Mild.RealPoly
