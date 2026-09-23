import Gimle.Asgard.External.Compiler

/-! Finite pointwise partitions. Nonzero weight is algebraic support; no
smoothness, analytic support or numerical execution theorem is implicit. -/
namespace Gimle.Asgard.External

noncomputable def blendValue {k m : Nat} (weights : Fin k → ℝ) (branches : Fin k → Point m) : Point m :=
  ∑ i, weights i • branches i

@[simp] theorem blendValue_apply {k m : Nat} (w : Fin k → ℝ) (b : Fin k → Point m) (j : Fin m) :
    blendValue w b j = ∑ i, w i * b i j := by
  simp [blendValue, Finset.sum_apply]

/-- Empty raw sums denote zero, but do not form a unit partition at any point. -/
def Source.sum {n m : Nat} : (k : Nat) → (Fin k → Source n m) → Source n m
  | 0, _ => .polynomial (fun _ => .constant 0)
  | k+1, branches => .add (branches 0) (Source.sum k (fun i => branches i.succ))

@[simp] theorem Source.sum_value {n m k : Nat} (branches : Fin k → Source n m)
    (env : Environment) (x : Point n) :
    (Source.sum k branches).value env x = ∑ i, (branches i).value env x := by
  induction k with
  | zero => funext j; simp [sum, value, Polynomial.Expr.eval]
  | succ k ih => simp [sum, value, ih, Fin.sum_univ_succ]

@[simp] theorem Source.sum_defined {n m k : Nat} (branches : Fin k → Source n m)
    (env : Environment) (x : Point n) :
    (Source.sum k branches).Defined env x ↔ ∀ i, (branches i).Defined env x := by
  induction k with
  | zero => simp [sum, Defined]
  | succ k ih => simp [sum, Defined, ih, Fin.forall_fin_succ]

def Source.partition {n m k : Nat} (gates : Fin k → Source n 1) (branches : Fin k → Source n m) : Source n m :=
  Source.sum k (fun i => .weighted (gates i) (branches i))

@[simp] theorem Source.partition_value {n m k : Nat} (gates : Fin k → Source n 1)
    (branches : Fin k → Source n m) (env : Environment) (x : Point n) :
    (Source.partition gates branches).value env x =
      blendValue (fun i => (gates i).value env x 0) (fun i => (branches i).value env x) := by
  simp [partition, blendValue, value, Pi.smul_def, smul_eq_mul]

@[simp] theorem Source.partition_defined {n m k : Nat} (gates : Fin k → Source n 1)
    (branches : Fin k → Source n m) (env : Environment) (x : Point n) :
    (Source.partition gates branches).Defined env x ↔
      ∀ i, (gates i).Defined env x ∧ (branches i).Defined env x := by
  simp [partition, Defined]

structure PartitionOn {n m k : Nat} (env : Environment) (region : Point n → Prop)
    (gates : Fin k → Source n 1) (branches : Fin k → Source n m) : Prop where
  defined : ∀ x, region x → ∀ i, (gates i).Defined env x ∧ (branches i).Defined env x
  nonnegative : ∀ x, region x → ∀ i, 0 ≤ (gates i).value env x 0
  unitSum : ∀ x, region x → ∑ i, (gates i).value env x 0 = 1

/-- Agreement is needed only for active branches. This is an exact value law;
using it as circuit behavior additionally requires every evaluation domain. -/
theorem blendValue_agrees {k m : Nat} (w : Fin k → ℝ) (b : Fin k → Point m) (target : Point m)
    (unitSum : ∑ i, w i = 1) (branchLaw : ∀ i, w i ≠ 0 → b i = target) :
    blendValue w b = target := by
  funext j
  rw [blendValue_apply]
  calc
    ∑ i, w i * b i j = ∑ i, w i * target j := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : w i = 0
      · simp [h]
      · rw [branchLaw i h]
    _ = target j := by rw [← Finset.sum_mul, unitSum, one_mul]

theorem Source.partition_agrees {n m k : Nat} (env : Environment) (region : Point n → Prop)
    (gates : Fin k → Source n 1) (branches : Fin k → Source n m)
    (h : PartitionOn env region gates branches) (target : Point n → Point m)
    (branchLaw : ∀ x, region x → ∀ i, (gates i).value env x 0 ≠ 0 → (branches i).value env x = target x)
    (x : Point n) (hx : region x) :
    (Source.partition gates branches).compile.Rel env x (target x) := by
  rw [compile_rel, partition_defined, partition_value]
  exact ⟨h.defined x hx, (blendValue_agrees _ _ _ (h.unitSum x hx) (branchLaw x hx)).symm⟩

theorem blendValue_bounds {k m : Nat} (w : Fin k → ℝ) (b : Fin k → Point m)
    (lower upper : Point m) (nonnegative : ∀ i, 0 ≤ w i) (unitSum : ∑ i, w i = 1)
    (branchLaw : ∀ i, w i ≠ 0 → ∀ j, lower j ≤ b i j ∧ b i j ≤ upper j) :
    ∀ j, lower j ≤ blendValue w b j ∧ blendValue w b j ≤ upper j := by
  intro j
  have low : ∑ i, w i * lower j ≤ ∑ i, w i * b i j := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : w i = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (branchLaw i h j).1 (nonnegative i)
  have high : ∑ i, w i * b i j ≤ ∑ i, w i * upper j := by
    apply Finset.sum_le_sum
    intro i _
    by_cases h : w i = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (branchLaw i h j).2 (nonnegative i)
  rw [← Finset.sum_mul, unitSum, one_mul] at low
  rw [← Finset.sum_mul, unitSum, one_mul] at high
  exact ⟨by simpa using low, by simpa using high⟩

/-- A compiled partition satisfies a coordinate enclosure on the stated region. -/
theorem Source.partition_contract {n m k : Nat} (env : Environment) (region : Point n → Prop)
    (gates : Fin k → Source n 1) (branches : Fin k → Source n m)
    (h : PartitionOn env region gates branches) (lower upper : Point m)
    (branchLaw : ∀ x, region x → ∀ i, (gates i).value env x 0 ≠ 0 →
      ∀ j, lower j ≤ (branches i).value env x j ∧ (branches i).value env x j ≤ upper j) :
    (Source.partition gates branches).compile.Satisfies env
      ⟨region, fun _ y => ∀ j, lower j ≤ y j ∧ y j ≤ upper j⟩ := by
  intro x hx
  constructor
  · rw [compile_defined, partition_defined]; exact h.defined x hx
  · rw [compile_value, partition_value]
    exact blendValue_bounds _ _ _ _ (h.nonnegative x hx) (h.unitSum x hx) (branchLaw x hx)

theorem blendValue_linear {k m o : Nat} (w : Fin k → ℝ) (b : Fin k → Point m)
    (L : Point m →ₗ[ℝ] Point o) : L (blendValue w b) = blendValue w (fun i => L (b i)) := by
  simp [blendValue]

/-- Distribute only a total linear postprocessor. A partial external component
with a linear auxiliary value cannot use this theorem without totality. -/
theorem Source.partition_postcompose {n m k o : Nat} (env : Environment)
    (gates : Fin k → Source n 1) (branches : Fin k → Source n m) (post : Source m o)
    (L : Point m →ₗ[ℝ] Point o) (total : ∀ x, post.Defined env x)
    (linear : ∀ x, post.value env x = L x) :
    ((Source.partition gates branches).compose post).compile.Equivalent env
      (Source.partition gates (fun i => (branches i).compose post)).compile := by
  intro x y
  simp only [compile_rel, Defined, partition_defined, partition_value, value, linear, total,
    and_true, blendValue_linear]

#print axioms Source.partition_defined
#print axioms Source.partition_agrees
#print axioms Source.partition_contract
#print axioms Source.partition_postcompose
end Gimle.Asgard.External
