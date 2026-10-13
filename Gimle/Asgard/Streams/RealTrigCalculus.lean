import Gimle.Asgard.Streams.MildField
import Gimle.Asgard.Streams.EulerSolution

/-! Finite real Fourier calculus for physical evaluations of mild terms.
The spatial derivatives and transport/Jacobian identity are proved for real
coefficients; the redundant exponential-polynomial carrier is not involved. -/
namespace Gimle.Asgard.Streams.Mild.RealPoly

open Torus Real

/-- Zero spatial mean. -/
def MeanZero (P : RealPoly) : Prop := P 0 = 0

/-- Even real Fourier coefficients, representing a cosine field. -/
def IsEven (P : RealPoly) : Prop := ∀ k, P (-k) = P k

/-- Finite Fourier support radius in the ℓ¹ wavevector norm. -/
def SizeLE (K : ℕ) (P : RealPoly) : Prop := ∀ k ∈ P.support, size k ≤ K

/-- The real Fourier Laplacian. -/
noncomputable def laplacian (P : RealPoly) : RealPoly :=
  Finsupp.onFinset P.support (fun k => -(lam k : ℝ) * P k)
    (fun _ h => Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h))

@[simp] theorem laplacian_apply (P : RealPoly) (k : Wave) :
    laplacian P k = -(lam k : ℝ) * P k := rfl

/-- The inverse Laplacian, zero at the mean mode. -/
noncomputable def laplacianInv (P : RealPoly) : RealPoly :=
  Finsupp.onFinset P.support (fun k => if k = 0 then 0 else -(P k / lam k))
    (fun k h => Finsupp.mem_support_iff.mpr (fun hz => h (by simp [hz])))

@[simp] theorem laplacianInv_apply (P : RealPoly) (k : Wave) :
    laplacianInv P k = if k = 0 then 0 else -(P k / lam k) := rfl

theorem laplacian_laplacianInv {P : RealPoly} (h : MeanZero P) :
    laplacian (laplacianInv P) = P := by
  ext k
  simp only [laplacian_apply, laplacianInv_apply]
  split_ifs with hk
  · subst k; simpa [MeanZero] using h.symm
  · have hl : (lam k : ℝ) ≠ 0 := by exact_mod_cast (lam_pos hk).ne'
    field_simp

theorem field_add (P Q : RealPoly) (x : ℝ × ℝ) : field (P + Q) x = field P x + field Q x := by
  unfold field
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)]

theorem field_single (k : Wave) (a : ℝ) (x : ℝ × ℝ) :
    field (Finsupp.single k a) x = a * cos (phase k x) := by
  unfold field
  rw [Finsupp.sum_single_index (by simp)]
  rfl

/-- `field P x` as a sum over the support with the phase named. -/
theorem field_eq_sum_phase (P : RealPoly) (x : ℝ × ℝ) :
    field P x = ∑ k ∈ P.support, (P k : ℝ) * cos (phase k x) := rfl

/-- `∂₁ field P x = −Σ_k k₁ P_k sin(k·x)`. -/
noncomputable def fieldD₁ (P : RealPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.1 : ℝ) * P k) * sin (phase k x)

/-- `∂₂ field P x = −Σ_k k₂ P_k sin(k·x)`. -/
noncomputable def fieldD₂ (P : RealPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.2 : ℝ) * P k) * sin (phase k x)

/-- `∂₁∂₁ field P x = −Σ_k k₁² P_k cos(k·x)`. -/
noncomputable def fieldD₁₁ (P : RealPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.1 : ℝ) * k.1 * P k) * cos (phase k x)

/-- `∂₂∂₂ field P x = −Σ_k k₂² P_k cos(k·x)`. -/
noncomputable def fieldD₂₂ (P : RealPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.2 : ℝ) * k.2 * P k) * cos (phase k x)

/-- `∂₁∂₂ field P x = ∂₂∂₁ field P x = −Σ_k k₁ k₂ P_k cos(k·x)`. -/
noncomputable def fieldD₁₂ (P : RealPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.1 : ℝ) * k.2 * P k) * cos (phase k x)

/-- `∂₁ field P = fieldD₁ P`. -/
theorem hasDerivAt_field_fst (P : RealPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => field P (s, x.2)) (fieldD₁ P x) x.1 :=
  (hasDerivAt_sum_cos_fst P.support (fun k => (P k : ℝ)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₂ field P = fieldD₂ P`. -/
theorem hasDerivAt_field_snd (P : RealPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => field P (x.1, s)) (fieldD₂ P x) x.2 :=
  (hasDerivAt_sum_cos_snd P.support (fun k => (P k : ℝ)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₁ fieldD₁ P = fieldD₁₁ P`. -/
theorem hasDerivAt_fieldD₁_fst (P : RealPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (s, x.2)) (fieldD₁₁ P x) x.1 :=
  (hasDerivAt_sum_sin_fst P.support (fun k => -((k.1 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₂ fieldD₂ P = fieldD₂₂ P`. -/
theorem hasDerivAt_fieldD₂_snd (P : RealPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₂ P (x.1, s)) (fieldD₂₂ P x) x.2 :=
  (hasDerivAt_sum_sin_snd P.support (fun k => -((k.2 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₁ fieldD₂ P = fieldD₁₂ P`. -/
theorem hasDerivAt_fieldD₂_fst (P : RealPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₂ P (s, x.2)) (fieldD₁₂ P x) x.1 :=
  (hasDerivAt_sum_sin_fst P.support (fun k => -((k.2 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₂ fieldD₁ P = fieldD₁₂ P`: the mixed derivatives agree. -/
theorem hasDerivAt_fieldD₁_snd (P : RealPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (x.1, s)) (fieldD₁₂ P x) x.2 :=
  (hasDerivAt_sum_sin_snd P.support (fun k => -((k.1 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `field (laplacian P) = ∂₁∂₁ field P + ∂₂∂₂ field P`. -/
theorem field_laplacian (P : RealPoly) (x : ℝ × ℝ) :
    field (laplacian P) x = fieldD₁₁ P x + fieldD₂₂ P x := by
  have sub : (laplacian P).support ⊆ P.support := fun k hk => by
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h
    apply hk
    simp [h]
  rw [field_eq_sum_phase, Finset.sum_subset sub (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk; simp [hk])]
  rw [fieldD₁₁, fieldD₂₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [laplacian_apply, lam]
  push_cast
  ring

/-! ## Continuity of a field and its derivatives -/

/-- The field is continuous. -/
theorem continuous_field (P : RealPoly) : Continuous (field P) := by
  have : field P = fun x => ∑ k ∈ P.support, (P k : ℝ) * cos (phase k x) := by
    funext x; exact field_eq_sum_phase P x
  rw [this]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

/-- The derivative fields are continuous. -/
theorem continuous_fieldD₁ (P : RealPoly) : Continuous (fieldD₁ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_sin.comp (continuous_phase k))

theorem continuous_fieldD₂ (P : RealPoly) : Continuous (fieldD₂ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_sin.comp (continuous_phase k))

theorem continuous_fieldD₁₁ (P : RealPoly) : Continuous (fieldD₁₁ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

theorem continuous_fieldD₂₂ (P : RealPoly) : Continuous (fieldD₂₂ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

theorem continuous_fieldD₁₂ (P : RealPoly) : Continuous (fieldD₁₂ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

/-! ## Bounds on the derivative fields -/

/-- Each coordinate of a mode of size at most `K` is at most `K`. -/
theorem abs_coord_le_size {K : ℕ} {P : RealPoly} (hP : SizeLE K P) {k : Wave}
    (hk : k ∈ P.support) : |(k.1 : ℝ)| ≤ K ∧ |(k.2 : ℝ)| ≤ K := by
  have := hP k hk
  rw [size] at this
  constructor
  · rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Nat.le_add_right _ _) this
  · rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Nat.le_add_left _ _) this

/-- A sum `Σ_k −(c_k P_k) f_k` with `|c_k| ≤ B` and `|f_k| ≤ 1` is at most `B · l1 P`. -/
theorem abs_sum_mul_le {P : RealPoly} {B : ℝ} (c f : Wave → ℝ)
    (hc : ∀ k ∈ P.support, |c k| ≤ B) (hf : ∀ k, |f k| ≤ 1) :
    |∑ k ∈ P.support, -(c k * P k) * f k| ≤ B * l1 P := by
  rw [l1_eq_sum subset_rfl]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_neg, abs_mul]
  calc |c k| * |(P k : ℝ)| * |f k| ≤ |c k| * |(P k : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (hf k) (by positivity)
    _ ≤ B * |(P k : ℝ)| := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (hc k hk) (abs_nonneg _)

/-- `|∂₁ field P x| ≤ K · l1 P` for modes of size at most `K`. -/
theorem abs_fieldD₁_le {K : ℕ} {P : RealPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁ P x| ≤ K * l1 P :=
  abs_sum_mul_le (fun k => (k.1 : ℝ)) (fun k => sin (phase k x))
    (fun _ hk => (abs_coord_le_size hP hk).1) fun _ => abs_sin_le_one _

/-- `|∂₂ field P x| ≤ K · l1 P` for modes of size at most `K`. -/
theorem abs_fieldD₂_le {K : ℕ} {P : RealPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₂ P x| ≤ K * l1 P :=
  abs_sum_mul_le (fun k => (k.2 : ℝ)) (fun k => sin (phase k x))
    (fun _ hk => (abs_coord_le_size hP hk).2) fun _ => abs_sin_le_one _

/-- The second-derivative fields are at most `K² · l1 P`. -/
theorem abs_fieldD₁₁_le {K : ℕ} {P : RealPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁₁ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_sum_mul_le (fun k => (k.1 : ℝ) * k.1) (fun k => cos (phase k x))
    (fun _ hk => by
      rw [abs_mul, sq]
      exact mul_le_mul (abs_coord_le_size hP hk).1 (abs_coord_le_size hP hk).1 (abs_nonneg _)
        (Nat.cast_nonneg _))
    fun _ => abs_cos_le_one _

theorem abs_fieldD₂₂_le {K : ℕ} {P : RealPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₂₂ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_sum_mul_le (fun k => (k.2 : ℝ) * k.2) (fun k => cos (phase k x))
    (fun _ hk => by
      rw [abs_mul, sq]
      exact mul_le_mul (abs_coord_le_size hP hk).2 (abs_coord_le_size hP hk).2 (abs_nonneg _)
        (Nat.cast_nonneg _))
    fun _ => abs_cos_le_one _

theorem abs_fieldD₁₂_le {K : ℕ} {P : RealPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁₂ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_sum_mul_le (fun k => (k.1 : ℝ) * k.2) (fun k => cos (phase k x))
    (fun _ hk => by
      rw [abs_mul, sq]
      exact mul_le_mul (abs_coord_le_size hP hk).1 (abs_coord_le_size hP hk).2 (abs_nonneg _)
        (Nat.cast_nonneg _))
    fun _ => abs_cos_le_one _

/-! ## Linearity of the field -/

theorem field_zero (x : ℝ × ℝ) : field (0 : RealPoly) x = 0 := by simp [field]

/-- The field is `ℝ`-linear: scaling. -/
theorem field_smul (c : ℝ) (P : RealPoly) (x : ℝ × ℝ) : field (c • P) x = c * field P x := by
  unfold field
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [smul_eq_mul]
  ring

/-- The field of `−P`. -/
theorem field_neg (P : RealPoly) (x : ℝ × ℝ) : field (-P) x = -field P x := by
  have := field_smul (-1) P x
  rwa [neg_one_smul, neg_one_mul] at this

/-- The field is `ℝ`-linear: finite sums. -/
theorem field_finset_sum {ι : Type*} (s : Finset ι) (f : ι → RealPoly) (x : ℝ × ℝ) :
    field (∑ i ∈ s, f i) x = ∑ i ∈ s, field (f i) x := by
  induction s using Finset.cons_induction with
  | empty => simp [field_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, field_add, ih]

/-! ## The stream function of a polynomial -/

/-- `1 ≤ |k|²` off the zero mode. -/
theorem one_le_lam {k : Wave} (hk : k ≠ 0) : (1 : ℝ) ≤ lam k := by exact_mod_cast lam_pos hk

/-- The support of `Δ⁻¹P` lies in the support of `P`. -/
theorem support_laplacianInv_subset (P : RealPoly) : (laplacianInv P).support ⊆ P.support :=
  fun k hk => by
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h
    simp [h] at hk

/-- `‖Δ⁻¹P‖_{ℓ¹} ≤ ‖P‖_{ℓ¹}`: every mode has `|k|² ≥ 1`. -/
theorem l1_laplacianInv_le (P : RealPoly) : l1 (laplacianInv P) ≤ l1 P := by
  rw [l1_eq_sum (support_laplacianInv_subset P), l1_eq_sum subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = 0
  · subst hk; simp
  · rw [laplacianInv_apply, if_neg hk, abs_neg, abs_div,
      abs_of_pos (show (0 : ℝ) < lam k by exact_mod_cast lam_pos hk)]
    exact div_le_self (abs_nonneg _) (one_le_lam hk)

/-- `Δ⁻¹` keeps the modes. -/
theorem sizeLE_laplacianInv {K : ℕ} {P : RealPoly} (hP : SizeLE K P) :
    SizeLE K (laplacianInv P) :=
  fun k hk => hP k (support_laplacianInv_subset P hk)

/-- A derivative sum of `Δ⁻¹P` read over the support of `P`: the coefficient at
`p` is `c_p P_p / |p|²` (the zero mode contributes nothing either way). -/
theorem sum_laplacianInv (P : RealPoly) (c f : Wave → ℝ) :
    ∑ k ∈ (laplacianInv P).support, -(c k * laplacianInv P k) * f k =
      ∑ p ∈ P.support, (c p * P p / lam p) * f p := by
  rw [Finset.sum_subset (support_laplacianInv_subset P) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk; simp [hk])]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p = 0
  · subst hp; simp [lam]
  · simp only [laplacianInv_apply, hp, if_false]
    ring

/-- `∂₁ ψ` for `ψ = field (Δ⁻¹P)`, over the support of `P`. -/
theorem fieldD₁_laplacianInv (P : RealPoly) (x : ℝ × ℝ) :
    fieldD₁ (laplacianInv P) x = ∑ p ∈ P.support, ((p.1 : ℝ) * P p / lam p) * sin (phase p x) :=
  sum_laplacianInv P (fun k => (k.1 : ℝ)) (fun k => sin (phase k x))

/-- `∂₂ ψ` for `ψ = field (Δ⁻¹P)`, over the support of `P`. -/
theorem fieldD₂_laplacianInv (P : RealPoly) (x : ℝ × ℝ) :
    fieldD₂ (laplacianInv P) x = ∑ p ∈ P.support, ((p.2 : ℝ) * P p / lam p) * sin (phase p x) :=
  sum_laplacianInv P (fun k => (k.2 : ℝ)) (fun k => sin (phase k x))

/-! ## The Jacobian identity -/

/-- Over the support of an even polynomial, `q ↦ −q` is a bijection. -/
theorem sum_support_neg {Q : RealPoly} (hQ : IsEven Q) (f : Wave → ℝ) :
    ∑ q ∈ Q.support, f q = ∑ q ∈ Q.support, f (-q) := by
  have mem : ∀ q, q ∈ Q.support → -q ∈ Q.support := fun q hq => by
    rw [Finsupp.mem_support_iff] at hq ⊢
    rwa [hQ q]
  refine Finset.sum_nbij' (fun q => -q) (fun q => -q) mem (fun q hq => by simpa using mem q hq)
    (fun q _ => neg_neg q) (fun q _ => neg_neg q) (fun q _ => ?_)
  simp

/-- The field of the transport as a double sum over the supports. -/
theorem field_transport_eq_sum (P Q : RealPoly) (x : ℝ × ℝ) :
    field (transport P Q) x =
      ∑ p ∈ P.support, ∑ q ∈ Q.support,
        (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
  rw [transport_eq_sum, Finsupp.sum, field_finset_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [field_smul, Finsupp.sum, field_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [field_smul, field_single]
  simp only [phase]
  ring

/-- **The Jacobian identity.** `field (transport P Q) = ∂₁ψ ∂₂q − ∂₂ψ ∂₁q` for
`ψ = field (laplacianInv P)`, `q = field Q`, when `Q` is even: the Lean tie
between the formal `transport` and the real `u·∇q` with `u = ∇⊥ψ = (−∂₂ψ, ∂₁ψ)`.
Nothing is assumed of `P`: at `p = 0` both sides' terms vanish. -/
theorem field_transport (P : RealPoly) {Q : RealPoly} (hQ : IsEven Q) (x : ℝ × ℝ) :
    field (transport P Q) x =
      fieldD₁ (laplacianInv P) x * fieldD₂ Q x - fieldD₂ (laplacianInv P) x * fieldD₁ Q x := by
  rw [field_transport_eq_sum, fieldD₁_laplacianInv, fieldD₂_laplacianInv, fieldD₁, fieldD₂,
    Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  -- the summand is `−coupling p q P_p Q_q sin(p·x) sin(q·x)`
  have step : ∀ q ∈ Q.support,
      (p.1 : ℝ) * P p / lam p * sin (phase p x) * (-((q.2 : ℝ) * Q q) * sin (phase q x)) -
        (p.2 : ℝ) * P p / lam p * sin (phase p x) * (-((q.1 : ℝ) * Q q) * sin (phase q x)) =
      -((coupling p q : ℝ) * P p * Q q) * (sin (phase p x) * sin (phase q x)) := by
    intro q _
    simp only [coupling, cross]
    push_cast
    ring
  rw [Finset.sum_congr rfl step]
  symm
  -- fold the `cos(a − b)` half by `q ↦ −q`
  have fold : ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase p x - phase q x) =
      -∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
    rw [sum_support_neg hQ, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coupling_neg_right, hQ q, phase_neg, phase_add]
    push_cast
    ring_nf
  calc ∑ q ∈ Q.support, -((coupling p q : ℝ) * P p * Q q) * (sin (phase p x) * sin (phase q x))
      = ∑ q ∈ Q.support,
          (-(1 / 2 : ℝ) * ((coupling p q : ℝ) * P p * Q q * cos (phase p x - phase q x))
            + (1 / 2 : ℝ) * ((coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [sin_mul_sin_eq, phase_add]; ring
    _ = -(1 / 2 : ℝ) *
            ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase p x - phase q x)
          + (1 / 2 : ℝ) *
            ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
        rw [fold]; ring


/-- A finite support radius bounds the derivative norm. -/
theorem dnorm_zero_le {K : ℕ} {P : RealPoly} (hK : SizeLE K P) :
    dnorm 0 P ≤ (K : ℝ) * l1 P := by
  rw [dnorm_eq_sum 0 subset_rfl, l1_eq_sum subset_rfl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  simp only [zero_mul, Real.exp_zero, mul_one]
  have hs : (size k : ℝ) ≤ K := by exact_mod_cast hK k hk
  nlinarith [abs_nonneg (P k)]

/-- The transport norm costs one derivative in its second argument. -/
theorem l1_transport_le {K : ℕ} (P : RealPoly) {Q : RealPoly} (hQ : SizeLE K Q) :
    l1 (transport P Q) ≤ (K : ℝ) * l1 P * l1 Q := by
  have h := wnorm_transport_le (σ := 0) le_rfl P Q
  rw [wnorm_zero, wnorm_zero] at h
  refine h.trans ?_
  have hb := mul_le_mul_of_nonneg_left (dnorm_zero_le hQ) (l1_nonneg P)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

/-- The Laplacian costs two spatial derivatives. -/
theorem l1_laplacian_le {K : ℕ} {P : RealPoly} (hP : SizeLE K P) :
    l1 (laplacian P) ≤ (K : ℝ) ^ 2 * l1 P := by
  have hs : (laplacian P).support ⊆ P.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro hz; exact hk (by simp [hz])
  rw [l1_eq_sum hs, l1_eq_sum subset_rfl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  simp only [laplacian_apply, abs_mul, abs_neg]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ lam k by exact_mod_cast Mild.lam_nonneg k)]
  have hl : (lam k : ℝ) ≤ (size k : ℝ) ^ 2 := by exact_mod_cast lam_le_size_sq k
  have hs' : (size k : ℝ) ≤ K := by exact_mod_cast hP k hk
  exact mul_le_mul_of_nonneg_right (hl.trans (by nlinarith [(Nat.cast_nonneg (size k) : (0 : ℝ) ≤ size k)])) (abs_nonneg _)

#print axioms field_transport
#print axioms field_laplacian
#print axioms l1_transport_le
end Gimle.Asgard.Streams.Mild.RealPoly
