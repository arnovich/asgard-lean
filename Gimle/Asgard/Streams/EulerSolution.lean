import Gimle.Asgard.Streams.EulerRadius
import Gimle.Asgard.Streams.Gevrey
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # The analytic field of the Euler stream is a classical solution

`TrigField` sums the formal vorticity stream's `t`-series to a real function,
`analyticField ω t x = Σ_n field (ω n) x tⁿ`, and bounds it. This module says
what that function is: on `|t| < 1/ρ`, for the Euler stream from an even,
mean-zero start, it is a classical solution of the vorticity equation
`∂_t ω + u·∇ω = 0` with `u = ∇⊥ψ`, `Δψ = ω`, every derivative taken pointwise.

The pieces are elementary once explicit. A trigonometric polynomial's field
has the partial derivatives `∂ᵢ field P x = −Σ_k kᵢ P_k sin(k·x)` (finite
sums, `HasDerivAt.sum`), second derivatives likewise, and
`field (laplacian P) = Δ (field P)`. The Jacobian identity
`field (transport P Q) = ∂₁ψ ∂₂q − ∂₂ψ ∂₁q` (`ψ = field (laplacianInv P)`,
`q = field Q`, `Q` even) is the heart: expanding the products of sines by
`sin a sin b = (cos(a − b) − cos(a + b))/2` and folding the `a − b` terms by
`q ↦ −q` turns the Jacobian into `Σ_{p,q} (p×q)/|p|² P_p Q_q cos((p+q)·x)`,
which is `transport_apply`. The series are differentiated termwise under the
geometric bound (`hasDerivAt_tsum_of_isPreconnected`): in `t` directly, in `x`
because the modes of `ω_n` have size at most `(n+1)K` (`sizeLE_stream`), so
the derivative coefficients are bounded by `(n+1) K M ρⁿ`. The Euler
recursion `euler_succ` then turns `∂_t` of the series into minus the Cauchy
product of the series of `ψ` and `ω`.

What stays on paper is said once, here: that the cosine field of an even
polynomial is the real exponential sum `Σ P_k e^{ik·x}`, and that the formal
`transport` is the Fourier side of the physical `u·∇ω` (its coupling was
derived by hand in `Torus`; the Jacobian identity below is the Lean tie
between `transport` and the real functions). -/

namespace Gimle.Asgard.Streams.Torus

open Real

/-! ## The phase and the partial derivatives of a field -/

/-- `k·x`. -/
noncomputable def phase (k : Wave) (x : ℝ × ℝ) : ℝ := k.1 * x.1 + k.2 * x.2

theorem phase_neg (k : Wave) (x : ℝ × ℝ) : phase (-k) x = -phase k x := by
  simp only [phase, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; ring

theorem phase_add (p q : Wave) (x : ℝ × ℝ) : phase (p + q) x = phase p x + phase q x := by
  simp only [phase, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

theorem field_eq_sum_phase (P : TrigPoly) (x : ℝ × ℝ) :
    field P x = ∑ k ∈ P.support, (P k : ℝ) * cos (phase k x) := rfl

/-- `∂₁ field P x = −Σ_k k₁ P_k sin(k·x)`. -/
noncomputable def fieldD₁ (P : TrigPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.1 : ℝ) * P k) * sin (phase k x)

/-- `∂₂ field P x = −Σ_k k₂ P_k sin(k·x)`. -/
noncomputable def fieldD₂ (P : TrigPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.2 : ℝ) * P k) * sin (phase k x)

/-- `∂₁∂₁ field P x = −Σ_k k₁² P_k cos(k·x)`. -/
noncomputable def fieldD₁₁ (P : TrigPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.1 : ℝ) * k.1 * P k) * cos (phase k x)

/-- `∂₂∂₂ field P x = −Σ_k k₂² P_k cos(k·x)`. -/
noncomputable def fieldD₂₂ (P : TrigPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.2 : ℝ) * k.2 * P k) * cos (phase k x)

/-- `∂₁∂₂ field P x = ∂₂∂₁ field P x = −Σ_k k₁ k₂ P_k cos(k·x)`. -/
noncomputable def fieldD₁₂ (P : TrigPoly) (x : ℝ × ℝ) : ℝ :=
  ∑ k ∈ P.support, -((k.1 : ℝ) * k.2 * P k) * cos (phase k x)

theorem hasDerivAt_phase_fst (k : Wave) (x : ℝ × ℝ) :
    HasDerivAt (fun s => phase k (s, x.2)) (k.1 : ℝ) x.1 := by
  simpa [phase] using ((hasDerivAt_id x.1).const_mul (k.1 : ℝ)).add_const ((k.2 : ℝ) * x.2)

theorem hasDerivAt_phase_snd (k : Wave) (x : ℝ × ℝ) :
    HasDerivAt (fun s => phase k (x.1, s)) (k.2 : ℝ) x.2 := by
  simpa [phase] using (((hasDerivAt_id x.2).const_mul (k.2 : ℝ)).const_add ((k.1 : ℝ) * x.1))

theorem hasDerivAt_field_fst (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => field P (s, x.2)) (fieldD₁ P x) x.1 := by
  simp only [field_eq_sum_phase, fieldD₁]
  refine HasDerivAt.fun_sum (A := fun k s => ((P k : ℚ) : ℝ) * cos (phase k (s, x.2))) (A' := fun k => -((k.1 : ℝ) * P k) * sin (phase k x)) fun k _ => ?_
  have h := (HasDerivAt.cos (hasDerivAt_phase_fst k x)).const_mul ((P k : ℚ) : ℝ)
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

theorem hasDerivAt_field_snd (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => field P (x.1, s)) (fieldD₂ P x) x.2 := by
  simp only [field_eq_sum_phase, fieldD₂]
  refine HasDerivAt.fun_sum (A := fun k s => ((P k : ℚ) : ℝ) * cos (phase k (x.1, s))) (A' := fun k => -((k.2 : ℝ) * P k) * sin (phase k x)) fun k _ => ?_
  have h := (HasDerivAt.cos (hasDerivAt_phase_snd k x)).const_mul ((P k : ℚ) : ℝ)
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

theorem hasDerivAt_fieldD₁_fst (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (s, x.2)) (fieldD₁₁ P x) x.1 := by
  simp only [fieldD₁, fieldD₁₁]
  refine HasDerivAt.fun_sum (A := fun k s => -((k.1 : ℝ) * P k) * sin (phase k (s, x.2))) (A' := fun k => -((k.1 : ℝ) * k.1 * P k) * cos (phase k x)) fun k _ => ?_
  have h := (HasDerivAt.sin (hasDerivAt_phase_fst k x)).const_mul (-((k.1 : ℝ) * P k))
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

theorem hasDerivAt_fieldD₂_snd (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₂ P (x.1, s)) (fieldD₂₂ P x) x.2 := by
  simp only [fieldD₂, fieldD₂₂]
  refine HasDerivAt.fun_sum (A := fun k s => -((k.2 : ℝ) * P k) * sin (phase k (x.1, s))) (A' := fun k => -((k.2 : ℝ) * k.2 * P k) * cos (phase k x)) fun k _ => ?_
  have h := (HasDerivAt.sin (hasDerivAt_phase_snd k x)).const_mul (-((k.2 : ℝ) * P k))
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

theorem hasDerivAt_fieldD₂_fst (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₂ P (s, x.2)) (fieldD₁₂ P x) x.1 := by
  simp only [fieldD₂, fieldD₁₂]
  refine HasDerivAt.fun_sum (A := fun k s => -((k.2 : ℝ) * P k) * sin (phase k (s, x.2))) (A' := fun k => -((k.1 : ℝ) * k.2 * P k) * cos (phase k x)) fun k _ => ?_
  have h := (HasDerivAt.sin (hasDerivAt_phase_fst k x)).const_mul (-((k.2 : ℝ) * P k))
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

theorem hasDerivAt_fieldD₁_snd (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (x.1, s)) (fieldD₁₂ P x) x.2 := by
  simp only [fieldD₁, fieldD₁₂]
  refine HasDerivAt.fun_sum (A := fun k s => -((k.1 : ℝ) * P k) * sin (phase k (x.1, s))) (A' := fun k => -((k.1 : ℝ) * k.2 * P k) * cos (phase k x)) fun k _ => ?_
  have h := (HasDerivAt.sin (hasDerivAt_phase_snd k x)).const_mul (-((k.1 : ℝ) * P k))
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

/-- `field (laplacian P) = ∂₁∂₁ field P + ∂₂∂₂ field P`. -/
theorem field_laplacian (P : TrigPoly) (x : ℝ × ℝ) :
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

/-! ## Bounds on the derivative fields -/

theorem abs_fieldD₁_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁ P x| ≤ K * l1 P := by
  rw [fieldD₁, l1_eq_sum subset_rfl]
  push_cast
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk1 : |(k.1 : ℝ)| ≤ K := by
    have := hP k hk
    rw [size] at this
    have h1 : k.1.natAbs ≤ K := le_trans (Nat.le_add_right _ _) this
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h1
  rw [abs_mul, abs_neg, abs_mul]
  calc |(k.1 : ℝ)| * |(P k : ℝ)| * |sin (phase k x)|
      ≤ |(k.1 : ℝ)| * |(P k : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (abs_sin_le_one _) (by positivity)
    _ ≤ K * |(P k : ℝ)| := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg _)

theorem abs_fieldD₂_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₂ P x| ≤ K * l1 P := by
  rw [fieldD₂, l1_eq_sum subset_rfl]
  push_cast
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk2 : |(k.2 : ℝ)| ≤ K := by
    have := hP k hk
    rw [size] at this
    have h2 : k.2.natAbs ≤ K := le_trans (Nat.le_add_left _ _) this
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h2
  rw [abs_mul, abs_neg, abs_mul]
  calc |(k.2 : ℝ)| * |(P k : ℝ)| * |sin (phase k x)|
      ≤ |(k.2 : ℝ)| * |(P k : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (abs_sin_le_one _) (by positivity)
    _ ≤ K * |(P k : ℝ)| := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right hk2 (abs_nonneg _)

/-- A second-derivative field is bounded by `K² l1 P` for modes of size `≤ K`. -/
theorem abs_fieldDD_le (K : ℕ) (P : TrigPoly) (x : ℝ × ℝ) (c : Wave → ℝ) (hc : ∀ k ∈ P.support, |c k| ≤ (K : ℝ) ^ 2) :
    |∑ k ∈ P.support, -(c k * P k) * cos (phase k x)| ≤ (K : ℝ) ^ 2 * l1 P := by
  rw [l1_eq_sum subset_rfl]
  push_cast
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_neg, abs_mul]
  calc |c k| * |(P k : ℝ)| * |cos (phase k x)|
      ≤ |c k| * |(P k : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (abs_cos_le_one _) (by positivity)
    _ ≤ (K : ℝ) ^ 2 * |(P k : ℝ)| := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (hc k hk) (abs_nonneg _)

theorem abs_coord_le_size {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) {k : Wave}
    (hk : k ∈ P.support) : |(k.1 : ℝ)| ≤ K ∧ |(k.2 : ℝ)| ≤ K := by
  have := hP k hk
  rw [size] at this
  constructor
  · rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Nat.le_add_right _ _) this
  · rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Nat.le_add_left _ _) this

theorem abs_fieldD₁₁_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁₁ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_fieldDD_le K P x (fun k => (k.1 : ℝ) * k.1) fun k hk => by
    rw [abs_mul, sq]
    exact mul_le_mul (abs_coord_le_size hP hk).1 (abs_coord_le_size hP hk).1
      (abs_nonneg _) (Nat.cast_nonneg _)

theorem abs_fieldD₂₂_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₂₂ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_fieldDD_le K P x (fun k => (k.2 : ℝ) * k.2) fun k hk => by
    rw [abs_mul, sq]
    exact mul_le_mul (abs_coord_le_size hP hk).2 (abs_coord_le_size hP hk).2
      (abs_nonneg _) (Nat.cast_nonneg _)

theorem abs_fieldD₁₂_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁₂ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_fieldDD_le K P x (fun k => (k.1 : ℝ) * k.2) fun k hk => by
    rw [abs_mul, sq]
    exact mul_le_mul (abs_coord_le_size hP hk).1 (abs_coord_le_size hP hk).2
      (abs_nonneg _) (Nat.cast_nonneg _)

/-! ## The Jacobian identity -/

/-- `sin a sin b = (cos(a − b) − cos(a + b))/2`. -/
theorem sin_mul_sin_eq (a b : ℝ) : sin a * sin b = (cos (a - b) - cos (a + b)) / 2 := by
  rw [cos_sub, cos_add]; ring

/-- Over the support of an even polynomial, `q ↦ −q` is a bijection. -/
theorem sum_support_neg {Q : TrigPoly} (hQ : IsEven Q) (f : Wave → ℝ) :
    ∑ q ∈ Q.support, f q = ∑ q ∈ Q.support, f (-q) := by
  have mem : ∀ q, q ∈ Q.support → -q ∈ Q.support := fun q hq => by
    rw [Finsupp.mem_support_iff] at hq ⊢
    rwa [hQ q]
  refine Finset.sum_nbij' (fun q => -q) (fun q => -q) mem (fun q hq => by simpa using mem q hq)
    (fun q _ => neg_neg q) (fun q _ => neg_neg q) (fun q _ => ?_)
  simp

/-- The support of `laplacianInv P` lies in the support of `P`. -/
theorem support_laplacianInv_subset (P : TrigPoly) : (laplacianInv P).support ⊆ P.support :=
  fun k hk => by
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h
    simp [h] at hk

theorem fieldD₁_laplacianInv (P : TrigPoly) (x : ℝ × ℝ) :
    fieldD₁ (laplacianInv P) x =
      ∑ p ∈ P.support, ((p.1 : ℝ) * P p / lam p) * sin (phase p x) := by
  rw [fieldD₁, Finset.sum_subset (support_laplacianInv_subset P) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk; simp [hk])]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p = 0
  · subst hp; simp [lam]
  · simp only [laplacianInv_apply, hp, if_false]
    push_cast
    ring

theorem fieldD₂_laplacianInv (P : TrigPoly) (x : ℝ × ℝ) :
    fieldD₂ (laplacianInv P) x =
      ∑ p ∈ P.support, ((p.2 : ℝ) * P p / lam p) * sin (phase p x) := by
  rw [fieldD₂, Finset.sum_subset (support_laplacianInv_subset P) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk; simp [hk])]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p = 0
  · subst hp; simp [lam]
  · simp only [laplacianInv_apply, hp, if_false]
    push_cast
    ring

theorem field_zero (x : ℝ × ℝ) : field (0 : TrigPoly) x = 0 := by simp [field]

theorem field_smul (c : ℚ) (P : TrigPoly) (x : ℝ × ℝ) : field (c • P) x = c * field P x := by
  unfold field
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Rat.cast_mul, smul_eq_mul]
  ring

theorem field_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly) (x : ℝ × ℝ) :
    field (∑ i ∈ s, f i) x = ∑ i ∈ s, field (f i) x := by
  induction s using Finset.cons_induction with
  | empty => simp [field_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, field_add, ih]

/-- The field of the transport as a double sum over the supports. -/
theorem field_transport_eq_sum (P Q : TrigPoly) (x : ℝ × ℝ) :
    field (transport P Q) x =
      ∑ p ∈ P.support, ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
  rw [transport_eq_sum, Finsupp.sum, field_finset_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [field_smul, Finsupp.sum, field_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [field_smul, field_single]
  simp only [phase]
  ring

/-- **The Jacobian identity.** `field (transport P Q) = ∂₁ψ ∂₂q − ∂₂ψ ∂₁q` for
`ψ = field (laplacianInv P)`, `q = field Q`, when `Q` is even: the Lean tie
between the formal `transport` and the real `u·∇q` with `u = ∇⊥ψ`. -/
theorem field_transport (P : TrigPoly) {Q : TrigPoly} (hQ : IsEven Q) (x : ℝ × ℝ) :
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
      = ∑ q ∈ Q.support, (-(1 / 2 : ℝ) * ((coupling p q : ℝ) * P p * Q q * cos (phase p x - phase q x))
          + (1 / 2 : ℝ) * ((coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [sin_mul_sin_eq, phase_add]; ring
    _ = -(1 / 2 : ℝ) * ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase p x - phase q x)
          + (1 / 2 : ℝ) * ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ q ∈ Q.support, (coupling p q : ℝ) * P p * Q q * cos (phase (p + q) x) := by
        rw [fold]; ring

end Gimle.Asgard.Streams.Torus

namespace Gimle.Asgard.Streams.Torus

/-! ## The stream function of a polynomial -/

theorem one_le_lam {k : Wave} (hk : k ≠ 0) : (1 : ℚ) ≤ lam k := by
  have := lam_pos hk
  exact_mod_cast this

/-- `‖Δ⁻¹P‖_{ℓ¹} ≤ ‖P‖_{ℓ¹}`: every mode has `|k|² ≥ 1`. -/
theorem l1_laplacianInv_le (P : TrigPoly) : l1 (laplacianInv P) ≤ l1 P := by
  rw [l1_eq_sum (support_laplacianInv_subset P), l1_eq_sum subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = 0
  · subst hk; simp
  · rw [laplacianInv_apply, if_neg hk, abs_neg, abs_div,
      abs_of_pos (show (0 : ℚ) < lam k by exact_mod_cast lam_pos hk)]
    exact div_le_self (abs_nonneg _) (one_le_lam hk)

theorem sizeLE_laplacianInv {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) : SizeLE K (laplacianInv P) :=
  fun k hk => hP k (support_laplacianInv_subset P hk)

theorem field_neg (P : TrigPoly) (x : ℝ × ℝ) : field (-P) x = -field P x := by
  have := field_smul (-1) P x
  rwa [neg_one_smul, Rat.cast_neg, Rat.cast_one, neg_one_mul] at this

end Gimle.Asgard.Streams.Torus

namespace Gimle.Asgard.Streams.TrigStream

open Torus Real

/-! ## The derivative series -/

/-- The stream-function stream `Δ⁻¹ ω_n`. -/
noncomputable def psi (ω : TrigStream) : TrigStream := fun n => laplacianInv (ω n)

theorem geometricBound_psi {ω : TrigStream} {M ρ : ℝ} (h : GeometricBound ω M ρ) :
    GeometricBound (psi ω) M ρ := fun n =>
  le_trans (by exact_mod_cast l1_laplacianInv_le (ω n)) (h n)

/-- `∂_t` of the field's series: `Σ_n (n+1) field ω_{n+1} tⁿ`. -/
noncomputable def seriesDt (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, field (ω (n + 1)) x * (((n : ℝ) + 1) * t ^ n)

/-- `∂₁` of the field's series. -/
noncomputable def seriesD₁ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₁ (ω n) x * t ^ n

/-- `∂₂` of the field's series. -/
noncomputable def seriesD₂ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₂ (ω n) x * t ^ n

noncomputable def seriesD₁₁ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₁₁ (ω n) x * t ^ n

noncomputable def seriesD₂₂ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₂₂ (ω n) x * t ^ n

noncomputable def seriesD₁₂ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₁₂ (ω n) x * t ^ n

/-! ## Summability -/

theorem summable_succ_mul_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * q ^ n := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q)
    (by rwa [Real.norm_eq_abs, abs_of_nonneg hq])
  have h0 := summable_geometric_of_lt_one hq hq1
  simpa [add_mul, pow_one] using h1.add h0

theorem summable_succ_sq_mul_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * q ^ n := by
  have hn : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hq]
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hn).mul_left 2
  have h0 := summable_geometric_of_lt_one hq hq1
  refine ((h2.add h1).add h0).congr fun n => ?_
  simp only [pow_one]
  ring

/-- A sequence bounded by `C (n+1) qⁿ` is absolutely summable. -/
theorem summable_norm_of_succ_bound {f : ℕ → ℝ} {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ n, |f n| ≤ C * (((n : ℝ) + 1) * q ^ n)) : Summable fun n => ‖f n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact hf n)
    ((summable_succ_mul_geometric hq hq1).mul_left C)

theorem summable_norm_of_succ_sq_bound {f : ℕ → ℝ} {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ n, |f n| ≤ C * (((n : ℝ) + 1) ^ 2 * q ^ n)) : Summable fun n => ‖f n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact hf n)
    ((summable_succ_sq_mul_geometric hq hq1).mul_left C)

variable {ω : TrigStream} {M ρ t : ℝ} {K : ℕ} {x : ℝ × ℝ}

/-- `ρ |t| < 1` is the open disc of convergence. -/
theorem mul_abs_lt_one (hρ : 0 < ρ) (ht : |t| < 1 / ρ) : ρ * |t| < 1 := by
  rwa [lt_div_iff₀ hρ, mul_comm] at ht

/-- The derivative coefficients are bounded by `K M (n+1) (ρ|t|)ⁿ`. -/
theorem abs_fieldD₁_mul_pow_le (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (n : ℕ) (y : ℝ × ℝ) :
    |fieldD₁ (ω n) y * t ^ n| ≤ (K * M) * (((n : ℝ) + 1) * (ρ * |t|) ^ n) := by
  have hM : 0 ≤ M := by
    have := h 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (by exact_mod_cast l1_nonneg _) this
  rw [abs_mul, abs_pow, mul_pow]
  have h1 : |fieldD₁ (ω n) y| ≤ ((n : ℝ) + 1) * K * (M * ρ ^ n) := by
    refine (abs_fieldD₁_le (hK n) y).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (h n) (by positivity)
  calc |fieldD₁ (ω n) y| * |t| ^ n ≤ ((n : ℝ) + 1) * K * (M * ρ ^ n) * |t| ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (K * M) * (((n : ℝ) + 1) * (ρ ^ n * |t| ^ n)) := by ring

theorem abs_fieldD₂_mul_pow_le (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (n : ℕ) (y : ℝ × ℝ) :
    |fieldD₂ (ω n) y * t ^ n| ≤ (K * M) * (((n : ℝ) + 1) * (ρ * |t|) ^ n) := by
  have hM : 0 ≤ M := by
    have := h 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (by exact_mod_cast l1_nonneg _) this
  rw [abs_mul, abs_pow, mul_pow]
  have h1 : |fieldD₂ (ω n) y| ≤ ((n : ℝ) + 1) * K * (M * ρ ^ n) := by
    refine (abs_fieldD₂_le (hK n) y).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (h n) (by positivity)
  calc |fieldD₂ (ω n) y| * |t| ^ n ≤ ((n : ℝ) + 1) * K * (M * ρ ^ n) * |t| ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (K * M) * (((n : ℝ) + 1) * (ρ ^ n * |t| ^ n)) := by ring

/-- The second-derivative coefficients are bounded by `K² M (n+1)² (ρ|t|)ⁿ`. -/
theorem abs_fieldDD_mul_pow_le (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (n : ℕ) (y : ℝ × ℝ)
    {D : TrigPoly → ℝ × ℝ → ℝ}
    (hD : ∀ (K' : ℕ) (P : TrigPoly), SizeLE K' P → |D P y| ≤ (K' : ℝ) ^ 2 * l1 P) :
    |D (ω n) y * t ^ n| ≤ ((K : ℝ) ^ 2 * M) * (((n : ℝ) + 1) ^ 2 * (ρ * |t|) ^ n) := by
  have hM : 0 ≤ M := by
    have := h 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (by exact_mod_cast l1_nonneg _) this
  rw [abs_mul, abs_pow, mul_pow]
  have h1 : |D (ω n) y| ≤ (((n : ℝ) + 1) * K) ^ 2 * (M * ρ ^ n) := by
    refine (hD _ _ (hK n)).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (h n) (by positivity)
  calc |D (ω n) y| * |t| ^ n ≤ (((n : ℝ) + 1) * K) ^ 2 * (M * ρ ^ n) * |t| ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((K : ℝ) ^ 2 * M) * (((n : ℝ) + 1) ^ 2 * (ρ ^ n * |t| ^ n)) := by ring

theorem summable_norm_D₁ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (y : ℝ × ℝ) :
    Summable fun n => ‖fieldD₁ (ω n) y * t ^ n‖ :=
  summable_norm_of_succ_bound (by positivity) (mul_abs_lt_one hρ ht)
    fun n => abs_fieldD₁_mul_pow_le h hK n y

theorem summable_norm_D₂ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (y : ℝ × ℝ) :
    Summable fun n => ‖fieldD₂ (ω n) y * t ^ n‖ :=
  summable_norm_of_succ_bound (by positivity) (mul_abs_lt_one hρ ht)
    fun n => abs_fieldD₂_mul_pow_le h hK n y

theorem summable_norm_field (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ)
    (y : ℝ × ℝ) : Summable fun n => ‖field (ω n) y * t ^ n‖ :=
  summable_norm_seriesTerm h hρ.le (mul_abs_lt_one hρ ht) le_rfl

/-! ## Termwise derivatives in `x` -/

theorem hasDerivAt_analyticField_fst (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ω t (s, x.2)) (seriesD₁ ω t x) x.1 := by
  have hu := (summable_succ_mul_geometric (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left (K * M)
  have := hasDerivAt_tsum (g := fun n s => field (ω n) (s, x.2) * t ^ n)
    (g' := fun n s => fieldD₁ (ω n) (s, x.2) * t ^ n) hu
    (fun n s => (hasDerivAt_field_fst (ω n) (s, x.2)).mul_const (t ^ n))
    (fun n s => by rw [Real.norm_eq_abs]; exact abs_fieldD₁_mul_pow_le h hK n (s, x.2))
    (y₀ := x.1) (summable_norm_field h hρ ht (x.1, x.2)).of_norm x.1
  simpa [analyticField, seriesTerm, seriesD₁] using this

theorem hasDerivAt_analyticField_snd (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ω t (x.1, s)) (seriesD₂ ω t x) x.2 := by
  have hu := (summable_succ_mul_geometric (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left (K * M)
  have := hasDerivAt_tsum (g := fun n s => field (ω n) (x.1, s) * t ^ n)
    (g' := fun n s => fieldD₂ (ω n) (x.1, s) * t ^ n) hu
    (fun n s => (hasDerivAt_field_snd (ω n) (x.1, s)).mul_const (t ^ n))
    (fun n s => by rw [Real.norm_eq_abs]; exact abs_fieldD₂_mul_pow_le h hK n (x.1, s))
    (y₀ := x.2) (summable_norm_field h hρ ht (x.1, x.2)).of_norm x.2
  simpa [analyticField, seriesTerm, seriesD₂] using this

theorem hasDerivAt_seriesD₁_fst (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₁ ω t (s, x.2)) (seriesD₁₁ ω t x) x.1 := by
  have hu := (summable_succ_sq_mul_geometric (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left ((K : ℝ) ^ 2 * M)
  have := hasDerivAt_tsum (g := fun n s => fieldD₁ (ω n) (s, x.2) * t ^ n)
    (g' := fun n s => fieldD₁₁ (ω n) (s, x.2) * t ^ n) hu
    (fun n s => (hasDerivAt_fieldD₁_fst (ω n) (s, x.2)).mul_const (t ^ n))
    (fun n s => by
      rw [Real.norm_eq_abs]
      exact abs_fieldDD_mul_pow_le h hK n (s, x.2) fun K' P hP => abs_fieldD₁₁_le hP _)
    (y₀ := x.1) (summable_norm_D₁ h hK hρ ht (x.1, x.2)).of_norm x.1
  simpa [seriesD₁, seriesD₁₁] using this

theorem hasDerivAt_seriesD₂_snd (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₂ ω t (x.1, s)) (seriesD₂₂ ω t x) x.2 := by
  have hu := (summable_succ_sq_mul_geometric (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left ((K : ℝ) ^ 2 * M)
  have := hasDerivAt_tsum (g := fun n s => fieldD₂ (ω n) (x.1, s) * t ^ n)
    (g' := fun n s => fieldD₂₂ (ω n) (x.1, s) * t ^ n) hu
    (fun n s => (hasDerivAt_fieldD₂_snd (ω n) (x.1, s)).mul_const (t ^ n))
    (fun n s => by
      rw [Real.norm_eq_abs]
      exact abs_fieldDD_mul_pow_le h hK n (x.1, s) fun K' P hP => abs_fieldD₂₂_le hP _)
    (y₀ := x.2) (summable_norm_D₂ h hK hρ ht (x.1, x.2)).of_norm x.2
  simpa [seriesD₂, seriesD₂₂] using this

theorem hasDerivAt_seriesD₂_fst (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₂ ω t (s, x.2)) (seriesD₁₂ ω t x) x.1 := by
  have hu := (summable_succ_sq_mul_geometric (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left ((K : ℝ) ^ 2 * M)
  have := hasDerivAt_tsum (g := fun n s => fieldD₂ (ω n) (s, x.2) * t ^ n)
    (g' := fun n s => fieldD₁₂ (ω n) (s, x.2) * t ^ n) hu
    (fun n s => (hasDerivAt_fieldD₂_fst (ω n) (s, x.2)).mul_const (t ^ n))
    (fun n s => by
      rw [Real.norm_eq_abs]
      exact abs_fieldDD_mul_pow_le h hK n (s, x.2) fun K' P hP => abs_fieldD₁₂_le hP _)
    (y₀ := x.1) (summable_norm_D₂ h hK hρ ht (x.1, x.2)).of_norm x.1
  simpa [seriesD₂, seriesD₁₂] using this

theorem hasDerivAt_seriesD₁_snd (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₁ ω t (x.1, s)) (seriesD₁₂ ω t x) x.2 := by
  have hu := (summable_succ_sq_mul_geometric (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left ((K : ℝ) ^ 2 * M)
  have := hasDerivAt_tsum (g := fun n s => fieldD₁ (ω n) (x.1, s) * t ^ n)
    (g' := fun n s => fieldD₁₂ (ω n) (x.1, s) * t ^ n) hu
    (fun n s => (hasDerivAt_fieldD₁_snd (ω n) (x.1, s)).mul_const (t ^ n))
    (fun n s => by
      rw [Real.norm_eq_abs]
      exact abs_fieldDD_mul_pow_le h hK n (x.1, s) fun K' P hP => abs_fieldD₁₂_le hP _)
    (y₀ := x.2) (summable_norm_D₁ h hK hρ ht (x.1, x.2)).of_norm x.2
  simpa [seriesD₁, seriesD₁₂] using this

/-! ## The termwise derivative in `t` -/

theorem summable_mul_pow_pred {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => (n : ℝ) * q ^ (n - 1) := by
  rw [← summable_nat_add_iff 1]
  refine (summable_succ_mul_geometric hq hq1).congr fun n => ?_
  simp

theorem hasDerivAt_analyticField_t (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ)
    (x : ℝ × ℝ) : HasDerivAt (fun s => analyticField ω s x) (seriesDt ω t x) t := by
  have hM : 0 ≤ M := by
    have := h 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (by exact_mod_cast l1_nonneg _) this
  -- the open disc `|s| < r` with `|t| < r < 1/ρ`
  set r : ℝ := (|t| + 1 / ρ) / 2 with hr
  have hrt : |t| < r := by rw [hr]; linarith
  have hr1 : ρ * r < 1 := by
    rw [hr]
    have : ρ * (1 / ρ) = 1 := mul_one_div_cancel hρ.ne'
    nlinarith [mul_abs_lt_one hρ ht]
  have hr0 : 0 ≤ r := (abs_nonneg t).trans hrt.le
  have hu : Summable fun n : ℕ => (M * ρ) * ((n : ℝ) * (ρ * r) ^ (n - 1)) :=
    (summable_mul_pow_pred (by positivity) hr1).mul_left (M * ρ)
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun n s => field (ω n) x * s ^ n)
    (g' := fun n s => field (ω n) x * ((n : ℝ) * s ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) r).isPreconnected
    (fun n s _ => (hasDerivAt_pow n s).const_mul (field (ω n) x))
    (fun n s hs => by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
      have h1 : |field (ω n) x| ≤ M * ρ ^ n := (abs_field_le_l1 _ _).trans (h n)
      have h2 : |s| ^ (n - 1) ≤ r ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg _) hs.le _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hρn : ρ ^ n = ρ * ρ ^ (n - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hn]
        rw [Nat.abs_cast]
        calc |field (ω n) x| * (n * |s| ^ (n - 1)) ≤ M * ρ ^ n * (n * r ^ (n - 1)) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n))
                (by positivity) (by positivity)
          _ = M * ρ * (n * (ρ * r) ^ (n - 1)) := by rw [hρn, mul_pow]; ring)
    (y₀ := t) (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hrt)
    (summable_norm_field h hρ ht x).of_norm
    (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hrt)
  -- reindex the derivative series
  have hs : Summable fun n : ℕ => field (ω n) x * ((n : ℝ) * t ^ (n - 1)) := by
    refine Summable.of_norm_bounded (g := fun n => (M * ρ) * ((n : ℝ) * (ρ * |t|) ^ (n - 1)))
      ((summable_mul_pow_pred (by positivity) (mul_abs_lt_one hρ ht)).mul_left (M * ρ)) ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have h1 : |field (ω n) x| ≤ M * ρ ^ n := (abs_field_le_l1 _ _).trans (h n)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hρn : ρ ^ n = ρ * ρ ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
      calc |field (ω n) x| * (n * |t| ^ (n - 1)) ≤ M * ρ ^ n * (n * |t| ^ (n - 1)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = M * ρ * (n * (ρ * |t|) ^ (n - 1)) := by rw [hρn, mul_pow]; ring
  have shift : (∑' n : ℕ, field (ω n) x * ((n : ℝ) * t ^ (n - 1))) = seriesDt ω t x := by
    rw [hs.tsum_eq_zero_add, seriesDt]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
  rw [← shift]
  exact key

/-! ## The Cauchy product of two series in `t` -/

theorem tsum_mul_tsum_pow {a b : ℕ → ℝ} (ha : Summable fun n => ‖a n * t ^ n‖)
    (hb : Summable fun n => ‖b n * t ^ n‖) :
    (∑' n, a n * t ^ n) * (∑' n, b n * t ^ n) =
      ∑' n, (∑ m ∈ Finset.range (n + 1), a m * b (n - m)) * t ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb]
  congr 1
  funext n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have : t ^ m * t ^ (n - m) = t ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hm)]
  calc a m * t ^ m * (b (n - m) * t ^ (n - m)) = a m * b (n - m) * (t ^ m * t ^ (n - m)) := by
        ring
    _ = a m * b (n - m) * t ^ n := by rw [this]

theorem summable_cauchy_pow {a b : ℕ → ℝ} (ha : Summable fun n => ‖a n * t ^ n‖)
    (hb : Summable fun n => ‖b n * t ^ n‖) :
    Summable fun n => (∑ m ∈ Finset.range (n + 1), a m * b (n - m)) * t ^ n := by
  have := (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_norm
  refine this.congr fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have : t ^ m * t ^ (n - m) = t ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hm)]
  calc a m * t ^ m * (b (n - m) * t ^ (n - m)) = a m * b (n - m) * (t ^ m * t ^ (n - m)) := by
        ring
    _ = a m * b (n - m) * t ^ n := by rw [this]

end Gimle.Asgard.Streams.TrigStream

namespace Gimle.Asgard.Streams.NS

open Torus TrigStream Real

variable (b : TrigStream)

local notation "ω" => stream Basis.ogf 0 b

/-- `(n+1) field ω_{n+1} = −Σ_{m ≤ n} (∂₁ψ_m ∂₂ω_{n−m} − ∂₂ψ_m ∂₁ω_{n−m})`: the Euler
recursion read through the Jacobian identity. -/
theorem succ_field_eq (hbe : IsEven (b 0)) (n : ℕ) (x : ℝ × ℝ) :
    ((n : ℝ) + 1) * field (ω (n + 1)) x =
      -(∑ m ∈ Finset.range (n + 1), fieldD₁ (psi ω m) x * fieldD₂ (ω (n - m)) x -
        ∑ m ∈ Finset.range (n + 1), fieldD₂ (psi ω m) x * fieldD₁ (ω (n - m)) x) := by
  rw [euler_succ, field_neg, field_smul, field_finset_sum, ← Finset.sum_sub_distrib]
  have ne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, mul_neg,
    ← mul_assoc, mul_inv_cancel₀ ne, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  exact field_transport (ω m) (stream_isEven .ogf 0 hbe (n - m)) x

/-- **The Euler equation for the analytic field.** On `|t| < 1/ρ`, for the Euler stream
from an even start with a geometric bound and modes of size at most `K`,
`∂_t F = −(∂₁Ψ ∂₂F − ∂₂Ψ ∂₁F)` where `F` is the analytic field and `Ψ` its stream function. -/
theorem seriesDt_eq (hbe : IsEven (b 0)) {K : ℕ} (hK : SizeLE K (b 0)) {M ρ t : ℝ}
    (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    seriesDt ω t x =
      -(seriesD₁ (psi ω) t x * seriesD₂ ω t x - seriesD₂ (psi ω) t x * seriesD₁ ω t x) := by
  have hKn : ∀ n, SizeLE ((n + 1) * K) (ω n) := sizeLE_stream 0 b hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  have s1 := summable_norm_D₁ hψ hKψ hρ ht x
  have s2 := summable_norm_D₂ h hKn hρ ht x
  have s3 := summable_norm_D₂ hψ hKψ hρ ht x
  have s4 := summable_norm_D₁ h hKn hρ ht x
  rw [seriesD₁, seriesD₂, seriesD₂, seriesD₁, tsum_mul_tsum_pow s1 s2, tsum_mul_tsum_pow s3 s4,
    ← (summable_cauchy_pow s1 s2).tsum_sub (summable_cauchy_pow s3 s4), ← tsum_neg, seriesDt]
  congr 1
  funext n
  rw [← sub_mul, ← neg_mul, ← succ_field_eq b hbe n x]
  ring

/-- `ΔΨ = F` termwise: the Laplacian of the stream function is the field. -/
theorem seriesD₁₁_psi_add_seriesD₂₂_psi (hb0 : MeanZero (b 0)) {K : ℕ} (hK : SizeLE K (b 0))
    {M ρ t : ℝ} (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    seriesD₁₁ (psi ω) t x + seriesD₂₂ (psi ω) t x = analyticField ω t x := by
  have hKn : ∀ n, SizeLE ((n + 1) * K) (ω n) := sizeLE_stream 0 b hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  have hq : ρ * |t| < 1 := mul_abs_lt_one hρ ht
  have s1 : Summable fun n => fieldD₁₁ (psi ω n) x * t ^ n :=
    (summable_norm_of_succ_sq_bound (by positivity) hq fun n =>
      abs_fieldDD_mul_pow_le hψ hKψ n x fun K' P hP => abs_fieldD₁₁_le hP _).of_norm
  have s2 : Summable fun n => fieldD₂₂ (psi ω n) x * t ^ n :=
    (summable_norm_of_succ_sq_bound (by positivity) hq fun n =>
      abs_fieldDD_mul_pow_le hψ hKψ n x fun K' P hP => abs_fieldD₂₂_le hP _).of_norm
  rw [seriesD₁₁, seriesD₂₂, ← s1.tsum_add s2, analyticField]
  congr 1
  funext n
  rw [seriesTerm, ← add_mul, ← field_laplacian, psi, laplacian_laplacianInv (stream_meanZero .ogf 0 hb0 n)]

/-- At `t = 0` the analytic field is the field of the start. -/
theorem analyticField_zero (x : ℝ × ℝ) : analyticField ω 0 x = field (b 0) x := by
  rw [analyticField, tsum_eq_single 0]
  · simp [seriesTerm, stream_slice]
  · intro n hn
    simp [seriesTerm, hn]

/-- **The analytic field of the Euler stream is a classical solution.** For an even,
mean-zero start with modes of size at most `K` and a geometric bound `l1 ω_n ≤ M ρⁿ`,
on `|t| < 1/ρ` and at every `x`: the field `F = analyticField ω` and its stream function
`Ψ = analyticField (psi ω)` have the partial derivatives named here, `ΔΨ = F`, the velocity
`u = ∇⊥Ψ = (−∂₂Ψ, ∂₁Ψ)` is divergence-free, and `∂_t F + u·∇F = 0`. -/
theorem euler_classical (hb0 : MeanZero (b 0)) (hbe : IsEven (b 0)) {K : ℕ} (hK : SizeLE K (b 0))
    {M ρ t : ℝ} (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    -- the field's derivatives
    HasDerivAt (fun s => analyticField ω s x) (seriesDt ω t x) t ∧
    HasDerivAt (fun s => analyticField ω t (s, x.2)) (seriesD₁ ω t x) x.1 ∧
    HasDerivAt (fun s => analyticField ω t (x.1, s)) (seriesD₂ ω t x) x.2 ∧
    -- the stream function's first and second derivatives
    HasDerivAt (fun s => analyticField (psi ω) t (s, x.2)) (seriesD₁ (psi ω) t x) x.1 ∧
    HasDerivAt (fun s => analyticField (psi ω) t (x.1, s)) (seriesD₂ (psi ω) t x) x.2 ∧
    HasDerivAt (fun s => seriesD₁ (psi ω) t (s, x.2)) (seriesD₁₁ (psi ω) t x) x.1 ∧
    HasDerivAt (fun s => seriesD₂ (psi ω) t (x.1, s)) (seriesD₂₂ (psi ω) t x) x.2 ∧
    HasDerivAt (fun s => seriesD₂ (psi ω) t (s, x.2)) (seriesD₁₂ (psi ω) t x) x.1 ∧
    HasDerivAt (fun s => seriesD₁ (psi ω) t (x.1, s)) (seriesD₁₂ (psi ω) t x) x.2 ∧
    -- `ΔΨ = F`, `div u = 0` and the vorticity equation
    seriesD₁₁ (psi ω) t x + seriesD₂₂ (psi ω) t x = analyticField ω t x ∧
    -seriesD₁₂ (psi ω) t x + seriesD₁₂ (psi ω) t x = 0 ∧
    seriesDt ω t x +
      (-seriesD₂ (psi ω) t x * seriesD₁ ω t x + seriesD₁ (psi ω) t x * seriesD₂ ω t x) = 0 := by
  have hKn : ∀ n, SizeLE ((n + 1) * K) (ω n) := sizeLE_stream 0 b hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  refine ⟨hasDerivAt_analyticField_t h hρ ht x, hasDerivAt_analyticField_fst h hKn hρ ht x,
    hasDerivAt_analyticField_snd h hKn hρ ht x, hasDerivAt_analyticField_fst hψ hKψ hρ ht x,
    hasDerivAt_analyticField_snd hψ hKψ hρ ht x, hasDerivAt_seriesD₁_fst hψ hKψ hρ ht x,
    hasDerivAt_seriesD₂_snd hψ hKψ hρ ht x, hasDerivAt_seriesD₂_fst hψ hKψ hρ ht x,
    hasDerivAt_seriesD₁_snd hψ hKψ hρ ht x,
    seriesD₁₁_psi_add_seriesD₂₂_psi b hb0 hK h hρ ht x, by ring, ?_⟩
  rw [seriesDt_eq b hbe hK h hρ ht x]
  ring

end Gimle.Asgard.Streams.NS

#print axioms Gimle.Asgard.Streams.Torus.field_transport
#print axioms Gimle.Asgard.Streams.Torus.field_laplacian
#print axioms Gimle.Asgard.Streams.TrigStream.hasDerivAt_analyticField_t
#print axioms Gimle.Asgard.Streams.NS.seriesDt_eq
#print axioms Gimle.Asgard.Streams.NS.euler_classical
