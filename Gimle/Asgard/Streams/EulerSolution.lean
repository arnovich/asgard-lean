import Gimle.Asgard.Streams.EulerRadius
import Gimle.Asgard.Streams.Gevrey
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # The analytic field of the Euler stream is a classical solution

`TrigField` sums the formal vorticity stream's `t`-series to a real function,
`analyticField ω t x = Σ_n field (ω n) x tⁿ`, and bounds it. This module says
what that function is. On `|t| < 1/ρ`, for the Euler stream from an even,
mean-zero start, it is a classical solution of the vorticity equation
`∂_t ω + u·∇ω = 0` with `u = ∇⊥ψ`, `Δψ = ω`: the field `F` and its stream
function `Ψ` have the partial derivatives that appear (`F` in `t` and in each
`x` coordinate, `Ψ` to second order in `x`), every one the sum of the termwise
derivatives and continuous in `(t, x)`, and the equations hold at every point
(`NS.euler_classical`, a `NS.IsClassicalSolution`).

The pieces are elementary once explicit. A trigonometric polynomial's field
has the partial derivatives `∂ᵢ field P x = −Σ_k kᵢ P_k sin(k·x)` (finite
sums, `HasDerivAt.fun_sum`), second derivatives likewise, and
`field (laplacian P) = Δ (field P)`. The **Jacobian identity**
`field (transport P Q) = ∂₁ψ ∂₂q − ∂₂ψ ∂₁q` (`ψ = field (laplacianInv P)`,
`q = field Q`, `Q` even) is the heart: expanding the products of sines by
`sin a sin b = (cos(a − b) − cos(a + b))/2` and folding the `a − b` terms by
`q ↦ −q` turns the Jacobian into `Σ_{p,q} (p×q)/|p|² P_p Q_q cos((p+q)·x)`,
which is `transport_apply`. The series are differentiated termwise under the
geometric bound (`hasDerivAt_tsum`, `hasDerivAt_tsum_of_isPreconnected`): in
`x` because the modes of `ω_n` have size at most `(n+1)K` (`sizeLE_stream`),
so the derivative coefficients are bounded by `(n+1) K M ρⁿ`, and continuity
comes from the same bounds on every strip `|t| ≤ r < 1/ρ` (`continuousOn_tsum`).
The Euler recursion `euler_succ` then turns `∂_t` of the series into minus the
Cauchy product of the series of `ψ` and `ω`.

Nothing about the real equation stays on paper: `F`, `Ψ` and `u = (−∂₂Ψ, ∂₁Ψ)`
are real functions defined here and the equation is proved for them. What is
not stated: regularity beyond the derivatives named (no joint Fréchet
derivative, no higher order), the velocity form of the equation and its
pressure, and uniqueness among classical solutions. The reading of a
`TrigPoly` as `Σ P_k e^{ik·x}`, whose real part `field` is, names the
coefficients the tables and the Galerkin family use; it plays no part in this
theorem. -/

namespace Gimle.Asgard.Streams.Torus

open Real

/-! ## The phase and the partial derivatives of a field -/

/-- `k·x`. -/
noncomputable def phase (k : Wave) (x : ℝ × ℝ) : ℝ := k.1 * x.1 + k.2 * x.2

/-- `(−k)·x = −(k·x)`. -/
theorem phase_neg (k : Wave) (x : ℝ × ℝ) : phase (-k) x = -phase k x := by
  simp only [phase, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]; ring

/-- `(p + q)·x = p·x + q·x`. -/
theorem phase_add (p q : Wave) (x : ℝ × ℝ) : phase (p + q) x = phase p x + phase q x := by
  simp only [phase, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

/-- `field P x` as a sum over the support with the phase named. -/
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

/-- The phase is linear in the first coordinate with slope `k₁`. -/
theorem hasDerivAt_phase_fst (k : Wave) (x : ℝ × ℝ) :
    HasDerivAt (fun s => phase k (s, x.2)) (k.1 : ℝ) x.1 := by
  simpa [phase] using ((hasDerivAt_id x.1).const_mul (k.1 : ℝ)).add_const ((k.2 : ℝ) * x.2)

/-- The phase is linear in the second coordinate with slope `k₂`. -/
theorem hasDerivAt_phase_snd (k : Wave) (x : ℝ × ℝ) :
    HasDerivAt (fun s => phase k (x.1, s)) (k.2 : ℝ) x.2 := by
  simpa [phase] using (((hasDerivAt_id x.2).const_mul (k.2 : ℝ)).const_add ((k.1 : ℝ) * x.1))

/-- A cosine sum's derivative in the first coordinate. -/
theorem hasDerivAt_sum_cos_fst (s : Finset Wave) (c : Wave → ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => ∑ k ∈ s, c k * cos (phase k (s', x.2)))
      (∑ k ∈ s, -(c k * k.1) * sin (phase k x)) x.1 := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := (HasDerivAt.cos (hasDerivAt_phase_fst k x)).const_mul (c k)
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

/-- A cosine sum's derivative in the second coordinate. -/
theorem hasDerivAt_sum_cos_snd (s : Finset Wave) (c : Wave → ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => ∑ k ∈ s, c k * cos (phase k (x.1, s')))
      (∑ k ∈ s, -(c k * k.2) * sin (phase k x)) x.2 := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := (HasDerivAt.cos (hasDerivAt_phase_snd k x)).const_mul (c k)
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

/-- A sine sum's derivative in the first coordinate. -/
theorem hasDerivAt_sum_sin_fst (s : Finset Wave) (c : Wave → ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => ∑ k ∈ s, c k * sin (phase k (s', x.2)))
      (∑ k ∈ s, (c k * k.1) * cos (phase k x)) x.1 := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := (HasDerivAt.sin (hasDerivAt_phase_fst k x)).const_mul (c k)
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

/-- A sine sum's derivative in the second coordinate. -/
theorem hasDerivAt_sum_sin_snd (s : Finset Wave) (c : Wave → ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun s' => ∑ k ∈ s, c k * sin (phase k (x.1, s')))
      (∑ k ∈ s, (c k * k.2) * cos (phase k x)) x.2 := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h := (HasDerivAt.sin (hasDerivAt_phase_snd k x)).const_mul (c k)
  convert h using 1
  · rfl
  · simp only [Prod.mk.eta]; ring

/-- `∂₁ field P = fieldD₁ P`. -/
theorem hasDerivAt_field_fst (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => field P (s, x.2)) (fieldD₁ P x) x.1 :=
  (hasDerivAt_sum_cos_fst P.support (fun k => (P k : ℝ)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₂ field P = fieldD₂ P`. -/
theorem hasDerivAt_field_snd (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => field P (x.1, s)) (fieldD₂ P x) x.2 :=
  (hasDerivAt_sum_cos_snd P.support (fun k => (P k : ℝ)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₁ fieldD₁ P = fieldD₁₁ P`. -/
theorem hasDerivAt_fieldD₁_fst (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (s, x.2)) (fieldD₁₁ P x) x.1 :=
  (hasDerivAt_sum_sin_fst P.support (fun k => -((k.1 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₂ fieldD₂ P = fieldD₂₂ P`. -/
theorem hasDerivAt_fieldD₂_snd (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₂ P (x.1, s)) (fieldD₂₂ P x) x.2 :=
  (hasDerivAt_sum_sin_snd P.support (fun k => -((k.2 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₁ fieldD₂ P = fieldD₁₂ P`. -/
theorem hasDerivAt_fieldD₂_fst (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₂ P (s, x.2)) (fieldD₁₂ P x) x.1 :=
  (hasDerivAt_sum_sin_fst P.support (fun k => -((k.2 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

/-- `∂₂ fieldD₁ P = fieldD₁₂ P`: the mixed derivatives agree. -/
theorem hasDerivAt_fieldD₁_snd (P : TrigPoly) (x : ℝ × ℝ) :
    HasDerivAt (fun s => fieldD₁ P (x.1, s)) (fieldD₁₂ P x) x.2 :=
  (hasDerivAt_sum_sin_snd P.support (fun k => -((k.1 : ℝ) * P k)) x).congr_deriv
    (Finset.sum_congr rfl fun k _ => by ring)

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

/-! ## Continuity of a field and its derivatives -/

/-- The phase is continuous. -/
theorem continuous_phase (k : Wave) : Continuous (phase k) := by
  unfold phase
  fun_prop

/-- The field is continuous. -/
theorem continuous_field (P : TrigPoly) : Continuous (field P) := by
  have : field P = fun x => ∑ k ∈ P.support, (P k : ℝ) * cos (phase k x) := by
    funext x; exact field_eq_sum_phase P x
  rw [this]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

/-- The derivative fields are continuous. -/
theorem continuous_fieldD₁ (P : TrigPoly) : Continuous (fieldD₁ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_sin.comp (continuous_phase k))

theorem continuous_fieldD₂ (P : TrigPoly) : Continuous (fieldD₂ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_sin.comp (continuous_phase k))

theorem continuous_fieldD₁₁ (P : TrigPoly) : Continuous (fieldD₁₁ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

theorem continuous_fieldD₂₂ (P : TrigPoly) : Continuous (fieldD₂₂ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

theorem continuous_fieldD₁₂ (P : TrigPoly) : Continuous (fieldD₁₂ P) :=
  continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Real.continuous_cos.comp (continuous_phase k))

/-! ## Bounds on the derivative fields -/

/-- Each coordinate of a mode of size at most `K` is at most `K`. -/
theorem abs_coord_le_size {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) {k : Wave}
    (hk : k ∈ P.support) : |(k.1 : ℝ)| ≤ K ∧ |(k.2 : ℝ)| ≤ K := by
  have := hP k hk
  rw [size] at this
  constructor
  · rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Nat.le_add_right _ _) this
  · rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Nat.le_add_left _ _) this

/-- A sum `Σ_k −(c_k P_k) f_k` with `|c_k| ≤ B` and `|f_k| ≤ 1` is at most `B · l1 P`. -/
theorem abs_sum_mul_le {P : TrigPoly} {B : ℝ} (c f : Wave → ℝ)
    (hc : ∀ k ∈ P.support, |c k| ≤ B) (hf : ∀ k, |f k| ≤ 1) :
    |∑ k ∈ P.support, -(c k * P k) * f k| ≤ B * l1 P := by
  rw [l1_eq_sum subset_rfl]
  push_cast
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_neg, abs_mul]
  calc |c k| * |(P k : ℝ)| * |f k| ≤ |c k| * |(P k : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (hf k) (by positivity)
    _ ≤ B * |(P k : ℝ)| := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (hc k hk) (abs_nonneg _)

/-- `|∂₁ field P x| ≤ K · l1 P` for modes of size at most `K`. -/
theorem abs_fieldD₁_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁ P x| ≤ K * l1 P :=
  abs_sum_mul_le (fun k => (k.1 : ℝ)) (fun k => sin (phase k x))
    (fun _ hk => (abs_coord_le_size hP hk).1) fun _ => abs_sin_le_one _

/-- `|∂₂ field P x| ≤ K · l1 P` for modes of size at most `K`. -/
theorem abs_fieldD₂_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₂ P x| ≤ K * l1 P :=
  abs_sum_mul_le (fun k => (k.2 : ℝ)) (fun k => sin (phase k x))
    (fun _ hk => (abs_coord_le_size hP hk).2) fun _ => abs_sin_le_one _

/-- The second-derivative fields are at most `K² · l1 P`. -/
theorem abs_fieldD₁₁_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁₁ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_sum_mul_le (fun k => (k.1 : ℝ) * k.1) (fun k => cos (phase k x))
    (fun _ hk => by
      rw [abs_mul, sq]
      exact mul_le_mul (abs_coord_le_size hP hk).1 (abs_coord_le_size hP hk).1 (abs_nonneg _)
        (Nat.cast_nonneg _))
    fun _ => abs_cos_le_one _

theorem abs_fieldD₂₂_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₂₂ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_sum_mul_le (fun k => (k.2 : ℝ) * k.2) (fun k => cos (phase k x))
    (fun _ hk => by
      rw [abs_mul, sq]
      exact mul_le_mul (abs_coord_le_size hP hk).2 (abs_coord_le_size hP hk).2 (abs_nonneg _)
        (Nat.cast_nonneg _))
    fun _ => abs_cos_le_one _

theorem abs_fieldD₁₂_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) (x : ℝ × ℝ) :
    |fieldD₁₂ P x| ≤ (K : ℝ) ^ 2 * l1 P :=
  abs_sum_mul_le (fun k => (k.1 : ℝ) * k.2) (fun k => cos (phase k x))
    (fun _ hk => by
      rw [abs_mul, sq]
      exact mul_le_mul (abs_coord_le_size hP hk).1 (abs_coord_le_size hP hk).2 (abs_nonneg _)
        (Nat.cast_nonneg _))
    fun _ => abs_cos_le_one _

/-! ## Linearity of the field -/

theorem field_zero (x : ℝ × ℝ) : field (0 : TrigPoly) x = 0 := by simp [field]

/-- The field is `ℚ`-linear: scaling. -/
theorem field_smul (c : ℚ) (P : TrigPoly) (x : ℝ × ℝ) : field (c • P) x = c * field P x := by
  unfold field
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Rat.cast_mul, smul_eq_mul]
  ring

/-- The field of `−P`. -/
theorem field_neg (P : TrigPoly) (x : ℝ × ℝ) : field (-P) x = -field P x := by
  have := field_smul (-1) P x
  rwa [neg_one_smul, Rat.cast_neg, Rat.cast_one, neg_one_mul] at this

/-- The field is `ℚ`-linear: finite sums. -/
theorem field_finset_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly) (x : ℝ × ℝ) :
    field (∑ i ∈ s, f i) x = ∑ i ∈ s, field (f i) x := by
  induction s using Finset.cons_induction with
  | empty => simp [field_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, field_add, ih]

/-! ## The stream function of a polynomial -/

/-- `1 ≤ |k|²` off the zero mode. -/
theorem one_le_lam {k : Wave} (hk : k ≠ 0) : (1 : ℚ) ≤ lam k := by exact_mod_cast lam_pos hk

/-- The support of `Δ⁻¹P` lies in the support of `P`. -/
theorem support_laplacianInv_subset (P : TrigPoly) : (laplacianInv P).support ⊆ P.support :=
  fun k hk => by
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h
    simp [h] at hk

/-- `‖Δ⁻¹P‖_{ℓ¹} ≤ ‖P‖_{ℓ¹}`: every mode has `|k|² ≥ 1`. -/
theorem l1_laplacianInv_le (P : TrigPoly) : l1 (laplacianInv P) ≤ l1 P := by
  rw [l1_eq_sum (support_laplacianInv_subset P), l1_eq_sum subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = 0
  · subst hk; simp
  · rw [laplacianInv_apply, if_neg hk, abs_neg, abs_div,
      abs_of_pos (show (0 : ℚ) < lam k by exact_mod_cast lam_pos hk)]
    exact div_le_self (abs_nonneg _) (one_le_lam hk)

/-- `Δ⁻¹` keeps the modes. -/
theorem sizeLE_laplacianInv {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) :
    SizeLE K (laplacianInv P) :=
  fun k hk => hP k (support_laplacianInv_subset P hk)

/-- A derivative sum of `Δ⁻¹P` read over the support of `P`: the coefficient at
`p` is `c_p P_p / |p|²` (the zero mode contributes nothing either way). -/
theorem sum_laplacianInv (P : TrigPoly) (c f : Wave → ℝ) :
    ∑ k ∈ (laplacianInv P).support, -(c k * laplacianInv P k) * f k =
      ∑ p ∈ P.support, (c p * P p / lam p) * f p := by
  rw [Finset.sum_subset (support_laplacianInv_subset P) (fun k _ hk => by
    simp only [Finsupp.mem_support_iff, not_not] at hk; simp [hk])]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p = 0
  · subst hp; simp [lam]
  · simp only [laplacianInv_apply, hp, if_false]
    push_cast
    ring

/-- `∂₁ ψ` for `ψ = field (Δ⁻¹P)`, over the support of `P`. -/
theorem fieldD₁_laplacianInv (P : TrigPoly) (x : ℝ × ℝ) :
    fieldD₁ (laplacianInv P) x = ∑ p ∈ P.support, ((p.1 : ℝ) * P p / lam p) * sin (phase p x) :=
  sum_laplacianInv P (fun k => (k.1 : ℝ)) (fun k => sin (phase k x))

/-- `∂₂ ψ` for `ψ = field (Δ⁻¹P)`, over the support of `P`. -/
theorem fieldD₂_laplacianInv (P : TrigPoly) (x : ℝ × ℝ) :
    fieldD₂ (laplacianInv P) x = ∑ p ∈ P.support, ((p.2 : ℝ) * P p / lam p) * sin (phase p x) :=
  sum_laplacianInv P (fun k => (k.2 : ℝ)) (fun k => sin (phase k x))

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

/-- The field of the transport as a double sum over the supports. -/
theorem field_transport_eq_sum (P Q : TrigPoly) (x : ℝ × ℝ) :
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

end Gimle.Asgard.Streams.Torus

namespace Gimle.Asgard.Streams.TrigStream

open Torus Real

/-! ## The derivative series -/

/-- The stream-function stream `Δ⁻¹ ω_n`; its analytic field is the stream function `Ψ`. -/
noncomputable def psi (ω : TrigStream) : TrigStream := fun n => laplacianInv (ω n)

/-- The stream function inherits the geometric bound. -/
theorem geometricBound_psi {ω : TrigStream} {M ρ : ℝ} (h : GeometricBound ω M ρ) :
    GeometricBound (psi ω) M ρ := fun n =>
  le_trans (by exact_mod_cast l1_laplacianInv_le (ω n)) (h n)

/-- A geometric bound has a nonnegative constant: `0 ≤ l1 ω₀ ≤ M`. -/
theorem GeometricBound.nonneg {ω : TrigStream} {M ρ : ℝ} (h : GeometricBound ω M ρ) : 0 ≤ M := by
  have := h 0
  simp only [pow_zero, mul_one] at this
  exact le_trans (by exact_mod_cast l1_nonneg _) this

/-- `∂_t` of the field's series: `Σ_n (n+1) field ω_{n+1} tⁿ`. -/
noncomputable def seriesDt (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, field (ω (n + 1)) x * (((n : ℝ) + 1) * t ^ n)

/-- `∂₁` of the field's series. -/
noncomputable def seriesD₁ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₁ (ω n) x * t ^ n

/-- `∂₂` of the field's series. -/
noncomputable def seriesD₂ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₂ (ω n) x * t ^ n

/-- `∂₁∂₁` of the field's series. -/
noncomputable def seriesD₁₁ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₁₁ (ω n) x * t ^ n

/-- `∂₂∂₂` of the field's series. -/
noncomputable def seriesD₂₂ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₂₂ (ω n) x * t ^ n

/-- `∂₁∂₂ = ∂₂∂₁` of the field's series. -/
noncomputable def seriesD₁₂ (ω : TrigStream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, fieldD₁₂ (ω n) x * t ^ n

/-! ## Summability -/

/-- `Σ_n (n+1)^k qⁿ` converges for `0 ≤ q < 1`. -/
theorem summable_succ_pow_mul_geometric (k : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ k * q ^ n := by
  rcases hq.lt_or_eq with hq0 | hq0
  · have hn : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hq0]
    have h := (summable_nat_add_iff (f := fun m : ℕ => (m : ℝ) ^ k * q ^ m) 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one k hn)
    refine (h.mul_left q⁻¹).congr fun n => ?_
    show q⁻¹ * (((n + 1 : ℕ) : ℝ) ^ k * q ^ (n + 1)) = ((n : ℝ) + 1) ^ k * q ^ n
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show q⁻¹ * (((n : ℝ) + 1) ^ k * (q ^ n * q)) = ((n : ℝ) + 1) ^ k * q ^ n * (q⁻¹ * q) by ring,
      inv_mul_cancel₀ hq0.ne', mul_one]
  · subst hq0
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [zero_pow hn]

/-- A sequence bounded by `C (n+1)^k qⁿ` is absolutely summable. -/
theorem summable_norm_of_bound {f : ℕ → ℝ} {C q : ℝ} (k : ℕ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ n, |f n| ≤ C * (((n : ℝ) + 1) ^ k * q ^ n)) : Summable fun n => ‖f n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact hf n)
    ((summable_succ_pow_mul_geometric k hq hq1).mul_left C)

variable {ω : TrigStream} {M ρ t : ℝ} {K : ℕ}

/-- `ρ |t| < 1` is the open disc of convergence. -/
theorem mul_abs_lt_one (hρ : 0 < ρ) (ht : |t| < 1 / ρ) : ρ * |t| < 1 := by
  rwa [lt_div_iff₀ hρ, mul_comm] at ht

/-- A derivative field bounded by `K'^k · l1 P` for modes of size `≤ K'` gives, along the
stream, the coefficient bound `K^k M (n+1)^k (ρ|t|)ⁿ`. -/
theorem abs_D_mul_pow_le (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    {D : TrigPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ), SizeLE K' P → |D P y| ≤ (K' : ℝ) ^ k * l1 P)
    (n : ℕ) (y : ℝ × ℝ) :
    |D (ω n) y * t ^ n| ≤ ((K : ℝ) ^ k * M) * (((n : ℝ) + 1) ^ k * (ρ * |t|) ^ n) := by
  rw [abs_mul, abs_pow, mul_pow]
  have h1 : |D (ω n) y| ≤ (((n : ℝ) + 1) * K) ^ k * (M * ρ ^ n) := by
    refine (hD _ _ _ (hK n)).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (h n) (by positivity)
  calc |D (ω n) y| * |t| ^ n ≤ (((n : ℝ) + 1) * K) ^ k * (M * ρ ^ n) * |t| ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ((K : ℝ) ^ k * M) * (((n : ℝ) + 1) ^ k * (ρ ^ n * |t| ^ n)) := by rw [mul_pow]; ring

/-- The field itself: `|field P y| ≤ K'^0 · l1 P`. -/
theorem abs_field_le_pow_zero (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ) (_ : SizeLE K' P) :
    |field P y| ≤ (K' : ℝ) ^ 0 * l1 P := by
  rw [pow_zero, one_mul]; exact abs_field_le_l1 P y

/-- The coefficient series of a derivative field is absolutely summable on the disc. -/
theorem summable_norm_D (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) {D : TrigPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ), SizeLE K' P → |D P y| ≤ (K' : ℝ) ^ k * l1 P)
    (y : ℝ × ℝ) : Summable fun n => ‖D (ω n) y * t ^ n‖ :=
  summable_norm_of_bound k (by positivity) (mul_abs_lt_one hρ ht)
    fun n => abs_D_mul_pow_le h hK hD n y

/-! ## Termwise derivatives in `x` -/

/-- Termwise derivative in the first coordinate: a series of derivative fields `D` with
derivatives `D'`, both bounded along the stream, differentiates termwise. -/
theorem hasDerivAt_series_fst (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) {D D' : TrigPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ), SizeLE K' P → |D P y| ≤ (K' : ℝ) ^ k * l1 P)
    (hD' : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ),
      SizeLE K' P → |D' P y| ≤ (K' : ℝ) ^ (k + 1) * l1 P)
    (hd : ∀ (P : TrigPoly) (y : ℝ × ℝ), HasDerivAt (fun s => D P (s, y.2)) (D' P y) y.1)
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => ∑' n, D (ω n) (s, x.2) * t ^ n) (∑' n, D' (ω n) x * t ^ n) x.1 := by
  have hu := (summable_succ_pow_mul_geometric (k + 1) (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left ((K : ℝ) ^ (k + 1) * M)
  have := hasDerivAt_tsum (g := fun n s => D (ω n) (s, x.2) * t ^ n)
    (g' := fun n s => D' (ω n) (s, x.2) * t ^ n) hu
    (fun n s => (hd (ω n) (s, x.2)).mul_const (t ^ n))
    (fun n s => by rw [Real.norm_eq_abs]; exact abs_D_mul_pow_le h hK hD' n (s, x.2))
    (y₀ := x.1) (summable_norm_D h hK hρ ht hD (x.1, x.2)).of_norm x.1
  simpa using this

/-- Termwise derivative in the second coordinate. -/
theorem hasDerivAt_series_snd (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) {D D' : TrigPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ), SizeLE K' P → |D P y| ≤ (K' : ℝ) ^ k * l1 P)
    (hD' : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ),
      SizeLE K' P → |D' P y| ≤ (K' : ℝ) ^ (k + 1) * l1 P)
    (hd : ∀ (P : TrigPoly) (y : ℝ × ℝ), HasDerivAt (fun s => D P (y.1, s)) (D' P y) y.2)
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => ∑' n, D (ω n) (x.1, s) * t ^ n) (∑' n, D' (ω n) x * t ^ n) x.2 := by
  have hu := (summable_succ_pow_mul_geometric (k + 1) (q := ρ * |t|) (by positivity)
    (mul_abs_lt_one hρ ht)).mul_left ((K : ℝ) ^ (k + 1) * M)
  have := hasDerivAt_tsum (g := fun n s => D (ω n) (x.1, s) * t ^ n)
    (g' := fun n s => D' (ω n) (x.1, s) * t ^ n) hu
    (fun n s => (hd (ω n) (x.1, s)).mul_const (t ^ n))
    (fun n s => by rw [Real.norm_eq_abs]; exact abs_D_mul_pow_le h hK hD' n (x.1, s))
    (y₀ := x.2) (summable_norm_D h hK hρ ht hD (x.1, x.2)).of_norm x.2
  simpa using this

/-- `|∂ᵢ field P| ≤ K'^1 · l1 P`, in the shape the generic lemmas take. -/
theorem abs_fieldD₁_le_pow (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ) (hP : SizeLE K' P) :
    |fieldD₁ P y| ≤ (K' : ℝ) ^ 1 * l1 P := by rw [pow_one]; exact abs_fieldD₁_le hP y

theorem abs_fieldD₂_le_pow (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ) (hP : SizeLE K' P) :
    |fieldD₂ P y| ≤ (K' : ℝ) ^ 1 * l1 P := by rw [pow_one]; exact abs_fieldD₂_le hP y

/-- `∂₁ F = seriesD₁` on the disc. -/
theorem hasDerivAt_analyticField_fst (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ω t (s, x.2)) (seriesD₁ ω t x) x.1 :=
  hasDerivAt_series_fst h hK hρ ht abs_field_le_pow_zero abs_fieldD₁_le_pow hasDerivAt_field_fst x

/-- `∂₂ F = seriesD₂` on the disc. -/
theorem hasDerivAt_analyticField_snd (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ω t (x.1, s)) (seriesD₂ ω t x) x.2 :=
  hasDerivAt_series_snd h hK hρ ht abs_field_le_pow_zero abs_fieldD₂_le_pow hasDerivAt_field_snd x

/-- `∂₁ seriesD₁ = seriesD₁₁` on the disc. -/
theorem hasDerivAt_seriesD₁_fst (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₁ ω t (s, x.2)) (seriesD₁₁ ω t x) x.1 :=
  hasDerivAt_series_fst h hK hρ ht abs_fieldD₁_le_pow
    (fun _ _ _ hP => abs_fieldD₁₁_le hP _) hasDerivAt_fieldD₁_fst x

/-- `∂₂ seriesD₂ = seriesD₂₂` on the disc. -/
theorem hasDerivAt_seriesD₂_snd (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₂ ω t (x.1, s)) (seriesD₂₂ ω t x) x.2 :=
  hasDerivAt_series_snd h hK hρ ht abs_fieldD₂_le_pow
    (fun _ _ _ hP => abs_fieldD₂₂_le hP _) hasDerivAt_fieldD₂_snd x

/-- `∂₁ seriesD₂ = seriesD₁₂` on the disc. -/
theorem hasDerivAt_seriesD₂_fst (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₂ ω t (s, x.2)) (seriesD₁₂ ω t x) x.1 :=
  hasDerivAt_series_fst h hK hρ ht abs_fieldD₂_le_pow
    (fun _ _ _ hP => abs_fieldD₁₂_le hP _) hasDerivAt_fieldD₂_fst x

/-- `∂₂ seriesD₁ = seriesD₁₂` on the disc: the mixed derivatives of the series agree. -/
theorem hasDerivAt_seriesD₁_snd (h : GeometricBound ω M ρ)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₁ ω t (x.1, s)) (seriesD₁₂ ω t x) x.2 :=
  hasDerivAt_series_snd h hK hρ ht abs_fieldD₁_le_pow
    (fun _ _ _ hP => abs_fieldD₁₂_le hP _) hasDerivAt_fieldD₁_snd x

/-! ## The termwise derivative in `t` -/

/-- `Σ_n n q^{n−1}` converges for `0 ≤ q < 1`. -/
theorem summable_mul_pow_pred {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => (n : ℝ) * q ^ (n - 1) := by
  rw [← summable_nat_add_iff 1]
  refine (summable_succ_pow_mul_geometric 1 hq hq1).congr fun n => ?_
  simp

/-- `|field ω_n (x) · n s^{n−1}| ≤ M ρ · n (ρ r)^{n−1}` for `|s| ≤ r`. -/
theorem abs_field_mul_deriv_pow_le (h : GeometricBound ω M ρ) (hρ : 0 < ρ) {r : ℝ}
    (x : ℝ × ℝ) (s : ℝ) (n : ℕ) (hs : |s| ≤ r) :
    |field (ω n) x * ((n : ℝ) * s ^ (n - 1))| ≤ (M * ρ) * ((n : ℝ) * (ρ * r) ^ (n - 1)) := by
  have hM := h.nonneg
  rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
  have h1 : |field (ω n) x| ≤ M * ρ ^ n := (abs_field_le_l1 _ _).trans (h n)
  have h2 : |s| ^ (n - 1) ≤ r ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg _) hs _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hρn : ρ ^ n = ρ * ρ ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
    calc |field (ω n) x| * (n * |s| ^ (n - 1)) ≤ M * ρ ^ n * (n * r ^ (n - 1)) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n))
            (by positivity) (by positivity)
      _ = M * ρ * (n * (ρ * r) ^ (n - 1)) := by rw [hρn, mul_pow]; ring

/-- The series has a derivative in `t` on the open disc: `∂_t F = seriesDt`. -/
theorem hasDerivAt_analyticField_t (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ)
    (x : ℝ × ℝ) : HasDerivAt (fun s => analyticField ω s x) (seriesDt ω t x) t := by
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
      rw [Real.norm_eq_abs]
      exact abs_field_mul_deriv_pow_le h hρ x s n hs.le)
    (y₀ := t) (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hrt)
    (summable_norm_seriesTerm h hρ.le (mul_abs_lt_one hρ ht) le_rfl).of_norm
    (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hrt)
  -- reindex the derivative series
  have hs : Summable fun n : ℕ => field (ω n) x * ((n : ℝ) * t ^ (n - 1)) :=
    Summable.of_norm_bounded hu fun n => by
      rw [Real.norm_eq_abs]; exact abs_field_mul_deriv_pow_le h hρ x t n hrt.le
  have shift : (∑' n : ℕ, field (ω n) x * ((n : ℝ) * t ^ (n - 1))) = seriesDt ω t x := by
    rw [hs.tsum_eq_zero_add, seriesDt]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
  rw [← shift]
  exact key

/-! ## Continuity of the series on the open disc -/

/-- A series `Σ_n g_n(y) sⁿ` of continuous terms with the bound `C (n+1)^k (ρ|s|)ⁿ`
is continuous on the strip `|s| ≤ r` when `ρ r < 1`. -/
theorem continuousOn_series {g : ℕ → ℝ × ℝ → ℝ} (hg : ∀ n, Continuous (g n)) {C ρ : ℝ}
    {k : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n (y : ℝ × ℝ) (s : ℝ), |g n y * s ^ n| ≤ C * (((n : ℝ) + 1) ^ k * (ρ * |s|) ^ n))
    (hρ : 0 < ρ) {r : ℝ} (hr0 : 0 ≤ r) (hr : ρ * r < 1) :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ∑' n, g n p.2 * p.1 ^ n) {p | |p.1| ≤ r} := by
  refine continuousOn_tsum
    (fun n => (((hg n).comp continuous_snd).mul (continuous_fst.pow n)).continuousOn)
    ((summable_succ_pow_mul_geometric k (mul_nonneg hρ.le hr0) hr).mul_left C)
    fun n p hp => ?_
  rw [Real.norm_eq_abs]
  refine (hb n p.2 p.1).trans ?_
  have hs : |p.1| ≤ r := hp
  gcongr

/-- Continuity on a strip around `t` gives continuity at `(t, x)`. -/
theorem continuousAt_of_strip {f : ℝ × (ℝ × ℝ) → ℝ} {r t : ℝ} {x : ℝ × ℝ}
    (hf : ContinuousOn f {p | |p.1| ≤ r}) (ht : |t| < r) : ContinuousAt f (t, x) := by
  have hopen : IsOpen {p : ℝ × (ℝ × ℝ) | |p.1| < r} :=
    isOpen_lt (continuous_fst.abs) continuous_const
  exact hf.continuousAt (Filter.mem_of_superset (hopen.mem_nhds ht) fun p hp => by
    show |p.1| ≤ r
    exact le_of_lt hp)

/-- A series with the bound `C (n+1)^k (ρ|s|)ⁿ` is continuous at every `(t, x)` with
`|t| < 1/ρ`. -/
theorem continuousAt_series {g : ℕ → ℝ × ℝ → ℝ} (hg : ∀ n, Continuous (g n)) {C ρ t : ℝ}
    {k : ℕ} (hC : 0 ≤ C)
    (hb : ∀ n (y : ℝ × ℝ) (s : ℝ), |g n y * s ^ n| ≤ C * (((n : ℝ) + 1) ^ k * (ρ * |s|) ^ n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => ∑' n, g n p.2 * p.1 ^ n) (t, x) := by
  set r : ℝ := (|t| + 1 / ρ) / 2 with hr
  have hrt : |t| < r := by rw [hr]; linarith
  have hr1 : ρ * r < 1 := by
    rw [hr]
    have : ρ * (1 / ρ) = 1 := mul_one_div_cancel hρ.ne'
    nlinarith [mul_abs_lt_one hρ ht]
  have hr0 : 0 ≤ r := (abs_nonneg t).trans hrt.le
  exact continuousAt_of_strip (continuousOn_series hg hC hb hρ hr0 hr1) hrt

/-- The analytic field is continuous in `(t, x)` on the disc. -/
theorem continuousAt_analyticField (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ)
    (x : ℝ × ℝ) : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => analyticField ω p.1 p.2) (t, x) := by
  refine continuousAt_series (k := 0) (C := M) (ρ := ρ) (fun n => continuous_field (ω n))
    h.nonneg (fun n y s => ?_) hρ ht x
  rw [pow_zero, one_mul, abs_mul, abs_pow, mul_pow]
  have h1 : |field (ω n) y| ≤ M * ρ ^ n := (abs_field_le_l1 _ _).trans (h n)
  calc |field (ω n) y| * |s| ^ n ≤ M * ρ ^ n * |s| ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = M * (ρ ^ n * |s| ^ n) := by ring

/-- `∂_t F` is continuous in `(t, x)` on the disc. -/
theorem continuousAt_seriesDt (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ)
    (x : ℝ × ℝ) : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesDt ω p.1 p.2) (t, x) := by
  have hM := h.nonneg
  have eq : (fun p : ℝ × (ℝ × ℝ) => seriesDt ω p.1 p.2) =
      fun p => ∑' n, (fun y => field (ω (n + 1)) y * ((n : ℝ) + 1)) p.2 * p.1 ^ n := by
    funext p
    simp only [seriesDt]
    congr 1
    funext n
    ring
  rw [eq]
  refine continuousAt_series (k := 1) (C := M * ρ) (ρ := ρ)
    (g := fun n y => field (ω (n + 1)) y * ((n : ℝ) + 1))
    (fun n => (continuous_field (ω (n + 1))).mul continuous_const) (by positivity)
    (fun n y s => ?_) hρ ht x
  show |field (ω (n + 1)) y * ((n : ℝ) + 1) * s ^ n| ≤ _
  rw [abs_mul, abs_mul, abs_pow, mul_pow, pow_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  have h1 : |field (ω (n + 1)) y| ≤ M * ρ ^ (n + 1) := (abs_field_le_l1 _ _).trans (h (n + 1))
  calc |field (ω (n + 1)) y| * ((n : ℝ) + 1) * |s| ^ n
      ≤ M * ρ ^ (n + 1) * ((n : ℝ) + 1) * |s| ^ n := by gcongr
    _ = M * ρ * (((n : ℝ) + 1) * (ρ ^ n * |s| ^ n)) := by ring

/-- A derivative series is continuous in `(t, x)` on the disc. -/
theorem continuousAt_series_D (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) {D : TrigPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hcont : ∀ P, Continuous (D P))
    (hD : ∀ (K' : ℕ) (P : TrigPoly) (y : ℝ × ℝ), SizeLE K' P → |D P y| ≤ (K' : ℝ) ^ k * l1 P)
    (x : ℝ × ℝ) : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => ∑' n, D (ω n) p.2 * p.1 ^ n) (t, x) :=
  continuousAt_series (k := k) (C := (K : ℝ) ^ k * M) (ρ := ρ) (fun n => hcont (ω n))
    (by have := h.nonneg; positivity) (fun n y s => abs_D_mul_pow_le (t := s) h hK hD n y) hρ ht x

theorem continuousAt_seriesD₁ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁ ω p.1 p.2) (t, x) :=
  continuousAt_series_D h hK hρ ht continuous_fieldD₁ abs_fieldD₁_le_pow x

theorem continuousAt_seriesD₂ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₂ ω p.1 p.2) (t, x) :=
  continuousAt_series_D h hK hρ ht continuous_fieldD₂ abs_fieldD₂_le_pow x

theorem continuousAt_seriesD₁₁ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁₁ ω p.1 p.2) (t, x) :=
  continuousAt_series_D h hK hρ ht continuous_fieldD₁₁ (fun _ _ _ hP => abs_fieldD₁₁_le hP _) x

theorem continuousAt_seriesD₂₂ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₂₂ ω p.1 p.2) (t, x) :=
  continuousAt_series_D h hK hρ ht continuous_fieldD₂₂ (fun _ _ _ hP => abs_fieldD₂₂_le hP _) x

theorem continuousAt_seriesD₁₂ (h : GeometricBound ω M ρ) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁₂ ω p.1 p.2) (t, x) :=
  continuousAt_series_D h hK hρ ht continuous_fieldD₁₂ (fun _ _ _ hP => abs_fieldD₁₂_le hP _) x

/-! ## The Cauchy product of two series in `t` -/

/-- The antidiagonal sum of two series' terms, regrouped along `t`-degree. -/
theorem sum_antidiagonal_mul_pow (a b : ℕ → ℝ) (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n, a kl.1 * t ^ kl.1 * (b kl.2 * t ^ kl.2) =
      (∑ m ∈ Finset.range (n + 1), a m * b (n - m)) * t ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have : t ^ m * t ^ (n - m) = t ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hm)]
  calc a m * t ^ m * (b (n - m) * t ^ (n - m)) = a m * b (n - m) * (t ^ m * t ^ (n - m)) := by
        ring
    _ = a m * b (n - m) * t ^ n := by rw [this]

/-- The Cauchy product of two absolutely convergent series in `t`. -/
theorem tsum_mul_tsum_pow {a b : ℕ → ℝ} (ha : Summable fun n => ‖a n * t ^ n‖)
    (hb : Summable fun n => ‖b n * t ^ n‖) :
    (∑' n, a n * t ^ n) * (∑' n, b n * t ^ n) =
      ∑' n, (∑ m ∈ Finset.range (n + 1), a m * b (n - m)) * t ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb]
  congr 1
  funext n
  exact sum_antidiagonal_mul_pow a b n

/-- The Cauchy product series is summable. -/
theorem summable_cauchy_pow {a b : ℕ → ℝ} (ha : Summable fun n => ‖a n * t ^ n‖)
    (hb : Summable fun n => ‖b n * t ^ n‖) :
    Summable fun n => (∑ m ∈ Finset.range (n + 1), a m * b (n - m)) * t ^ n :=
  (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_norm.congr fun n =>
    sum_antidiagonal_mul_pow a b n

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

/-- **The vorticity equation for the analytic field.** On `|t| < 1/ρ`, for the Euler
stream from an even start with a geometric bound and modes of size at most `K`,
`∂_t F = −(∂₁Ψ ∂₂F − ∂₂Ψ ∂₁F)`, `F` the analytic field and `Ψ` its stream function. -/
theorem seriesDt_eq (hbe : IsEven (b 0)) {K : ℕ} (hK : SizeLE K (b 0)) {M ρ t : ℝ}
    (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    seriesDt ω t x =
      -(seriesD₁ (psi ω) t x * seriesD₂ ω t x - seriesD₂ (psi ω) t x * seriesD₁ ω t x) := by
  have hKn : ∀ n, SizeLE ((n + 1) * K) (ω n) := sizeLE_stream 0 b hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  have s1 := summable_norm_D hψ hKψ hρ ht abs_fieldD₁_le_pow x
  have s2 := summable_norm_D h hKn hρ ht abs_fieldD₂_le_pow x
  have s3 := summable_norm_D hψ hKψ hρ ht abs_fieldD₂_le_pow x
  have s4 := summable_norm_D h hKn hρ ht abs_fieldD₁_le_pow x
  rw [seriesD₁, seriesD₂, seriesD₂, seriesD₁, tsum_mul_tsum_pow s1 s2, tsum_mul_tsum_pow s3 s4,
    ← (summable_cauchy_pow s1 s2).tsum_sub (summable_cauchy_pow s3 s4), ← tsum_neg, seriesDt]
  congr 1
  funext n
  rw [← sub_mul, ← neg_mul, ← succ_field_eq b hbe n x]
  ring

/-- `ΔΨ = F` termwise: the Laplacian of the stream function is the field. Needs only
the mean-zero start (for `Δ Δ⁻¹ = id`), the size bound and the geometric bound. -/
theorem seriesD₁₁_psi_add_seriesD₂₂_psi (hb0 : MeanZero (b 0)) {K : ℕ} (hK : SizeLE K (b 0))
    {M ρ t : ℝ} (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    seriesD₁₁ (psi ω) t x + seriesD₂₂ (psi ω) t x = analyticField ω t x := by
  have hKn : ∀ n, SizeLE ((n + 1) * K) (ω n) := sizeLE_stream 0 b hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  have s1 : Summable fun n => fieldD₁₁ (psi ω n) x * t ^ n :=
    (summable_norm_D hψ hKψ hρ ht (fun _ _ _ hP => abs_fieldD₁₁_le hP _) x).of_norm
  have s2 : Summable fun n => fieldD₂₂ (psi ω n) x * t ^ n :=
    (summable_norm_D hψ hKψ hρ ht (fun _ _ _ hP => abs_fieldD₂₂_le hP _) x).of_norm
  rw [seriesD₁₁, seriesD₂₂, ← s1.tsum_add s2, analyticField]
  congr 1
  funext n
  rw [seriesTerm, ← add_mul, ← field_laplacian, psi,
    laplacian_laplacianInv (stream_meanZero .ogf 0 hb0 n)]

/-- At `t = 0` the analytic field is the field of the start, for every start. -/
theorem analyticField_zero (x : ℝ × ℝ) : analyticField ω 0 x = field (b 0) x := by
  rw [analyticField, tsum_eq_single 0]
  · simp [seriesTerm, stream_slice]
  · intro n hn
    simp [seriesTerm, hn]

/-- **A classical solution of the vorticity equation at `(t, x)`.** For the stream `ω`
with field `F = analyticField ω` and stream function `Ψ = analyticField (psi ω)`:
every partial derivative named here exists (`HasDerivAt`, each the sum of the termwise
derivatives) and is continuous in `(t, x)`, `ΔΨ = F`, and `∂_t F + u·∇F = 0` for the
velocity `u = ∇⊥Ψ = (−∂₂Ψ, ∂₁Ψ)`. The velocity is divergence-free because `∂₁(∂₂Ψ)` and
`∂₂(∂₁Ψ)` both exist and are the one series `seriesD₁₂ (psi ω)` (`psi_derivX₂X₁`,
`psi_derivX₁X₂`), so `∂₁u₁ + ∂₂u₂ = −seriesD₁₂ + seriesD₁₂ = 0` (`div_eq_zero`). -/
structure IsClassicalSolution (a : TrigStream) (t : ℝ) (x : ℝ × ℝ) : Prop where
  /-- `∂_t F = seriesDt ω`. -/
  derivT : HasDerivAt (fun s => analyticField a s x) (seriesDt a t x) t
  /-- `∂₁ F = seriesD₁ ω`. -/
  derivX₁ : HasDerivAt (fun s => analyticField a t (s, x.2)) (seriesD₁ a t x) x.1
  /-- `∂₂ F = seriesD₂ ω`. -/
  derivX₂ : HasDerivAt (fun s => analyticField a t (x.1, s)) (seriesD₂ a t x) x.2
  /-- `∂_t Ψ = seriesDt (psi a)`. -/
  psi_derivT : HasDerivAt (fun s => analyticField (psi a) s x) (seriesDt (psi a) t x) t
  /-- `∂₁ Ψ = seriesD₁ (psi a)`. -/
  psi_derivX₁ :
    HasDerivAt (fun s => analyticField (psi a) t (s, x.2)) (seriesD₁ (psi a) t x) x.1
  /-- `∂₂ Ψ = seriesD₂ (psi a)`. -/
  psi_derivX₂ :
    HasDerivAt (fun s => analyticField (psi a) t (x.1, s)) (seriesD₂ (psi a) t x) x.2
  /-- `∂₁∂₁ Ψ = seriesD₁₁ (psi a)`. -/
  psi_derivX₁X₁ : HasDerivAt (fun s => seriesD₁ (psi a) t (s, x.2)) (seriesD₁₁ (psi a) t x) x.1
  /-- `∂₂∂₂ Ψ = seriesD₂₂ (psi a)`. -/
  psi_derivX₂X₂ : HasDerivAt (fun s => seriesD₂ (psi a) t (x.1, s)) (seriesD₂₂ (psi a) t x) x.2
  /-- `∂₁ (∂₂ Ψ) = seriesD₁₂ (psi a)`. -/
  psi_derivX₂X₁ : HasDerivAt (fun s => seriesD₂ (psi a) t (s, x.2)) (seriesD₁₂ (psi a) t x) x.1
  /-- `∂₂ (∂₁ Ψ) = seriesD₁₂ (psi a)`: the mixed derivatives agree, so `div u = 0`. -/
  psi_derivX₁X₂ : HasDerivAt (fun s => seriesD₁ (psi a) t (x.1, s)) (seriesD₁₂ (psi a) t x) x.2
  /-- `F` is continuous in `(t, x)`. -/
  continuous_field : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => analyticField a p.1 p.2) (t, x)
  /-- `∂_t F` is continuous in `(t, x)`. -/
  continuous_derivT : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesDt a p.1 p.2) (t, x)
  /-- `∂₁ F` is continuous in `(t, x)`. -/
  continuous_derivX₁ : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁ a p.1 p.2) (t, x)
  /-- `∂₂ F` is continuous in `(t, x)`. -/
  continuous_derivX₂ : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₂ a p.1 p.2) (t, x)
  /-- `Ψ` is continuous in `(t, x)`. -/
  continuous_psi : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => analyticField (psi a) p.1 p.2) (t, x)
  /-- `∂_t Ψ` is continuous in `(t, x)`. -/
  continuous_psi_derivT : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesDt (psi a) p.1 p.2) (t, x)
  /-- `∂₁ Ψ` is continuous in `(t, x)`. -/
  continuous_psi_derivX₁ : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁ (psi a) p.1 p.2) (t, x)
  /-- `∂₂ Ψ` is continuous in `(t, x)`. -/
  continuous_psi_derivX₂ : ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₂ (psi a) p.1 p.2) (t, x)
  /-- `∂₁∂₁ Ψ` is continuous in `(t, x)`. -/
  continuous_psi_derivX₁X₁ :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁₁ (psi a) p.1 p.2) (t, x)
  /-- `∂₂∂₂ Ψ` is continuous in `(t, x)`. -/
  continuous_psi_derivX₂X₂ :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₂₂ (psi a) p.1 p.2) (t, x)
  /-- `∂₁∂₂ Ψ` is continuous in `(t, x)`. -/
  continuous_psi_derivX₁X₂ :
    ContinuousAt (fun p : ℝ × (ℝ × ℝ) => seriesD₁₂ (psi a) p.1 p.2) (t, x)
  /-- `ΔΨ = F`. -/
  laplacian : seriesD₁₁ (psi a) t x + seriesD₂₂ (psi a) t x = analyticField a t x
  /-- `∂_t F + u·∇F = 0` with `u = (−∂₂Ψ, ∂₁Ψ)`. -/
  equation : seriesDt a t x +
    (-seriesD₂ (psi a) t x * seriesD₁ a t x + seriesD₁ (psi a) t x * seriesD₂ a t x) = 0

/-- `div u = 0`: `u₁ = −∂₂Ψ` has `∂₁u₁ = −seriesD₁₂ (psi a)`, `u₂ = ∂₁Ψ` has
`∂₂u₂ = seriesD₁₂ (psi a)`, and they cancel. -/
theorem IsClassicalSolution.div_eq_zero {a : TrigStream} {t : ℝ} {x : ℝ × ℝ}
    (h : IsClassicalSolution a t x) :
    HasDerivAt (fun s => -seriesD₂ (psi a) t (s, x.2)) (-seriesD₁₂ (psi a) t x) x.1 ∧
    HasDerivAt (fun s => seriesD₁ (psi a) t (x.1, s)) (seriesD₁₂ (psi a) t x) x.2 ∧
    -seriesD₁₂ (psi a) t x + seriesD₁₂ (psi a) t x = 0 :=
  ⟨h.psi_derivX₂X₁.neg, h.psi_derivX₁X₂, by ring⟩

/-- **The analytic field of the Euler stream is a classical solution.** For an even,
mean-zero start with modes of size at most `K` and a geometric bound `l1 ω_n ≤ M ρⁿ`,
at every `(t, x)` with `|t| < 1/ρ`. -/
theorem euler_classical (hb0 : MeanZero (b 0)) (hbe : IsEven (b 0)) {K : ℕ} (hK : SizeLE K (b 0))
    {M ρ t : ℝ} (h : GeometricBound ω M ρ) (hρ : 0 < ρ) (ht : |t| < 1 / ρ) (x : ℝ × ℝ) :
    IsClassicalSolution ω t x := by
  have hKn : ∀ n, SizeLE ((n + 1) * K) (ω n) := sizeLE_stream 0 b hK
  have hKψ : ∀ n, SizeLE ((n + 1) * K) (psi ω n) := fun n => sizeLE_laplacianInv (hKn n)
  have hψ := geometricBound_psi h
  refine ⟨hasDerivAt_analyticField_t h hρ ht x, hasDerivAt_analyticField_fst h hKn hρ ht x,
    hasDerivAt_analyticField_snd h hKn hρ ht x, hasDerivAt_analyticField_t hψ hρ ht x,
    hasDerivAt_analyticField_fst hψ hKψ hρ ht x, hasDerivAt_analyticField_snd hψ hKψ hρ ht x,
    hasDerivAt_seriesD₁_fst hψ hKψ hρ ht x, hasDerivAt_seriesD₂_snd hψ hKψ hρ ht x,
    hasDerivAt_seriesD₂_fst hψ hKψ hρ ht x, hasDerivAt_seriesD₁_snd hψ hKψ hρ ht x,
    continuousAt_analyticField h hρ ht x, continuousAt_seriesDt h hρ ht x,
    continuousAt_seriesD₁ h hKn hρ ht x, continuousAt_seriesD₂ h hKn hρ ht x,
    continuousAt_analyticField hψ hρ ht x, continuousAt_seriesDt hψ hρ ht x,
    continuousAt_seriesD₁ hψ hKψ hρ ht x, continuousAt_seriesD₂ hψ hKψ hρ ht x,
    continuousAt_seriesD₁₁ hψ hKψ hρ ht x, continuousAt_seriesD₂₂ hψ hKψ hρ ht x,
    continuousAt_seriesD₁₂ hψ hKψ hρ ht x,
    seriesD₁₁_psi_add_seriesD₂₂_psi b hb0 hK h hρ ht x, ?_⟩
  rw [seriesDt_eq b hbe hK h hρ ht x]
  ring

end Gimle.Asgard.Streams.NS

#print axioms Gimle.Asgard.Streams.Torus.field_transport
#print axioms Gimle.Asgard.Streams.Torus.field_laplacian
#print axioms Gimle.Asgard.Streams.TrigStream.hasDerivAt_analyticField_t
#print axioms Gimle.Asgard.Streams.TrigStream.hasDerivAt_analyticField_fst
#print axioms Gimle.Asgard.Streams.TrigStream.hasDerivAt_seriesD₁_fst
#print axioms Gimle.Asgard.Streams.TrigStream.continuousAt_analyticField
#print axioms Gimle.Asgard.Streams.NS.seriesDt_eq
#print axioms Gimle.Asgard.Streams.NS.seriesD₁₁_psi_add_seriesD₂₂_psi
#print axioms Gimle.Asgard.Streams.NS.analyticField_zero
#print axioms Gimle.Asgard.Streams.NS.euler_classical
