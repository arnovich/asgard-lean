import Gimle.Asgard.Streams.Laws
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Finite polynomial streams and their real fields

A stream is *polynomially realized* when its **whole** decoded coefficient
family is that of one mathlib `MvPolynomial`: `Realizes basis a p` says
`a = ofPoly basis p`. Agreement on a finite window is not such a witness;
`finiteSupport_iff` makes the full-stream condition explicit.

Every stream-circuit primitive maps realized inputs to realized outputs
(`Circuit.rel_ofPoly`), and the evaluated real field of each output is the
corresponding analytic operation on the input fields: sums, products,
selected-axis partial derivatives (`hasDerivAt_field`), integrals from the
axis origin carrying the full boundary profile (`field_integralPoly`) and
single-axis substitution (`field_composePoly`). Derivatives and integrals here
are those of the evaluated real function, not coefficient shifts; the shifts
are proved to agree with them.

No convergence of infinite series is used or claimed. -/
namespace Gimle.Asgard.Streams

/-- Finite rational polynomials on `d` ordered axes. -/
abbrev Poly (d : Nat) := MvPolynomial (Fin d) ℚ

/-! ## Embedding -/

/-- The exact stream of a polynomial in the chosen basis. OGF raw coefficients
are the polynomial coefficients; EGF raw coefficients carry the full
multi-factorial `α₁!⋯α_d!`, on every axis. -/
noncomputable def ofPoly {d : Nat} (basis : Basis) (p : Poly d) : Stream d :=
  encode basis (p : MvPowerSeries (Fin d) ℚ)

@[simp] theorem decode_ofPoly {d : Nat} (basis : Basis) (p : Poly d) :
    decode basis (ofPoly basis p) = (p : MvPowerSeries (Fin d) ℚ) :=
  decode_encode basis _

theorem ofPoly_ogf_apply {d : Nat} (p : Poly d) (n : Index d) :
    ofPoly .ogf p n = MvPolynomial.coeff n p :=
  MvPolynomial.coeff_coe p n

theorem ofPoly_egf_apply {d : Nat} (p : Poly d) (n : Index d) :
    ofPoly .egf p n = factorial n * MvPolynomial.coeff n p := by
  change factorial n * MvPowerSeries.coeff n (p : MvPowerSeries (Fin d) ℚ) = _
  rw [MvPolynomial.coeff_coe]

/-- The decoded coefficient at every index is the polynomial coefficient. -/
theorem decode_ofPoly_apply {d : Nat} (basis : Basis) (p : Poly d) (n : Index d) :
    decode basis (ofPoly basis p) n = MvPolynomial.coeff n p := by
  rw [decode_ofPoly]
  exact MvPolynomial.coeff_coe p n

theorem encode_injective {d : Nat} (basis : Basis) :
    Function.Injective (encode (d := d) basis) := by
  intro a b h
  rw [← decode_encode basis a, h, decode_encode]

theorem ofPoly_injective {d : Nat} (basis : Basis) :
    Function.Injective (ofPoly (d := d) basis) := by
  intro p q h
  exact MvPolynomial.coe_inj.mp (encode_injective basis h)

/-- The whole stream `a` is the embedding of `p`. -/
def Realizes {d : Nat} (basis : Basis) (a : Stream d) (p : Poly d) : Prop :=
  a = ofPoly basis p

/-- Finitely many raw coefficients of the **entire** stream are nonzero. -/
def FiniteSupport {d : Nat} (a : Stream d) : Prop :=
  ∃ s : Finset (Index d), ∀ n, a n ≠ 0 → n ∈ s

/-- A polynomial from a finite coefficient table. -/
noncomputable def polyOfCoeffs {d : Nat} (s : Finset (Index d)) (f : Index d → ℚ) : Poly d :=
  ∑ n ∈ s, MvPolynomial.monomial n (f n)

theorem coeff_polyOfCoeffs {d : Nat} (s : Finset (Index d)) (f : Index d → ℚ)
    (support : ∀ n, f n ≠ 0 → n ∈ s) (m : Index d) :
    MvPolynomial.coeff m (polyOfCoeffs s f) = f m := by
  classical
  simp only [polyOfCoeffs, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra ne
    exact h (support m (Ne.symm ne))

private theorem decode_ne_zero {d : Nat} (basis : Basis) (a : Stream d) (n : Index d)
    (h : decode basis a n ≠ 0) : a n ≠ 0 := by
  cases basis with
  | ogf => exact h
  | egf =>
      intro zero
      apply h
      change a n / factorial n = 0
      rw [zero, zero_div]

/-- A stream is realized by some polynomial exactly when its whole raw
coefficient family has finite support, in either basis. -/
theorem finiteSupport_iff {d : Nat} (basis : Basis) (a : Stream d) :
    FiniteSupport a ↔ ∃ p, Realizes basis a p := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨polyOfCoeffs s (decode basis a), ?_⟩
    have coe : ((polyOfCoeffs s (decode basis a) : Poly d) : MvPowerSeries (Fin d) ℚ) =
        decode basis a := by
      ext m
      rw [MvPolynomial.coeff_coe,
        coeff_polyOfCoeffs s _ (fun n h => hs n (decode_ne_zero basis a n h))]
      rfl
    unfold Realizes ofPoly
    rw [coe, encode_decode]
  · rintro ⟨p, rfl⟩
    refine ⟨p.support, fun n h => ?_⟩
    rw [MvPolynomial.mem_support_iff]
    intro zero
    apply h
    cases basis with
    | ogf => rw [ofPoly_ogf_apply, zero]
    | egf => rw [ofPoly_egf_apply, zero, mul_zero]

/-! ## Real evaluation -/

/-- The evaluated real field of a rational polynomial. -/
noncomputable def field {d : Nat} (p : Poly d) (x : Fin d → ℝ) : ℝ :=
  MvPolynomial.aeval x p

/-- Evaluation is the finite sum of the **decoded stream** coefficients against
monomials, in either basis: coefficient-by-coefficient agreement. -/
theorem field_eq_sum {d : Nat} (basis : Basis) (p : Poly d) (x : Fin d → ℝ) :
    field p x = ∑ n ∈ p.support,
      ((decode basis (ofPoly basis p) n : ℚ) : ℝ) * ∏ i, x i ^ n i := by
  unfold field
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [decode_ofPoly_apply]
  rfl

@[simp] theorem field_C {d : Nat} (q : ℚ) (x : Fin d → ℝ) :
    field (MvPolynomial.C q) x = q := by
  simp [field]

@[simp] theorem field_X {d : Nat} (i : Fin d) (x : Fin d → ℝ) :
    field (MvPolynomial.X i) x = x i := by
  simp [field]

@[simp] theorem field_zero {d : Nat} (x : Fin d → ℝ) : field (0 : Poly d) x = 0 := by
  simp [field]

@[simp] theorem field_one {d : Nat} (x : Fin d → ℝ) : field (1 : Poly d) x = 1 := by
  simp [field]

@[simp] theorem field_add {d : Nat} (p q : Poly d) (x : Fin d → ℝ) :
    field (p + q) x = field p x + field q x := by
  simp [field]

@[simp] theorem field_mul {d : Nat} (p q : Poly d) (x : Fin d → ℝ) :
    field (p * q) x = field p x * field q x := by
  simp [field]

@[simp] theorem field_pow {d : Nat} (p : Poly d) (k : ℕ) (x : Fin d → ℝ) :
    field (p ^ k) x = field p x ^ k := by
  simp [field]

@[simp] theorem field_natCast {d : Nat} (k : ℕ) (x : Fin d → ℝ) :
    field (k : Poly d) x = k := by
  simp [field]

@[simp] theorem field_ofNat {d : Nat} (k : ℕ) [k.AtLeastTwo] (x : Fin d → ℝ) :
    field (ofNat(k) : Poly d) x = ofNat(k) := by
  simp [field]

@[simp] theorem field_sub {d : Nat} (p q : Poly d) (x : Fin d → ℝ) :
    field (p - q) x = field p x - field q x := by
  simp [field]

/-- Polynomial fields over ℝ determine the rational polynomial. -/
theorem field_injective {d : Nat} {p q : Poly d} (h : ∀ x, field p x = field q x) : p = q := by
  apply MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
  apply MvPolynomial.funext
  intro x
  have hx := h x
  simp only [field, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] at hx
  exact hx

/-! ## Primitive operations on realized streams -/

theorem constant_eq_ofPoly {d : Nat} (basis : Basis) (q : ℚ) :
    constant (d := d) basis q = ofPoly basis (MvPolynomial.C q) := by
  simp [constant, ofPoly, MvPolynomial.coe_C]

theorem axisVariable_eq_ofPoly {d : Nat} (basis : Basis) (i : Fin d) :
    axisVariable basis i = ofPoly basis (MvPolynomial.X i) := by
  simp [axisVariable, ofPoly, MvPolynomial.coe_X]

theorem ofPoly_add {d : Nat} (basis : Basis) (p q : Poly d) :
    ofPoly basis p + ofPoly basis q = ofPoly basis (p + q) := by
  cases basis with
  | ogf => simp [ofPoly, encode, MvPolynomial.coe_add]
  | egf =>
      ext n
      change ofPoly .egf p n + ofPoly .egf q n = ofPoly .egf (p + q) n
      simp [ofPoly_egf_apply, mul_add]

theorem product_ofPoly {d : Nat} (basis : Basis) (p q : Poly d) :
    product basis (ofPoly basis p) (ofPoly basis q) = ofPoly basis (p * q) := by
  simp [product, ofPoly, MvPolynomial.coe_mul]

private theorem update_succ {d : Nat} (n : Index d) (i : Fin d) :
    n.update i (n i + 1) = n + Finsupp.single i 1 := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Finsupp.update_apply, h]

/-- Formal OGF differentiation of an embedded polynomial is `pderiv`. -/
theorem derivative_coe {d : Nat} (i : Fin d) (p : Poly d) :
    derivative .ogf i (p : MvPowerSeries (Fin d) ℚ) = ↑(MvPolynomial.pderiv i p) := by
  funext n
  change _ = MvPowerSeries.coeff n (↑(MvPolynomial.pderiv i p) : MvPowerSeries (Fin d) ℚ)
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_pderiv]
  change (n i + 1 : ℚ) *
    MvPowerSeries.coeff (n.update i (n i + 1)) (p : MvPowerSeries (Fin d) ℚ) = _
  rw [MvPolynomial.coeff_coe, update_succ, mul_comm]

theorem derivative_ofPoly {d : Nat} (basis : Basis) (i : Fin d) (p : Poly d) :
    derivative basis i (ofPoly basis p) = ofPoly basis (MvPolynomial.pderiv i p) := by
  unfold ofPoly
  rw [derivative_encode, derivative_coe]

/-- The formal integral along `i` of `p`, with boundary slice taken from `b`:
coefficients of `b` at axis-degree zero, plus the antiderivative of `p`. -/
noncomputable def integralPoly {d : Nat} (i : Fin d) (p b : Poly d) : Poly d :=
  polyOfCoeffs ((b.support.filter (fun n => n i = 0)) ∪
      p.support.image (fun n => n + Finsupp.single i 1))
    (integral .ogf i (p : MvPowerSeries (Fin d) ℚ) (b : MvPowerSeries (Fin d) ℚ))

theorem integral_coe {d : Nat} (i : Fin d) (p b : Poly d) :
    integral .ogf i (p : MvPowerSeries (Fin d) ℚ) (b : MvPowerSeries (Fin d) ℚ) =
      ↑(integralPoly i p b) := by
  classical
  ext n
  rw [MvPolynomial.coeff_coe, integralPoly, coeff_polyOfCoeffs]
  · rfl
  intro m hm
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, MvPolynomial.mem_support_iff]
  by_cases zero : m i = 0
  · left
    refine ⟨?_, zero⟩
    have := hm
    simp only [integral, zero, if_true] at this
    rwa [← MvPolynomial.coeff_coe]
  · right
    have pos : 0 < m i := Nat.pos_of_ne_zero zero
    refine ⟨m.update i (m i - 1), ?_, ?_⟩
    · intro coeff_zero
      apply hm
      simp only [integral, zero, if_false]
      change MvPowerSeries.coeff _ (p : MvPowerSeries (Fin d) ℚ) / _ = 0
      rw [MvPolynomial.coeff_coe, coeff_zero, zero_div]
    · rw [← update_succ]
      ext j
      by_cases h : j = i
      · subst h; simp; omega
      · simp [Finsupp.update_apply, h]

theorem integral_ofPoly {d : Nat} (basis : Basis) (i : Fin d) (p b : Poly d) :
    integral basis i (ofPoly basis p) (ofPoly basis b) = ofPoly basis (integralPoly i p b) := by
  unfold ofPoly
  rw [integral_encode, integral_coe]

/-- Formal integration followed by `pderiv` recovers the integrand. -/
theorem pderiv_integralPoly {d : Nat} (i : Fin d) (p b : Poly d) :
    MvPolynomial.pderiv i (integralPoly i p b) = p := by
  apply ofPoly_injective .ogf
  rw [← derivative_ofPoly, ← integral_ofPoly]
  exact derivative_integral .ogf i _ _

/-- Along axis degree zero the integral keeps every boundary coefficient. -/
theorem coeff_integralPoly_boundary {d : Nat} (i : Fin d) (p b : Poly d) (n : Index d)
    (zero : n i = 0) : MvPolynomial.coeff n (integralPoly i p b) = MvPolynomial.coeff n b := by
  rw [← ofPoly_ogf_apply, ← integral_ofPoly, integral_boundary _ _ _ _ _ zero, ofPoly_ogf_apply]

/-- Single-axis polynomial substitution: axis `i` of `p` is replaced by `q`. -/
noncomputable def composePoly {d : Nat} (i : Fin d) (p q : Poly d) : Poly d :=
  MvPolynomial.aeval (fun j => if j = i then q else MvPolynomial.X j) p

private theorem coe_aeval {d : Nat} (f : Fin d → Poly d) (p : Poly d) :
    MvPolynomial.aeval (fun j => (f j : MvPowerSeries (Fin d) ℚ)) p =
      ((MvPolynomial.aeval f p : Poly d) : MvPowerSeries (Fin d) ℚ) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.coe_C]
      rfl
  | add p q hp hq => simp [hp, hq, MvPolynomial.coe_add]
  | mul_X p j hp => simp [hp, MvPolynomial.coe_mul]

theorem canCompose_ofPoly {d : Nat} (basis : Basis) (q : Poly d) :
    CanCompose basis (ofPoly basis q) ↔ MvPolynomial.constantCoeff q = 0 := by
  unfold CanCompose
  rw [decode_ofPoly, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    MvPolynomial.constantCoeff_eq]

theorem seriesCompose_ofPoly {d : Nat} (basis : Basis) (i : Fin d) (p q : Poly d)
    (valid : MvPolynomial.constantCoeff q = 0) :
    seriesCompose basis i (ofPoly basis p) (ofPoly basis q) = ofPoly basis (composePoly i p q) := by
  have ha := substitution_valid basis i (ofPoly basis q) ((canCompose_ofPoly basis q).mpr valid)
  rw [decode_ofPoly] at ha
  unfold seriesCompose ofPoly composePoly
  have subst : substitution i (q : MvPowerSeries (Fin d) ℚ) =
      fun j => ((if j = i then q else MvPolynomial.X j : Poly d) : MvPowerSeries (Fin d) ℚ) := by
    funext j
    by_cases h : j = i <;> simp [substitution, h, MvPolynomial.coe_X]
  rw [decode_encode, decode_encode, ← MvPowerSeries.substAlgHom_apply ha,
    MvPowerSeries.substAlgHom_coe, subst, coe_aeval]

/-! ## Analytic meaning of the operations -/

/-- The partial derivative of the evaluated field along axis `i` is the field
of `pderiv i p`. This is the real derivative of the function, not a shift. -/
theorem hasDerivAt_field {d : Nat} (p : Poly d) (i : Fin d) (x : Fin d → ℝ) :
    HasDerivAt (fun s => field p (Function.update x i s))
      (field (MvPolynomial.pderiv i p) x) (x i) := by
  suffices ∀ s, HasDerivAt (fun s => field p (Function.update x i s))
      (field (MvPolynomial.pderiv i p) (Function.update x i s)) s by
    simpa using this (x i)
  induction p using MvPolynomial.induction_on with
  | C a =>
      intro s
      simp only [field_C, MvPolynomial.pderiv_C, field_zero]
      exact hasDerivAt_const s (a : ℝ)
  | add p q hp hq =>
      intro s
      simp only [field_add, map_add]
      exact (hp s).add (hq s)
  | mul_X p j hp =>
      intro s
      have leibniz : MvPolynomial.pderiv i (p * MvPolynomial.X j) =
          MvPolynomial.pderiv i p * MvPolynomial.X j +
            p * MvPolynomial.pderiv i (MvPolynomial.X j) :=
        MvPolynomial.pderiv_mul
      simp only [field_mul, field_X, leibniz, field_add]
      by_cases h : j = i
      · subst h
        simp only [Function.update_self, MvPolynomial.pderiv_X_self, field_one, mul_one]
        exact (hp s).mul (hasDerivAt_id' s) |>.congr_deriv (by ring)
      · simp only [Function.update_of_ne h, MvPolynomial.pderiv_X_of_ne h, field_zero,
          mul_zero, add_zero]
        exact (hp s).mul_const (x j)

theorem deriv_field {d : Nat} (p : Poly d) (i : Fin d) (x : Fin d → ℝ) :
    deriv (fun s => field p (Function.update x i s)) (x i) = field (MvPolynomial.pderiv i p) x :=
  (hasDerivAt_field p i x).deriv

theorem continuous_field_update {d : Nat} (p : Poly d) (i : Fin d) (x : Fin d → ℝ) :
    Continuous (fun s => field p (Function.update x i s)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have h := hasDerivAt_field p i (Function.update x i s)
  simp only [Function.update_idem, Function.update_self] at h
  exact h.continuousAt

/-- The slice of `p` at axis-`i` origin, as a polynomial. -/
noncomputable def restrictZero {d : Nat} (i : Fin d) (p : Poly d) : Poly d :=
  MvPolynomial.bind₁ (Function.update MvPolynomial.X i 0) p

theorem field_restrictZero {d : Nat} (i : Fin d) (p : Poly d) (x : Fin d → ℝ) :
    field (restrictZero i p) x = field p (Function.update x i 0) := by
  unfold field restrictZero
  have point : (fun j => MvPolynomial.aeval x (Function.update MvPolynomial.X i 0 j : Poly d)) =
      Function.update x i 0 := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [MvPolynomial.aeval_bind₁, point]

theorem coeff_restrictZero {d : Nat} (i : Fin d) (p : Poly d) (n : Index d) :
    MvPolynomial.coeff n (restrictZero i p) = if n i = 0 then MvPolynomial.coeff n p else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [restrictZero, map_add, MvPolynomial.coeff_add] at hp hq ⊢
      rw [hp, hq]
      split_ifs <;> simp
  | monomial m c =>
      unfold restrictZero
      rw [MvPolynomial.bind₁_monomial]
      by_cases hm : m i = 0
      · have prod : ∏ j ∈ m.support, (Function.update MvPolynomial.X i 0 j : Poly d) ^ m j =
            ∏ j ∈ m.support, MvPolynomial.X j ^ m j := by
          apply Finset.prod_congr rfl
          intro j hj
          have : j ≠ i := by
            rintro rfl
            exact (Finsupp.mem_support_iff.mp hj) hm
          simp [Function.update_of_ne this]
        have mono : MvPolynomial.C c * ∏ j ∈ m.support, (MvPolynomial.X j : Poly d) ^ m j =
            MvPolynomial.monomial m c := by
          rw [MvPolynomial.monomial_eq]; rfl
        rw [prod, mono, MvPolynomial.coeff_monomial]
        by_cases e : m = n
        · subst e; simp [hm]
        · simp [e]
      · have prod : ∏ j ∈ m.support, (Function.update MvPolynomial.X i 0 j : Poly d) ^ m j = 0 := by
          apply Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr hm)
          simp [zero_pow hm]
        rw [prod, mul_zero, MvPolynomial.coeff_zero, MvPolynomial.coeff_monomial]
        split_ifs with e h
        · subst h; exact absurd e hm
        · rfl
        · rfl

/-- Two polynomials with equal coefficients on the axis-`i` zero slice have equal
fields on the hyperplane `x_i = 0`, and conversely. -/
theorem slice_iff {d : Nat} (i : Fin d) (p q : Poly d) :
    (∀ n : Index d, n i = 0 → MvPolynomial.coeff n p = MvPolynomial.coeff n q) ↔
      ∀ x, field p (Function.update x i 0) = field q (Function.update x i 0) := by
  constructor
  · intro h x
    rw [← field_restrictZero, ← field_restrictZero]
    congr 1
    ext n
    rw [coeff_restrictZero, coeff_restrictZero]
    split_ifs with zero
    · exact h n zero
    · rfl
  · intro h n zero
    have eq : restrictZero i p = restrictZero i q :=
      field_injective fun x => by rw [field_restrictZero, field_restrictZero, h]
    have := congrArg (MvPolynomial.coeff n) eq
    rwa [coeff_restrictZero, coeff_restrictZero, if_pos zero, if_pos zero] at this

/-- The integral keeps the full boundary profile on the hyperplane `x_i = 0`. -/
theorem field_integralPoly_zero {d : Nat} (i : Fin d) (p b : Poly d) (x : Fin d → ℝ) :
    field (integralPoly i p b) (Function.update x i 0) = field b (Function.update x i 0) :=
  (slice_iff i _ _).mp (coeff_integralPoly_boundary i p b) x

/-- Analytic meaning of the formal integral: boundary value at the axis origin
plus the real integral of the integrand field from the origin to `x_i`. -/
theorem field_integralPoly {d : Nat} (i : Fin d) (p b : Poly d) (x : Fin d → ℝ) :
    field (integralPoly i p b) x =
      field b (Function.update x i 0) + ∫ s in (0 : ℝ)..x i, field p (Function.update x i s) := by
  have ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => field (integralPoly i p b) (Function.update x i s))
    (f' := fun s => field p (Function.update x i s)) (a := 0) (b := x i)
    (fun s _ => by
      have h := hasDerivAt_field (integralPoly i p b) i (Function.update x i s)
      simpa [Function.update_idem, pderiv_integralPoly] using h)
    ((continuous_field_update p i x).intervalIntegrable _ _)
  rw [ftc, field_integralPoly_zero]
  simp

/-- Analytic meaning of single-axis substitution. -/
theorem field_composePoly {d : Nat} (i : Fin d) (p q : Poly d) (x : Fin d → ℝ) :
    field (composePoly i p q) x = field p (Function.update x i (field q x)) := by
  unfold field composePoly
  have point : (fun j => MvPolynomial.aeval x (if j = i then q else MvPolynomial.X j : Poly d)) =
      Function.update x i (MvPolynomial.aeval x q) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  change MvPolynomial.aeval x (MvPolynomial.bind₁ _ p) = _
  rw [MvPolynomial.aeval_bind₁, point]

/-! ## Circuits over realized inputs -/

noncomputable def Unary.polyValue {d : Nat} : Unary d → Poly d → Poly d
  | .derivative i, p => MvPolynomial.pderiv i p

noncomputable def Binary.polyValue {d : Nat} : Binary d → Poly d → Poly d → Poly d
  | .add, p, q => p + q
  | .product, p, q => p * q
  | .integral i, p, q => integralPoly i p q
  | .seriesCompose i, p, q => composePoly i p q

/-- The polynomial side condition of each operation; only substitution has one. -/
def Binary.PolyDomain {d : Nat} : Binary d → Poly d → Poly d → Prop
  | .add, _, _ => True
  | .product, _, _ => True
  | .integral _, _, _ => True
  | .seriesCompose _, _, q => MvPolynomial.constantCoeff q = 0

theorem Unary.value_ofPoly {d : Nat} (basis : Basis) (op : Unary d) (p : Poly d) :
    op.value basis (ofPoly basis p) = ofPoly basis (op.polyValue p) := by
  cases op with
  | derivative i => exact derivative_ofPoly basis i p

theorem Binary.domain_ofPoly {d : Nat} (basis : Basis) (op : Binary d) (p q : Poly d) :
    op.Domain basis (ofPoly basis p) (ofPoly basis q) ↔ op.PolyDomain p q := by
  cases op with
  | add => exact Iff.rfl
  | product => exact Iff.rfl
  | integral i => exact Iff.rfl
  | seriesCompose i => exact canCompose_ofPoly basis q

theorem Binary.value_ofPoly {d : Nat} (basis : Basis) (op : Binary d) (p q : Poly d)
    (domain : op.PolyDomain p q) :
    op.value basis (ofPoly basis p) (ofPoly basis q) = ofPoly basis (op.polyValue p q) := by
  cases op with
  | add => exact ofPoly_add basis p q
  | product => exact product_ofPoly basis p q
  | integral i => exact integral_ofPoly basis i p q
  | seriesCompose i => exact seriesCompose_ofPoly basis i p q domain

/-- Polynomial semantics of a stream circuit, wire for wire. -/
noncomputable def Circuit.polyValue {basis : Basis} {d n m : Nat} :
    Circuit basis d n m → (Fin n → Poly d) → Fin m → Poly d
  | .route f, x => x ∘ f
  | .constant q, _ => ![MvPolynomial.C q]
  | .axisVariable i, _ => ![MvPolynomial.X i]
  | .unary op, x => ![op.polyValue (x 0)]
  | .binary op, x => ![op.polyValue (x 0) (x 1)]
  | .compose a b, x => b.polyValue (a.polyValue x)
  | .parallel a b, x => Fin.addCases (a.polyValue (fun i => x (Fin.castAdd _ i)))
      (b.polyValue (fun i => x (Fin.natAdd _ i)))

def Circuit.PolyDefined {basis : Basis} {d n m : Nat} :
    Circuit basis d n m → (Fin n → Poly d) → Prop
  | .route _, _ => True
  | .constant _, _ => True
  | .axisVariable _, _ => True
  | .unary _, _ => True
  | .binary op, x => op.PolyDomain (x 0) (x 1)
  | .compose a b, x => a.PolyDefined x ∧ b.PolyDefined (a.polyValue x)
  | .parallel a b, x => a.PolyDefined (fun i => x (Fin.castAdd _ i)) ∧
      b.PolyDefined (fun i => x (Fin.natAdd _ i))

private theorem ofPoly_vec1 {d : Nat} (basis : Basis) (p : Poly d) :
    (fun j => ofPoly basis ((![p] : Fin 1 → Poly d) j)) = ![ofPoly basis p] := by
  funext j; fin_cases j; rfl

private theorem append_ofPoly {d n m : Nat} (basis : Basis) (u : Fin n → Poly d)
    (v : Fin m → Poly d) :
    append (fun j => ofPoly basis (u j)) (fun j => ofPoly basis (v j)) =
      fun j => ofPoly basis (Fin.addCases u v j) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp [append]
  · simp [append]

private theorem Circuit.ofPoly_aux {basis : Basis} {d n m : Nat} (c : Circuit basis d n m)
    (x : Fin n → Poly d) :
    (c.Defined (fun j => ofPoly basis (x j)) ↔ c.PolyDefined x) ∧
      (c.PolyDefined x → c.value (fun j => ofPoly basis (x j)) =
        fun j => ofPoly basis (c.polyValue x j)) := by
  induction c with
  | route f => exact ⟨Iff.rfl, fun _ => rfl⟩
  | constant q => exact ⟨Iff.rfl, fun _ => by
      simp only [value, polyValue]; rw [constant_eq_ofPoly, ofPoly_vec1]⟩
  | axisVariable i => exact ⟨Iff.rfl, fun _ => by
      simp only [value, polyValue]; rw [axisVariable_eq_ofPoly, ofPoly_vec1]⟩
  | unary op => exact ⟨Iff.rfl, fun _ => by
      simp only [value, polyValue]; rw [Unary.value_ofPoly, ofPoly_vec1]⟩
  | binary op =>
      refine ⟨Binary.domain_ofPoly basis op _ _, fun h => ?_⟩
      simp only [value, polyValue]
      rw [Binary.value_ofPoly basis op _ _ h, ofPoly_vec1]
  | compose a b ha hb =>
      simp only [Defined, PolyDefined, value, polyValue]
      constructor
      · rw [(ha x).1]
        apply and_congr_right
        intro pa
        rw [(ha x).2 pa]
        exact (hb _).1
      · rintro ⟨pa, pb⟩
        rw [(ha x).2 pa]
        exact (hb _).2 pb
  | parallel a b ha hb =>
      simp only [Defined, PolyDefined, value, polyValue]
      have hl : left (fun j => ofPoly basis (x j)) =
          fun i => ofPoly basis (x (Fin.castAdd _ i)) := rfl
      have hr : right (fun j => ofPoly basis (x j)) =
          fun i => ofPoly basis (x (Fin.natAdd _ i)) := rfl
      rw [hl, hr]
      refine ⟨and_congr (ha _).1 (hb _).1, fun ⟨pa, pb⟩ => ?_⟩
      rw [(ha _).2 pa, (hb _).2 pb, append_ofPoly]

/-- On realized inputs, circuit definedness is the polynomial side condition. -/
theorem Circuit.defined_ofPoly {basis : Basis} {d n m : Nat} (c : Circuit basis d n m)
    (x : Fin n → Poly d) :
    c.Defined (fun j => ofPoly basis (x j)) ↔ c.PolyDefined x :=
  (c.ofPoly_aux x).1

/-- Realized inputs give realized outputs: the polynomial semantics. -/
theorem Circuit.value_ofPoly {basis : Basis} {d n m : Nat} (c : Circuit basis d n m)
    (x : Fin n → Poly d) (defined : c.PolyDefined x) :
    c.value (fun j => ofPoly basis (x j)) = fun j => ofPoly basis (c.polyValue x j) :=
  (c.ofPoly_aux x).2 defined

/-- The original stream relation on realized inputs, stated through
`Circuit.rel_iff`: outputs are exactly the realized polynomial outputs. -/
theorem Circuit.rel_ofPoly {basis : Basis} {d n m : Nat} (c : Circuit basis d n m)
    (x : Fin n → Poly d) (y : StreamPoint d m) :
    c.Rel (fun j => ofPoly basis (x j)) y ↔
      c.PolyDefined x ∧ y = fun j => ofPoly basis (c.polyValue x j) := by
  rw [Circuit.rel_iff, c.defined_ofPoly]
  constructor
  · rintro ⟨h, rfl⟩; exact ⟨h, c.value_ofPoly x h⟩
  · rintro ⟨h, rfl⟩; exact ⟨h, (c.value_ofPoly x h).symm⟩

end Gimle.Asgard.Streams
