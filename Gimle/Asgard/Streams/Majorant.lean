import Gimle.Asgard.Streams.Tail
import Gimle.Asgard.Streams.Grid
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! # A calculus for coefficient majorants

`Tail.lean` certifies a truncation from a proved majorant `|a_α| ≤ M ∏ R_i^{−α_i}`
but says nothing about how majorants combine. This module supplies what a
quotient of streams needs, in the OGF reading (ordinary coefficients, where
the stream *is* its `MvPowerSeries`): scaling, monotonicity in the radii, the
Cauchy product (bounds multiply, radii halve), and the multiplicative inverse
of a stream with nonzero constant term (bound `1/|c|`, radii shrunk until the
tail of the rest is small). It also gives the ordinary derivative its
algebra: additivity, the Leibniz rule and commutation of axes, so that
formal identities between quotients close by `ring`. -/
namespace Gimle.Asgard.Streams

open MvPowerSeries Lowering

/-! ## The ordinary derivative as a derivation -/

/-- The OGF derivative along `i`, on raw `MvPowerSeries`. -/
noncomputable abbrev ogfD {d : Nat} (i : Fin d) (a : Stream d) : Stream d := derivative .ogf i a

/-- The coefficient formula of the derivative. -/
theorem ogfD_apply {d : Nat} (i : Fin d) (a : Stream d) (n : Index d) :
    ogfD i a n = (n i + 1 : ℚ) * a (n.update i (n i + 1)) := rfl

theorem coeff_ogfD {d : Nat} (i : Fin d) (a : Stream d) (n : Index d) :
    coeff n (ogfD i a) = (n i + 1 : ℚ) * a (n.update i (n i + 1)) := rfl

/-- Additivity. -/
theorem ogfD_add {d : Nat} (i : Fin d) (a b : Stream d) : ogfD i (a + b) = ogfD i a + ogfD i b := by
  funext n
  change (n i + 1 : ℚ) * (a + b) (n.update i (n i + 1)) = _
  change _ = (n i + 1 : ℚ) * a (n.update i (n i + 1)) + (n i + 1 : ℚ) * b (n.update i (n i + 1))
  rw [show (a + b) (n.update i (n i + 1)) = a (n.update i (n i + 1)) + b (n.update i (n i + 1))
    from rfl]
  ring

theorem ogfD_neg {d : Nat} (i : Fin d) (a : Stream d) : ogfD i (-a) = -ogfD i a := by
  funext n
  change (n i + 1 : ℚ) * (-a) (n.update i (n i + 1)) = -((n i + 1 : ℚ) * a (n.update i (n i + 1)))
  rw [show (-a) (n.update i (n i + 1)) = -(a (n.update i (n i + 1))) from rfl]
  ring

theorem ogfD_sub {d : Nat} (i : Fin d) (a b : Stream d) : ogfD i (a - b) = ogfD i a - ogfD i b := by
  rw [sub_eq_add_neg, ogfD_add, ogfD_neg, sub_eq_add_neg]

theorem ogfD_C {d : Nat} (i : Fin d) (q : ℚ) : ogfD i (C q : Stream d) = 0 := by
  funext n
  change (n i + 1 : ℚ) * (C q : Stream d) (n.update i (n i + 1)) = 0
  rw [show (C q : Stream d) (n.update i (n i + 1)) = coeff (n.update i (n i + 1)) (C q) from rfl,
    coeff_C, if_neg]
  · simp
  · intro h
    have := congrArg (fun m : Index d => m i) h
    simp at this

/-- Constants pass through the derivative. -/
theorem ogfD_C_mul {d : Nat} (i : Fin d) (q : ℚ) (a : Stream d) : ogfD i (C q * a) = C q * ogfD i a := by
  funext n
  change (n i + 1 : ℚ) * coeff (n.update i (n i + 1)) (C q * a) = coeff n (C q * ogfD i a)
  rw [coeff_C_mul, coeff_C_mul, coeff_apply]
  change _ = q * ((n i + 1 : ℚ) * a (n.update i (n i + 1)))
  ring

/-- Each coefficient scaled by its degree along `i`. -/
noncomputable def degreeScale {d : Nat} (i : Fin d) (a : Stream d) : Stream d :=
  fun n => (n i : ℚ) * a n

/-- Its coefficient. -/
theorem coeff_degreeScale {d : Nat} (i : Fin d) (a : Stream d) (n : Index d) :
    coeff n (degreeScale i a) = (n i : ℚ) * a n := rfl

/-- `X_i · D_i a` multiplies each coefficient by its degree along `i`. -/
theorem X_mul_ogfD {d : Nat} (i : Fin d) (a : Stream d) : X i * ogfD i a = degreeScale i a := by
  funext n
  change coeff n (X i * ogfD i a) = (n i : ℚ) * a n
  rw [X_def, coeff_monomial_mul]
  by_cases h : Finsupp.single i 1 ≤ n
  · rw [if_pos h]
    have pos : 1 ≤ n i := by simpa using h i
    have back : (n - Finsupp.single i 1).update i ((n - Finsupp.single i 1 : Index d) i + 1) = n := by
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Finsupp.update_apply, hj]
    rw [show coeff (n - Finsupp.single i 1) (ogfD i a) = ogfD i a (n - Finsupp.single i 1) from rfl,
      ogfD_apply, back]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, one_mul]
    have cast : ((n i - 1 : ℕ) : ℚ) + 1 = n i := by exact_mod_cast Nat.sub_add_cancel pos
    rw [cast]
  · rw [if_neg h]
    have zero : n i = 0 := by
      by_contra ne
      apply h
      intro j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Ne.symm hj]
    simp [zero]

/-- **Leibniz.** Proved by cancelling `X_i`: `X_i · D_i` is the degree operator,
which is a derivation coefficientwise, and `MvPowerSeries ℚ` has no zero
divisors. -/
theorem ogfD_mul {d : Nat} (i : Fin d) (a b : Stream d) :
    ogfD i (a * b) = ogfD i a * b + a * ogfD i b := by
  have degree : X i * ogfD i (a * b) = X i * (ogfD i a * b + a * ogfD i b) := by
    rw [mul_add, ← mul_assoc, mul_left_comm (X i) a, X_mul_ogfD, X_mul_ogfD, X_mul_ogfD]
    funext n
    change (n i : ℚ) * coeff n (a * b) = coeff n (degreeScale i a * b) +
      coeff n (a * degreeScale i b)
    rw [coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [coeff_degreeScale]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    have split : (n i : ℚ) = p.1 i + p.2 i := by
      have := congrArg (fun m : Index d => m i) hp
      simp at this
      exact_mod_cast this.symm
    change (n i : ℚ) * (a p.1 * b p.2) = (p.1 i : ℚ) * a p.1 * b p.2 + a p.1 * ((p.2 i : ℚ) * b p.2)
    rw [split]
    ring
  have hx : (X i : Stream d) ≠ 0 := fun h => by
    have := congrArg (coeff (Finsupp.single i 1)) h
    simp [coeff_X] at this
  exact mul_left_cancel₀ hx degree

/-- Derivatives along two axes commute. -/
theorem ogfD_comm {d : Nat} (i j : Fin d) (a : Stream d) : ogfD i (ogfD j a) = ogfD j (ogfD i a) := by
  funext n
  by_cases h : i = j
  · subst h; rfl
  rw [ogfD_apply, ogfD_apply, ogfD_apply, ogfD_apply]
  have e : (n.update i (n i + 1)).update j ((n.update i (n i + 1)) j + 1) =
      (n.update j (n j + 1)).update i ((n.update j (n j + 1)) i + 1) := by
    ext k
    by_cases hk : k = i
    · subst hk; simp [Finsupp.update_apply, h, Ne.symm h]
    by_cases hk' : k = j
    · subst hk'; simp [Finsupp.update_apply, h, Ne.symm h]
    simp [Finsupp.update_apply, hk, hk']
  rw [e]
  simp [Finsupp.update_apply, h, Ne.symm h]
  ring

/-- The derivative of the inverse, from Leibniz on `φ · φ⁻¹ = 1`. -/
theorem ogfD_inv {d : Nat} (i : Fin d) (φ : Stream d) (h : constantCoeff φ ≠ 0) :
    ogfD i φ⁻¹ = -(φ⁻¹ * φ⁻¹ * ogfD i φ) := by
  have one : φ * φ⁻¹ = 1 := MvPowerSeries.mul_inv_cancel φ h
  have := congrArg (ogfD i) one
  rw [ogfD_mul, show (1 : Stream d) = C 1 from (map_one C).symm, ogfD_C] at this
  have key : φ⁻¹ * (ogfD i φ * φ⁻¹ + φ * ogfD i φ⁻¹) = 0 := by rw [this, mul_zero]
  have expand : φ⁻¹ * (ogfD i φ * φ⁻¹ + φ * ogfD i φ⁻¹) = φ⁻¹ * φ⁻¹ * ogfD i φ + ogfD i φ⁻¹ := by
    calc φ⁻¹ * (ogfD i φ * φ⁻¹ + φ * ogfD i φ⁻¹) = φ⁻¹ * φ⁻¹ * ogfD i φ + (φ⁻¹ * φ) * ogfD i φ⁻¹ := by ring
      _ = φ⁻¹ * φ⁻¹ * ogfD i φ + ogfD i φ⁻¹ := by rw [mul_comm φ⁻¹ φ, one, one_mul]
  rw [expand] at key
  linear_combination key

/-! ## Combining majorants -/

/-- A majorant read on ordinary coefficients: `|a_α| ≤ M ∏ R_i^(−α_i)`. -/
theorem majorizes_ogf_iff {d : Nat} (a : Stream d) (m : Majorant d) :
    Majorizes .ogf a m ↔ ∀ α : Index d, |coeff α a| ≤ m.bound * ∏ i, (m.radius i ^ α i)⁻¹ :=
  Iff.rfl

/-- The weight `∏ R_i^(−α_i)` of a majorant at an index. -/
noncomputable def radiiWeight {d : Nat} (R : Fin d → ℚ) (α : Index d) : ℚ := ∏ i, (R i ^ α i)⁻¹

/-- Weights are positive. -/
theorem radiiWeight_pos {d : Nat} {R : Fin d → ℚ} (hR : ∀ i, 0 < R i) (α : Index d) : 0 < radiiWeight R α :=
  Finset.prod_pos fun i _ => inv_pos.mpr (pow_pos (hR i) _)

/-- Weights are multiplicative in the index. -/
theorem radiiWeight_add {d : Nat} (R : Fin d → ℚ) (α β : Index d) :
    radiiWeight R (α + β) = radiiWeight R α * radiiWeight R β := by
  unfold radiiWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply, pow_add, mul_inv]

/-- Shrinking the radii and raising the bound keeps a majorant. -/
theorem majorizes_mono {d : Nat} {a : Stream d} {m : Majorant d} (h : Majorizes .ogf a m)
    (m' : Majorant d) (bound : m.bound ≤ m'.bound)
    (radius : ∀ i, m'.radius i ≤ m.radius i) :
    Majorizes .ogf a m' := by
  intro α
  refine (h α).trans (mul_le_mul bound ?_ (le_of_lt (radiiWeight_pos m.radius_pos α)) m'.bound_nonneg)
  refine Finset.prod_le_prod (fun i _ => le_of_lt (inv_pos.mpr (pow_pos (m.radius_pos i) _)))
    fun i _ => ?_
  exact inv_anti₀ (pow_pos (m'.radius_pos i) _) (pow_le_pow_left₀ (le_of_lt (m'.radius_pos i))
    (radius i) _)

/-- Scaling by a constant scales the bound. -/
theorem majorizes_C_mul {d : Nat} {a : Stream d} {m : Majorant d} (h : Majorizes .ogf a m)
    (q : ℚ) : Majorizes .ogf (C q * a)
      ⟨|q| * m.bound, m.radius, mul_nonneg (abs_nonneg q) m.bound_nonneg, m.radius_pos⟩ := by
  rw [majorizes_ogf_iff] at h ⊢
  intro α
  rw [coeff_C_mul, abs_mul]
  calc |q| * |coeff α a| ≤ |q| * (m.bound * ∏ i, (m.radius i ^ α i)⁻¹) :=
        mul_le_mul_of_nonneg_left (h α) (abs_nonneg q)
    _ = _ := by ring

/-- The antidiagonal of `α` has `∏ (α_i + 1)` elements: it is the grid below `α`. -/
theorem grid_length {d : Nat} (k : Degrees d) : (grid d k).length = ∏ i, (k i + 1) := by
  induction d with
  | zero => simp [grid]
  | succ d ih =>
      simp only [grid, List.length_flatMap, List.length_map, ih, List.map_const', List.length_range,
        List.sum_replicate, smul_eq_mul, Fin.prod_univ_succ]
      rfl

/-- The cardinality of the antidiagonal, as a rational. -/
theorem card_antidiagonal_eq {d : Nat} (α : Index d) :
    ((Finset.antidiagonal α).card : ℚ) = ∏ i, ((α i : ℚ) + 1) := by
  have hk : Degrees.toIndex (⇑α : Degrees d) = α := Finsupp.ext fun i => rfl
  have ones : ((Finset.antidiagonal α).card : ℚ) = ∑ _p ∈ Finset.antidiagonal α, (1 : ℚ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [ones, ← hk, sum_antidiagonal (⇑α : Degrees d) fun _ _ => (1 : ℚ)]
  simp only [List.map_const', List.sum_replicate, grid_length, nsmul_eq_mul, mul_one]
  push_cast
  rfl

/-- At most `2^|α|` terms. -/
theorem card_antidiagonal_le {d : Nat} (α : Index d) :
    ((Finset.antidiagonal α).card : ℚ) ≤ ∏ i, (2 : ℚ) ^ α i := by
  rw [card_antidiagonal_eq]
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  exact_mod_cast Nat.lt_two_pow_self (n := α i)

/-- **Products.** Bounds multiply and radii halve: the antidiagonal of `α` has
at most `2^|α|` terms. -/
theorem majorizes_mul {d : Nat} {a b : Stream d} {ma mb : Majorant d} (R : Fin d → ℚ)
    (ha : Majorizes .ogf a ma) (hb : Majorizes .ogf b mb)
    (ra : ∀ i, ma.radius i = R i) (rb : ∀ i, mb.radius i = R i) :
    Majorizes .ogf (a * b)
      ⟨ma.bound * mb.bound, fun i => R i / 2, mul_nonneg ma.bound_nonneg mb.bound_nonneg,
        fun i => by rw [← ra i]; exact half_pos (ma.radius_pos i)⟩ := by
  rw [majorizes_ogf_iff] at ha hb ⊢
  intro α
  have hR : ∀ i, 0 < R i := fun i => ra i ▸ ma.radius_pos i
  rw [coeff_mul]
  calc |∑ p ∈ Finset.antidiagonal α, coeff p.1 a * coeff p.2 b|
      ≤ ∑ p ∈ Finset.antidiagonal α, |coeff p.1 a * coeff p.2 b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal α, ma.bound * mb.bound * radiiWeight R α := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_antidiagonal] at hp
        rw [abs_mul]
        have h1 := ha p.1
        have h2 := hb p.2
        simp only [ra, rb] at h1 h2
        calc |coeff p.1 a| * |coeff p.2 b| ≤ (ma.bound * radiiWeight R p.1) * (mb.bound * radiiWeight R p.2) :=
              mul_le_mul h1 h2 (abs_nonneg _)
                (mul_nonneg ma.bound_nonneg (le_of_lt (radiiWeight_pos hR p.1)))
          _ = ma.bound * mb.bound * radiiWeight R (p.1 + p.2) := by rw [radiiWeight_add]; ring
          _ = ma.bound * mb.bound * radiiWeight R α := by rw [hp]
    _ = (Finset.antidiagonal α).card * (ma.bound * mb.bound * radiiWeight R α) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ i, (2 : ℚ) ^ α i) * (ma.bound * mb.bound * radiiWeight R α) :=
        mul_le_mul_of_nonneg_right (card_antidiagonal_le α)
          (mul_nonneg (mul_nonneg ma.bound_nonneg mb.bound_nonneg) (le_of_lt (radiiWeight_pos hR α)))
    _ = ma.bound * mb.bound * ∏ i, ((R i / 2) ^ α i)⁻¹ := by
        unfold radiiWeight
        rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [div_pow, inv_div, div_eq_mul_inv, mul_comm]


/-! ## The inverse -/

/-- `∏ q_i^{β_i}`, the ratio of two radiiWeights. -/
noncomputable def qpow {d : Nat} (q : Fin d → ℚ) (β : Index d) : ℚ := ∏ i, q i ^ β i

/-- The empty index has ratio power `1`. -/
theorem qpow_zero {d : Nat} (q : Fin d → ℚ) : qpow q 0 = 1 := by simp [qpow]

/-- A weight at the larger radii is the weight at the smaller times a ratio power. -/
theorem radiiWeight_eq_radiiWeight_mul_qpow {d : Nat} {R r : Fin d → ℚ} (hR : ∀ i, 0 < R i)
    (hr : ∀ i, 0 < r i) (β : Index d) :
    radiiWeight R β = radiiWeight r β * qpow (fun i => r i / R i) β := by
  unfold radiiWeight qpow
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have := (hR i).ne'
  have := (hr i).ne'
  rw [div_pow]
  field_simp

/-- The first components of the antidiagonal of `α` run over the box below `α`,
so a product-form sum over them factors axis by axis. -/
theorem sum_antidiagonal_qpow {d : Nat} (q : Fin d → ℚ) (α : Index d) :
    ∑ p ∈ Finset.antidiagonal α, qpow q p.1 = ∏ i, ∑ j ∈ Finset.range (α i + 1), q i ^ j := by
  have hk : Degrees.toIndex (⇑α : Degrees d) = α := Finsupp.ext fun i => rfl
  rw [← hk, sum_antidiagonal (⇑α : Degrees d) fun p _ => qpow q p,
    ← List.sum_toFinset _ (grid_nodup (⇑α : Degrees d)), Finset.prod_univ_sum]
  have box : (grid d (⇑α : Degrees d)).toFinset = Fintype.piFinset fun i => Finset.range (α i + 1) := by
    ext g
    simp [mem_grid, Fintype.mem_piFinset]
  rw [box]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [qpow, Degrees.toIndex_apply]

/-- A partial geometric sum with ratio in `[0, 1)` is below `(1 − q)⁻¹`. -/
theorem geom_partial_le {q : ℚ} (h0 : 0 ≤ q) (h1 : q < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, q ^ j ≤ (1 - q)⁻¹ := by
  have hq : q ≠ 1 := h1.ne
  rw [geom_sum_eq hq, div_le_iff_of_neg (by linarith : q - 1 < 0)]
  have e : (1 - q)⁻¹ * (q - 1) = -1 := by
    have : (1 - q) ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  linarith [pow_nonneg h0 n]

/-- The sum of ratio powers over the box below `α`, minus the empty index, is below
`∏ (1 − q_i)⁻¹ − 1`. -/
theorem sum_antidiagonal_qpow_lt_le {d : Nat} {q : Fin d → ℚ} (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∀ i, q i < 1) (α : Index d) :
    ∑ p ∈ Finset.antidiagonal α, (if p.2 < α then qpow q p.1 else 0) ≤
      (∏ i, (1 - q i)⁻¹) - 1 := by
  have mem : ((0 : Index d), α) ∈ Finset.antidiagonal α := by simp
  have filter_eq : (Finset.antidiagonal α).filter (fun p => p.2 < α) =
      (Finset.antidiagonal α).erase (0, α) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_antidiagonal]
    constructor
    · rintro ⟨sum, lt⟩
      refine ⟨fun e => ?_, sum⟩
      rw [e] at lt
      exact lt_irrefl _ lt
    · rintro ⟨ne, sum⟩
      refine ⟨sum, lt_of_le_of_ne ?_ fun e => ne ?_⟩
      · rw [← sum]; exact le_add_self
      · have first : p.1 = 0 := by
          rw [e] at sum
          exact add_right_cancel (sum.trans (zero_add α).symm)
        exact Prod.ext first e
  rw [← Finset.sum_filter, filter_eq, Finset.sum_erase_eq_sub mem, qpow_zero,
    sum_antidiagonal_qpow]
  refine sub_le_sub_right ?_ 1
  exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => pow_nonneg (hq0 i) _)
    fun i _ => geom_partial_le (hq0 i) (hq1 i) _
/-- **Inverse.** If `φ` has constant term `c` and the rest of it is majorized
by `M` at radii `R`, then `φ⁻¹` is majorized by `1/|c|` at any smaller radii `r`
whose ratio tail is small: `(M/|c|)(∏ (1 − r_i/R_i)⁻¹ − 1) ≤ 1`. By
well-founded induction on the index through `coeff_inv`. (`c = 0` is allowed: Mathlib's inverse is then `0`,
`M / |c|` is `0`, and the bound `0 ≤ 0` is trivially true.) -/
theorem coeff_inv_le {d : Nat} (φ : Stream d) {c M : ℚ} (hc : constantCoeff φ = c)
    (hM : 0 ≤ M) {R r : Fin d → ℚ} (hR : ∀ i, 0 < R i) (hr : ∀ i, 0 < r i)
    (inside : ∀ i, r i < R i)
    (rest : ∀ α : Index d, α ≠ 0 → |coeff α φ| ≤ M * radiiWeight R α)
    (small : M / |c| * ((∏ i, (1 - r i / R i)⁻¹) - 1) ≤ 1) (α : Index d) :
    |coeff α φ⁻¹| ≤ |c|⁻¹ * radiiWeight r α := by
  refine WellFounded.induction (wellFounded_lt (α := Index d))
    (C := fun α => |coeff α φ⁻¹| ≤ |c|⁻¹ * radiiWeight r α) α ?_
  intro α ih
  set q : Fin d → ℚ := fun i => r i / R i with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => div_nonneg (le_of_lt (hr i)) (le_of_lt (hR i))
  have hq1 : ∀ i, q i < 1 := fun i => (div_lt_one (hR i)).mpr (inside i)
  by_cases hα : α = 0
  · subst hα
    rw [show coeff (0 : Index d) φ⁻¹ = (constantCoeff φ)⁻¹ from
      (congrFun coeff_zero_eq_constantCoeff φ⁻¹).trans (constantCoeff_inv φ), hc, abs_inv]
    simp [radiiWeight]
  rw [coeff_inv, if_neg hα, hc, abs_mul, abs_neg, abs_inv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg c))
  have wpos := radiiWeight_pos hr α
  calc |∑ x ∈ Finset.antidiagonal α, if x.2 < α then coeff x.1 φ * coeff x.2 φ⁻¹ else 0|
      ≤ ∑ x ∈ Finset.antidiagonal α, |if x.2 < α then coeff x.1 φ * coeff x.2 φ⁻¹ else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.antidiagonal α,
          (if x.2 < α then M * |c|⁻¹ * radiiWeight r α * qpow q x.1 else 0) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with lt
        · have first : x.1 ≠ 0 := fun e => by
            rw [e, zero_add] at hx
            rw [hx] at lt
            exact lt_irrefl _ lt
          rw [abs_mul]
          calc |coeff x.1 φ| * |coeff x.2 φ⁻¹|
              ≤ (M * radiiWeight R x.1) * (|c|⁻¹ * radiiWeight r x.2) :=
                mul_le_mul (rest x.1 first) (ih x.2 lt) (abs_nonneg _)
                  (mul_nonneg hM (le_of_lt (radiiWeight_pos hR x.1)))
            _ = M * |c|⁻¹ * radiiWeight r α * qpow q x.1 := by
                rw [radiiWeight_eq_radiiWeight_mul_qpow hR hr, ← hx, radiiWeight_add]
                ring
        · simp
    _ = M * |c|⁻¹ * radiiWeight r α *
          ∑ x ∈ Finset.antidiagonal α, (if x.2 < α then qpow q x.1 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
    _ ≤ M * |c|⁻¹ * radiiWeight r α * ((∏ i, (1 - q i)⁻¹) - 1) :=
        mul_le_mul_of_nonneg_left (sum_antidiagonal_qpow_lt_le hq0 hq1 α)
          (mul_nonneg (mul_nonneg hM (inv_nonneg.mpr (abs_nonneg c))) (le_of_lt wpos))
    _ = radiiWeight r α * (M / |c| * ((∏ i, (1 - q i)⁻¹) - 1)) := by ring
    _ ≤ radiiWeight r α * 1 := mul_le_mul_of_nonneg_left small (le_of_lt wpos)
    _ = radiiWeight r α := mul_one _

/-- The inverse's majorant, packaged for `Tail`. -/
theorem majorizes_inv {d : Nat} (φ : Stream d) {c M : ℚ} (hc : constantCoeff φ = c)
    (hM : 0 ≤ M) {R r : Fin d → ℚ} (hR : ∀ i, 0 < R i) (hr : ∀ i, 0 < r i)
    (inside : ∀ i, r i < R i)
    (rest : ∀ α : Index d, α ≠ 0 → |coeff α φ| ≤ M * radiiWeight R α)
    (small : M / |c| * ((∏ i, (1 - r i / R i)⁻¹) - 1) ≤ 1) :
    Majorizes .ogf φ⁻¹ ⟨|c|⁻¹, r, inv_nonneg.mpr (abs_nonneg c), hr⟩ := by
  rw [majorizes_ogf_iff]
  exact coeff_inv_le φ hc hM hR hr inside rest small

#print axioms ogfD_mul
#print axioms ogfD_inv
#print axioms majorizes_mul
#print axioms majorizes_inv
end Gimle.Asgard.Streams
