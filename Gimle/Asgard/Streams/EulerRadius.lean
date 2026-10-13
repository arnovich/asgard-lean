import Gimle.Asgard.Streams.TrigNorm
import Gimle.Asgard.Streams.TrigField
import Gimle.Asgard.Streams.Vorticity
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The Euler radius: a Cauchy–Kowalevski induction in a scale

For `ν = 0` the vorticity stream of `Streams.Vorticity` is the Euler
equation, `ω_{n+1} = −(n+1)⁻¹ Σ_{m ≤ n} transport ω_m ω_{n−m}`. Each step costs
one derivative (`wnorm_transport_le`), which a termwise geometric bound cannot
absorb, so the induction runs in the scale of weighted norms `wnorm σ`,
`0 ≤ σ < σ₀`, paying the derivative with a loss of radius (Nagumo,
`dnorm_le_wnorm_div`) and keeping the loss summable with the weight
`1/(n+1)²`:

  `wnorm σ (ω_n) ≤ M (C/(σ₀ − σ))ⁿ / (n+1)²`,  `C = 24 M`,  `M ≥ wnorm σ₀ ω₀`

(`euler_wnorm_bound`), the classical argument of Nirenberg and Nishida in its
weighted form, with the intermediate radius `σ' = σ + (σ₀ − σ)/(n+2)` and the
convolution sum `Σ_m 1/((m+1)²(n−m+1)²) ≤ 8/(n+2)²`. At `σ = 0` this is a
geometric bound on the ℓ¹ norms, `l1 ω_n ≤ M (24M/σ₀)ⁿ` (`euler_l1_bound`),
hence a radius of convergence in `t` of at least `σ₀/(24M)`. With `σ₀ = 1/K`
for a start whose modes have size at most `K` and ℓ¹ norm at most `L`, every
constant is rational: `l1 ω_n ≤ 3 L (72 L K)ⁿ` (`euler_l1_geometric`), a bound
the kernel can evaluate. The constant `24` is tight for the ingredients chosen
(`1/2` for `1/e` in Nagumo, `3` for `e`, `8` for the convolution sum, `2` for
`(n+2)/(n+1)`); with the sharp ingredients the same scheme closes near `9M`,
and the abstract Nirenberg–Nishida theorem gives a radius of the same order.
The Cauchy–Kowalevski device is pessimistic by nature; the radius it certifies
is small, and honest. Nothing here concerns `ν > 0`, where the viscous term
costs two derivatives and this induction does not close (`Streams.Gevrey`). -/
namespace Gimle.Asgard.Streams.NS

open Torus TrigStream Real

/-- The Euler recursion in the OGF reading: `stream_succ_ogf` at `ν = 0`. -/
theorem euler_succ (b : TrigStream) (n : ℕ) :
    stream .ogf 0 b (n + 1) = -(((n : ℚ) + 1)⁻¹ • ∑ m ∈ Finset.range (n + 1),
      transport (stream .ogf 0 b m) (stream .ogf 0 b (n - m))) := by
  rw [stream_succ_ogf, zero_smul, zero_sub, smul_neg]

/-- `e ≤ 3`. -/
theorem exp_one_le_three : exp 1 ≤ 3 := exp_one_lt_three.le

/-! ## Two sums -/

/-- `Σ_{m ≤ n} 1/(m+1)² ≤ 2 − 1/(n+1)`. -/
theorem sum_inv_sq_le (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith

/-- The convolution sum `Σ_{m ≤ n} 1/((m+1)²(n−m+1)²) ≤ 8/(n+2)²`. -/
theorem convolution_sum_le (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * (((n - m : ℕ) : ℝ) + 1) ^ 2) ≤
      8 / ((n : ℝ) + 2) ^ 2 := by
  have termwise : ∀ m ∈ Finset.range (n + 1),
      (1 : ℝ) / (((m : ℝ) + 1) ^ 2 * (((n - m : ℕ) : ℝ) + 1) ^ 2) ≤
        2 / ((n : ℝ) + 2) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2 + 1 / (((n - m : ℕ) : ℝ) + 1) ^ 2) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hsum : ((m : ℝ) + 1) + (((n - m : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
      have : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by
        rw [Nat.cast_sub (by omega)]
      rw [this]; ring
    set a : ℝ := (m : ℝ) + 1 with ha
    set c : ℝ := ((n - m : ℕ) : ℝ) + 1 with hc
    have apos : 0 < a := by positivity
    have cpos : 0 < c := by positivity
    rw [← hsum]
    rw [div_add_div _ _ (by positivity) (by positivity), div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a - c), mul_pos apos cpos, sq_nonneg (a * c)]
  refine (Finset.sum_le_sum termwise).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have reflect : ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / (((n - m : ℕ) : ℝ) + 1) ^ 2 =
      ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2 := by
    have := Finset.sum_range_reflect (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) (n + 1)
    simpa using this
  rw [reflect]
  have bound := sum_inv_sq_le n
  have le_two : ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 2 := by
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have pos : (0 : ℝ) < 2 / ((n : ℝ) + 2) ^ 2 := by positivity
  calc 2 / ((n : ℝ) + 2) ^ 2 * (∑ m ∈ Finset.range (n + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2 +
        ∑ m ∈ Finset.range (n + 1), (1 : ℝ) / ((m : ℝ) + 1) ^ 2)
      ≤ 2 / ((n : ℝ) + 2) ^ 2 * (2 + 2) := by gcongr
    _ = 8 / ((n : ℝ) + 2) ^ 2 := by ring

/-- `((n+2)/(n+1))^j ≤ 3` for `j ≤ n + 1`: below `(1 + 1/(n+1))^{n+1} ≤ e < 3`. -/
theorem ratio_pow_le_three (n j : ℕ) (hj : j ≤ n + 1) :
    (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ j ≤ 3 := by
  have base : 1 ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have step : ((n : ℝ) + 2) / ((n : ℝ) + 1) ≤ exp (1 / ((n : ℝ) + 1)) := by
    have h := add_one_le_exp (1 / ((n : ℝ) + 1))
    have e : ((n : ℝ) + 2) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 := by
      field_simp; ring
    rw [e]; exact h
  calc (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ j ≤ (((n : ℝ) + 2) / ((n : ℝ) + 1)) ^ (n + 1) :=
        pow_le_pow_right₀ base hj
    _ ≤ exp (1 / ((n : ℝ) + 1)) ^ (n + 1) := pow_le_pow_left₀ (by positivity) step _
    _ = exp 1 := by
        rw [← exp_nat_mul]
        congr 1
        push_cast
        field_simp
    _ ≤ 3 := exp_one_le_three

/-! ## The weighted induction -/

variable (b : TrigStream)

/-- The Euler stream from `b`, written `ω`. -/
local notation "ω" => stream Basis.ogf 0 b

/-- **The Cauchy–Kowalevski bound in a scale.** With `M ≥ wnorm σ₀ ω₀`, for every
`0 ≤ σ < σ₀` and every `n`, `wnorm σ ω_n ≤ M (24M/(σ₀ − σ))ⁿ / (n+1)²`. -/
theorem euler_wnorm_bound {σ₀ M : ℝ} (hM : wnorm σ₀ (b 0) ≤ M) (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ₀ : σ < σ₀) :
    wnorm σ (ω n) ≤ M * (24 * M / (σ₀ - σ)) ^ n / ((n : ℝ) + 1) ^ 2 := by
  have M_nonneg : 0 ≤ M := (wnorm_nonneg _ _).trans hM
  -- strong induction, carried as "every degree up to `n`"
  suffices h : ∀ n, ∀ m ≤ n, ∀ σ, 0 ≤ σ → σ < σ₀ →
      wnorm σ (ω m) ≤ M * (24 * M / (σ₀ - σ)) ^ m / ((m : ℝ) + 1) ^ 2 from
    h n n le_rfl σ hσ hσ₀
  intro n
  induction n with
  | zero =>
      intro m hm σ _ hσ₀
      rw [Nat.le_zero.mp hm]
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, one_pow, div_one]
      exact (wnorm_mono hσ₀.le _).trans (by rwa [stream_slice])
  | succ n ih =>
      intro m hm σ hσ hσ₀
      rcases Nat.lt_or_ge m (n + 1) with lt | ge
      · exact ih m (by omega) σ hσ hσ₀
      have hm' : m = n + 1 := by omega
      subst hm'
      -- the step: intermediate radius `σ' = σ + D/(n+2)`
      set D : ℝ := σ₀ - σ with hD
      have D_pos : 0 < D := sub_pos.mpr hσ₀
      have D_ne : D ≠ 0 := D_pos.ne'
      set A : ℝ := 24 * M / D with hA
      have A_nonneg : 0 ≤ A := by positivity
      set δ : ℝ := D / ((n : ℝ) + 2) with hδ
      have δ_pos : 0 < δ := by positivity
      set σ' : ℝ := σ + δ with hσ'
      have σ'_lt : σ' < σ₀ := by
        rw [hσ', hδ]
        have : D / ((n : ℝ) + 2) < D := by
          rw [div_lt_iff₀ (by positivity)]; nlinarith
        linarith
      have σ'_nonneg : 0 ≤ σ' := by positivity
      have gap : σ₀ - σ' = D * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
        rw [hσ', hδ, hD]; field_simp; ring
      -- the scale ratio at `σ'`
      have ratio : 24 * M / (σ₀ - σ') = A * (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
        rw [gap, hA]; field_simp
      -- each convolution term
      have term : ∀ m ∈ Finset.range (n + 1),
          wnorm σ (ω m) * dnorm σ (ω (n - m)) ≤
            (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) *
              (1 / (((m : ℝ) + 1) ^ 2 * (((n - m : ℕ) : ℝ) + 1) ^ 2)) := by
        intro m hm
        rw [Finset.mem_range] at hm
        have h1 := ih m (by omega) σ hσ hσ₀
        have h2 := ih (n - m) (by omega) σ' σ'_nonneg σ'_lt
        have nag := dnorm_le_wnorm_div (show σ < σ' by linarith) (ω (n - m))
        have inv_δ : 1 / (2 * (σ' - σ)) = ((n : ℝ) + 2) / (2 * D) := by
          have e : σ' - σ = D / ((n : ℝ) + 2) := by rw [hσ', hδ]; ring
          rw [e]
          field_simp
        have h2' : wnorm σ' (ω (n - m)) ≤ 3 * M * A ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 := by
          refine h2.trans ?_
          rw [ratio, mul_pow]
          have r3 := ratio_pow_le_three n (n - m) (by omega)
          have nn : 0 ≤ A ^ (n - m) := pow_nonneg A_nonneg _
          rw [div_le_div_iff_of_pos_right (by positivity)]
          have := mul_le_mul_of_nonneg_left r3 (mul_nonneg M_nonneg nn)
          nlinarith [this]
        have dn : dnorm σ (ω (n - m)) ≤ 3 * M * A ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 *
            (((n : ℝ) + 2) / (2 * D)) := by
          calc dnorm σ (ω (n - m)) ≤ wnorm σ' (ω (n - m)) / (2 * (σ' - σ)) := nag
            _ = wnorm σ' (ω (n - m)) * (1 / (2 * (σ' - σ))) := by rw [mul_one_div]
            _ ≤ 3 * M * A ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) / (2 * D)) := by
                rw [inv_δ]; exact mul_le_mul_of_nonneg_right h2' (by positivity)
        have pow_split : A ^ m * A ^ (n - m) = A ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        calc wnorm σ (ω m) * dnorm σ (ω (n - m))
            ≤ (M * A ^ m / ((m : ℝ) + 1) ^ 2) *
              (3 * M * A ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) / (2 * D))) :=
              mul_le_mul h1 dn (dnorm_nonneg _ _) (by positivity)
          _ = (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) *
              (1 / (((m : ℝ) + 1) ^ 2 * (((n - m : ℕ) : ℝ) + 1) ^ 2)) := by
              rw [← pow_split]
              field_simp
      -- assemble
      have c_eq : |((((n : ℚ) + 1)⁻¹ : ℚ) : ℝ)| = (1 : ℝ) / ((n : ℝ) + 1) := by
        push_cast
        rw [abs_of_pos (by positivity), one_div]
      rw [euler_succ, wnorm_neg, wnorm_smul, c_eq]
      have sum_le : wnorm σ (∑ m ∈ Finset.range (n + 1), transport (ω m) (ω (n - m))) ≤
          ∑ m ∈ Finset.range (n + 1), wnorm σ (ω m) * dnorm σ (ω (n - m)) :=
        (wnorm_sum_le σ _ _).trans
          (Finset.sum_le_sum fun m _ => wnorm_transport_le hσ (ω m) (ω (n - m)))
      have conv : ∑ m ∈ Finset.range (n + 1), wnorm σ (ω m) * dnorm σ (ω (n - m)) ≤
          (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * (8 / ((n : ℝ) + 2) ^ 2) := by
        refine (Finset.sum_le_sum term).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (convolution_sum_le n) (by positivity)
      have total := sum_le.trans conv
      -- both sides are `M² Aⁿ / D` times a rational function of `n`
      have final : (1 : ℝ) / ((n : ℝ) + 1) *
          ((3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * (8 / ((n : ℝ) + 2) ^ 2)) ≤
          M * A ^ (n + 1) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
        have X_nonneg : 0 ≤ M ^ 2 * A ^ n / D := by positivity
        have lhs_eq : (1 : ℝ) / ((n : ℝ) + 1) *
            ((3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * (8 / ((n : ℝ) + 2) ^ 2)) =
            M ^ 2 * A ^ n / D * (12 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
          field_simp; ring
        have rhs_eq : M * A ^ (n + 1) / (((n + 1 : ℕ) : ℝ) + 1) ^ 2 =
            M ^ 2 * A ^ n / D * (24 / ((n : ℝ) + 2) ^ 2) := by
          push_cast
          rw [pow_succ, hA]
          field_simp; ring
        rw [lhs_eq, rhs_eq]
        refine mul_le_mul_of_nonneg_left ?_ X_nonneg
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact (mul_le_mul_of_nonneg_left total (by positivity)).trans final

/-! ## Corollaries: a geometric ℓ¹ bound and a rational radius -/

/-- **Geometric ℓ¹ bound.** At `σ = 0`: `l1 ω_n ≤ M (24M/σ₀)ⁿ`, so the
`t`-series converges for `|t| < σ₀/(24M)`. -/
theorem euler_l1_bound {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) (hM : wnorm σ₀ (b 0) ≤ M) (n : ℕ) :
    (l1 (ω n) : ℝ) ≤ M * (24 * M / σ₀) ^ n := by
  have M_nonneg : 0 ≤ M := (wnorm_nonneg _ _).trans hM
  have h := euler_wnorm_bound b hM n (σ := 0) le_rfl hσ₀
  rw [sub_zero, wnorm_zero] at h
  refine h.trans ?_
  have one_le : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact div_le_self (mul_nonneg M_nonneg (pow_nonneg (div_nonneg (by linarith) hσ₀.le) n)) one_le

/-- **A rational radius.** For a start whose modes have size at most `K ≥ 1`
and whose ℓ¹ norm is at most `L`: `l1 ω_n ≤ 3L (72 L K)ⁿ` — the scale
`σ₀ = 1/K`, where `wnorm σ₀ ω₀ ≤ L e ≤ 3L`. The radius is at least
`1/(72 L K)`. -/
theorem euler_l1_geometric {K : ℕ} (hK : 1 ≤ K) (hsupp : SizeLE K (b 0)) {L : ℚ}
    (hL : l1 (b 0) ≤ L) (n : ℕ) : l1 (ω n) ≤ 3 * L * (72 * L * K) ^ n := by
  have Kpos : (0 : ℝ) < K := by exact_mod_cast hK
  have L_nonneg : (0 : ℝ) ≤ L := by exact_mod_cast (l1_nonneg (b 0)).trans hL
  have hL' : (l1 (b 0) : ℝ) ≤ L := by exact_mod_cast hL
  have hM : wnorm (1 / K) (b 0) ≤ 3 * L := by
    refine (wnorm_le_l1_mul_exp (by positivity) hsupp).trans ?_
    rw [one_div, inv_mul_cancel₀ Kpos.ne']
    have := mul_le_mul hL' exp_one_le_three (exp_pos 1).le L_nonneg
    linarith
  have h := euler_l1_bound b (σ₀ := 1 / K) (by positivity) hM n
  have e : 24 * (3 * (L : ℝ)) / (1 / K) = 72 * L * K := by field_simp; ring
  rw [e] at h
  exact_mod_cast h

/-- The same, as a `GeometricBound` for the field. -/
theorem euler_geometricBound {K : ℕ} (hK : 1 ≤ K) (hsupp : SizeLE K (b 0)) {L : ℚ}
    (hL : l1 (b 0) ≤ L) :
    TrigStream.GeometricBound (ω) (3 * L) (72 * L * K) := fun n => by
  have := euler_l1_geometric b hK hsupp hL n
  exact_mod_cast this

#print axioms euler_succ
#print axioms convolution_sum_le
#print axioms euler_wnorm_bound
#print axioms euler_l1_bound
#print axioms euler_l1_geometric
#print axioms euler_geometricBound
end Gimle.Asgard.Streams.NS
