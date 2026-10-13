import Gimle.Asgard.Streams.MildNorm
import Gimle.Asgard.Streams.EulerRadius

/-! The Euler-scale bound for the mild interaction expansion at every
nonnegative viscosity. Time integration replaces Taylor coefficient division. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

variable {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P)
local notation "ω" => wild ν b
include hν hb

/-- The weighted scale estimate, uniformly at every nonnegative viscosity. -/
theorem wild_wnorm_bound {σ₀ M : ℝ} (hM : Torus.wnorm σ₀ P ≤ M) (n : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ₀ : σ < σ₀) {t : ℝ} (ht : 0 ≤ t) :
    mwnorm σ ν (ω n) t ≤ M * (24 * M / (σ₀ - σ)) ^ n * t ^ n / ((n : ℝ) + 1) ^ 2 := by
  have M_nonneg : 0 ≤ M := (Torus.wnorm_nonneg _ _).trans hM
  -- strong induction, carried as "every degree up to `n`"
  suffices h : ∀ n, ∀ m ≤ n, ∀ σ, 0 ≤ σ → σ < σ₀ → ∀ t, 0 ≤ t →
      mwnorm σ ν (ω m) t ≤ M * (24 * M / (σ₀ - σ)) ^ m * t ^ m / ((m : ℝ) + 1) ^ 2 from
    h n n le_rfl σ hσ hσ₀ t ht
  intro n
  induction n with
  | zero =>
      intro m hm σ _ hσ₀ t ht
      rw [Nat.le_zero.mp hm]
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_add, one_pow, div_one]
      rw [wild_zero, hb]
      exact (mwnorm_heat_embed_le σ hν P ht).trans ((Torus.wnorm_mono hσ₀.le P).trans hM)
  | succ n ih =>
      intro m hm σ hσ hσ₀ t ht
      rcases Nat.lt_or_ge m (n + 1) with lt | ge
      · exact ih m (by omega) σ hσ hσ₀ t ht
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
      have term : ∀ s, 0 ≤ s → ∀ m ∈ Finset.range (n + 1),
          mwnorm σ ν (ω m) s * mdnorm σ ν (ω (n - m)) s ≤
            (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * s ^ n *
              (1 / (((m : ℝ) + 1) ^ 2 * (((n - m : ℕ) : ℝ) + 1) ^ 2)) := by
        intro s hs m hm
        rw [Finset.mem_range] at hm
        have h1 := ih m (by omega) σ hσ hσ₀ s hs
        have h2 := ih (n - m) (by omega) σ' σ'_nonneg σ'_lt s hs
        have nag := mdnorm_le_mwnorm_div (show σ < σ' by linarith) ν (ω (n - m)) s
        have inv_δ : 1 / (2 * (σ' - σ)) = ((n : ℝ) + 2) / (2 * D) := by
          have e : σ' - σ = D / ((n : ℝ) + 2) := by rw [hσ', hδ]; ring
          rw [e]
          field_simp
        have h2' : mwnorm σ' ν (ω (n - m)) s ≤ 3 * M * A ^ (n - m) * s ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 := by
          refine h2.trans ?_
          rw [ratio, mul_pow]
          have r3 := NS.ratio_pow_le_three n (n - m) (by omega)
          have nn : 0 ≤ A ^ (n - m) * s ^ (n - m) := by positivity
          rw [div_le_div_iff_of_pos_right (by positivity)]
          have := mul_le_mul_of_nonneg_left r3 (mul_nonneg M_nonneg nn)
          nlinarith [this]
        have dn : mdnorm σ ν (ω (n - m)) s ≤ 3 * M * A ^ (n - m) * s ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 *
            (((n : ℝ) + 2) / (2 * D)) := by
          calc mdnorm σ ν (ω (n - m)) s ≤ mwnorm σ' ν (ω (n - m)) s / (2 * (σ' - σ)) := nag
            _ = mwnorm σ' ν (ω (n - m)) s * (1 / (2 * (σ' - σ))) := by rw [mul_one_div]
            _ ≤ 3 * M * A ^ (n - m) * s ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) / (2 * D)) := by
                rw [inv_δ]; exact mul_le_mul_of_nonneg_right h2' (by positivity)
        have pow_split : A ^ m * A ^ (n - m) = A ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        calc mwnorm σ ν (ω m) s * mdnorm σ ν (ω (n - m)) s
            ≤ (M * A ^ m * s ^ m / ((m : ℝ) + 1) ^ 2) *
              (3 * M * A ^ (n - m) * s ^ (n - m) / (((n - m : ℕ) : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) / (2 * D))) :=
              mul_le_mul h1 dn (mdnorm_nonneg _ _ _ _) (by positivity)
          _ = (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * s ^ n *
              (1 / (((m : ℝ) + 1) ^ 2 * (((n - m : ℕ) : ℝ) + 1) ^ 2)) := by
              have spow : s ^ m * s ^ (n - m) = s ^ n := by
                rw [← pow_add, Nat.add_sub_cancel' (by omega)]
              rw [← pow_split, ← spow]
              field_simp
      let F := ∑ m ∈ Finset.range (n + 1), transport (ω m) (ω (n - m))
      let C := (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * (8 / ((n : ℝ) + 2) ^ 2)
      have bound (s : ℝ) (hs : 0 ≤ s) : mwnorm σ ν F s ≤ C * s ^ n := by
        have sum_le : mwnorm σ ν F s ≤
            ∑ m ∈ Finset.range (n + 1), mwnorm σ ν (ω m) s * mdnorm σ ν (ω (n - m)) s :=
          (mwnorm_sum_le σ ν _ _ s).trans
            (Finset.sum_le_sum fun m _ => mwnorm_transport_le hσ ν (ω m) (ω (n - m)) s)
        refine sum_le.trans ((Finset.sum_le_sum (term s hs)).trans ?_)
        rw [← Finset.mul_sum]
        have hc := mul_le_mul_of_nonneg_left (NS.convolution_sum_le n)
          (show 0 ≤ (3 * M ^ 2 * A ^ n * ((n : ℝ) + 2) / (2 * D)) * s ^ n by positivity)
        simpa only [C, mul_assoc, mul_comm, mul_left_comm] using hc
      have integral_le : mwnorm σ ν (ω (n + 1)) t ≤ C * (t ^ (n + 1) / ((n : ℝ) + 1)) := by
        rw [wild_succ, mwnorm_neg]
        refine (mwnorm_duhamel_le σ hν F ht).trans ?_
        calc (∫ s in (0 : ℝ)..t, mwnorm σ ν F s) ≤ ∫ s in (0 : ℝ)..t, C * s ^ n :=
            intervalIntegral.integral_mono_on ht ((continuous_mwnorm σ ν F).intervalIntegrable 0 t)
              ((continuous_const.mul (continuous_id.pow n)).intervalIntegrable 0 t)
              (fun s hs => bound s hs.1)
          _ = _ := by rw [intervalIntegral.integral_const_mul, integral_pow]; simp
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
      have hf := mul_le_mul_of_nonneg_right final (pow_nonneg ht (n + 1))
      dsimp only [C] at integral_le
      refine integral_le.trans ?_
      convert hf using 1 <;> ring

/-- The unweighted geometric estimate for physical coefficients. -/
theorem wild_l1_bound {σ₀ M : ℝ} (hσ₀ : 0 < σ₀) (hM : Torus.wnorm σ₀ P ≤ M)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    RealPoly.l1 (eval ν t (ω n)) ≤ M * (24 * M / σ₀) ^ n * t ^ n := by
  have M_nonneg : 0 ≤ M := (Torus.wnorm_nonneg _ _).trans hM
  have h := wild_wnorm_bound hν b P hb hM n (σ := 0) le_rfl hσ₀ ht
  rw [sub_zero, mwnorm, RealPoly.wnorm_zero] at h
  refine h.trans ?_
  have one_le : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact div_le_self (by positivity) one_le

/-- Rational constants: the Euler time scale is valid at every nonnegative
viscosity for the mild expansion, including zero viscosity. -/
theorem wild_l1_geometric {K : ℕ} (hK : 1 ≤ K) (hsupp : Torus.SizeLE K P)
    {L : ℚ} (hL : Torus.l1 P ≤ L) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    RealPoly.l1 (eval ν t (ω n)) ≤ 3 * (L : ℝ) * (72 * L * K * t) ^ n := by
  have Kpos : (0 : ℝ) < K := by exact_mod_cast hK
  have L_nonneg : (0 : ℝ) ≤ L := by exact_mod_cast (Torus.l1_nonneg P).trans hL
  have hL' : (Torus.l1 P : ℝ) ≤ L := by exact_mod_cast hL
  have hM : Torus.wnorm (1 / K) P ≤ 3 * L := by
    refine (Torus.wnorm_le_l1_mul_exp (by positivity) hsupp).trans ?_
    rw [one_div, inv_mul_cancel₀ Kpos.ne']
    have := mul_le_mul hL' NS.exp_one_le_three (exp_pos 1).le L_nonneg
    linarith
  have h := wild_l1_bound hν b P hb (σ₀ := 1 / K) (by positivity) hM n ht
  have e : 24 * (3 * (L : ℝ)) / (1 / K) = 72 * L * K := by field_simp; ring
  rw [e] at h
  simpa only [mul_pow, mul_assoc] using h

#print axioms wild_wnorm_bound
#print axioms wild_l1_geometric
end Gimle.Asgard.Streams.Mild
