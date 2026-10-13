import Gimle.Asgard.Streams.TrigNorm
import Gimle.Asgard.Streams.Vorticity

/-! # Gevrey-1 growth for the viscous stream

For `ν > 0` the viscous term `νΔω_n` costs two derivatives, and no induction
in a scale closes: the `t`-series of the vorticity stream is not expected to
converge for periodic data (radius zero is the generic parabolic behaviour;
single-shell data are the exception, with an entire series), and nothing here
certifies a radius. What a short induction does give is Gevrey-1 growth,

  `l1 ω_n ≤ L Cⁿ n!`,  `L = l1 ω₀`,  `C = νK² + K L`,

for a start whose modes have size at most `K` (`gevrey_one`): the modes of
`ω_n` have size at most `(n+1)K` (`sizeLE_stream`), so `Δ` costs `((n+1)K)²`
and each transport one factor `(n−m+1)K`, and the crude `m!(n−m)! ≤ n!` closes
the induction with `Σ_{m ≤ n} (n−m+1) = (n+1)(n+2)/2 ≤ (n+1)²`. "Gevrey-1" is
meant for the formal series in `t`: a radius for its Borel transform, not for
the series itself. The docs record the Tonelli computation that makes radius
zero exact for viscous Burgers. -/
namespace Gimle.Asgard.Streams.Torus

/-! ## ℓ¹ bounds with the size -/

/-- `Δ` costs `K²` on modes of size at most `K`. -/
theorem l1_laplacian_le {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) :
    l1 (laplacian P) ≤ (K : ℚ) ^ 2 * l1 P := by
  have sub : (laplacian P).support ⊆ P.support := fun k hk => by
    rw [Finsupp.mem_support_iff] at hk ⊢
    rw [laplacian_apply] at hk
    exact right_ne_zero_of_mul hk
  rw [l1_eq_sum sub, l1_eq_sum subset_rfl, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [laplacian_apply, abs_mul, abs_neg]
  have hlam : |(lam k : ℚ)| ≤ (K : ℚ) ^ 2 := by
    rw [abs_of_nonneg (by exact_mod_cast (by simp [lam]; positivity : (0 : ℤ) ≤ lam k))]
    have h1 : lam k ≤ (size k : ℤ) ^ 2 := lam_le_size_sq k
    have h2 : (size k : ℤ) ^ 2 ≤ (K : ℤ) ^ 2 := by
      have := hP k hk
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast this) 2
    exact_mod_cast h1.trans h2
  exact mul_le_mul_of_nonneg_right hlam (abs_nonneg _)

/-- A transport by `Q` costs one factor `K` when `Q`'s modes have size at most `K`. -/
theorem l1_transport_le {K : ℕ} (P : TrigPoly) {Q : TrigPoly} (hQ : SizeLE K Q) :
    (l1 (transport P Q) : ℝ) ≤ l1 P * ((K : ℝ) * l1 Q) := by
  have h := wnorm_transport_le (le_refl (0 : ℝ)) P Q
  rw [wnorm_zero, wnorm_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast l1_nonneg P))
  rw [dnorm_eq_sum 0 subset_rfl, l1_eq_sum subset_rfl]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have : (size q : ℝ) ≤ K := by exact_mod_cast hQ q hq
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [mul_comm (K : ℝ)]
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

end Gimle.Asgard.Streams.Torus

namespace Gimle.Asgard.Streams.NS

open Torus TrigStream

variable (ν : ℚ) (b : TrigStream)

local notation "ω" => stream Basis.ogf ν b

/-- The modes of `ω_n` have size at most `(n+1)K`. -/
theorem sizeLE_stream {K : ℕ} (hb : SizeLE K (b 0)) : ∀ n, SizeLE ((n + 1) * K) (ω n) := by
  suffices h : ∀ n, ∀ m ≤ n, SizeLE ((m + 1) * K) (ω m) from fun n => h n n le_rfl
  intro n
  induction n with
  | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm, stream_slice]
      simpa using hb
  | succ n ih =>
      intro m hm
      rcases Nat.lt_or_ge m (n + 1) with lt | ge
      · exact ih m (by omega)
      have hm' : m = n + 1 := by omega
      subst hm'
      rw [stream_succ_ogf]
      refine sizeLE_smul _ (sizeLE_sub (sizeLE_smul _ (sizeLE_laplacian
        ((ih n le_rfl).mono (by nlinarith)))) (sizeLE_sum _ fun m hm => ?_))
      rw [Finset.mem_range] at hm
      have := sizeLE_transport (ih m (by omega)) (ih (n - m) (by omega))
      refine this.mono (le_of_eq ?_)
      have : m + (n - m) = n := Nat.add_sub_cancel' (by omega)
      nlinarith [this]

/-- `Σ_{m ≤ n} (m + 1) = (n+1)(n+2)/2`. -/
theorem sum_range_add_one (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), ((m : ℝ) + 1) = ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
  induction n with
  | zero => norm_num
  | succ k ihk =>
      rw [Finset.sum_range_succ, ihk]
      push_cast; ring

/-- `m!(n−m)! ≤ n!`. -/
theorem factorial_mul_factorial_le {m n : ℕ} (h : m ≤ n) :
    m.factorial * (n - m).factorial ≤ n.factorial := by
  have := Nat.choose_mul_factorial_mul_factorial h
  have pos := Nat.choose_pos h
  nlinarith [this, pos, Nat.factorial_pos m, Nat.factorial_pos (n - m)]

/-- **Gevrey-1.** For a start with modes of size at most `K` and ℓ¹ norm at
most `L`, `l1 ω_n ≤ L Cⁿ n!` with `C = νK² + K L`, for `ν ≥ 0`. -/
theorem gevrey_one (hν : 0 ≤ ν) {K : ℕ} (hb : SizeLE K (b 0)) {L : ℚ} (hL : l1 (b 0) ≤ L)
    (n : ℕ) : (l1 (ω n) : ℝ) ≤ L * ((ν : ℝ) * K ^ 2 + K * L) ^ n * n.factorial := by
  set C : ℝ := (ν : ℝ) * K ^ 2 + K * L with hC
  have L_nonneg : (0 : ℝ) ≤ L := by exact_mod_cast (l1_nonneg (b 0)).trans hL
  have ν_nonneg : (0 : ℝ) ≤ ν := by exact_mod_cast hν
  have C_nonneg : 0 ≤ C := by positivity
  suffices h : ∀ n, ∀ m ≤ n, (l1 (ω m) : ℝ) ≤ L * C ^ m * m.factorial from h n n le_rfl
  intro n
  induction n with
  | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm, stream_slice]
      simpa using (show (l1 (b 0) : ℝ) ≤ L by exact_mod_cast hL)
  | succ n ih =>
      intro m hm
      rcases Nat.lt_or_ge m (n + 1) with lt | ge
      · exact ih m (by omega)
      have hm' : m = n + 1 := by omega
      subst hm'
      rw [stream_succ_ogf]
      have c_eq : |(((n : ℝ) + 1)⁻¹)| = 1 / ((n : ℝ) + 1) := by
        rw [abs_of_pos (by positivity), one_div]
      -- the viscous term
      have visc : (l1 (ν • laplacian (ω n)) : ℝ) ≤ ν * ((n : ℝ) + 1) ^ 2 * K ^ 2 * (L * C ^ n * n.factorial) := by
        have h1 := l1_laplacian_le (sizeLE_stream ν b hb n)
        have h2 := ih n le_rfl
        rw [l1_smul, abs_of_nonneg hν]
        push_cast
        have : ((((n + 1) * K : ℕ) : ℚ) : ℝ) ^ 2 = ((n : ℝ) + 1) ^ 2 * K ^ 2 := by push_cast; ring
        have h1' : (l1 (laplacian (ω n)) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * K ^ 2 * l1 (ω n) := by
          have := (Rat.cast_le (K := ℝ)).mpr h1
          push_cast at this
          linarith [this]
        calc (ν : ℝ) * l1 (laplacian (ω n)) ≤ ν * (((n : ℝ) + 1) ^ 2 * K ^ 2 * l1 (ω n)) :=
              mul_le_mul_of_nonneg_left h1' ν_nonneg
          _ ≤ ν * (((n : ℝ) + 1) ^ 2 * K ^ 2 * (L * C ^ n * n.factorial)) := by gcongr
          _ = _ := by ring
      -- the transport terms
      have trans : ∀ m ∈ Finset.range (n + 1),
          (l1 (transport (ω m) (ω (n - m))) : ℝ) ≤
            K * L ^ 2 * C ^ n * n.factorial * (((n - m : ℕ) : ℝ) + 1) := by
        intro m hm
        rw [Finset.mem_range] at hm
        have h1 := ih m (by omega)
        have h2 := ih (n - m) (by omega)
        have hsize := sizeLE_stream ν b hb (n - m)
        have ht := l1_transport_le (ω m) hsize
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at ht
        have fac : (m.factorial : ℝ) * (n - m).factorial ≤ n.factorial := by
          exact_mod_cast factorial_mul_factorial_le (by omega : m ≤ n)
        have pow_split : C ^ m * C ^ (n - m) = C ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        calc (l1 (transport (ω m) (ω (n - m))) : ℝ)
            ≤ l1 (ω m) * (((((n - m : ℕ) : ℝ) + 1) * K) * l1 (ω (n - m))) := ht
          _ ≤ (L * C ^ m * m.factorial) * ((((n - m : ℕ) : ℝ) + 1) * K * (L * C ^ (n - m) * (n - m).factorial)) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
                (mul_nonneg (by positivity) (by exact_mod_cast l1_nonneg _)) (by positivity)
          _ = K * L ^ 2 * (C ^ m * C ^ (n - m)) * ((m.factorial : ℝ) * (n - m).factorial) *
              (((n - m : ℕ) : ℝ) + 1) := by ring
          _ ≤ K * L ^ 2 * C ^ n * n.factorial * (((n - m : ℕ) : ℝ) + 1) := by
              rw [pow_split]; gcongr
      have sum_index : ∑ m ∈ Finset.range (n + 1), (((n - m : ℕ) : ℝ) + 1) =
          ((n : ℝ) + 1) * ((n : ℝ) + 2) / 2 := by
        have := Finset.sum_range_reflect (fun m : ℕ => ((m : ℝ) + 1)) (n + 1)
        simp only [add_tsub_cancel_right] at this
        rw [this, sum_range_add_one]
      have transport_sum : (l1 (∑ m ∈ Finset.range (n + 1), transport (ω m) (ω (n - m))) : ℝ) ≤
          K * L ^ 2 * C ^ n * n.factorial * (((n : ℝ) + 1) * ((n : ℝ) + 2) / 2) := by
        have := l1_sum_le (Finset.range (n + 1)) fun m => transport (ω m) (ω (n - m))
        have cast := (Rat.cast_le (K := ℝ)).mpr this
        push_cast at cast
        refine cast.trans ?_
        rw [← sum_index, Finset.mul_sum]
        exact Finset.sum_le_sum trans
      -- assemble
      rw [l1_smul]
      push_cast
      rw [c_eq]
      have sub := l1_sub_le (ν • laplacian (ω n)) (∑ m ∈ Finset.range (n + 1), transport (ω m) (ω (n - m)))
      have cast := (Rat.cast_le (K := ℝ)).mpr sub
      push_cast at cast
      have total := cast.trans (add_le_add visc transport_sum)
      have fac_succ : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
        push_cast [Nat.factorial_succ]; ring
      rw [fac_succ, pow_succ]
      have Xn : 0 ≤ L * C ^ n * n.factorial := by positivity
      calc (1 : ℝ) / ((n : ℝ) + 1) * l1 (ν • laplacian (ω n) - ∑ m ∈ Finset.range (n + 1),
            transport (ω m) (ω (n - m)))
          ≤ 1 / ((n : ℝ) + 1) * (ν * ((n : ℝ) + 1) ^ 2 * K ^ 2 * (L * C ^ n * n.factorial) +
              K * L ^ 2 * C ^ n * n.factorial * (((n : ℝ) + 1) * ((n : ℝ) + 2) / 2)) := by
            gcongr
        _ = (L * C ^ n * n.factorial) * (ν * K ^ 2 * ((n : ℝ) + 1) + K * L * (((n : ℝ) + 2) / 2)) := by
            field_simp
        _ ≤ (L * C ^ n * n.factorial) * (C * ((n : ℝ) + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ Xn
            rw [hC]
            nlinarith [mul_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K) L_nonneg,
              (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        _ = L * (C ^ n * C) * (((n : ℝ) + 1) * n.factorial) := by ring

#print axioms l1_laplacian_le
#print axioms l1_transport_le
#print axioms sizeLE_stream
#print axioms gevrey_one
end Gimle.Asgard.Streams.NS
