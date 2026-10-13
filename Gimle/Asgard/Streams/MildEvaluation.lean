import Gimle.Asgard.Streams.Mild
import Gimle.Asgard.Streams.Vorticity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Physical evaluation of the mild stream and its zero-viscosity agreement.

Evaluation forgets the redundant exponential indices at ν = 0. Statements
compare evaluated Fourier coefficients, never the redundant exact carriers.
-/
namespace Gimle.Asgard.Streams.Mild

open Torus

/-- Real Fourier polynomials obtained by physical evaluation. -/
abbrev RealPoly := Wave →₀ ℝ

namespace RealPoly

/-- The bilinear transport term as a linear map in each argument: on single
modes, `transport (e_p) (e_q) = coupling p q · e_{p+q}`. -/
noncomputable def transportₗ : RealPoly →ₗ[ℝ] RealPoly →ₗ[ℝ] RealPoly :=
  Finsupp.lsum ℝ fun p => LinearMap.toSpanSingleton ℝ _
    (Finsupp.lsum ℝ fun q => LinearMap.toSpanSingleton ℝ _ (Finsupp.single (p + q) (coupling p q : ℝ)))

/-- `transport P Q`: the bilinear form with the coupling `(p × q)/|p|²` on
`p + q = k`, the Fourier side of `u·∇Q` for `u = ∇⊥Δ⁻¹P`. -/
noncomputable def transport (P Q : RealPoly) : RealPoly := transportₗ P Q

theorem transport_eq_sum (P Q : RealPoly) :
    transport P Q = P.sum fun p a => a • Q.sum fun q b => b • Finsupp.single (p + q) (coupling p q : ℝ) := by
  simp only [transport, transportₗ, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.toSpanSingleton_apply]

theorem transport_add_left (P P' Q : RealPoly) :
    transport (P + P') Q = transport P Q + transport P' Q := by
  simp [transport, map_add]

theorem transport_add_right (P Q Q' : RealPoly) :
    transport P (Q + Q') = transport P Q + transport P Q' := by
  simp [transport, map_add]

theorem transport_zero_left (Q : RealPoly) : transport 0 Q = 0 := by simp [transport]

theorem transport_zero_right (P : RealPoly) : transport P 0 = 0 := by simp [transport]

/-- On single modes the transport is the coupling on the sum of the modes. -/
theorem transport_single_single (p q : Wave) (a b : ℝ) :
    transport (Finsupp.single p a) (Finsupp.single q b) =
      Finsupp.single (p + q) ((coupling p q : ℝ) * a * b) := by
  rw [transport_eq_sum, Finsupp.sum_single_index, Finsupp.sum_single_index]
  · rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
    congr 1; ring
  · simp
  · simp

/-- The coefficient at `k`: a double sum over the supports with `p + q = k`. -/
theorem transport_apply (P Q : RealPoly) (k : Wave) :
    transport P Q k = ∑ p ∈ P.support, ∑ q ∈ Q.support,
      if p + q = k then (coupling p q : ℝ) * P p * Q q else 0 := by
  rw [transport_eq_sum, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem transport_smul_left (c : ℝ) (P Q : RealPoly) :
    transport (c • P) Q = c • transport P Q := by simp [transport]

theorem transport_smul_right (c : ℝ) (P Q : RealPoly) :
    transport P (c • Q) = c • transport P Q := by simp [transport]

end RealPoly

@[simp] theorem eval_single (ν : ℚ) (t : ℝ) (k : Wave) (P : ExpPoly) :
    eval ν t (Finsupp.single k P) = Finsupp.single k (ExpPoly.eval ν t P) := by
  apply Finsupp.ext
  intro j
  by_cases h : k = j <;> simp [h]

/-- Physical evaluation respects the exact Fourier transport. -/
theorem eval_transport (ν : ℚ) (t : ℝ) (P Q : MildPoly) :
    eval ν t (transport P Q) = RealPoly.transport (eval ν t P) (eval ν t Q) := by
  induction P using Finsupp.induction_linear with
  | zero => simp [transport_zero_left, RealPoly.transport_zero_left]
  | add P P' hP hP' => simp [transport_add_left, RealPoly.transport_add_left, hP, hP']
  | single p a =>
      induction Q using Finsupp.induction_linear with
      | zero => simp [transport_zero_right, RealPoly.transport_zero_right]
      | add Q Q' hQ hQ' => simp [transport_add_right, RealPoly.transport_add_right, hQ, hQ']
      | single q b => simp [transport_single_single, RealPoly.transport_single_single]

/-- Cast exact rational Fourier data to real coefficients. -/
noncomputable def realEmbed : TrigPoly →ₗ[ℚ] RealPoly :=
  Finsupp.mapRange.linearMap (Algebra.linearMap ℚ ℝ)

@[simp] theorem realEmbed_apply (P : TrigPoly) (k : Wave) : realEmbed P k = (P k : ℝ) := rfl

@[simp] theorem realEmbed_single (k : Wave) (a : ℚ) :
    realEmbed (Finsupp.single k a) = Finsupp.single k (a : ℝ) := by
  apply Finsupp.ext
  intro j
  by_cases h : k = j <;> simp [h]

theorem realEmbed_transport (P Q : TrigPoly) :
    realEmbed (Torus.transport P Q) = RealPoly.transport (realEmbed P) (realEmbed Q) := by
  induction P using Finsupp.induction_linear with
  | zero => simp [Torus.transport_zero_left, RealPoly.transport_zero_left]
  | add P P' hP hP' => simp [Torus.transport_add_left, RealPoly.transport_add_left, hP, hP']
  | single p a =>
      induction Q using Finsupp.induction_linear with
      | zero => simp [Torus.transport_zero_right, RealPoly.transport_zero_right]
      | add Q Q' hQ hQ' => simp [Torus.transport_add_right, RealPoly.transport_add_right, hQ, hQ']
      | single q b => simp [Torus.transport_single_single, RealPoly.transport_single_single]

/-- At zero viscosity the mild interaction terms evaluate to Euler's Taylor terms. -/
theorem wild_eval_zero (b : TrigStream) (n : ℕ) (t : ℝ) :
    eval 0 t (wild 0 (fun m => embed (b m)) n) =
      t ^ n • realEmbed (NS.stream .ogf 0 b n) := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
      cases n with
      | zero =>
          apply Finsupp.ext
          intro k
          simp [heat_apply, NS.stream_slice]
      | succ n =>
          let w := wild 0 (fun m => embed (b m))
          let S := ∑ m ∈ Finset.range (n + 1),
            Torus.transport (NS.stream .ogf 0 b m) (NS.stream .ogf 0 b (n - m))
          have hi (s : ℝ) : eval 0 s
              (∑ m ∈ Finset.range (n + 1), transport (w m) (w (n - m))) =
              s ^ n • realEmbed S := by
            dsimp only [S]
            simp only [map_sum, eval_transport]
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            have hm' := Finset.mem_range.mp hm
            rw [show eval 0 s (w m) = _ from ih m hm' s,
              show eval 0 s (w (n - m)) = _ from ih (n - m) (by omega) s,
              RealPoly.transport_smul_left, RealPoly.transport_smul_right,
              smul_smul, ← pow_add, Nat.add_sub_of_le (by omega : m ≤ n),
              ← realEmbed_transport]
          rw [wild_succ, NS.stream_succ_ogf]
          simp only [zero_smul, zero_sub, map_smul, map_neg]
          apply Finsupp.ext
          intro k
          have hik (s : ℝ) := congrArg (fun P : RealPoly => P k) (hi s)
          simp only [eval_apply, Finsupp.smul_apply, smul_eq_mul, Rat.cast_zero] at hik
          simp only [Finsupp.neg_apply, eval_apply, map_neg, duhamel_apply, Rat.cast_zero,
            ExpPoly.eval_duhamel_zero_viscosity]
          change -(∫ s in (0 : ℝ)..t, ExpPoly.eval 0 s
              ((∑ m ∈ Finset.range (n + 1), transport (w m) (w (n - m))) k)) = _
          simp_rw [hik]
          rw [intervalIntegral.integral_mul_const, integral_pow]
          simp [S, Algebra.smul_def, div_eq_mul_inv, mul_assoc]

/-- At initial physical time only the interaction-degree-zero term survives. -/
theorem wild_initial (ν : ℚ) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) (n : ℕ) :
    eval ν 0 (wild ν b n) = if n = 0 then realEmbed P else 0 := by
  cases n with
  | zero =>
      apply Finsupp.ext
      intro k
      simp [hb]
  | succ n =>
      apply Finsupp.ext
      intro k
      simp [wild_succ]

/-- The degree-zero heat equation requires a physical, constant-time initial slice. -/
theorem deriv_wild_zero (ν : ℚ) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) :
    deriv ν (wild ν b 0) = ν • laplacian (wild ν b 0) := by
  rw [wild_zero, hb]
  exact deriv_heat_embed ν P

#print axioms eval_transport
#print axioms wild_eval_zero
#print axioms wild_initial
#print axioms deriv_wild_zero

end Gimle.Asgard.Streams.Mild
