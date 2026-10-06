import Gimle.Asgard.Streams.FourierExchanges
import Gimle.Asgard.Streams.MildModeCalculus

/-! The coefficient equation for the actual summed mild circuit output. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Finset

/-- Regroup an arbitrary absolutely summable degree pair by its total degree. -/
theorem interaction_hasSum {F : ℕ → ℕ → ℝ}
    (h : Summable (fun z : ℕ × ℕ => F z.1 z.2)) :
    HasSum (fun n => ∑ m ∈ range (n + 1), F m (n - m)) (∑' n, ∑' m, F n m) := by
  let e := HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hh := e.summable_iff.mpr h
  have he := hh.hasSum.sigma (fun n => (hasSum_fintype
    (fun z : antidiagonal n => F z.val.1 z.val.2)))
  simp only [Function.comp_def] at he
  rw [e.tsum_eq (fun z => F z.1 z.2), h.tsum_prod] at he
  have hf (n : ℕ) : (∑ z : antidiagonal n, F z.val.1 z.val.2) = ∑ m ∈ range (n + 1), F m (n - m) := by
    rw [sum_coe_sort (antidiagonal n) (fun z : ℕ × ℕ => F z.1 z.2), Nat.sum_antidiagonal_eq_sum_range_succ]
  simpa only [hf] using he

/-- The finite transport pairs are summable over both degrees. -/
theorem summable_transport_degree {ν : ℚ} {ω : Stream} {K : ℕ} {t C q : ℝ}
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ C * q ^ n)
    (k : Wave) : Summable (fun z : ℕ × ℕ => RealPoly.transport (eval ν t (ω z.1)) (eval ν t (ω z.2)) k) := by
  have hs := (summable_norm_transportTerm hK hC hq hq1 h k).of_norm
  let e := Equiv.prodProdProdComm ℕ ℕ Wave Wave
  have hh : Summable (fun z : (ℕ × ℕ) × Wave × Wave => transportTerm ν ω t k z.1.1 z.2.1 z.1.2 z.2.2) :=
    (e.summable_iff (f := fun z : (ℕ × Wave) × ℕ × Wave => transportTerm ν ω t k z.1.1 z.1.2 z.2.1 z.2.2)).mpr hs
  apply hh.prod.congr
  intro z
  rw [(hh.prod_factor z).tsum_prod]
  exact fourierTransport_finite (eval ν t (ω z.1)) (eval ν t (ω z.2)) k

variable {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P)
  {K : ℕ} (hK : SizeLE K (b 0)) {T M q : ℝ}
  (h : GeometricBound ν (wild ν b) T M q) (hq : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)
local notation "ω" => wild ν b
include hν hb hK h hq hq1 hM

/-- The summed Fourier coefficients satisfy the full nonlinear viscous equation. -/
theorem fourierDt_eq {t : ℝ} (ht : t ∈ Set.Icc 0 T) (k : Wave) :
    fourierDt ν ω t k = -(ν : ℝ) * (lam k : ℝ) * fourierCoeff ν ω t k -
      fourierTransport (fourierCoeff ν ω t) (fourierCoeff ν ω t) k := by
  let W := fun n => ExpPoly.eval ν t (ω n k)
  let C := fun n => ∑ m ∈ range (n + 1),
    RealPoly.transport (eval ν t (ω m)) (eval ν t (ω (n - m))) k
  have sk := wild_sizeLE ν b K hK
  have sc := interaction_hasSum
    (F := fun n m => RealPoly.transport (eval ν t (ω n)) (eval ν t (ω m)) k)
    (summable_transport_degree («ω» := wild ν b) sk hM hq.le hq1 (h t ht) k)
  have sW : Summable W := (TrigStream.summable_norm_of_bound (f := W) (C := M) 0 hq.le hq1 (fun n => by
    simpa using (RealPoly.abs_apply_le_l1 (eval ν t (ω n)) k).trans (h t ht n))).of_norm
  have sd : Summable (fun n => ExpPoly.eval ν t (deriv ν (ω n) k)) :=
    (TrigStream.summable_norm_of_bound (f := fun n => ExpPoly.eval ν t (deriv ν (ω n) k)) 2 hq.le hq1 (fun n =>
      (RealPoly.abs_apply_le_l1 (eval ν t (deriv ν (ω n))) k).trans
        (wild_deriv_l1_le hν b P hb hK h hq hM ht n))).of_norm
  have he0 : ExpPoly.eval ν t (deriv ν (ω 0) k) = -(ν : ℝ) * (lam k : ℝ) * W 0 := by
    have he := congrArg (fun R : RealPoly => R k) (eval_deriv_wild_zero ν b P hb t)
    simpa [RealPoly.laplacian_apply, W, mul_neg, neg_mul, mul_assoc] using he
  have hes (n : ℕ) : ExpPoly.eval ν t (deriv ν (ω (n + 1)) k) =
      -(ν : ℝ) * (lam k : ℝ) * W (n + 1) - C n := by
    have he := congrArg (fun R : RealPoly => R k) (eval_deriv_wild_succ ν b n t)
    simpa [RealPoly.laplacian_apply, W, C, mul_neg, neg_mul, mul_assoc] using he
  rw [fourierDt, sd.tsum_eq_zero_add, he0]
  simp_rw [hes]
  have sws : Summable (fun n => W (n + 1)) := (summable_nat_add_iff 1).mpr sW
  rw [(sws.mul_left _).tsum_sub sc.summable, tsum_mul_left, sc.tsum_eq,
    ← fourierTransport_coeff sk hM hq.le hq1 (h t ht) k]
  change _ = -(ν : ℝ) * (lam k : ℝ) * (∑' n, W n) - _
  rw [sW.tsum_eq_zero_add]
  ring

omit hν hb hK h hq hq1 hM in
/-- The summed coefficients remain even. -/
theorem fourierCoeff_even (he : IsEven (b 0)) (t : ℝ) (k : Wave) :
    fourierCoeff ν ω t (-k) = fourierCoeff ν ω t k := by
  apply tsum_congr
  intro n
  rw [wild_isEven ν b he n k]

omit hν hb hK h hq hq1 hM in
/-- The summed coefficient of the mean remains zero. -/
theorem fourierCoeff_meanZero (hz : MeanZero (b 0)) (t : ℝ) : fourierCoeff ν ω t 0 = 0 := by
  unfold fourierCoeff
  have he (n : ℕ) : ω n 0 = 0 := wild_meanZero ν b hz n
  simp only [he, map_zero, tsum_zero]

#print axioms fourierDt_eq
end Gimle.Asgard.Streams.Mild
