import Gimle.Asgard.Streams.RealTrigCalculus

/-! Finite Fourier cancellations behind enstrophy and energy dissipation.
The pairing uses the opposite Fourier mode. Even real data specialize it to
squares, but the algebraic transport cancellations do not require evenness. -/
namespace Gimle.Asgard.Streams.Mild.RealPoly

open Torus

/-- A finite Fourier linear functional with arbitrary real weights. -/
noncomputable def functional (c : Wave → ℝ) : RealPoly →ₗ[ℝ] ℝ where
  toFun P := P.sum (fun k a => c k * a)
  map_add' P Q := by
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)]
  map_smul' a P := by
    rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.sum, Finsupp.sum]
    simp only [smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

@[simp] theorem functional_single (c : Wave → ℝ) (k : Wave) (a : ℝ) :
    functional c (Finsupp.single k a) = c k * a := by
  change (Finsupp.single k a).sum _ = _
  rw [Finsupp.sum_single_index (by simp)]

/-- The opposite-mode pairing, with an additional spectral weight. -/
noncomputable def pairing (w : Wave → ℝ) (W V : RealPoly) : ℝ :=
  functional (fun k => w k * W (-k)) V

/-- Expand transport against any spectral pairing. -/
theorem pairing_transport (w : Wave → ℝ) (W P Q : RealPoly) :
    pairing w W (transport P Q) = ∑ p ∈ P.support, ∑ q ∈ Q.support,
      w (p + q) * W (-(p + q)) * (coupling p q : ℝ) * P p * Q q := by
  rw [pairing, transport_eq_sum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_smul, Finsupp.sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, functional_single]
  simp only [smul_eq_mul]
  ring

/-- Triad closure singles out the opposite output mode. -/
theorem sum_triad_coeff (W : RealPoly) (p q : Wave) :
    (∑ r ∈ W.support, if p + q + r = 0 then W r else 0) = W (-(p + q)) := by
  have he (r : Wave) : p + q + r = 0 ↔ r = -(p + q) := by
    constructor
    · exact eq_neg_of_add_eq_zero_right
    · intro h; rw [h, add_neg_cancel]
  simp_rw [he]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hm).symm

/-- The ordered triad contribution to a weighted transport pairing. -/
noncomputable def triad (w : Wave → ℝ) (W : Wave → ℝ) (p q r : Wave) : ℝ :=
  if p + q + r = 0 then w r * (coupling p q : ℝ) * W p * W q * W r else 0

/-- Even spectral weights allow a symmetric finite triple-sum representation. -/
theorem pairing_transport_triad (w : Wave → ℝ) (hw : ∀ k, w (-k) = w k) (W : RealPoly) :
    pairing w W (transport W W) =
      ∑ p ∈ W.support, ∑ q ∈ W.support, ∑ r ∈ W.support, triad w W p q r := by
  rw [pairing_transport]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [← sum_triad_coeff W p q]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  unfold triad
  split_ifs with hr
  · have he : r = -(p + q) := eq_neg_of_add_eq_zero_right hr
    rw [he, hw]
    ring
  · ring

/-- At a closed triad, exchanging the two vorticity factors flips the coupling. -/
theorem coupling_triad_swap_right (p q r : Wave) (h : p + q + r = 0) :
    coupling p r = -coupling p q := by
  have hr : r = -(p + q) := eq_neg_of_add_eq_zero_right h
  have hc : cross p r = -cross p q := by rw [hr]; simp [cross]; ring
  simp only [coupling, hc, Int.cast_neg, neg_div]

/-- At a closed triad, exchanging the stream-function and energy factors flips the weighted coupling. -/
theorem coupling_triad_swap_left (p q r : Wave) (h : p + q + r = 0) :
    (coupling r q : ℝ) / lam p = -( (coupling p q : ℝ) / lam r) := by
  have hr : r = -(p + q) := eq_neg_of_add_eq_zero_right h
  have hc : cross r q = -cross p q := by rw [hr]; simp [cross]; ring
  rw [coupling, coupling, hc]
  push_cast
  ring

/-- The enstrophy triad is antisymmetric in its last two indices. -/
theorem triad_enstrophy_swap (W : Wave → ℝ) (p q r : Wave) :
    triad (fun _ => 1) W p r q = -triad (fun _ => 1) W p q r := by
  have he : p + r + q = 0 ↔ p + q + r = 0 := by constructor <;> intro h <;> linear_combination h
  simp only [triad, he]
  split_ifs with h
  · rw [coupling_triad_swap_right p q r h, Rat.cast_neg]; ring
  · ring

/-- The energy triad is antisymmetric in its first and last indices. -/
theorem triad_energy_swap (W : Wave → ℝ) (p q r : Wave) :
    triad (fun k => (lam k : ℝ)⁻¹) W r q p = -triad (fun k => (lam k : ℝ)⁻¹) W p q r := by
  have he : r + q + p = 0 ↔ p + q + r = 0 := by constructor <;> intro h <;> linear_combination h
  simp only [triad, he]
  split_ifs with h
  · have hc := coupling_triad_swap_left p q r h
    simp only [div_eq_mul_inv] at hc
    linear_combination (W p * W q * W r) * hc
  · ring

/-- The finite nonlinear enstrophy flux vanishes. -/
theorem enstrophy_flux_zero (W : RealPoly) : pairing (fun _ => 1) W (transport W W) = 0 := by
  rw [pairing_transport_triad _ (fun _ => rfl)]
  have he : (∑ p ∈ W.support, ∑ q ∈ W.support, ∑ r ∈ W.support, triad (fun _ => 1) W p q r) =
      -(∑ p ∈ W.support, ∑ q ∈ W.support, ∑ r ∈ W.support, triad (fun _ => 1) W p q r) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun r _ => triad_enstrophy_swap W p q r)
  linarith

/-- Swap the outside indices of a finite cubic sum. -/
theorem sum_triple_swap (s : Finset Wave) (f : Wave → Wave → Wave → ℝ) :
    (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f p q r) = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f r q p := by
  calc (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, f p q r)
      = ∑ q ∈ s, ∑ p ∈ s, ∑ r ∈ s, f p q r := Finset.sum_comm
    _ = ∑ q ∈ s, ∑ r ∈ s, ∑ p ∈ s, f p q r := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

/-- The finite nonlinear energy flux vanishes. -/
theorem energy_flux_zero (W : RealPoly) : pairing (fun k => (lam k : ℝ)⁻¹) W (transport W W) = 0 := by
  rw [pairing_transport_triad _ (fun k => by simp)]
  have he : (∑ p ∈ W.support, ∑ q ∈ W.support, ∑ r ∈ W.support,
      triad (fun k => (lam k : ℝ)⁻¹) W p q r) =
      -(∑ p ∈ W.support, ∑ q ∈ W.support, ∑ r ∈ W.support,
        triad (fun k => (lam k : ℝ)⁻¹) W p q r) := by
    conv_lhs => rw [sum_triple_swap]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun r _ => triad_energy_swap W p q r)
  linarith

#print axioms enstrophy_flux_zero
#print axioms energy_flux_zero
end Gimle.Asgard.Streams.Mild.RealPoly
