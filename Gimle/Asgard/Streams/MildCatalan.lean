import Gimle.Asgard.Streams.MildMajorant
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-! Catalan majorants for the actual Wild interaction terms. -/
namespace Gimle.Asgard.Streams.Mild

open Torus

/-- The scalar Wiener-algebra majorant. -/
def catalanBound (L r : ℚ) (n : ℕ) : ℚ := L * (r * L) ^ n * catalan n

@[simp] theorem catalanBound_zero (L r : ℚ) : catalanBound L r 0 = L := by simp [catalanBound]

theorem catalanBound_nonneg {L r : ℚ} (hL : 0 ≤ L) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ catalanBound L r n := by unfold catalanBound; positivity

/-- The Catalan recurrence matches the quadratic interaction convolution. -/
theorem catalanBound_succ (L r : ℚ) (n : ℕ) :
    catalanBound L r (n + 1) = r * ∑ m : Fin (n + 1),
      catalanBound L r m * catalanBound L r (n - m) := by
  unfold catalanBound
  rw [catalan_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hp : (r * L) ^ (m : ℕ) * (r * L) ^ (n - m) = (r * L) ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' (by have := m.isLt; omega)]
  rw [pow_succ]
  linear_combination -(r * L ^ 2 * (catalan m : ℚ) * (catalan (n - m) : ℚ)) * hp

/-- Successive Catalan numbers grow by at most four. -/
theorem catalan_succ_le_four (n : ℕ) : catalan (n + 1) ≤ 4 * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1), ← succ_mul_catalan_eq_centralBinom n] at h
  have he : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
    nlinarith [h]
  nlinarith

/-- A rational geometric ratio controls the Catalan tail. -/
theorem catalanBound_succ_le {L r : ℚ} (hL : 0 ≤ L) (hr : 0 ≤ r) (n : ℕ) :
    catalanBound L r (n + 1) ≤ (4 * r * L) * catalanBound L r n := by
  have h : (catalan (n + 1) : ℚ) ≤ 4 * catalan n := by exact_mod_cast catalan_succ_le_four n
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ L * (r * L) ^ (n + 1) by positivity)
  simpa only [catalanBound, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hm

/-- The coarser global geometric majorant. -/
theorem catalanBound_le_geometric {L r : ℚ} (hL : 0 ≤ L) (hr : 0 ≤ r) (n : ℕ) :
    catalanBound L r n ≤ L * (4 * r * L) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine (catalanBound_succ_le hL hr n).trans ?_
      have h := mul_le_mul_of_nonneg_left ih (show 0 ≤ 4 * r * L by positivity)
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- Each actual interaction term has a rational modewise majorant with the
Catalan mass bound. Only the boundary's initial slice is constrained. -/
theorem wild_catalan {ν r : ℚ} {T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {L : ℚ} (hL : Torus.l1 P ≤ L)
    (n : ℕ) : ∃ m : TrigPoly, Majorized ν T (wild ν b n) m ∧ Torus.l1 m ≤ catalanBound L r n := by
  have hL0 : 0 ≤ L := (Torus.l1_nonneg P).trans hL
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          refine ⟨initialMajorant P, ?_, ?_⟩
          · rw [wild_zero, hb]; exact heat_majorized hν.le T P
          · simpa [initialMajorant_l1] using hL
      | succ n =>
          let m (i : Fin (n + 1)) := Classical.choose (ih i (by have := i.isLt; omega))
          let l (i : Fin (n + 1)) := Classical.choose (ih (n - i) (by omega))
          have hm (i : Fin (n + 1)) := Classical.choose_spec (ih i (by have := i.isLt; omega))
          have hl (i : Fin (n + 1)) := Classical.choose_spec (ih (n - i) (by omega))
          let a (i : Fin (n + 1)) := transportMajorant r (wild ν b i) (wild ν b (n - i)) (m i) (l i)
          refine ⟨∑ i, a i, ?_, ?_⟩
          · rw [wild_succ, ← Fin.sum_univ_eq_sum_range, duhamel_sum]
            exact (Majorized.sum Finset.univ (fun i _ =>
              transport_majorized hν hT hr hTr (hm i).1 (hl i).1)).neg
          · refine (Torus.l1_sum_le _ _).trans ?_
            rw [catalanBound_succ, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro i _
            refine (transportMajorant_l1 hr _ _ _ _).trans ?_
            have hmi : Torus.l1 (m i) ≤ catalanBound L r i := (hm i).2
            have hli : Torus.l1 (l i) ≤ catalanBound L r (n - i) := (hl i).2
            calc r * Torus.l1 (m i) * Torus.l1 (l i)
                ≤ r * catalanBound L r i * catalanBound L r (n - i) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hmi hr) hli (Torus.l1_nonneg _)
                    (mul_nonneg hr (catalanBound_nonneg hL0 hr _))
              _ = _ := by ring

/-- The physical ℓ¹ norm inherits the sharper Catalan bound on the whole interval. -/
theorem wild_l1_catalan {ν r : ℚ} {T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {L : ℚ} (hL : Torus.l1 P ≤ L)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    RealPoly.l1 (eval ν t (wild ν b n)) ≤ (catalanBound L r n : ℝ) := by
  obtain ⟨m, hm, hl⟩ := wild_catalan hν hT hr hTr b P hb hL n
  exact (hm.l1_le ht).trans (by exact_mod_cast hl)

#print axioms wild_catalan
#print axioms wild_l1_catalan
#print axioms catalanBound_succ_le
end Gimle.Asgard.Streams.Mild
