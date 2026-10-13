import Gimle.Asgard.Streams.MildNorm

/-! Rational modewise majorants of physical values on a closed time interval.
These witnesses do not take absolute sums in the redundant exact carrier. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Set

/-- A rational, finitely supported bound on each physical Fourier coefficient. -/
def Majorized (ν : ℚ) (T : ℝ) (P : MildPoly) (m : TrigPoly) : Prop :=
  ∀ k, ∀ t ∈ Icc 0 T, |ExpPoly.eval ν t (P k)| ≤ (m k : ℝ)

namespace Majorized

theorem nonneg {ν : ℚ} {T : ℝ} {P : MildPoly} {m : TrigPoly}
    (h : Majorized ν T P m) (hT : 0 ≤ T) (k : Wave) : 0 ≤ m k := by
  exact_mod_cast (abs_nonneg (ExpPoly.eval ν 0 (P k))).trans (h k 0 ⟨le_rfl, hT⟩)

theorem zero (ν : ℚ) (T : ℝ) : Majorized ν T 0 0 := by intro k t ht; simp

theorem add {ν : ℚ} {T : ℝ} {P Q : MildPoly} {m l : TrigPoly}
    (hP : Majorized ν T P m) (hQ : Majorized ν T Q l) : Majorized ν T (P + Q) (m + l) := by
  intro k t ht
  simpa only [Finsupp.add_apply, map_add, Rat.cast_add] using
    (abs_add_le (ExpPoly.eval ν t (P k)) (ExpPoly.eval ν t (Q k))).trans
      (add_le_add (hP k t ht) (hQ k t ht))

theorem neg {ν : ℚ} {T : ℝ} {P : MildPoly} {m : TrigPoly}
    (h : Majorized ν T P m) : Majorized ν T (-P) m := by
  intro k t ht
  simpa only [Finsupp.neg_apply, map_neg, abs_neg] using h k t ht

theorem sum {ι : Type*} {ν : ℚ} {T : ℝ} (s : Finset ι)
    {P : ι → MildPoly} {m : ι → TrigPoly} (h : ∀ i ∈ s, Majorized ν T (P i) (m i)) :
    Majorized ν T (∑ i ∈ s, P i) (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero ν T
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem single {ν : ℚ} {T : ℝ} (k : Wave) {P : ExpPoly} {a : ℚ}
    (h : ∀ t ∈ Icc 0 T, |ExpPoly.eval ν t P| ≤ (a : ℝ)) :
    Majorized ν T (Finsupp.single k P) (Finsupp.single k a) := by
  intro j t ht
  by_cases hj : k = j
  · subst j; simpa using h t ht
  · simp [hj]

/-- The physical ℓ¹ norm is bounded by the rational witness mass. -/
theorem l1_le {ν : ℚ} {T : ℝ} {P : MildPoly} {m : TrigPoly}
    (h : Majorized ν T P m) {t : ℝ} (ht : t ∈ Icc 0 T) :
    RealPoly.l1 (eval ν t P) ≤ (Torus.l1 m : ℝ) := by
  let s := (eval ν t P).support ∪ m.support
  rw [RealPoly.l1_eq_sum (show (eval ν t P).support ⊆ s from Finset.subset_union_left),
    Torus.l1_eq_sum (show m.support ⊆ s from Finset.subset_union_right)]
  push_cast
  exact Finset.sum_le_sum (fun k _ => (h k t ht).trans (le_abs_self _))

end Majorized

/-- Taking absolute values of the rational initial Fourier data is sound. -/
noncomputable def initialMajorant (P : TrigPoly) : TrigPoly := P.mapRange abs (abs_zero)

@[simp] theorem initialMajorant_apply (P : TrigPoly) (k : Wave) : initialMajorant P k = |P k| := rfl

theorem initialMajorant_l1 (P : TrigPoly) : Torus.l1 (initialMajorant P) = Torus.l1 P := by
  rw [Torus.l1_eq_sum (show (initialMajorant P).support ⊆ P.support from Finsupp.support_mapRange),
    Torus.l1_eq_sum subset_rfl]
  simp

theorem heat_majorized {ν : ℚ} (hν : 0 ≤ ν) (T : ℝ) (P : TrigPoly) :
    Majorized ν T (heat (embed P)) (initialMajorant P) := by
  intro k t ht
  simp only [heat_apply, map_mul, ExpPoly.eval_single, map_one, one_mul,
    embed_apply, AlgHom.commutes, initialMajorant_apply, Rat.cast_abs]
  rw [abs_mul, abs_of_pos (exp_pos _)]
  apply mul_le_of_le_one_left (abs_nonneg _)
  exact exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg
    (mul_nonneg (by exact_mod_cast hν) (Nat.cast_nonneg _)) ht.1))

/-- Exact Duhamel integration commutes with finite forcing sums. -/
theorem expPoly_duhamel_sum {ι : Type*} (ν : ℚ) (μ : ℕ) (s : Finset ι) (f : ι → ExpPoly) :
    ExpPoly.duhamel ν μ (∑ i ∈ s, f i) = ∑ i ∈ s, ExpPoly.duhamel ν μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, ExpPoly.duhamel_add, ih]

/-- Exact Fourier Duhamel integration commutes with finite forcing sums. -/
theorem duhamel_sum {ι : Type*} (ν : ℚ) (s : Finset ι) (f : ι → MildPoly) :
    duhamel ν (∑ i ∈ s, f i) = ∑ i ∈ s, duhamel ν (f i) := by
  apply Finsupp.ext
  intro k
  simp only [duhamel_apply, Finsupp.finsetSum_apply, expPoly_duhamel_sum]

/-- One interacting pair, including both zero-mode branches, satisfies the
rational heat-absorbed bound. -/
theorem duhamel_pair_bound {ν : ℚ} {T : ℝ} {r a b : ℚ} (hν : 0 < ν)
    (hT : 0 ≤ T) (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (p q : Wave) (P Q : ExpPoly)
    (hP : ∀ t ∈ Icc 0 T, |ExpPoly.eval ν t P| ≤ (a : ℝ))
    (hQ : ∀ t ∈ Icc 0 T, |ExpPoly.eval ν t Q| ≤ (b : ℝ)) :
    ∀ t ∈ Icc 0 T, |ExpPoly.eval ν t
      (ExpPoly.duhamel ν (heatRate (p + q)) (algebraMap ℚ ExpPoly (coupling p q) * P * Q))|
      ≤ ((r * a * b : ℚ) : ℝ) := by
  intro t ht
  by_cases hc : coupling p q = 0
  · simp only [hc, map_zero, zero_mul, ExpPoly.duhamel_zero, abs_zero]
    positivity
  have hk : p + q ≠ 0 := by
    intro hz
    have hq : q = -p := eq_neg_of_add_eq_zero_right hz
    exact hc (by simp [hq])
  have hrate : (heatRate (p + q) : ℝ) = (lam (p + q) : ℝ) := by
    exact_mod_cast heatRate_cast (p + q)
  have hn : (0 : ℝ) < ν := by exact_mod_cast hν
  have hl : (0 : ℝ) < lam (p + q) := by exact_mod_cast lam_pos hk
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
  let c : ℝ := |(coupling p q : ℝ)| * a * b
  have hforce (s : ℝ) (hs : s ∈ Icc 0 t) :
      |ExpPoly.eval ν s (algebraMap ℚ ExpPoly (coupling p q) * P * Q)| ≤ c := by
    simp only [map_mul, AlgHom.commutes, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hP s ⟨hs.1, hs.2.trans ht.2⟩) (abs_nonneg _))
      (hQ s ⟨hs.1, hs.2.trans ht.2⟩) (abs_nonneg _) (mul_nonneg (abs_nonneg _) ha')
  rw [ExpPoly.eval_duhamel, hrate]
  have hf := ExpPoly.continuous_eval ν (algebraMap ℚ ExpPoly (coupling p q) * P * Q)
  have htime := abs_heat_integral_le_time (mul_pos hn hl).le ht.1 hf hforce
  have hdecay := abs_heat_integral_le_rate (mul_pos hn hl) ht.1 hf hforce
  have hz : c * min T (1 / ((ν : ℝ) * lam (p + q))) ≤ (r : ℝ) * a * b := by
    have h := mul_le_mul_of_nonneg_right
      (coupling_heat_min_le p q hn hT (by exact_mod_cast hr) hTr) (mul_nonneg ha' hb')
    simpa only [c, mul_assoc, mul_comm, mul_left_comm] using h
  have hmin : min (t * c) (c / ((ν : ℝ) * lam (p + q))) ≤
      c * min T (1 / ((ν : ℝ) * lam (p + q))) := by
    rw [mul_min_of_nonneg _ _ (show 0 ≤ c by dsimp [c]; positivity)]
    apply min_le_min
    · simpa [mul_comm] using mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ c by dsimp [c]; positivity)
    · simp [div_eq_mul_inv]
  exact (le_min htime hdecay).trans (hmin.trans (by exact_mod_cast hz))

/-- The forcing as a finite sum of its ordered interacting pairs. -/
theorem transport_eq_pairs (P Q : MildPoly) :
    transport P Q = ∑ p ∈ P.support, ∑ q ∈ Q.support,
      Finsupp.single (p + q) (algebraMap ℚ ExpPoly (coupling p q) * P p * Q q) := by
  apply Finsupp.ext
  intro k
  simp only [transport_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- The rational per-pair majorant, using only physical bounds of the inputs. -/
noncomputable def transportMajorant (r : ℚ) (P Q : MildPoly) (m l : TrigPoly) : TrigPoly :=
  ∑ p ∈ P.support, ∑ q ∈ Q.support, Finsupp.single (p + q) (r * m p * l q)

/-- Duhamel transport absorbs the derivative loss into a rational constant. -/
theorem transport_majorized {ν r : ℚ} {T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    {P Q : MildPoly} {m l : TrigPoly} (hP : Majorized ν T P m) (hQ : Majorized ν T Q l) :
    Majorized ν T (duhamel ν (transport P Q)) (transportMajorant r P Q m l) := by
  rw [transport_eq_pairs, duhamel_sum]
  unfold transportMajorant
  apply Majorized.sum
  intro p _
  rw [duhamel_sum]
  apply Majorized.sum
  intro q _
  rw [duhamel_single]
  exact Majorized.single (p + q) (duhamel_pair_bound hν hT hr hTr
    (hP.nonneg hT p) (hQ.nonneg hT q) p q (P p) (Q q) (hP p) (hQ q))

/-- Any finite partial absolute coefficient sum is at most the full ℓ¹ norm. -/
theorem sum_abs_le_l1 (m : TrigPoly) (s : Finset Wave) :
    ∑ k ∈ s, |m k| ≤ Torus.l1 m := by
  have he : ∑ k ∈ s, |m k| = ∑ k ∈ s ∩ m.support, |m k| := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro k _ hk
    have : m k = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hm
      exact hk (Finset.mem_inter.mpr ⟨by assumption, hm⟩)
    simp [this]
  rw [he, Torus.l1_eq_sum subset_rfl]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun k _ _ => abs_nonneg _)

/-- The mass of the pairwise majorant has the bilinear Wiener-algebra bound. -/
theorem transportMajorant_l1 {r : ℚ} (hr : 0 ≤ r) (P Q : MildPoly) (m l : TrigPoly) :
    Torus.l1 (transportMajorant r P Q m l) ≤ r * Torus.l1 m * Torus.l1 l := by
  unfold transportMajorant
  refine (Torus.l1_sum_le _ _).trans ?_
  calc (∑ p ∈ P.support, Torus.l1 (∑ q ∈ Q.support, Finsupp.single (p + q) (r * m p * l q)))
      ≤ ∑ p ∈ P.support, ∑ q ∈ Q.support, r * |m p| * |l q| := by
        apply Finset.sum_le_sum
        intro p _
        refine (Torus.l1_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => ?_))
        simpa only [abs_mul, abs_of_nonneg hr] using Torus.l1_single_le (p + q) (r * m p * l q)
    _ = r * (∑ p ∈ P.support, |m p|) * (∑ q ∈ Q.support, |l q|) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_comm
    _ ≤ r * Torus.l1 m * Torus.l1 l :=
        mul_le_mul (mul_le_mul_of_nonneg_left (sum_abs_le_l1 m _) hr) (sum_abs_le_l1 l _)
          (Finset.sum_nonneg (fun k _ => abs_nonneg _)) (mul_nonneg hr (Torus.l1_nonneg _))

#print axioms duhamel_pair_bound
#print axioms transport_majorized
#print axioms transportMajorant_l1
end Gimle.Asgard.Streams.Mild
