import Gimle.Asgard.Streams.MildSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Physical-time differentiation on the open forward interval, and continuity
of the derivative series up to its closed endpoints. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Set

/-- Restrict joint continuity to a fixed spatial point. -/
theorem continuousOn_fixed_spatial {f : ℝ × (ℝ × ℝ) → ℝ} {T : ℝ}
    (hf : ContinuousOn f {z | z.1 ∈ Icc 0 T}) (x : ℝ × ℝ) :
    ContinuousOn (fun s => f (s, x)) (Icc 0 T) :=
  hf.comp (f := fun s => (s, x)) (s := Icc 0 T)
    (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => hs)

variable {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P)
  {K : ℕ} (hK : SizeLE K (b 0)) {T M q : ℝ}
  (h : GeometricBound ν (wild ν b) T M q) (hq : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)

include hν hb hK h hq hq1 hM

/-- The physical time derivative series is absolutely summable throughout the closed interval. -/
theorem summable_norm_time {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ × ℝ) :
    Summable (fun n => ‖RealPoly.field (eval ν t (deriv ν (wild ν b n))) x‖) :=
  TrigStream.summable_norm_of_bound 2 hq.le hq1 (fun n =>
    (RealPoly.abs_field_le_l1 _ _).trans (wild_deriv_l1_le hν b P hb hK h hq hM ht n))

/-- The derivative field is jointly continuous on the closed time strip. -/
theorem continuousOn_seriesDt :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesDt ν (wild ν b) z.1 z.2)
      {z | z.1 ∈ Icc 0 T} := by
  refine continuousOn_tsum (fun n => (continuous_eval_field ν (deriv ν (wild ν b n))).continuousOn)
    ((TrigStream.summable_succ_pow_mul_geometric 2 hq.le hq1).mul_left
      ((ν : ℝ) * K ^ 2 * M + (K : ℝ) * M ^ 2 / q)) ?_
  intro n z hz
  rw [Real.norm_eq_abs]
  exact (RealPoly.abs_field_le_l1 _ _).trans (wild_deriv_l1_le hν b P hb hK h hq hM hz n)

/-- Differentiation of the physical field on the open forward interval. -/
theorem hasDerivAt_analyticField_t {t : ℝ} (ht : t ∈ Ioo 0 T) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ν (wild ν b) s x) (seriesDt ν (wild ν b) t x) t := by
  have hu := (TrigStream.summable_succ_pow_mul_geometric 2 hq.le hq1).mul_left
    ((ν : ℝ) * K ^ 2 * M + (K : ℝ) * M ^ 2 / q)
  have hs := summable_norm_spatial h (wild_sizeLE ν b K hK) ⟨ht.1.le, ht.2.le⟩ hq.le hq1
    abs_field_le_pow_zero x
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun n s _ => hasDerivAt_eval_field ν (wild ν b n) s x)
    (fun n s hs => by
      rw [Real.norm_eq_abs]
      exact (RealPoly.abs_field_le_l1 _ _).trans
        (wild_deriv_l1_le hν b P hb hK h hq hM ⟨hs.1.le, hs.2.le⟩ n))
    (y₀ := t) ht hs.of_norm ht

/-- The right derivative at the initial time is the same continuous derivative
series; no negative-time convergence is assumed. -/
theorem hasDerivWithinAt_analyticField_zero (hT : 0 < T) (x : ℝ × ℝ) :
    HasDerivWithinAt (fun s => analyticField ν (wild ν b) s x)
      (seriesDt ν (wild ν b) 0 x) (Ici 0) 0 := by
  have hc : ContinuousOn (fun s => analyticField ν (wild ν b) s x) (Icc 0 T) := by
    exact continuousOn_fixed_spatial (continuousOn_analyticField h (wild_sizeLE ν b K hK) hq.le hq1) x
  have hdc : ContinuousOn (fun s => seriesDt ν (wild ν b) s x) (Icc 0 T) := by
    exact continuousOn_fixed_spatial (continuousOn_seriesDt hν b P hb hK h hq hq1 hM) x
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) := hasDerivAt_analyticField_t hν b P hb hK h hq hq1 hM hs x
  have hn : Ioo (0 : ℝ) T ∈ nhdsWithin 0 (Ioi 0) := Ioo_mem_nhdsGT hT
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    ((hc 0 ⟨le_rfl, hT.le⟩).mono Ioo_subset_Icc_self) hn
  have hlim : Filter.Tendsto (fun s => seriesDt ν (wild ν b) s x)
      (nhdsWithin 0 (Ioi 0)) (nhds (seriesDt ν (wild ν b) 0 x)) := by
    exact (hdc 0 ⟨le_rfl, hT.le⟩).tendsto.mono_left
      (nhdsWithin_le_of_mem (Filter.mem_of_superset hn Ioo_subset_Icc_self))
  apply hlim.congr'
  exact Filter.mem_of_superset hn (fun s hs => (hd s hs).deriv.symm)

#print axioms hasDerivAt_analyticField_t
#print axioms continuousOn_seriesDt
#print axioms hasDerivWithinAt_analyticField_zero
end Gimle.Asgard.Streams.Mild
