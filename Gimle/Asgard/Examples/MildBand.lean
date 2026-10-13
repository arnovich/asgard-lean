import Gimle.Asgard.Streams.MildDissipation
import Gimle.Asgard.Streams.MildCircuit
import Gimle.Asgard.Examples.EulerBand

/-! Two certified bounds for the three-mode mild interaction series.
At ν = 1/10 the Catalan bound gives `[0,1/5760]`, the four-term tail
`21/1024`, and the band ±3.519. The Euler-scale bound works on every
`[0,T]` with `T < 1/648`, for every ν ≥ 0. Both bounds also certify classical realization, the forward initial derivative,
and the two infinite Fourier dissipation identities. -/
namespace Gimle.Asgard.Examples.MildBand

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild

/-- Physical initial data; the other boundary slices have no effect. -/
noncomputable def start : Stream := fun _ => embed EulerThreeMode.ω₀

/-- The output of the typed mild circuit. -/
noncomputable def ω (ν : ℚ) : Stream := wild ν start

/-- The stream used below is a related circuit output. -/
theorem circuit_output (ν : ℚ) : (mildCircuit ν).Rel ![start] ![ω ν] :=
  mildCircuit_solution ν start

/-- The exact rational four-term tail from the Catalan recurrence. -/
theorem tail_constant : catalanTail 3 (1 / 24) 4 = 21 / 1024 := by
  decide +kernel

/-- The certified finite-prefix band rounds upward to 3.519. -/
theorem band_constant : catalanBand 3 (1 / 24) 4 ≤ 3519 / 1000 := by
  decide +kernel

/-- The viscosity-dependent truncation at ν = 1/10. -/
theorem truncation : MildTruncationBound (1 / 10) (ω (1 / 10)) (1 / 5760) 4 (21 / 1024) := by
  have h := wild_catalan_truncation (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    start EulerThreeMode.ω₀ rfl EulerBand.start_l1 (by norm_num) 4
  simpa only [ω, tail_constant, Rat.cast_div, Rat.cast_ofNat] using h

/-- A band from physical majorants alone, with no carrier coefficient norms. -/
theorem band : MildBandBound (1 / 10) (ω (1 / 10)) (1 / 5760) (3519 / 1000) := by
  have h := wild_catalan_band (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    start EulerThreeMode.ω₀ rfl EulerBand.start_l1 (by norm_num) 4
  intro t ht x
  have hbc := (Rat.cast_le (K := ℝ)).mpr band_constant
  norm_num at hbc
  exact (h t ht x).trans hbc

/-- The Euler-scale tail works at every nonnegative viscosity. -/
theorem euler_truncation {ν T : ℚ} (hν : 0 ≤ ν) (hT : 0 ≤ T) (hsmall : T < 1 / 648) :
    MildTruncationBound ν (ω ν) T 4 (9 * (648 * (T : ℝ)) ^ 4 / (1 - 648 * T)) := by
  have h := wild_euler_truncation hν hT start EulerThreeMode.ω₀ rfl
    (by norm_num : 1 ≤ 3) EulerBand.start_sizeLE EulerBand.start_l1 (by norm_num; linarith) 4
  norm_num [eulerTail] at h
  exact h

/-- At every real forward time below the Euler scale, the field series converges. -/
theorem converges {ν : ℚ} (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) (hsmall : t < 1 / 648)
    (x : ℝ × ℝ) : Summable (fun n => ‖seriesTerm ν (ω ν) t x n‖) := by
  have hg := wild_euler_geometric hν start EulerThreeMode.ω₀ rfl
    (by norm_num : 1 ≤ 3) EulerBand.start_sizeLE EulerBand.start_l1 t
  have hq : 72 * (3 : ℝ) * (3 : ℕ) * t < 1 := by norm_num; linarith
  exact (truncation_of_geometric hg (by positivity) hq 4 t ⟨ht, le_rfl⟩ x).1

/-- At ratio 1/2 the two certified interval lengths cross at viscosity 8/9. -/
theorem bound_crossing (ν : ℚ) : 1 / 648 < ν * (1 / 24) ^ 2 ↔ 8 / 9 < ν := by
  constructor <;> intro h <;> norm_num at * <;> linarith

/-- The Catalan interval realizes the actual circuit stream as a classical solution. -/
theorem classical : IsMildClassicalSolution (1 / 10) (ω (1 / 10)) EulerThreeMode.ω₀ (1 / 5760) := by
  have hg := wild_geometric (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    start EulerThreeMode.ω₀ rfl EulerBand.start_l1
  exact mild_classical (by norm_num) start EulerThreeMode.ω₀ rfl
    EulerThreeMode.ω₀_meanZero EulerThreeMode.ω₀_isEven EulerBand.start_sizeLE
    (by norm_num) hg (by norm_num) (by norm_num)

/-- Both infinite dissipation identities on the Catalan interval. -/
theorem dissipation : HasDissipation (1 / 10) (ω (1 / 10)) (1 / 5760) := by
  have hg := wild_geometric (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    start EulerThreeMode.ω₀ rfl EulerBand.start_l1
  exact mild_dissipation (by norm_num) start EulerThreeMode.ω₀ rfl
    EulerThreeMode.ω₀_meanZero EulerThreeMode.ω₀_isEven EulerBand.start_sizeLE
    (by norm_num) hg (by norm_num) (by norm_num)

/-- Classical realization and dissipation also follow from the Euler-scale bound,
including zero viscosity. -/
theorem euler_classical_dissipation {ν : ℚ} {T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hsmall : T < 1 / 648) :
    IsMildClassicalSolution ν (ω ν) EulerThreeMode.ω₀ T ∧ HasDissipation ν (ω ν) T := by
  have hg := wild_euler_geometric hν start EulerThreeMode.ω₀ rfl
    (by norm_num : 1 ≤ 3) EulerBand.start_sizeLE EulerBand.start_l1 T
  have hq : (0 : ℝ) ≤ 72 * 3 * (3 : ℕ) * T := by positivity
  have hq1 : 72 * (3 : ℝ) * (3 : ℕ) * T < 1 := by norm_num; linarith
  exact ⟨mild_classical hν start EulerThreeMode.ω₀ rfl EulerThreeMode.ω₀_meanZero
      EulerThreeMode.ω₀_isEven EulerBand.start_sizeLE hT hg hq hq1,
    mild_dissipation hν start EulerThreeMode.ω₀ rfl EulerThreeMode.ω₀_meanZero
      EulerThreeMode.ω₀_isEven EulerBand.start_sizeLE hT hg hq hq1⟩

#print axioms classical
#print axioms dissipation
#print axioms euler_classical_dissipation
#print axioms circuit_output
#print axioms truncation
#print axioms band
#print axioms euler_truncation
#print axioms converges
end Gimle.Asgard.Examples.MildBand
