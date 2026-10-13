import Gimle.Asgard.Streams.MildCatalan
import Gimle.Asgard.Streams.MildEulerRadius
import Gimle.Asgard.Streams.MildField

/-! Two certified convergence/tail/band bounds on the actual mild stream.
The Wiener bound uses positive viscosity; the Euler scale works for every
nonnegative viscosity. Both concern the series, not yet a classical PDE. -/
namespace Gimle.Asgard.Streams.Mild

open Torus

/-- Uniform geometric control of physical interaction terms on `[0,T]`. -/
def GeometricBound (ν : ℚ) (ω : Stream) (T M q : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ n, RealPoly.l1 (eval ν t (ω n)) ≤ M * q ^ n

/-- Either geometric majorant proves absolute convergence and a window bound. -/
theorem truncation_of_geometric {ν : ℚ} {ω : Stream} {T M q : ℝ}
    (h : GeometricBound ν ω T M q) (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    MildTruncationBound ν ω T N (M * q ^ N / (1 - q)) := by
  intro t ht x
  exact geometric_tail hq hq1 (fun n _ => (RealPoly.abs_field_le_l1 _ _).trans (h t ht n))

/-- Bound two, in the common physical geometric interface. -/
theorem wild_euler_geometric {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly)
    (hb : b 0 = embed P) {K : ℕ} (hK : 1 ≤ K) (hsupp : Torus.SizeLE K P)
    {L : ℚ} (hL : Torus.l1 P ≤ L) (T : ℝ) :
    GeometricBound ν (wild ν b) T (3 * L) (72 * L * K * T) := by
  intro t ht n
  refine (wild_l1_geometric hν b P hb hK hsupp hL n ht.1).trans ?_
  have hL0 : (0 : ℝ) ≤ L := by exact_mod_cast (Torus.l1_nonneg P).trans hL
  have hmul : 72 * (L : ℝ) * K * t ≤ 72 * L * K * T := by gcongr; exact ht.2
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by positivity) ht.1) hmul n) (by positivity)

/-- Bound one, with the coarser global geometric majorant. -/
theorem wild_geometric {ν r : ℚ} {T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {L : ℚ} (hL : Torus.l1 P ≤ L) :
    GeometricBound ν (wild ν b) T L (4 * r * L) := by
  intro t ht n
  refine (wild_l1_catalan hν hT hr hTr b P hb hL n ht).trans ?_
  exact_mod_cast catalanBound_le_geometric ((Torus.l1_nonneg P).trans hL) hr n

/-- The sharper geometric tail starts at the actual Catalan bound for `N`. -/
theorem catalanBound_add_le {L r : ℚ} (hL : 0 ≤ L) (hr : 0 ≤ r) (N n : ℕ) :
    catalanBound L r (n + N) ≤ catalanBound L r N * (4 * r * L) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_add]
      refine (catalanBound_succ_le hL hr (n + N)).trans ?_
      have h := mul_le_mul_of_nonneg_left ih (show 0 ≤ 4 * r * L by positivity)
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- Bound one's rational tail, retaining the Catalan prefactor. -/
def catalanTail (L r : ℚ) (N : ℕ) : ℚ := catalanBound L r N / (1 - 4 * r * L)

/-- Bound one's rational band, including the whole finite prefix. -/
def catalanBand (L r : ℚ) (N : ℕ) : ℚ :=
  (∑ n ∈ Finset.range N, catalanBound L r n) + catalanTail L r N

/-- The viscosity-dependent certified window for the actual stream. -/
theorem wild_catalan_truncation {ν r : ℚ} {T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {L : ℚ} (hL : Torus.l1 P ≤ L)
    (hq : 4 * r * L < 1) (N : ℕ) :
    MildTruncationBound ν (wild ν b) T N (catalanTail L r N) := by
  have hL0 := (Torus.l1_nonneg P).trans hL
  have hq0 : (0 : ℝ) ≤ (4 * r * L : ℚ) := by exact_mod_cast (show 0 ≤ 4 * r * L by positivity)
  intro t ht x
  have h := geometric_tail_shifted (N := N) hq0 (by exact_mod_cast hq)
    (A := (catalanBound L r N : ℝ)) (f := seriesTerm ν (wild ν b) t x) (fun n => by
      refine (RealPoly.abs_field_le_l1 _ _).trans
        ((wild_l1_catalan hν hT hr hTr b P hb hL (n + N) ht).trans ?_)
      exact_mod_cast catalanBound_add_le hL0 hr N n)
  simpa only [analyticField, windowField, catalanTail, Rat.cast_div, Rat.cast_sub, Rat.cast_one, Rat.cast_mul,
    Rat.cast_ofNat] using h

/-- Bound one's certified band. -/
theorem wild_catalan_band {ν r : ℚ} {T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {L : ℚ} (hL : Torus.l1 P ≤ L)
    (hq : 4 * r * L < 1) (N : ℕ) :
    MildBandBound ν (wild ν b) T (catalanBand L r N) := by
  have h := band_of_truncation (wild_catalan_truncation hν hT hr hTr b P hb hL hq N)
    (fun n => (catalanBound L r n : ℝ))
    (fun t ht n _ => wild_l1_catalan hν hT hr hTr b P hb hL n ht)
  simpa [catalanBand] using h

/-- Bound two's rational tail on an interval of rational length. -/
def eulerTail (L : ℚ) (K : ℕ) (T : ℚ) (N : ℕ) : ℚ :=
  3 * L * (72 * L * K * T) ^ N / (1 - 72 * L * K * T)

/-- Bound two's band uses the sharper heat bound for interaction degree zero. -/
def eulerBand (L : ℚ) (K : ℕ) (T : ℚ) (N : ℕ) : ℚ :=
  L + (∑ n ∈ Finset.Ico 1 N, 3 * L * (72 * L * K * T) ^ n) + eulerTail L K T N

/-- The Euler-scale certified window at every nonnegative viscosity. -/
theorem wild_euler_truncation {ν T : ℚ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : Torus.SizeLE K P) {L : ℚ} (hL : Torus.l1 P ≤ L)
    (hq : 72 * L * K * T < 1) (N : ℕ) :
    MildTruncationBound ν (wild ν b) T N (eulerTail L K T N) := by
  have hL0 := (Torus.l1_nonneg P).trans hL
  have hg := wild_euler_geometric hν b P hb hK hsupp hL T
  have h := truncation_of_geometric hg (by positivity) (by exact_mod_cast hq) N
  simpa [eulerTail] using h

/-- The Euler-scale band retains the initial heat contraction. -/
theorem wild_euler_band {ν T : ℚ} (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : Torus.SizeLE K P) {L : ℚ} (hL : Torus.l1 P ≤ L)
    (hq : 72 * L * K * T < 1) {N : ℕ} (hN : 0 < N) :
    MildBandBound ν (wild ν b) T (eulerBand L K T N) := by
  let a : ℕ → ℝ := fun n => if n = 0 then L else 3 * L * ((72 * L * K * T : ℚ) : ℝ) ^ n
  have ha : ∀ t ∈ Set.Icc 0 (T : ℝ), ∀ n ∈ Finset.range N,
      RealPoly.l1 (eval ν t (wild ν b n)) ≤ a n := by
    intro t ht n _
    by_cases hn : n = 0
    · subst n
      simp only [a, if_pos rfl]
      have h := mwnorm_heat_embed_le 0 hν P ht.1
      rw [mwnorm, RealPoly.wnorm_zero, Torus.wnorm_zero] at h
      rw [wild_zero, hb]
      exact h.trans (by exact_mod_cast hL)
    · simp only [a, if_neg hn]
      have h := wild_euler_geometric hν b P hb hK hsupp hL T t ht n
      simpa using h
  have h := band_of_truncation (wild_euler_truncation hν hT b P hb hK hsupp hL hq N) a ha
  have hs : ∑ n ∈ Finset.range N, a n =
      (L : ℝ) + ∑ n ∈ Finset.Ico 1 N, 3 * L * ((72 * L * K * T : ℚ) : ℝ) ^ n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
    simp only [a, if_pos rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_neg (by have := (Finset.mem_Ico.mp hn).1; omega)]
  rw [hs] at h
  simpa [eulerBand] using h

#print axioms wild_catalan_truncation
#print axioms wild_catalan_band
#print axioms wild_euler_truncation
#print axioms wild_euler_band
end Gimle.Asgard.Streams.Mild
