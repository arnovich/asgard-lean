import Gimle.Asgard.Streams.MildPDE

/-! Classical realization of the actual mild circuit output. The physical
field has time derivatives in the open forward interval, a right derivative
at the start, and all required fields continuous on the closed interval. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real Set

/-- The physical vorticity field obtained from a rational initial profile. -/
noncomputable def mildField (ν : ℚ) (P : TrigPoly) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  analyticField ν (wild ν (fun _ => embed P)) t x

/-- Spatial C² regularity and joint continuity on the closed time strip. -/
structure SpatialRegularity (ν : ℚ) (ω : Stream) (T : ℝ) : Prop where
  derivX₁ : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => analyticField ν ω t (s, x.2)) (seriesD₁ ν ω t x) x.1
  derivX₂ : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => analyticField ν ω t (x.1, s)) (seriesD₂ ν ω t x) x.2
  derivX₁X₁ : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => seriesD₁ ν ω t (s, x.2)) (seriesD₁₁ ν ω t x) x.1
  derivX₂X₂ : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => seriesD₂ ν ω t (x.1, s)) (seriesD₂₂ ν ω t x) x.2
  derivX₂X₁ : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => seriesD₂ ν ω t (s, x.2)) (seriesD₁₂ ν ω t x) x.1
  derivX₁X₂ : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => seriesD₁ ν ω t (x.1, s)) (seriesD₁₂ ν ω t x) x.2
  continuous_field : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => analyticField ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_derivX₁ : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₁ ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_derivX₂ : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₂ ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_derivX₁X₁ : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₁₁ ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_derivX₂X₂ : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₂₂ ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_derivX₁X₂ : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₁₂ ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}

/-- Geometric bounds and finite support give the required spatial regularity. -/
theorem spatialRegularity {ν : ℚ} {ω : Stream} {T M q : ℝ} {K : ℕ}
    (h : GeometricBound ν ω T M q) (hK : ∀ n, SizeLE ((n + 1) * K) (ω n))
    (hq : 0 ≤ q) (hq1 : q < 1) : SpatialRegularity ν ω T :=
  ⟨fun _ ht x => hasDerivAt_analyticField_fst h hK ht hq hq1 x,
    fun _ ht x => hasDerivAt_analyticField_snd h hK ht hq hq1 x,
    fun _ ht x => hasDerivAt_seriesD₁_fst h hK ht hq hq1 x,
    fun _ ht x => hasDerivAt_seriesD₂_snd h hK ht hq hq1 x,
    fun _ ht x => hasDerivAt_seriesD₂_fst h hK ht hq hq1 x,
    fun _ ht x => hasDerivAt_seriesD₁_snd h hK ht hq hq1 x,
    continuousOn_analyticField h hK hq hq1, continuousOn_seriesD₁ h hK hq hq1,
    continuousOn_seriesD₂ h hK hq hq1, continuousOn_seriesD₁₁ h hK hq hq1,
    continuousOn_seriesD₂₂ h hK hq hq1, continuousOn_seriesD₁₂ h hK hq hq1⟩

/-- The physical vorticity PDE, with certified derivatives and initial value. -/
structure IsMildClassicalSolution (ν : ℚ) (ω : Stream) (P : TrigPoly) (T : ℝ) : Prop where
  spatial : SpatialRegularity ν ω T
  streamFunction : SpatialRegularity ν (psi ω) T
  summable : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ, Summable (fun n => ‖seriesTerm ν ω t x n‖)
  derivT : ∀ t ∈ Ioo 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => analyticField ν ω s x) (seriesDt ν ω t x) t
  continuous_derivT : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesDt ν ω z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  right_derivT : 0 < T → ∀ x : ℝ × ℝ,
    HasDerivWithinAt (fun s => analyticField ν ω s x) (seriesDt ν ω 0 x) (Ici 0) 0
  initial : ∀ x, analyticField ν ω 0 x = RealPoly.field (realEmbed P) x
  laplacian : ∀ t ∈ Icc 0 T, ∀ x,
    seriesD₁₁ ν (psi ω) t x + seriesD₂₂ ν (psi ω) t x = analyticField ν ω t x
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    seriesDt ν ω t x +
      (-seriesD₂ ν (psi ω) t x * seriesD₁ ν ω t x + seriesD₁ ν (psi ω) t x * seriesD₂ ν ω t x) =
      (ν : ℝ) * (seriesD₁₁ ν ω t x + seriesD₂₂ ν ω t x)

/-- The summed initial field, without any convergence assumption at other times. -/
theorem analyticField_zero (ν : ℚ) (b : Stream) (P : TrigPoly) (hb : b 0 = embed P) (x : ℝ × ℝ) :
    analyticField ν (wild ν b) 0 x = RealPoly.field (realEmbed P) x := by
  rw [analyticField, tsum_eq_single 0]
  · simp only [seriesTerm, wild_initial ν b P hb, ite_true]
  · intro n hn
    simp only [seriesTerm, wild_initial ν b P hb, if_neg hn, RealPoly.field_zero]

/-- Either certified bound realizes the same stream as a classical solution.
A slightly larger internal ratio covers exact zero data without dividing by zero. -/
theorem mild_classical {ν : ℚ} (hν : 0 ≤ ν) (b : Stream) (P : TrigPoly)
    (hb : b 0 = embed P) (hb0 : Torus.MeanZero P) (hbe : Torus.IsEven P)
    {K : ℕ} (hK : Torus.SizeLE K P) {T M q : ℝ} (hT : 0 ≤ T)
    (h : GeometricBound ν (wild ν b) T M q) (hq : 0 ≤ q) (hq1 : q < 1) :
    IsMildClassicalSolution ν (wild ν b) P T := by
  have hK' : SizeLE K (b 0) := by rw [hb]; exact sizeLE_embed hK
  have hz : MeanZero (b 0) := by rw [hb]; exact meanZero_embed hb0
  have he : IsEven (b 0) := by rw [hb]; exact isEven_embed hbe
  have hM : 0 ≤ M := by
    have hh := (RealPoly.l1_nonneg (eval ν 0 (wild ν b 0))).trans (h 0 ⟨le_rfl, hT⟩ 0)
    simpa using hh
  let q' := (q + 1) / 2
  have hq' : 0 < q' := by dsimp [q']; linarith
  have hq1' : q' < 1 := by dsimp [q']; linarith
  have hqq : q ≤ q' := by dsimp [q']; linarith
  have h' : GeometricBound ν (wild ν b) T M q' := by
    intro t ht n
    exact (h t ht n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqq n) hM)
  have hKn := wild_sizeLE ν b K hK'
  refine ⟨spatialRegularity h' hKn hq'.le hq1',
    spatialRegularity (geometricBound_psi h') (fun n => sizeLE_laplacianInv (hKn n)) hq'.le hq1',
    ?_, ?_, continuousOn_seriesDt hν b P hb hK' h' hq' hq1' hM,
    hasDerivWithinAt_analyticField_zero hν b P hb hK' h' hq' hq1' hM,
    analyticField_zero ν b P hb, ?_, ?_⟩
  · intro t ht x
    exact summable_norm_spatial h' hKn ht hq'.le hq1' abs_field_le_pow_zero x
  · intro t ht x
    exact hasDerivAt_analyticField_t hν b P hb hK' h' hq' hq1' hM ht x
  · intro t ht x
    exact series_laplacian_psi b hK' h' hq' hq1' hz ht x
  · intro t ht x
    rw [seriesDt_eq hν b P hb hK' h' hq' hq1' hM he ⟨ht.1.le, ht.2.le⟩ x]
    ring

/-- The two mixed stream-function derivatives certify divergence-free velocity. -/
theorem IsMildClassicalSolution.div_eq_zero {ν : ℚ} {ω : Stream} {P : TrigPoly} {T t : ℝ}
    (h : IsMildClassicalSolution ν ω P T) (ht : t ∈ Icc 0 T) (x : ℝ × ℝ) :
    HasDerivAt (fun s => -seriesD₂ ν (psi ω) t (s, x.2)) (-seriesD₁₂ ν (psi ω) t x) x.1 ∧
    HasDerivAt (fun s => seriesD₁ ν (psi ω) t (x.1, s)) (seriesD₁₂ ν (psi ω) t x) x.2 ∧
    -seriesD₁₂ ν (psi ω) t x + seriesD₁₂ ν (psi ω) t x = 0 :=
  ⟨(h.streamFunction.derivX₂X₁ t ht x).neg, h.streamFunction.derivX₁X₂ t ht x, by ring⟩

#print axioms mild_classical
#print axioms analyticField_zero
end Gimle.Asgard.Streams.Mild
