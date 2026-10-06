import Gimle.Asgard.Streams.MildDerivativeBounds

/-! Spatial and time differentiation of convergent physical interaction series. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

/-- The inverse spatial Laplacian acts termwise on an interaction stream. -/
noncomputable def psi (ω : Stream) : Stream := fun n => laplacianInv (ω n)

/-- The physical time derivative series. -/
noncomputable def seriesDt (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, RealPoly.field (eval ν t (deriv ν (ω n))) x

/-- The spatial derivative series corresponding to `fieldD₁`. -/
noncomputable def seriesD₁ (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, RealPoly.fieldD₁ (eval ν t (ω n)) x

/-- The spatial derivative series corresponding to `fieldD₂`. -/
noncomputable def seriesD₂ (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, RealPoly.fieldD₂ (eval ν t (ω n)) x

/-- The spatial derivative series corresponding to `fieldD₁₁`. -/
noncomputable def seriesD₁₁ (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, RealPoly.fieldD₁₁ (eval ν t (ω n)) x

/-- The spatial derivative series corresponding to `fieldD₂₂`. -/
noncomputable def seriesD₂₂ (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, RealPoly.fieldD₂₂ (eval ν t (ω n)) x

/-- The spatial derivative series corresponding to `fieldD₁₂`. -/
noncomputable def seriesD₁₂ (ν : ℚ) (ω : Stream) (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n, RealPoly.fieldD₁₂ (eval ν t (ω n)) x

theorem geometricBound_psi {ν : ℚ} {ω : Stream} {T M q : ℝ}
    (h : GeometricBound ν ω T M q) : GeometricBound ν (psi ω) T M q := by
  intro t ht n
  rw [psi, eval_laplacianInv]
  exact (RealPoly.l1_laplacianInv_le _).trans (h t ht n)

variable {ν : ℚ} {ω : Stream} {T M q t : ℝ} {K : ℕ}

/-- A spatial derivative costs only a polynomial in interaction degree. -/
theorem abs_spatial_term_le (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    {D : RealPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D P x| ≤ (K' : ℝ) ^ k * RealPoly.l1 P)
    (n : ℕ) (x : ℝ × ℝ) :
    |D (eval ν t (ω n)) x| ≤ ((K : ℝ) ^ k * M) * (((n : ℝ) + 1) ^ k * q ^ n) := by
  refine (hD _ _ _ (sizeLE_eval ν t (hK n))).trans ?_
  have hb := mul_le_mul_of_nonneg_left (h t ht n) (show 0 ≤ (((n + 1) * K : ℕ) : ℝ) ^ k by positivity)
  convert hb using 1
  push_cast
  rw [mul_pow]
  ring

/-- Absolute summability of every spatial derivative controlled by finite support. -/
theorem summable_norm_spatial (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) {D : RealPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D P x| ≤ (K' : ℝ) ^ k * RealPoly.l1 P)
    (x : ℝ × ℝ) : Summable (fun n => ‖D (eval ν t (ω n)) x‖) :=
  TrigStream.summable_norm_of_bound k hq hq1 (fun n => abs_spatial_term_le h hK ht hD n x)

/-- Differentiation in the first spatial coordinate is termwise. -/
theorem hasDerivAt_spatial_fst (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) {D D' : RealPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D P x| ≤ (K' : ℝ) ^ k * RealPoly.l1 P)
    (hD' : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D' P x| ≤ (K' : ℝ) ^ (k + 1) * RealPoly.l1 P)
    (hd : ∀ (P : RealPoly) (x : ℝ × ℝ), HasDerivAt (fun s => D P (s, x.2)) (D' P x) x.1)
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => ∑' n, D (eval ν t (ω n)) (s, x.2))
      (∑' n, D' (eval ν t (ω n)) x) x.1 := by
  have hu := (TrigStream.summable_succ_pow_mul_geometric (k + 1) hq hq1).mul_left ((K : ℝ) ^ (k + 1) * M)
  have hh := hasDerivAt_tsum (g := fun n s => D (eval ν t (ω n)) (s, x.2))
    (g' := fun n s => D' (eval ν t (ω n)) (s, x.2)) hu
    (fun n s => hd (eval ν t (ω n)) (s, x.2))
    (fun n s => by rw [Real.norm_eq_abs]; exact abs_spatial_term_le h hK ht hD' n (s, x.2))
    (y₀ := x.1) (summable_norm_spatial h hK ht hq hq1 hD (x.1, x.2)).of_norm x.1
  simpa using hh

/-- Differentiation in the second spatial coordinate is termwise. -/
theorem hasDerivAt_spatial_snd (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) {D D' : RealPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hD : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D P x| ≤ (K' : ℝ) ^ k * RealPoly.l1 P)
    (hD' : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D' P x| ≤ (K' : ℝ) ^ (k + 1) * RealPoly.l1 P)
    (hd : ∀ (P : RealPoly) (x : ℝ × ℝ), HasDerivAt (fun s => D P (x.1, s)) (D' P x) x.2)
    (x : ℝ × ℝ) :
    HasDerivAt (fun s => ∑' n, D (eval ν t (ω n)) (x.1, s))
      (∑' n, D' (eval ν t (ω n)) x) x.2 := by
  have hu := (TrigStream.summable_succ_pow_mul_geometric (k + 1) hq hq1).mul_left ((K : ℝ) ^ (k + 1) * M)
  have hh := hasDerivAt_tsum (g := fun n s => D (eval ν t (ω n)) (x.1, s))
    (g' := fun n s => D' (eval ν t (ω n)) (x.1, s)) hu
    (fun n s => hd (eval ν t (ω n)) (x.1, s))
    (fun n s => by rw [Real.norm_eq_abs]; exact abs_spatial_term_le h hK ht hD' n (x.1, s))
    (y₀ := x.2) (summable_norm_spatial h hK ht hq hq1 hD (x.1, x.2)).of_norm x.2
  simpa using hh

/-- Uniform spatial majorants give joint continuity on the closed forward strip. -/
theorem continuousOn_spatial (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1)
    {D : RealPoly → ℝ × ℝ → ℝ} {k : ℕ}
    (hc : ∀ P : MildPoly, Continuous (fun z : ℝ × (ℝ × ℝ) => D (eval ν z.1 P) z.2))
    (hD : ∀ (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ),
      RealPoly.SizeLE K' P → |D P x| ≤ (K' : ℝ) ^ k * RealPoly.l1 P) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => ∑' n, D (eval ν z.1 (ω n)) z.2)
      {z | z.1 ∈ Set.Icc 0 T} := by
  refine continuousOn_tsum (fun n => (hc (ω n)).continuousOn)
    ((TrigStream.summable_succ_pow_mul_geometric k hq hq1).mul_left ((K : ℝ) ^ k * M)) ?_
  intro n z hz
  rw [Real.norm_eq_abs]
  exact abs_spatial_term_le h hK hz hD n z.2

/-- The field has spatial order zero. -/
theorem abs_field_le_pow_zero (K' : ℕ) (P : RealPoly) (x : ℝ × ℝ) (_ : RealPoly.SizeLE K' P) :
    |RealPoly.field P x| ≤ (K' : ℝ) ^ 0 * RealPoly.l1 P := by
  rw [pow_zero, one_mul]; exact RealPoly.abs_field_le_l1 P x

theorem hasDerivAt_analyticField_fst (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ν ω t (s, x.2)) (seriesD₁ ν ω t x) x.1 :=
  hasDerivAt_spatial_fst h hK ht hq hq1 (k := 0) abs_field_le_pow_zero
    (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁_le hs _) RealPoly.hasDerivAt_field_fst x

theorem hasDerivAt_analyticField_snd (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) (x : ℝ × ℝ) :
    HasDerivAt (fun s => analyticField ν ω t (x.1, s)) (seriesD₂ ν ω t x) x.2 :=
  hasDerivAt_spatial_snd h hK ht hq hq1 (k := 0) abs_field_le_pow_zero
    (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₂_le hs _) RealPoly.hasDerivAt_field_snd x

theorem hasDerivAt_seriesD₁_fst (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₁ ν ω t (s, x.2)) (seriesD₁₁ ν ω t x) x.1 :=
  hasDerivAt_spatial_fst h hK ht hq hq1 (k := 1) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁_le hs _)
    (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁₁_le hs _) RealPoly.hasDerivAt_fieldD₁_fst x

theorem hasDerivAt_seriesD₂_snd (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₂ ν ω t (x.1, s)) (seriesD₂₂ ν ω t x) x.2 :=
  hasDerivAt_spatial_snd h hK ht hq hq1 (k := 1) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₂_le hs _)
    (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₂₂_le hs _) RealPoly.hasDerivAt_fieldD₂_snd x

theorem hasDerivAt_seriesD₂_fst (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₂ ν ω t (s, x.2)) (seriesD₁₂ ν ω t x) x.1 :=
  hasDerivAt_spatial_fst h hK ht hq hq1 (k := 1) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₂_le hs _)
    (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁₂_le hs _) RealPoly.hasDerivAt_fieldD₂_fst x

theorem hasDerivAt_seriesD₁_snd (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (ht : t ∈ Set.Icc 0 T)
    (hq : 0 ≤ q) (hq1 : q < 1) (x : ℝ × ℝ) :
    HasDerivAt (fun s => seriesD₁ ν ω t (x.1, s)) (seriesD₁₂ ν ω t x) x.2 :=
  hasDerivAt_spatial_snd h hK ht hq hq1 (k := 1) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁_le hs _)
    (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁₂_le hs _) RealPoly.hasDerivAt_fieldD₁_snd x

theorem continuousOn_analyticField (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => analyticField ν ω z.1 z.2) {z | z.1 ∈ Set.Icc 0 T} :=
  continuousOn_spatial h hK hq hq1 (k := 0) (continuous_eval_field ν) abs_field_le_pow_zero

theorem continuousOn_seriesD₁ (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₁ ν ω z.1 z.2) {z | z.1 ∈ Set.Icc 0 T} :=
  continuousOn_spatial h hK hq hq1 (k := 1) (continuous_eval_fieldD₁ ν) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁_le hs _)

theorem continuousOn_seriesD₂ (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₂ ν ω z.1 z.2) {z | z.1 ∈ Set.Icc 0 T} :=
  continuousOn_spatial h hK hq hq1 (k := 1) (continuous_eval_fieldD₂ ν) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₂_le hs _)

theorem continuousOn_seriesD₁₁ (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₁₁ ν ω z.1 z.2) {z | z.1 ∈ Set.Icc 0 T} :=
  continuousOn_spatial h hK hq hq1 (k := 2) (continuous_eval_fieldD₁₁ ν) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁₁_le hs _)

theorem continuousOn_seriesD₂₂ (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₂₂ ν ω z.1 z.2) {z | z.1 ∈ Set.Icc 0 T} :=
  continuousOn_spatial h hK hq hq1 (k := 2) (continuous_eval_fieldD₂₂ ν) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₂₂_le hs _)

theorem continuousOn_seriesD₁₂ (h : GeometricBound ν ω T M q)
    (hK : ∀ n, SizeLE ((n + 1) * K) (ω n)) (hq : 0 ≤ q) (hq1 : q < 1) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => seriesD₁₂ ν ω z.1 z.2) {z | z.1 ∈ Set.Icc 0 T} :=
  continuousOn_spatial h hK hq hq1 (k := 2) (continuous_eval_fieldD₁₂ ν) (fun _ _ _ hs => by simpa using RealPoly.abs_fieldD₁₂_le hs _)

#print axioms hasDerivAt_spatial_fst
#print axioms continuousOn_spatial
end Gimle.Asgard.Streams.Mild
