import Gimle.Asgard.Streams.Majorant
import Gimle.Asgard.Streams.AnalyticField
import Gimle.Asgard.Streams.Window
import Gimle.Asgard.Streams.Burgers
import Gimle.Asgard.Streams.AnalyticHeat
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Cole–Hopf: a certified truncation of a Burgers stream

The formal Burgers series from a polynomial profile diverges, but Cole–Hopf
writes a Burgers stream as a quotient of heat streams: if `φ` solves
`D_t φ = ν D_x² φ` then `u = −2ν · D_x φ · φ⁻¹` solves
`D_t u = −u·D_x u + ν D_x² u`. For an exponential-sum profile `φ(0, x)` the
heat stream has an explicit coefficient majorant (as in `AnalyticHeat`, now
with viscosity), the majorant calculus of `Majorant.lean` carries it through
the derivative, the inverse and the product, and `Tail.lean` turns the result
into a uniform truncation bound on a box. Everything is in the OGF reading.

Nothing here is about the real Burgers equation: the analytic field is that
of this series on this box, and the bound is deliberately loose (factorials
are dropped, the inverse and the product each cost a factor of the radii).
The last section identifies that field: the heat stream of an exponential sum
sums to `Σ cᵢ e^(ν aᵢ² t + aᵢ x)` everywhere, and on a box inside the front's
radii the front's field is `−2ν (Σ cᵢ aᵢ e^(…)) / (Σ cᵢ e^(…))`
(`analyticField_front`), by `AnalyticField.lean`'s product and inverse rules. -/
namespace Gimle.Asgard.Streams.ColeHopf

open MvPowerSeries
open Gimle.Asgard.Streams.AnalyticHeat (expSum expSumFits expSumWeight)

/-! ## The heat stream with viscosity -/

/-- OGF coefficients of the heat stream `D_t φ = ν D_x² φ` from the profile with
raw EGF coefficients `g`: `ν^n g_(k+2n) / (n!·k!)` at `(n, k)`. -/
noncomputable def heatSeries (ν : ℚ) (g : ℕ → ℚ) : Stream 2 :=
  fun α => ν ^ α 0 * g (α 1 + 2 * α 0) / factorial α

/-- Its coefficient. -/
theorem coeff_heatSeries (ν : ℚ) (g : ℕ → ℚ) (α : Index 2) :
    coeff α (heatSeries ν g) = ν ^ α 0 * g (α 1 + 2 * α 0) / factorial α := rfl

private theorem factorial_two (α : Index 2) :
    factorial α = ((α 0).factorial : ℚ) * ((α 1).factorial : ℚ) := by
  simp [factorial, Fin.prod_univ_two]

/-- The viscous heat equation, coefficient by coefficient. -/
theorem heatSeries_pde (ν : ℚ) (g : ℕ → ℚ) :
    ogfD 0 (heatSeries ν g) = C ν * ogfD 1 (ogfD 1 (heatSeries ν g)) := by
  ext α
  rw [coeff_C_mul, coeff_ogfD, coeff_ogfD, ogfD_apply]
  simp only [heatSeries, Finsupp.update_apply, if_true, show ((1 : Fin 2) = 0) = False by decide,
    show ((0 : Fin 2) = 1) = False by decide, if_false, factorial_two]
  rw [show α 1 + 2 * (α 0 + 1) = α 1 + 1 + 1 + 2 * α 0 by ring]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have h0 : ((α 0).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : ((α 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- Differentiating along `x` shifts the profile: `D_x φ` is the heat stream of `g_(j+1)`. -/
theorem ogfD_heatSeries (ν : ℚ) (g : ℕ → ℚ) :
    ogfD 1 (heatSeries ν g) = heatSeries ν fun j => g (j + 1) := by
  ext α
  rw [coeff_ogfD, coeff_heatSeries]
  simp only [heatSeries, Finsupp.update_apply, if_true, show ((0 : Fin 2) = 1) = False by decide,
    if_false, factorial_two]
  rw [show α 1 + 1 + 2 * α 0 = α 1 + 2 * α 0 + 1 by ring]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have h0 : ((α 0).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : ((α 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

/-- The constant term is the profile's value at `0`. -/
theorem constantCoeff_heatSeries (ν : ℚ) (g : ℕ → ℚ) : constantCoeff (heatSeries ν g) = g 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_heatSeries]
  simp [factorial]

/-! ## Majorants of the heat stream -/

/-- The radii `[ρ²/ν, ρ]` of the viscous heat majorant. -/
def heatRadii (ν ρ : ℚ) : Fin 2 → ℚ := ![ρ ^ 2 / ν, ρ]

/-- Positive radii need `ν > 0`. -/
theorem heatRadii_pos {ν ρ : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (i : Fin 2) : 0 < heatRadii ν ρ i := by
  fin_cases i <;> simp [heatRadii] <;> positivity

/-- The weight of the heat radii at `(n, k)` is `ν^n ρ^(−(k+2n))`. -/
theorem radiiWeight_heatRadii {ν ρ : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (α : Index 2) :
    radiiWeight (heatRadii ν ρ) α = ν ^ α 0 * (ρ ^ (α 1 + 2 * α 0))⁻¹ := by
  unfold radiiWeight heatRadii
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have := hν.ne'
  have := hρ.ne'
  rw [div_pow, inv_div, pow_add, pow_mul]
  field_simp

/-- A profile bound that is only required from degree `j₀` on. -/
def ProfileBoundFrom (g : ℕ → ℚ) (j₀ : ℕ) (M ρ : ℚ) : Prop :=
  ∀ j, j₀ ≤ j → |g j| ≤ M * (ρ ^ j)⁻¹

/-- **Majorant transfer with viscosity.** Coefficients of degree at least `j₀`
in the profile control the stream at every index with `k + 2n ≥ j₀`. -/
theorem abs_coeff_heatSeries_le {ν ρ M : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) {g : ℕ → ℚ}
    {j₀ : ℕ} (bound : ProfileBoundFrom g j₀ M ρ) (α : Index 2)
    (hα : j₀ ≤ α 1 + 2 * α 0) :
    |coeff α (heatSeries ν g)| ≤ M * radiiWeight (heatRadii ν ρ) α := by
  rw [coeff_heatSeries, radiiWeight_heatRadii hν hρ, abs_div, abs_mul, abs_pow, abs_of_pos hν]
  have fact : (1 : ℚ) ≤ factorial α := by
    rw [factorial_two]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  rw [abs_of_pos (a := factorial α) (by linarith)]
  calc ν ^ α 0 * |g (α 1 + 2 * α 0)| / factorial α ≤ ν ^ α 0 * |g (α 1 + 2 * α 0)| :=
        div_le_self (by positivity) fact
    _ ≤ ν ^ α 0 * (M * (ρ ^ (α 1 + 2 * α 0))⁻¹) :=
        mul_le_mul_of_nonneg_left (bound _ hα) (by positivity)
    _ = M * (ν ^ α 0 * (ρ ^ (α 1 + 2 * α 0))⁻¹) := by ring

/-- **Majorant transfer with viscosity.** The factorials are dropped, as in
`AnalyticHeat.majorizes_stream`; `ν^n` is absorbed into the `t`-radius `ρ²/ν`. -/
theorem majorizes_heatSeries {ν ρ M : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (hM : 0 ≤ M) {g : ℕ → ℚ}
    (bound : ProfileBoundFrom g 0 M ρ) :
    Majorizes .ogf (heatSeries ν g) ⟨M, heatRadii ν ρ, hM, heatRadii_pos hν hρ⟩ := by
  rw [majorizes_ogf_iff]
  exact fun α => abs_coeff_heatSeries_le hν hρ bound α (Nat.zero_le _)

/-- Every index but `0` reads a profile coefficient of degree at least `1`. -/
theorem rest_heatSeries {ν ρ M : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) {g : ℕ → ℚ}
    (bound : ProfileBoundFrom g 1 M ρ) (α : Index 2) (hα : α ≠ 0) :
    |coeff α (heatSeries ν g)| ≤ M * radiiWeight (heatRadii ν ρ) α := by
  refine abs_coeff_heatSeries_le hν hρ bound α ?_
  by_contra h
  apply hα
  ext i
  fin_cases i <;> simp <;> omega

#print axioms heatSeries_pde
#print axioms rest_heatSeries

/-! ## The quotient and its equation -/

/-- `u = −2ν · D_x φ · φ⁻¹`. -/
noncomputable def quotient (ν : ℚ) (φ : Stream 2) : Stream 2 := C (-2 * ν) * (ogfD 1 φ * φ⁻¹)

/-- The Burgers right-hand side in the OGF reading is plain ring arithmetic. -/
theorem rhs_ogf (ν : ℚ) (u : Stream 2) :
    Burgers.rhs .ogf ν u = C ν * ogfD 1 (ogfD 1 u) + C (-1) * (u * ogfD 1 u) := rfl

/-- **Cole–Hopf.** If `D_t φ = ν D_x² φ` and `φ` is invertible, the quotient
solves `D_t u = −u·D_x u + ν D_x² u`. After the derivation rules the identity
is polynomial in `D_x φ`, `D_x² φ`, `D_x³ φ` and `φ⁻¹`. -/
theorem quotient_pde (ν : ℚ) (φ : Stream 2) (hc : constantCoeff φ ≠ 0)
    (heat : ogfD 0 φ = C ν * ogfD 1 (ogfD 1 φ)) :
    ogfD 0 (quotient ν φ) = Burgers.rhs .ogf ν (quotient ν φ) := by
  rw [rhs_ogf]
  have dψ1 : ogfD 1 φ⁻¹ = -(φ⁻¹ * φ⁻¹ * ogfD 1 φ) := ogfD_inv 1 φ hc
  have dψ0 : ogfD 0 φ⁻¹ = -(φ⁻¹ * φ⁻¹ * (C ν * ogfD 1 (ogfD 1 φ))) := by rw [ogfD_inv 0 φ hc, heat]
  have dφx0 : ogfD 0 (ogfD 1 φ) = C ν * ogfD 1 (ogfD 1 (ogfD 1 φ)) := by rw [ogfD_comm, heat, ogfD_C_mul]
  have c2 : (C (-2 * ν) : Stream 2) = -(2 * C ν) := by
    rw [map_mul, map_neg, map_ofNat]
    ring
  have c1 : (C (-1) : Stream 2) = -1 := by rw [map_neg, map_one]
  simp only [quotient, ogfD_C_mul]
  simp only [ogfD_add, ogfD_mul, ogfD_neg, dψ1, dψ0, dφx0]
  rw [c2, c1]
  ring

/-- The `t = 0` slice of a stream, as a boundary input. -/
noncomputable def zeroSlice (u : Stream 2) : Stream 2 := fun α => if α 0 = 0 then u α else 0

/-- On the slice it is the stream. -/
theorem zeroSlice_apply (u : Stream 2) (α : Index 2) (zero : α 0 = 0) : zeroSlice u α = u α := by
  simp [zeroSlice, zero]

/-- The quotient is the formal Burgers stream from its own slice. -/
theorem quotient_eq_stream (ν : ℚ) (φ : Stream 2) (hc : constantCoeff φ ≠ 0)
    (heat : ogfD 0 φ = C ν * ogfD 1 (ogfD 1 φ)) :
    quotient ν φ = Burgers.stream .ogf ν (zeroSlice (quotient ν φ)) :=
  Burgers.eq_stream .ogf ν _ _ (quotient_pde ν φ hc heat) fun α zero => (zeroSlice_apply _ α zero).symm

/-- The Burgers circuit reconstructs the quotient from its slice, and nothing else. -/
theorem candidate_quotient (ν : ℚ) (φ : Stream 2) (hc : constantCoeff φ ≠ 0)
    (heat : ogfD 0 φ = C ν * ogfD 1 (ogfD 1 φ)) (a unused v : Stream 2)
    (rel : (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (quotient ν φ), unused] ![v, a]) :
    a = quotient ν φ := by
  rw [Burgers.candidate_stream .ogf ν _ a unused v rel, ← quotient_eq_stream ν φ hc heat]

#print axioms quotient_pde
#print axioms candidate_quotient

/-! ## Exponential-sum profiles -/

/-- The profile of `D_x φ`: each `cᵢ e^(aᵢ x)` differentiates to `cᵢ aᵢ e^(aᵢ x)`. -/
def shifted (terms : List (ℚ × ℚ)) : List (ℚ × ℚ) := terms.map fun t => (t.1 * t.2, t.2)

/-- Shifting the profile is the derivative's profile. -/
theorem expSum_shifted (terms : List (ℚ × ℚ)) (j : ℕ) :
    expSum terms (j + 1) = expSum (shifted terms) j := by
  unfold expSum shifted
  induction terms with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.map_map] at ih ⊢
      rw [pow_succ, ih]
      ring

/-- The fit to `ρ` is unchanged by the shift. -/
theorem expSumFits_shifted (terms : List (ℚ × ℚ)) (ρ : ℚ) :
    expSumFits (shifted terms) ρ = expSumFits terms ρ := by
  unfold expSumFits shifted
  induction terms with
  | nil => rfl
  | cons head tail ih => simp [List.all_cons, ih]

/-- The constant term of the profile, `Σᵢ cᵢ`. -/
def constantTerm (terms : List (ℚ × ℚ)) : ℚ := (terms.map Prod.fst).sum

/-- The profile's value at `0`. -/
theorem expSum_zero (terms : List (ℚ × ℚ)) : expSum terms 0 = constantTerm terms := by
  unfold expSum constantTerm
  induction terms with
  | nil => rfl
  | cons head tail ih => simp

/-- The weight of the terms with `aᵢ ≠ 0`: the ones that survive at positive degree. -/
def restWeight (terms : List (ℚ × ℚ)) : ℚ :=
  (terms.map fun t => if t.2 = 0 then 0 else |t.1|).sum

/-- Non-negative. -/
theorem restWeight_nonneg (terms : List (ℚ × ℚ)) : 0 ≤ restWeight terms := by
  unfold restWeight
  induction terms with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      refine add_nonneg ?_ ih
      split_ifs <;> simp

/-- At positive degree only the terms with `aᵢ ≠ 0` contribute. -/
theorem profileBoundFrom_expSum (terms : List (ℚ × ℚ)) {ρ : ℚ} (hρ : 0 < ρ)
    (fits : expSumFits terms ρ = true) :
    ProfileBoundFrom (expSum terms) 1 (restWeight terms) ρ := by
  intro j hj
  unfold expSum restWeight
  induction terms with
  | nil => simp
  | cons head tail ih =>
      simp only [expSumFits, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at fits
      simp only [List.map_cons, List.sum_cons, add_mul]
      refine (abs_add_le _ _).trans (add_le_add ?_ (ih fits.2))
      split_ifs with h
      · rw [h, zero_pow (by omega), mul_zero, abs_zero, zero_mul]
      · exact AnalyticHeat.abs_term_le hρ fits.1 j

/-! ## The front: a Burgers stream with a certified truncation -/

/-- The heat stream of the exponential-sum profile. -/
noncomputable def expSumHeat (ν : ℚ) (terms : List (ℚ × ℚ)) : Stream 2 := heatSeries ν (expSum terms)

/-- The Burgers stream `−2ν · D_x φ · φ⁻¹`. -/
noncomputable def front (ν : ℚ) (terms : List (ℚ × ℚ)) : Stream 2 := quotient ν (expSumHeat ν terms)

/-- The heat stream's constant term is the profile's. -/
theorem constantCoeff_expSumHeat (ν : ℚ) (terms : List (ℚ × ℚ)) :
    constantCoeff (expSumHeat ν terms) = constantTerm terms := by
  rw [expSumHeat, constantCoeff_heatSeries, expSum_zero]

/-- `D_x φ` is the heat stream of the shifted profile. -/
theorem ogfD_expSumHeat (ν : ℚ) (terms : List (ℚ × ℚ)) :
    ogfD 1 (expSumHeat ν terms) = heatSeries ν (expSum (shifted terms)) := by
  rw [expSumHeat, ogfD_heatSeries]
  congr 1
  funext j
  exact expSum_shifted terms j

/-- The majorant bound of the front: `|2ν| · (Σ |cᵢ aᵢ|) / |Σ cᵢ|`. -/
noncomputable def frontBound (ν : ℚ) (terms : List (ℚ × ℚ)) : ℚ :=
  |(-2) * ν| * (expSumWeight (shifted terms) * |constantTerm terms|⁻¹)

/-- Non-negative. -/
theorem frontBound_nonneg (ν : ℚ) (terms : List (ℚ × ℚ)) : 0 ≤ frontBound ν terms :=
  mul_nonneg (abs_nonneg _)
    (mul_nonneg (AnalyticHeat.expSumWeight_nonneg _) (inv_nonneg.mpr (abs_nonneg _)))

/-- The decidable smallness condition for the inverse at radii `r`:
`(M_rest / |c|) · (∏ (1 − r_i/R_i)⁻¹ − 1) ≤ 1`. An `abbrev`, so `decide +kernel`
sees the inequality directly. -/
abbrev smallEnough (ν ρ : ℚ) (terms : List (ℚ × ℚ)) (r : Fin 2 → ℚ) : Prop :=
  restWeight terms / |constantTerm terms| * ((∏ i, (1 - r i / heatRadii ν ρ i)⁻¹) - 1) ≤ 1

/-- The front's majorant: bound `frontBound`, radii `r/2`. -/
noncomputable def frontMajorant (ν : ℚ) (terms : List (ℚ × ℚ)) (r : Fin 2 → ℚ)
    (hr : ∀ i, 0 < r i) : Majorant 2 :=
  ⟨frontBound ν terms, fun i => r i / 2, frontBound_nonneg ν terms, fun i => half_pos (hr i)⟩

/-- **The front is majorized.** Heat majorant of `D_x φ` at radii `r`, inverse
majorant of `φ⁻¹` at radii `r`, product at `r/2`, scaled by `|2ν|`. -/
theorem majorizes_front {ν ρ : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (terms : List (ℚ × ℚ))
    (fits : expSumFits terms ρ = true) {r : Fin 2 → ℚ} (hr : ∀ i, 0 < r i)
    (inside : ∀ i, r i < heatRadii ν ρ i) (small : smallEnough ν ρ terms r) :
    Majorizes .ogf (front ν terms) (frontMajorant ν terms r hr) := by
  have hR := heatRadii_pos hν hρ
  -- the inverse
  have inv : Majorizes .ogf (expSumHeat ν terms)⁻¹ ⟨|constantTerm terms|⁻¹, r, _, hr⟩ :=
    majorizes_inv (expSumHeat ν terms) (constantCoeff_expSumHeat ν terms) (restWeight_nonneg terms) hR hr inside
      (rest_heatSeries hν hρ (profileBoundFrom_expSum terms hρ fits)) small
  -- the derivative, at the heat radii and then at `r`
  have der : Majorizes .ogf (ogfD 1 (expSumHeat ν terms))
      ⟨expSumWeight (shifted terms), heatRadii ν ρ, AnalyticHeat.expSumWeight_nonneg _, hR⟩ := by
    rw [ogfD_expSumHeat]
    refine majorizes_heatSeries hν hρ (AnalyticHeat.expSumWeight_nonneg _) fun j _ => ?_
    exact AnalyticHeat.profileBound_expSum (shifted terms) hρ
      (by rw [expSumFits_shifted]; exact fits) j
  have der' : Majorizes .ogf (ogfD 1 (expSumHeat ν terms))
      ⟨expSumWeight (shifted terms), r, AnalyticHeat.expSumWeight_nonneg _, hr⟩ :=
    majorizes_mono der _ le_rfl fun i => le_of_lt (inside i)
  -- the product and the scaling
  have prod := majorizes_mul r der' inv (fun _ => rfl) (fun _ => rfl)
  have scaled := majorizes_C_mul prod (-2 * ν)
  exact majorizes_mono scaled _ le_rfl fun i => le_rfl

/-- The front's constant term: `−2ν · (Σ cᵢ aᵢ) / (Σ cᵢ)`, the value of
`−2ν φ_x/φ` at the origin. The one coefficient of the opaque boundary
`zeroSlice (front ν terms)` that is read off directly. -/
theorem constantCoeff_front (ν : ℚ) (terms : List (ℚ × ℚ)) :
    constantCoeff (front ν terms) =
      -2 * ν * (constantTerm (shifted terms) * (constantTerm terms)⁻¹) := by
  simp only [front, quotient, map_mul, constantCoeff_C, ogfD_expSumHeat, constantCoeff_heatSeries,
    expSum_zero, constantCoeff_inv, constantCoeff_expSumHeat]

/-- The front's tail certificate, named so that `hasSum` and `truncationBound`
are available separately. -/
noncomputable def certificate {ν ρ : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (terms : List (ℚ × ℚ))
    (fits : expSumFits terms ρ = true) {r : Fin 2 → ℚ} (hr : ∀ i, 0 < r i)
    (inside : ∀ i, r i < heatRadii ν ρ i) (small : smallEnough ν ρ terms r) (box : Box 2)
    (boxInside : ∀ i, box.radius i < r i / 2) : TailCertificate .ogf (front ν terms) :=
  ⟨frontMajorant ν terms r hr, box, boxInside, majorizes_front hν hρ terms fits hr inside small⟩

/-- **Existence.** The circuit relates the front to its own slice, so the root
claim below is not vacuous. -/
theorem circuit_front (ν : ℚ) (terms : List (ℚ × ℚ)) (c0 : constantTerm terms ≠ 0)
    (unused : Stream 2) :
    (Burgers.circuit .ogf ν).Rel ![front ν terms, zeroSlice (front ν terms), unused]
      ![Burgers.rhs .ogf ν (front ν terms), front ν terms] := by
  have hc : constantCoeff (expSumHeat ν terms) ≠ 0 := by rw [constantCoeff_expSumHeat]; exact c0
  have eq := quotient_eq_stream ν (expSumHeat ν terms) hc (heatSeries_pde ν _)
  have rel := Burgers.circuit_solution .ogf ν (zeroSlice (quotient ν (expSumHeat ν terms))) unused
  rw [← eq] at rel
  exact rel

/-- **Certified truncation of the front.** Whatever the Burgers circuit
reconstructs from the front's `t = 0` zeroSlice is the front, so a box inside
`r/2` and a checked `tailBound ≤ ε` bound its truncation error at window `N`
by `ε`. Every side condition is decidable for concrete data. -/
theorem front_truncation {ν ρ ε : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (terms : List (ℚ × ℚ))
    (c0 : constantTerm terms ≠ 0) (fits : expSumFits terms ρ = true) {r : Fin 2 → ℚ}
    (hr : ∀ i, 0 < r i) (inside : ∀ i, r i < heatRadii ν ρ i) (small : smallEnough ν ρ terms r)
    (box : Box 2) (boxInside : ∀ i, box.radius i < r i / 2) (N : Fin 2 → ℕ)
    (le : tailBound (frontMajorant ν terms r hr) box N ≤ ε) :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        TruncationBound .ogf a box N ε := by
  intro a unused v rel
  have hc : constantCoeff (expSumHeat ν terms) ≠ 0 := by rw [constantCoeff_expSumHeat]; exact c0
  simp only [front] at rel
  rw [candidate_quotient ν _ hc (heatSeries_pde ν _) a unused v rel]
  exact ((certificate hν hρ terms fits hr inside small box boxInside).truncationBound N).mono le

/-! ## The analytic field of the heat stream and of the front -/

/-- The classical field of the heat stream of the exponential sum:
`Σᵢ cᵢ e^(ν aᵢ² t + aᵢ x)` at `(t, x)`. -/
noncomputable def expSumField (ν : ℚ) (terms : List (ℚ × ℚ)) (x : Fin 2 → ℝ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * Real.exp (ν * t.2 ^ 2 * x 0 + t.2 * x 1)).sum

private theorem hasSum_exp (r : ℝ) :
    HasSum (fun k => r ^ k / (k.factorial : ℝ)) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

/-- One exponential: the heat stream of the profile `a^j` sums to
`e^(ν a² t + a x)` at every real point. -/
theorem hasSum_heatSeries_pow (ν a : ℚ) (x : Fin 2 → ℝ) :
    HasSum (seriesTerm .ogf (heatSeries ν fun j => a ^ j) x)
      (Real.exp (ν * a ^ 2 * x 0 + a * x 1)) := by
  let y : Fin 2 → ℝ := ![(ν : ℝ) * a ^ 2 * x 0, (a : ℝ) * x 1]
  have h := hasSum_index_prod (fun i k => y i ^ k / (k.factorial : ℝ)) (fun i => Real.exp (y i))
    (fun i => by
      simpa [norm_div, norm_pow, Real.norm_eq_abs] using Real.summable_pow_div_factorial |y i|)
    (fun i => hasSum_exp (y i))
  rw [Fin.prod_univ_two, ← Real.exp_add] at h
  refine h.congr_fun fun α => ?_
  rw [seriesTerm_ogf, coeff_heatSeries, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one, factorial_two]
  push_cast
  have h0 : ((α 0).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : ((α 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  ring

/-- The heat stream is linear in the profile: one more exponential term. -/
theorem heatSeries_expSum_cons (ν : ℚ) (t : ℚ × ℚ) (ts : List (ℚ × ℚ)) :
    heatSeries ν (expSum (t :: ts)) =
      C t.1 * heatSeries ν (fun j => t.2 ^ j) + heatSeries ν (expSum ts) := by
  ext α
  rw [map_add, coeff_C_mul, coeff_heatSeries, coeff_heatSeries, coeff_heatSeries]
  simp only [expSum, List.map_cons, List.sum_cons]
  ring

theorem heatSeries_expSum_nil (ν : ℚ) : heatSeries ν (expSum []) = 0 := by
  ext α
  simp [coeff_heatSeries, expSum]

/-- **The heat stream of an exponential sum sums to its classical field** at
every real point: no box is needed, the field is entire. -/
theorem hasSum_heatSeries_expSum (ν : ℚ) (terms : List (ℚ × ℚ)) (x : Fin 2 → ℝ) :
    HasSum (seriesTerm .ogf (heatSeries ν (expSum terms)) x) (expSumField ν terms x) := by
  induction terms with
  | nil =>
      rw [heatSeries_expSum_nil]
      simp only [expSumField, List.map_nil, List.sum_nil]
      refine hasSum_zero.congr_fun fun α => ?_
      rw [seriesTerm_ogf, map_zero]
      simp
  | cons t ts ih =>
      rw [heatSeries_expSum_cons]
      have h := ((hasSum_heatSeries_pow ν t.2 x).mul_left (t.1 : ℝ)).add ih
      simp only [expSumField, List.map_cons, List.sum_cons] at h ⊢
      refine h.congr_fun fun α => ?_
      rw [seriesTerm_ogf, seriesTerm_ogf, seriesTerm_ogf, map_add, coeff_C_mul]
      push_cast
      ring

theorem analyticField_heatSeries_expSum (ν : ℚ) (terms : List (ℚ × ℚ)) (x : Fin 2 → ℝ) :
    analyticField .ogf (heatSeries ν (expSum terms)) x = expSumField ν terms x :=
  (hasSum_heatSeries_expSum ν terms x).tsum_eq

/-- **The front's analytic field is the Cole–Hopf quotient of classical
fields**, `−2ν (Σ cᵢ aᵢ e^(ν aᵢ² t + aᵢ x)) / (Σ cᵢ e^(ν aᵢ² t + aᵢ x))`, on a box
strictly inside the radii `r/2` of its majorant; the denominator does not
vanish there. The premises are those of `front_truncation`. -/
theorem analyticField_front {ν ρ : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (terms : List (ℚ × ℚ))
    (c0 : constantTerm terms ≠ 0) (fits : expSumFits terms ρ = true) {r : Fin 2 → ℚ}
    (hr : ∀ i, 0 < r i) (inside : ∀ i, r i < heatRadii ν ρ i) (small : smallEnough ν ρ terms r)
    (box : Box 2) (boxInside : ∀ i, box.radius i < r i / 2) {x : Fin 2 → ℝ} (hx : box.Mem x) :
    expSumField ν terms x ≠ 0 ∧
      analyticField .ogf (front ν terms) x =
        -2 * ν * expSumField ν (shifted terms) x / expSumField ν terms x := by
  have hR := heatRadii_pos hν hρ
  have hc : constantCoeff (expSumHeat ν terms) ≠ 0 := by rw [constantCoeff_expSumHeat]; exact c0
  have inv : Majorizes .ogf (expSumHeat ν terms)⁻¹ ⟨|constantTerm terms|⁻¹, r, _, hr⟩ :=
    majorizes_inv (expSumHeat ν terms) (constantCoeff_expSumHeat ν terms) (restWeight_nonneg terms)
      hR hr inside (rest_heatSeries hν hρ (profileBoundFrom_expSum terms hρ fits)) small
  have phi : Majorizes .ogf (expSumHeat ν terms)
      ⟨expSumWeight terms, heatRadii ν ρ, AnalyticHeat.expSumWeight_nonneg _, hR⟩ :=
    majorizes_heatSeries hν hρ (AnalyticHeat.expSumWeight_nonneg _) fun j _ =>
      AnalyticHeat.profileBound_expSum terms hρ fits j
  have der : Majorizes .ogf (ogfD 1 (expSumHeat ν terms))
      ⟨expSumWeight (shifted terms), heatRadii ν ρ, AnalyticHeat.expSumWeight_nonneg _, hR⟩ := by
    rw [ogfD_expSumHeat]
    refine majorizes_heatSeries hν hρ (AnalyticHeat.expSumWeight_nonneg _) fun j _ => ?_
    exact AnalyticHeat.profileBound_expSum (shifted terms) hρ
      (by rw [expSumFits_shifted]; exact fits) j
  have insideR : ∀ i, box.radius i < r i := fun i =>
    lt_of_lt_of_le (boxInside i) (half_le_self (hr i).le)
  have insideH : ∀ i, box.radius i < heatRadii ν ρ i := fun i => (insideR i).trans (inside i)
  obtain ⟨finv, fne⟩ := analyticField_inv hc phi inv insideH insideR hx
  have fφ : analyticField .ogf (expSumHeat ν terms) x = expSumField ν terms x :=
    analyticField_heatSeries_expSum ν terms x
  have fD : analyticField .ogf (ogfD 1 (expSumHeat ν terms)) x = expSumField ν (shifted terms) x := by
    rw [ogfD_expSumHeat]
    exact analyticField_heatSeries_expSum ν (shifted terms) x
  refine ⟨fφ ▸ fne, ?_⟩
  simp only [front, quotient]
  rw [analyticField_C_mul, analyticField_mul der inv insideH insideR hx, finv, fD, fφ,
    div_eq_mul_inv]
  push_cast
  ring

/-! ## Windows: the front's coefficients from a checked inverse table

A field bound on the front needs its window coefficients as rationals the
kernel can compute. `φ` and `D_x φ` have closed-form coefficients; the window
of `φ⁻¹` is a table `Q` computed outside Lean and *checked* here by the
finite identity `(φ · Q)_k = [k = 0]` on the grid (`coeff_inv_window`). The
front's window is then `−2ν · (D_x φ · Q)` on the grid, and
`abs_windowField_sub_le` bounds the window field by a rational sum. -/

open Lowering in
/-- The heat stream's coefficient at a degree vector, as the kernel computes it. -/
def heatCoeff (ν : ℚ) (terms : List (ℚ × ℚ)) (k : Degrees 2) : ℚ :=
  ν ^ k 0 * expSum terms (k 1 + 2 * k 0) / (((k 0).factorial : ℚ) * ((k 1).factorial : ℚ))

open Lowering in
theorem coeff_toIndex_expSumHeat (ν : ℚ) (terms : List (ℚ × ℚ)) (k : Degrees 2) :
    coeff k.toIndex (expSumHeat ν terms) = heatCoeff ν terms k := by
  rw [expSumHeat, coeff_heatSeries, factorial_two]
  simp only [heatCoeff, Degrees.toIndex_apply]

open Lowering in
/-- The checked identity: `Q` is the window of `φ⁻¹` below `N`. An `abbrev`,
so `decide +kernel` sees the bounded quantifier and the rational equalities. -/
abbrev WindowIdentity (ν : ℚ) (terms : List (ℚ × ℚ)) (N : Fin 2 → ℕ) (Q : Degrees 2 → ℚ) : Prop :=
  ∀ k ∈ grid 2 (fun i => N i - 1),
    ((grid 2 k).map fun a => heatCoeff ν terms a * Q (k - a)).sum = if k = 0 then 1 else 0

open Lowering in
theorem coe_toIndex (k : Degrees 2) : ⇑(k.toIndex) = k := funext (Degrees.toIndex_apply k)

open Lowering in
theorem toIndex_zero : (0 : Degrees 2).toIndex = 0 := by
  ext i
  rfl

open Lowering in
theorem toIndex_eq_zero (k : Degrees 2) : k.toIndex = 0 ↔ k = 0 := by
  constructor
  · intro h
    exact Degrees.toIndex_injective (h.trans toIndex_zero.symm)
  · rintro rfl
    exact toIndex_zero

open Lowering in
theorem mem_grid_of_le {N : Fin 2 → ℕ} {k : Degrees 2}
    (hk : k ∈ grid 2 (fun i => N i - 1)) (a : Degrees 2) :
    k - a ∈ grid 2 (fun i => N i - 1) := by
  rw [mem_grid] at hk ⊢
  intro i
  have := hk i
  simp only [Pi.sub_apply]
  omega

open Lowering in
/-- The inverse's window is the checked table. -/
theorem coeff_inv_expSumHeat_window {ν : ℚ} {terms : List (ℚ × ℚ)} (c0 : constantTerm terms ≠ 0)
    {N : Fin 2 → ℕ} (hN : ∀ i, 0 < N i) {Q : Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) :
    ∀ k ∈ grid 2 (fun i => N i - 1), coeff k.toIndex (expSumHeat ν terms)⁻¹ = Q k := by
  intro k hk
  have hc : constantCoeff (expSumHeat ν terms) ≠ 0 := by
    rw [constantCoeff_expSumHeat]; exact c0
  have below : Below N k.toIndex := by
    intro i
    have := (mem_grid _ k).mp hk i
    have := hN i
    simp only [Degrees.toIndex_apply]
    omega
  refine coeff_inv_window (expSumHeat ν terms) hc N (fun β => Q ⇑β) ?_ k.toIndex below
  intro α hα
  have h := identity ⇑α (by
    rw [mem_grid]
    intro i
    have := hα i
    have := hN i
    omega)
  rw [← toIndex_coe α, sum_antidiagonal (⇑α) (fun p q => coeff p (expSumHeat ν terms) * Q ⇑q)]
  simp only [toIndex_eq_zero]
  rw [← h]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [coeff_toIndex_expSumHeat, coe_toIndex]

open Lowering in
/-- The front's window coefficient from the checked table: `−2ν (D_x φ · Q)_k`. -/
def frontWindow (ν : ℚ) (terms : List (ℚ × ℚ)) (Q : Degrees 2 → ℚ) (k : Degrees 2) : ℚ :=
  -2 * ν * ((grid 2 k).map fun a => heatCoeff ν (shifted terms) a * Q (k - a)).sum

open Lowering in
theorem coeff_toIndex_front {ν : ℚ} {terms : List (ℚ × ℚ)} (c0 : constantTerm terms ≠ 0)
    {N : Fin 2 → ℕ} (hN : ∀ i, 0 < N i) {Q : Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) :
    ∀ k ∈ grid 2 (fun i => N i - 1), coeff k.toIndex (front ν terms) = frontWindow ν terms Q k := by
  intro k hk
  simp only [front, quotient]
  rw [coeff_C_mul, coeff_mul,
    sum_antidiagonal k (fun p q => coeff p (ogfD 1 (expSumHeat ν terms)) * coeff q (expSumHeat ν terms)⁻¹)]
  unfold frontWindow
  congr 1
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [ogfD_expSumHeat, show heatSeries ν (expSum (shifted terms)) = expSumHeat ν (shifted terms)
    from rfl, coeff_toIndex_expSumHeat,
    coeff_inv_expSumHeat_window c0 hN identity (k - a) (mem_grid_of_le hk a)]

open Lowering in
/-- `Σ_{0 ≠ k < N} |W_k| ∏ rᵢ^kᵢ`, the window's spread over the box. -/
def windowSpread (ν : ℚ) (terms : List (ℚ × ℚ)) (Q : Degrees 2 → ℚ) (b : Box 2) (N : Fin 2 → ℕ) : ℚ :=
  ((grid 2 fun i => N i - 1).map fun k =>
    if k = 0 then 0 else |frontWindow ν terms Q k| * ∏ i, b.radius i ^ k i).sum

open Lowering in
/-- The window polynomial at a rational point. -/
def frontValue (ν : ℚ) (terms : List (ℚ × ℚ)) (Q : Degrees 2 → ℚ) (N : Fin 2 → ℕ)
    (p : Fin 2 → ℚ) : ℚ :=
  ((grid 2 fun i => N i - 1).map fun k => frontWindow ν terms Q k * ∏ i, p i ^ k i).sum

open Lowering in
theorem windowSpread_eq {ν : ℚ} {terms : List (ℚ × ℚ)} (c0 : constantTerm terms ≠ 0)
    {N : Fin 2 → ℕ} (hN : ∀ i, 0 < N i) {Q : Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) (b : Box 2) :
    (∑ α ∈ window N, (if α = 0 then (0 : ℝ) else
      |((coeff α (front ν terms) : ℚ) : ℝ)| * ∏ i, ((b.radius i : ℚ) : ℝ) ^ α i)) =
      ((windowSpread ν terms Q b N : ℚ) : ℝ) := by
  rw [sum_window_eq_grid N hN]
  unfold windowSpread
  rw [Rat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  simp only [Function.comp, coeff_toIndex_front c0 hN identity k hk, toIndex_eq_zero,
    Degrees.toIndex_apply]
  split_ifs <;> push_cast <;> rfl

open Lowering in
theorem frontValue_eq {ν : ℚ} {terms : List (ℚ × ℚ)} (c0 : constantTerm terms ≠ 0)
    {N : Fin 2 → ℕ} (hN : ∀ i, 0 < N i) {Q : Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) (p : Fin 2 → ℚ) :
    windowField .ogf N (front ν terms) (fun i => (p i : ℝ)) =
      ((frontValue ν terms Q N p : ℚ) : ℝ) := by
  rw [windowField_rat, sum_window_eq_grid N hN]
  unfold frontValue
  congr 2
  refine List.map_congr_left fun k hk => ?_
  rw [coeff_toIndex_front c0 hN identity k hk]
  simp only [Degrees.toIndex_apply]

open Lowering in
theorem frontWindow_zero_eq {ν : ℚ} {terms : List (ℚ × ℚ)} (c0 : constantTerm terms ≠ 0)
    {N : Fin 2 → ℕ} (hN : ∀ i, 0 < N i) {Q : Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) :
    coeff 0 (front ν terms) = frontWindow ν terms Q 0 := by
  rw [← toIndex_zero]
  exact coeff_toIndex_front c0 hN identity 0 ((mem_grid _ 0).mpr fun i => Nat.zero_le _)

/-- **A band on the front from a checked window.** With the premises of
`front_truncation` and a table `Q` passing `WindowIdentity`, if
`lo ≤ W₀ − B − ε` and `W₀ + B + ε ≤ hi` (all rationals the kernel computes)
then every stream the circuit reconstructs from the front's slice has its
analytic field in `[lo, hi]` everywhere on the box. -/
theorem front_band_of_window {ν ρ ε : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (terms : List (ℚ × ℚ))
    (c0 : constantTerm terms ≠ 0) (fits : expSumFits terms ρ = true) {r : Fin 2 → ℚ}
    (hr : ∀ i, 0 < r i) (inside : ∀ i, r i < heatRadii ν ρ i) (small : smallEnough ν ρ terms r)
    (box : Box 2) (boxInside : ∀ i, box.radius i < r i / 2) (N : Fin 2 → ℕ) (hN : ∀ i, 0 < N i)
    (le : tailBound (frontMajorant ν terms r hr) box N ≤ ε) {Q : Lowering.Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) {lo hi : ℚ}
    (low : lo ≤ frontWindow ν terms Q 0 - windowSpread ν terms Q box N - ε)
    (high : frontWindow ν terms Q 0 + windowSpread ν terms Q box N + ε ≤ hi) :
    ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, box.Mem x →
          lo ≤ analyticField .ogf a x ∧ analyticField .ogf a x ≤ hi := by
  intro a unused v rel x hx
  have trunc : ∀ y, box.Mem y →
      |analyticField .ogf a y - windowField .ogf N a y| ≤ ε :=
    front_truncation hν hρ terms c0 fits hr inside small box boxInside N le a unused v rel
  have hc : constantCoeff (expSumHeat ν terms) ≠ 0 := by
    rw [constantCoeff_expSumHeat]; exact c0
  have eq : a = front ν terms := by
    simp only [front] at rel
    exact candidate_quotient ν _ hc (heatSeries_pde ν _) a unused v rel
  subst eq
  have win := abs_windowField_sub_le N hN (front ν terms) box hx
  rw [windowSpread_eq c0 hN identity box, frontWindow_zero_eq c0 hN identity] at win
  have t := abs_le.mp (trunc x hx)
  have w := abs_le.mp win
  have low' : (lo : ℝ) ≤ frontWindow ν terms Q 0 - windowSpread ν terms Q box N - ε := by
    exact_mod_cast low
  have high' : (frontWindow ν terms Q 0 + windowSpread ν terms Q box N + ε : ℝ) ≤ hi := by
    exact_mod_cast high
  constructor <;> linarith [t.1, t.2, w.1, w.2]

/-- **A point above the band refutes it.** A rational point of the box where
the window exceeds `hi` by more than `ε` shows that `u ≤ hi` fails on the
box, for the front itself, which the circuit does reconstruct. -/
theorem front_above_of_window {ν ρ ε : ℚ} (hν : 0 < ν) (hρ : 0 < ρ) (terms : List (ℚ × ℚ))
    (c0 : constantTerm terms ≠ 0) (fits : expSumFits terms ρ = true) {r : Fin 2 → ℚ}
    (hr : ∀ i, 0 < r i) (inside : ∀ i, r i < heatRadii ν ρ i) (small : smallEnough ν ρ terms r)
    (box : Box 2) (boxInside : ∀ i, box.radius i < r i / 2) (N : Fin 2 → ℕ) (hN : ∀ i, 0 < N i)
    (le : tailBound (frontMajorant ν terms r hr) box N ≤ ε) {Q : Lowering.Degrees 2 → ℚ}
    (identity : WindowIdentity ν terms N Q) (p : Fin 2 → ℚ) (hp : ∀ i, |p i| ≤ box.radius i)
    {hi : ℚ} (gt : hi < frontValue ν terms Q N p - ε) :
    ¬ ∀ a unused v : Stream 2,
      (Burgers.circuit .ogf ν).Rel ![a, zeroSlice (front ν terms), unused] ![v, a] →
        ∀ x : Fin 2 → ℝ, box.Mem x → analyticField .ogf a x ≤ hi := by
  intro h
  have hx : box.Mem (fun i => (p i : ℝ)) := fun i => by
    show |(p i : ℝ)| ≤ ((box.radius i : ℚ) : ℝ)
    exact_mod_cast hp i
  have above := h (front ν terms) 0 _ (circuit_front ν terms c0 0) _ hx
  have trunc : |analyticField .ogf (front ν terms) (fun i => (p i : ℝ)) -
      windowField .ogf N (front ν terms) (fun i => (p i : ℝ))| ≤ ε :=
    front_truncation hν hρ terms c0 fits hr inside small box boxInside N le (front ν terms) 0 _
      (circuit_front ν terms c0 0) _ hx
  rw [frontValue_eq c0 hN identity p] at trunc
  have t := abs_le.mp trunc
  have gt' : (hi : ℝ) < frontValue ν terms Q N p - ε := by exact_mod_cast gt
  linarith [t.1, t.2]

#print axioms majorizes_front
#print axioms circuit_front
#print axioms front_truncation
#print axioms analyticField_front
#print axioms front_band_of_window
#print axioms front_above_of_window
end Gimle.Asgard.Streams.ColeHopf
