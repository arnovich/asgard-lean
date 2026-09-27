import Gimle.Asgard.Streams.Heat
import Gimle.Asgard.Streams.Tail

/-! # Heat evolution of an analytic profile, with a certified majorant

Axes are ordered `[t, x]`, as in `Streams.Heat`. An analytic spatial profile is
given by its raw EGF coefficients `g : ℕ → ℚ`, so that formally
`p(x) = Σ_j g_j x^j / j!` and `g_j = p^(j)(0)`. The same profile as a one-axis
formal stream, in either basis, is `profile basis g`; `coeffs basis p` recovers
`g` from any such stream (`coeffs_profile`, `profile_coeffs`).

The formal heat solution `u = Σ_n t^n/n! · D_x^(2n) p` has raw EGF coefficients

`u_(n,k) = g_(k+2n)`   (`stream_egf_apply`),

that is, decoded (OGF) coefficients `g_(k+2n) / (n!·k!)` (`stream_ogf_apply`).

What is proved:

* **Circuit relation** (`circuit_stream`): the original `D_x²`/`I_t` heat circuit
  of `Streams.Heat` returns `[D_x² u, u]` on `[u, boundary basis g, unused]`,
  where `boundary basis g` is the whole profile on the `t = 0` slice. Any stream
  the circuit reconstructs from that boundary is `stream basis g`
  (`candidate_stream`).
* **Agreement with 024** (`stream_ofPolynomial`, `boundary_ofPolynomial`): for a
  polynomial profile `p`, with `g_j = j! · p_j`, both are exactly
  `Heat.stream basis p` and `Heat.boundary basis p`.
* **Majorant transfer** (`majorizes_stream`): a certified profile bound
  `|g_j| ≤ M · ρ^(−j)` for **every** `j` (`ProfileBound g M ρ`, exact `M ≥ 0`,
  `ρ > 0`) gives `Majorizes basis (stream basis g) (heatMajorant M ρ _ _)`, the
  majorant `M` with radii `[ρ², ρ]`. The factorials are dropped
  (`n!·k! ≥ 1`), so the majorant is conservative.
* **Certificate** (`certificate`, `truncationBound`): hence a `TailCertificate`
  on every box strictly inside `[ρ², ρ]`, and the uniform truncation bound
  `tailBound (heatMajorant M ρ _ _) box N` at every window `N`.

A profile bound on raw EGF coefficients says the profile is entire of
exponential type at most `1/ρ`; a profile with a finite radius of convergence
has no such bound (see the hostile tests). Nothing here discovers `M` or `ρ`,
and no statement is made about the real field solving the PDE beyond what
`Streams.Tail` proves about convergence. -/
namespace Gimle.Asgard.Streams.AnalyticHeat

open Gimle.Asgard.Streams

/-! ## The profile, in either basis -/

/-- The profile with raw EGF coefficients `g` as a one-axis formal stream in
`basis`: OGF raw coefficients `g_j / j!`, EGF raw coefficients `g_j`. -/
noncomputable def profile (basis : Basis) (g : ℕ → ℚ) : Stream 1 :=
  encode basis fun α => g (α 0) / ((α 0).factorial : ℚ)

/-- The raw EGF coefficients `g_j = j! · [x^j] p` of a one-axis stream `p`
stored in `basis`. -/
noncomputable def coeffs (basis : Basis) (p : Stream 1) : ℕ → ℚ :=
  fun j => ((j.factorial : ℚ)) * decode basis p (Finsupp.single 0 j)

private theorem factorial_one (α : Index 1) : factorial α = ((α 0).factorial : ℚ) := by
  simp [factorial]

private theorem single_zero_eq (α : Index 1) : Finsupp.single 0 (α 0) = α := by
  refine Finsupp.ext fun i => ?_
  fin_cases i
  simp

theorem profile_egf_apply (g : ℕ → ℚ) (α : Index 1) : profile .egf g α = g (α 0) := by
  change factorial α * (g (α 0) / ((α 0).factorial : ℚ)) = g (α 0)
  rw [factorial_one]
  field_simp

theorem profile_ogf_apply (g : ℕ → ℚ) (α : Index 1) :
    profile .ogf g α = g (α 0) / ((α 0).factorial : ℚ) := rfl

@[simp] theorem coeffs_profile (basis : Basis) (g : ℕ → ℚ) :
    coeffs basis (profile basis g) = g := by
  funext j
  simp only [coeffs, profile, decode_encode, Finsupp.single_eq_same]
  field_simp

@[simp] theorem profile_coeffs (basis : Basis) (p : Stream 1) :
    profile basis (coeffs basis p) = p := by
  have : (fun α : Index 1 => coeffs basis p (α 0) / ((α 0).factorial : ℚ)) = decode basis p := by
    funext α
    simp only [coeffs, single_zero_eq]
    field_simp
  rw [profile, this, encode_decode]

/-! ## The heat stream on axes `[t, x]` -/

/-- Decoded (OGF) coefficients of the heat solution: `g_(k+2n) / (n!·k!)` at
multi-index `(n, k)` of `[t, x]`. -/
def series (g : ℕ → ℚ) : Stream 2 := fun α => g (α 1 + 2 * α 0) / factorial α

/-- The heat stream of the profile `g`, in `basis`. -/
noncomputable def stream (basis : Basis) (g : ℕ → ℚ) : Stream 2 := encode basis (series g)

/-- The decoded profile on the `t = 0` slice, zero at positive `t`-degree. -/
def boundarySeries (g : ℕ → ℚ) : Stream 2 :=
  fun α => if α 0 = 0 then g (α 1) / ((α 1).factorial : ℚ) else 0

/-- The whole profile as the circuit's boundary input on `[t, x]`, in `basis`. -/
noncomputable def boundary (basis : Basis) (g : ℕ → ℚ) : Stream 2 :=
  encode basis (boundarySeries g)

private theorem factorial_two (α : Index 2) :
    factorial α = ((α 0).factorial : ℚ) * ((α 1).factorial : ℚ) := by
  simp [factorial, Fin.prod_univ_two]

@[simp] theorem decode_stream (basis : Basis) (g : ℕ → ℚ) :
    decode basis (stream basis g) = series g :=
  decode_encode basis _

@[simp] theorem decode_boundary (basis : Basis) (g : ℕ → ℚ) :
    decode basis (boundary basis g) = boundarySeries g :=
  decode_encode basis _

/-- **EGF coefficients:** `u_(n,k) = g_(k+2n)`. -/
theorem stream_egf_apply (g : ℕ → ℚ) (α : Index 2) : stream .egf g α = g (α 1 + 2 * α 0) := by
  change factorial α * (g (α 1 + 2 * α 0) / factorial α) = _
  field_simp [factorial_ne_zero]

/-- **OGF coefficients:** `u_(n,k) = g_(k+2n) / (n!·k!)`. -/
theorem stream_ogf_apply (g : ℕ → ℚ) (α : Index 2) :
    stream .ogf g α = g (α 1 + 2 * α 0) / (((α 0).factorial : ℚ) * ((α 1).factorial : ℚ)) := by
  change g (α 1 + 2 * α 0) / factorial α = _
  rw [factorial_two]

theorem boundary_egf_apply (g : ℕ → ℚ) (α : Index 2) :
    boundary .egf g α = if α 0 = 0 then g (α 1) else 0 := by
  change factorial α * boundarySeries g α = _
  rw [factorial_two, boundarySeries]
  split_ifs with h
  · rw [h, Nat.factorial_zero, Nat.cast_one, one_mul]
    field_simp
  · simp

theorem boundary_ogf_apply (g : ℕ → ℚ) (α : Index 2) :
    boundary .ogf g α = if α 0 = 0 then g (α 1) / ((α 1).factorial : ℚ) else 0 := rfl

/-- The boundary is the profile placed on the `t = 0` slice: at `t`-degree `0`
its decoded coefficients are the profile's, elsewhere zero. -/
theorem decode_boundary_apply (basis : Basis) (g : ℕ → ℚ) (α : Index 2) :
    decode basis (boundary basis g) α =
      if α 0 = 0 then decode basis (profile basis g) (Finsupp.single 0 (α 1)) else 0 := by
  simp [boundarySeries, profile]

/-! ## The PDE and the circuit -/

private theorem egf_stream_pde (g : ℕ → ℚ) :
    derivative .egf 0 (stream .egf g) =
      derivative .egf 1 (derivative .egf 1 (stream .egf g)) := by
  funext n
  simp only [derivative, stream_egf_apply, Finsupp.update_apply]
  simp only [Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False by decide,
    show ((0 : Fin 2) = 1) = False by decide, if_false]
  congr 1
  ring

private theorem series_pde (g : ℕ → ℚ) :
    derivative .ogf 0 (series g) = derivative .ogf 1 (derivative .ogf 1 (series g)) := by
  have h := egf_stream_pde g
  simp only [stream, derivative_encode] at h
  exact encode_injective .egf h

/-- The formal heat equation `D_t u = D_x² u`, in either basis. -/
theorem stream_pde (basis : Basis) (g : ℕ → ℚ) :
    derivative basis 0 (stream basis g) =
      derivative basis 1 (derivative basis 1 (stream basis g)) := by
  simp only [stream, derivative_encode, series_pde]

private theorem series_slice (g : ℕ → ℚ) (n : Index 2) (zero : n 0 = 0) :
    series g n = boundarySeries g n := by
  simp only [series, boundarySeries, zero, factorial_two, if_true, mul_zero, add_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul]

/-- On the `t = 0` slice the heat stream is the boundary profile. -/
theorem stream_slice (basis : Basis) (g : ℕ → ℚ) (n : Index 2) (zero : n 0 = 0) :
    stream basis g n = boundary basis g n := by
  cases basis with
  | ogf => exact series_slice g n zero
  | egf =>
      change factorial n * series g n = factorial n * boundarySeries g n
      rw [series_slice g n zero]

/-- **Circuit relation.** The original derivative/integration heat circuit of
`Streams.Heat` returns `[D_x² u, u]` on `[u, boundary basis g, unused]`: the
analytic profile is the full boundary input, in either basis. -/
theorem circuit_stream (basis : Basis) (g : ℕ → ℚ) (unused : Stream 2) :
    (Heat.circuit basis).Rel ![stream basis g, boundary basis g, unused]
      ![derivative basis 1 (derivative basis 1 (stream basis g)), stream basis g] := by
  rw [Heat.circuit_rel_iff, (Heat.reconstructs_iff basis _ _).mpr
    ⟨stream_pde basis g, stream_slice basis g⟩]

/-- **Supplied candidate stream:** any stream the heat circuit reconstructs from
the analytic profile is the constructed heat stream. -/
theorem candidate_stream (basis : Basis) (g : ℕ → ℚ) (a unused v : Stream 2)
    (rel : (Heat.circuit basis).Rel ![a, boundary basis g, unused] ![v, a]) :
    a = stream basis g := by
  rw [Heat.circuit_rel_iff] at rel
  have reconstructed := congrFun rel 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at reconstructed
  obtain ⟨pde, slice⟩ := (Heat.reconstructs_iff basis a _).mp reconstructed.symm
  exact Heat.formal_unique basis a _ pde (stream_pde basis g)
    (fun n zero => by rw [slice n zero, stream_slice basis g n zero])

/-! ## Agreement with polynomial profiles (024) -/

/-- The raw EGF coefficients `g_j = j! · p_j` of a polynomial profile. -/
noncomputable def ofPolynomial (p : Heat.Profile) : ℕ → ℚ :=
  fun j => (j.factorial : ℚ) * p.coeff j

private theorem coeff_lift (p : Heat.Profile) (n : Index 2) :
    MvPolynomial.coeff n (Heat.lift p) = if n 0 = 0 then p.coeff (n 1) else 0 := by
  classical
  have expand : Heat.lift p =
      ∑ i ∈ p.support, MvPolynomial.monomial (Finsupp.single 1 i) (p.coeff i) := by
    conv_lhs => rw [Heat.lift, p.as_sum_support_C_mul_X_pow]
    simp only [map_sum, map_mul, _root_.Polynomial.aeval_C, _root_.Polynomial.aeval_X_pow,
      MvPolynomial.algebraMap_eq, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
      mul_one]
  rw [expand, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs with zero
  · have shape : ∀ i, (Finsupp.single (1 : Fin 2) i = n) ↔ (i = n 1) := by
      intro i
      constructor
      · rintro rfl; simp
      · rintro rfl
        ext j
        fin_cases j
        · simp [zero]
        · simp
    simp only [shape, Finset.sum_ite_eq', _root_.Polynomial.mem_support_iff]
    split_ifs with h
    · rfl
    · exact (not_not.mp h).symm
  · refine Finset.sum_eq_zero fun i _ => if_neg fun h => zero ?_
    rw [← h]
    simp

theorem boundary_ofPolynomial (basis : Basis) (p : Heat.Profile) :
    boundary basis (ofPolynomial p) = Heat.boundary basis p := by
  rw [Heat.boundary, ofPoly, boundary]
  congr 1
  funext n
  change boundarySeries (ofPolynomial p) n = MvPolynomial.coeff n (Heat.lift p)
  rw [coeff_lift, boundarySeries, ofPolynomial]
  split_ifs
  · field_simp
  · rfl

/-- **Agreement with 024:** for a polynomial profile the analytic heat stream is
`Heat.stream`. -/
theorem stream_ofPolynomial (basis : Basis) (p : Heat.Profile) :
    stream basis (ofPolynomial p) = Heat.stream basis p :=
  Heat.formal_unique basis _ _ (stream_pde basis _) (Heat.stream_pde basis p)
    (fun n zero => by
      rw [stream_slice basis _ n zero, boundary_ofPolynomial, Heat.stream_boundary basis p n zero])

/-! ## The majorant transfer -/

/-- A certified profile bound: `|g_j| ≤ M · ρ^(−j)` for **every** `j`, on the raw
EGF coefficients. -/
def ProfileBound (g : ℕ → ℚ) (M ρ : ℚ) : Prop :=
  ∀ j, |g j| ≤ M * (ρ ^ j)⁻¹

/-- The heat majorant `M` with radii `[ρ², ρ]` on `[t, x]`. -/
def heatMajorant (M ρ : ℚ) (hM : 0 ≤ M) (hρ : 0 < ρ) : Majorant 2 :=
  ⟨M, ![ρ ^ 2, ρ], hM, fun i => by fin_cases i <;> simp [hρ]⟩

@[simp] theorem heatMajorant_radius_zero (M ρ : ℚ) (hM : 0 ≤ M) (hρ : 0 < ρ) :
    (heatMajorant M ρ hM hρ).radius 0 = ρ ^ 2 := rfl

@[simp] theorem heatMajorant_radius_one (M ρ : ℚ) (hM : 0 ≤ M) (hρ : 0 < ρ) :
    (heatMajorant M ρ hM hρ).radius 1 = ρ := rfl

/-- A box is inside the heat majorant exactly when `r_t < ρ²` and `r_x < ρ`. -/
theorem inside_iff (M ρ : ℚ) (hM : 0 ≤ M) (hρ : 0 < ρ) (b : Box 2) :
    (∀ i, b.radius i < (heatMajorant M ρ hM hρ).radius i) ↔
      b.radius 0 < ρ ^ 2 ∧ b.radius 1 < ρ := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · exact h0
    · exact h1

/-- **Majorant transfer.** `|g_j| ≤ M · ρ^(−j)` for every `j` gives
`|g_(k+2n)| / (n!·k!) ≤ M · (ρ²)^(−n) · ρ^(−k)` for every decoded coefficient of
the heat stream, in either basis. -/
theorem majorizes_stream (basis : Basis) {g : ℕ → ℚ} {M ρ : ℚ} (hM : 0 ≤ M) (hρ : 0 < ρ)
    (bound : ProfileBound g M ρ) :
    Majorizes basis (stream basis g) (heatMajorant M ρ hM hρ) := by
  intro α
  rw [decode_stream]
  have fact : (1 : ℚ) ≤ factorial α := by
    rw [factorial_two]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
  have radii : M * ∏ i, ((heatMajorant M ρ hM hρ).radius i ^ α i)⁻¹ =
      M * (ρ ^ (α 1 + 2 * α 0))⁻¹ := by
    rw [Fin.prod_univ_two, heatMajorant_radius_zero, heatMajorant_radius_one, ← mul_inv,
      ← pow_mul, ← pow_add, add_comm, mul_comm 2]
  change |g (α 1 + 2 * α 0) / factorial α| ≤ M * _
  rw [radii, abs_div, abs_of_pos (a := factorial α) (by linarith)]
  exact (div_le_self (abs_nonneg _) fact).trans (bound _)

/-- **Certificate constructor.** A certified profile bound and a box strictly
inside `[ρ², ρ]` give a `TailCertificate` for the heat stream. -/
def certificate (basis : Basis) {g : ℕ → ℚ} {M ρ : ℚ} (hM : 0 ≤ M) (hρ : 0 < ρ)
    (bound : ProfileBound g M ρ) (box : Box 2)
    (inside : ∀ i, box.radius i < (heatMajorant M ρ hM hρ).radius i) :
    TailCertificate basis (stream basis g) :=
  ⟨heatMajorant M ρ hM hρ, box, inside, majorizes_stream basis hM hρ bound⟩

@[simp] theorem certificate_error (basis : Basis) {g : ℕ → ℚ} {M ρ : ℚ} (hM : 0 ≤ M)
    (hρ : 0 < ρ) (bound : ProfileBound g M ρ) (box : Box 2)
    (inside : ∀ i, box.radius i < (heatMajorant M ρ hM hρ).radius i) (N : Fin 2 → ℕ) :
    (certificate basis hM hρ bound box inside).error N = tailBound (heatMajorant M ρ hM hρ) box N :=
  rfl

/-- **Certified truncation of the heat stream.** Uniformly on the box, the
analytic field of the heat stream differs from its window `N` by at most
`tailBound (heatMajorant M ρ _ _) box N`. -/
theorem truncationBound (basis : Basis) {g : ℕ → ℚ} {M ρ : ℚ} (hM : 0 ≤ M) (hρ : 0 < ρ)
    (bound : ProfileBound g M ρ) (box : Box 2)
    (inside : ∀ i, box.radius i < (heatMajorant M ρ hM hρ).radius i) (N : Fin 2 → ℕ) :
    TruncationBound basis (stream basis g) box N (tailBound (heatMajorant M ρ hM hρ) box N) :=
  (certificate basis hM hρ bound box inside).truncationBound N

/-- The analytic field and window field do not depend on the basis. -/
theorem analyticField_stream (basis : Basis) (g : ℕ → ℚ) :
    analyticField basis (stream basis g) = analyticField .ogf (series g) :=
  analyticField_encode basis _

theorem windowField_stream (basis : Basis) (g : ℕ → ℚ) (N : Fin 2 → ℕ) :
    windowField basis N (stream basis g) = windowField .ogf N (series g) :=
  windowField_encode basis N _

/-! ## Exponential sums

The family `p(x) = Σᵢ cᵢ · e^(aᵢ x)` with exact rational `cᵢ, aᵢ` has raw EGF
coefficients `g_j = Σᵢ cᵢ · aᵢ^j`, a computable term. Its profile bound is
decided: `M = Σᵢ |cᵢ|` works for every `ρ > 0` with `|aᵢ| · ρ ≤ 1` for all `i`. -/

/-- The raw EGF coefficients of `Σᵢ cᵢ · e^(aᵢ x)`, from the pairs `(cᵢ, aᵢ)`. -/
def expSum (terms : List (ℚ × ℚ)) (j : ℕ) : ℚ :=
  (terms.map fun term => term.1 * term.2 ^ j).sum

/-- The bound `Σᵢ |cᵢ|`. -/
def expSumWeight (terms : List (ℚ × ℚ)) : ℚ :=
  (terms.map fun term => |term.1|).sum

/-- The decidable side condition: `|aᵢ| · ρ ≤ 1` for every term. -/
def expSumFits (terms : List (ℚ × ℚ)) (ρ : ℚ) : Bool :=
  terms.all fun term => decide (|term.2| * ρ ≤ 1)

theorem expSumWeight_nonneg (terms : List (ℚ × ℚ)) : 0 ≤ expSumWeight terms := by
  unfold expSumWeight
  induction terms with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (abs_nonneg _) ih

/-- One term: `|c · a^j| ≤ |c| · ρ^(−j)` when `|a| · ρ ≤ 1`. -/
theorem abs_term_le {c a ρ : ℚ} (hρ : 0 < ρ) (fits : |a| * ρ ≤ 1) (j : ℕ) :
    |c * a ^ j| ≤ |c| * (ρ ^ j)⁻¹ := by
  rw [abs_mul, abs_pow]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  have pos : 0 < ρ ^ j := pow_pos hρ j
  rw [← one_div, le_div_iff₀ pos, ← mul_pow]
  exact pow_le_one₀ (mul_nonneg (abs_nonneg a) hρ.le) fits

/-- **Exponential sums are certified profiles.** -/
theorem profileBound_expSum (terms : List (ℚ × ℚ)) {ρ : ℚ} (hρ : 0 < ρ)
    (fits : expSumFits terms ρ = true) :
    ProfileBound (expSum terms) (expSumWeight terms) ρ := by
  intro j
  unfold expSum expSumWeight
  induction terms with
  | nil => simp
  | cons head tail ih =>
    simp only [expSumFits, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at fits
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (abs_term_le hρ fits.1 j) (ih fits.2))

/-! ## Root claims -/

/-- **Truncation of every reconstruction.** Whatever the heat circuit
reconstructs from the boundary `boundary basis g` is the heat stream
(`candidate_stream`), so a certified profile bound, a box inside `[ρ², ρ]` and
a checked `tailBound ≤ ε` bound its truncation error at window `N` by `ε`. -/
theorem circuit_truncation (basis : Basis) {g : ℕ → ℚ} {M ρ ε : ℚ} (hM : 0 ≤ M)
    (hρ : 0 < ρ) (bound : ProfileBound g M ρ) (box : Box 2)
    (inside : ∀ i, box.radius i < (heatMajorant M ρ hM hρ).radius i) (N : Fin 2 → ℕ)
    (le : tailBound (heatMajorant M ρ hM hρ) box N ≤ ε) :
    ∀ a unused v : Stream 2,
      (Heat.circuit basis).Rel ![a, boundary basis g, unused] ![v, a] →
        TruncationBound basis a box N ε := by
  intro a unused v rel
  rw [candidate_stream basis g a unused v rel]
  exact (truncationBound basis hM hρ bound box inside N).mono le

/-- `circuit_truncation` for an exponential sum, with every side condition a
decidable check. -/
theorem expSum_truncation (basis : Basis) (terms : List (ℚ × ℚ)) {ρ ε : ℚ} (hρ : 0 < ρ)
    (fits : expSumFits terms ρ = true) (box : Box 2)
    (inside : box.radius 0 < ρ ^ 2 ∧ box.radius 1 < ρ) (N : Fin 2 → ℕ)
    (le : tailBound (heatMajorant (expSumWeight terms) ρ (expSumWeight_nonneg terms) hρ)
      box N ≤ ε) :
    ∀ a unused v : Stream 2,
      (Heat.circuit basis).Rel ![a, boundary basis (expSum terms), unused] ![v, a] →
        TruncationBound basis a box N ε :=
  circuit_truncation basis (expSumWeight_nonneg terms) hρ (profileBound_expSum terms hρ fits)
    box ((inside_iff _ _ _ _ box).mpr inside) N le

end Gimle.Asgard.Streams.AnalyticHeat
