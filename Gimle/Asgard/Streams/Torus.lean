import Gimle.Asgard.Streams.Core

/-! # Trigonometric polynomials on the torus

Exact coefficients for the two-dimensional periodic setting: a trigonometric
polynomial is a finitely supported `ℚ`-valued function on integer wavevectors,
the coefficient of `e^{i k·x}`. The carrier is all of `Wave →₀ ℚ`; two
predicates single out the subspaces the equation preserves. `MeanZero` is the
absence of a zero mode. `IsEven` is evenness in `k`: in the exponential
reading a function is real-valued exactly when `c_{−k} = conj c_k`, so with
rational coefficients the real-valued elements are the even ones, the cosine
subspace used by forseti-lean's Galerkin members. Sine modes need the
coefficient `∓i/2` and are not representable here at all, and a non-even
element stands for a complex-valued field; the equation is formally defined
for those too. The three operators the vorticity equation needs act exactly:

* `laplacian`, multiplication by `−|k|²`;
* `laplacianInv`, its inverse on mean-zero polynomials, zero on the zero mode;
* `transport P Q`, bilinear with the coupling `(p × q)/|p|²` on `p + q = k`.

The coupling is the Fourier symbol of `u·∇Q` for the velocity `u = ∇⊥ψ`,
`Δψ = P`, with `∇⊥ = (−∂_y, ∂_x)` so that `curl u = Δψ`: `ψ̂_p = −P_p/|p|²`,
`û_p = i p⊥ ψ̂_p`, `(∇Q)^_q = i q Q_q`, and `i² = −1` makes the product
rational. That derivation is on paper, as it must be — a single derivative
multiplies by `i k₁` and cannot be formed in this carrier — and
`transport_eq_jacobian` records what Lean does tie together: the coupling is
`−(p × q)` against `laplacianInv P`. All three operators preserve the two
subspaces (`transport` is mean zero outright, since `p × (−p) = 0`).

`cosineCoupling` restates, over `ℚ`, the ordered-pair coupling
`GalerkinNS.Family.coefficient` of forseti-lean, which this repository cannot
import; the identification of the two definitions is by inspection of the two
sources, and the one-line cast identity belongs in forseti-lean.
`transport_eq_cosine` then says that on even polynomials supported on `±H`
the exponential-basis transport at any nonzero mode is the cosine-basis
quadratic form, up to the change to cosine amplitudes `a = 2P`. Nothing here is
analytic: no function on the torus is ever formed. -/
namespace Gimle.Asgard.Streams.Torus

/-- An integer wavevector on the `2π`-periodic square. -/
abbrev Wave := ℤ × ℤ

/-- The planar cross product `p × q`. -/
def cross (p q : Wave) : ℤ := p.1 * q.2 - p.2 * q.1

/-- `|k|²`, the eigenvalue of `−Δ` on `e^{i k·x}`. -/
def lam (k : Wave) : ℤ := k.1 ^ 2 + k.2 ^ 2

@[simp] theorem cross_neg_left (p q : Wave) : cross (-p) q = -cross p q := by
  simp [cross]; ring

@[simp] theorem cross_neg_right (p q : Wave) : cross p (-q) = -cross p q := by
  simp [cross]; ring

@[simp] theorem cross_self (p : Wave) : cross p p = 0 := by
  simp [cross]; ring

@[simp] theorem cross_neg_self (p : Wave) : cross p (-p) = 0 := by
  simp [cross]; ring

@[simp] theorem cross_zero_left (q : Wave) : cross 0 q = 0 := by simp [cross]

@[simp] theorem lam_neg (k : Wave) : lam (-k) = lam k := by simp [lam]

@[simp] theorem lam_zero : lam 0 = 0 := by simp [lam]

theorem lam_pos {k : Wave} (hk : k ≠ 0) : 0 < lam k := by
  obtain ⟨k1, k2⟩ := k
  simp only [ne_eq, Prod.mk_eq_zero, not_and_or] at hk
  unfold lam
  rcases hk with h | h <;> positivity

theorem lam_ne_zero {k : Wave} (hk : k ≠ 0) : (lam k : ℚ) ≠ 0 := by
  exact_mod_cast (lam_pos hk).ne'

/-- A trigonometric polynomial in exponential coordinates: finitely many
rational coefficients, `P k` on `e^{i k·x}`. -/
abbrev TrigPoly := Wave →₀ ℚ

/-- No zero mode: the mean over the torus vanishes. -/
def MeanZero (P : TrigPoly) : Prop := P 0 = 0

/-- Coefficients even in `k`: with rational coefficients, the real-valued
(cosine) subspace. -/
def IsEven (P : TrigPoly) : Prop := ∀ k, P (-k) = P k

theorem meanZero_add {P Q : TrigPoly} (hP : MeanZero P) (hQ : MeanZero Q) : MeanZero (P + Q) := by
  unfold MeanZero at *
  simp [hP, hQ]

theorem meanZero_sub {P Q : TrigPoly} (hP : MeanZero P) (hQ : MeanZero Q) : MeanZero (P - Q) := by
  unfold MeanZero at *
  simp [hP, hQ]

theorem meanZero_smul (c : ℚ) {P : TrigPoly} (hP : MeanZero P) : MeanZero (c • P) := by
  unfold MeanZero at *
  simp [hP]

theorem meanZero_sum {ι : Type*} (s : Finset ι) {f : ι → TrigPoly}
    (h : ∀ i ∈ s, MeanZero (f i)) : MeanZero (∑ i ∈ s, f i) := by
  unfold MeanZero at *
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero h

theorem isEven_add {P Q : TrigPoly} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P + Q) := by
  intro k
  simp [hP k, hQ k]

theorem isEven_sub {P Q : TrigPoly} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P - Q) := by
  intro k
  simp [hP k, hQ k]

theorem isEven_smul (c : ℚ) {P : TrigPoly} (hP : IsEven P) : IsEven (c • P) := by
  intro k
  simp [hP k]

theorem isEven_sum {ι : Type*} (s : Finset ι) {f : ι → TrigPoly}
    (h : ∀ i ∈ s, IsEven (f i)) : IsEven (∑ i ∈ s, f i) := by
  intro k
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i hi => h i hi k

/-- `cos(k·x)` in exponential coordinates: `(e^{i k·x} + e^{−i k·x}) / 2`. -/
noncomputable def cosine (k : Wave) : TrigPoly :=
  Finsupp.single k (1 / 2) + Finsupp.single (-k) (1 / 2)

theorem isEven_cosine (k : Wave) : IsEven (cosine k) := by
  intro m
  simp only [cosine, Finsupp.add_apply, Finsupp.single_apply, neg_eq_iff_eq_neg, neg_neg]
  rw [add_comm]

theorem meanZero_cosine {k : Wave} (hk : k ≠ 0) : MeanZero (cosine k) := by
  unfold MeanZero
  simp [cosine, hk, Ne.symm hk]

/-! ## The Laplacian and its inverse -/

/-- `Δ`: multiplication of the coefficient at `k` by `−|k|²`. -/
noncomputable def laplacian (P : TrigPoly) : TrigPoly :=
  Finsupp.onFinset P.support (fun k => -(lam k : ℚ) * P k) fun k h => by
    rw [Finsupp.mem_support_iff]
    exact right_ne_zero_of_mul h

@[simp] theorem laplacian_apply (P : TrigPoly) (k : Wave) :
    laplacian P k = -(lam k : ℚ) * P k := Finsupp.onFinset_apply

/-- `Δ⁻¹` on mean-zero polynomials: division of the coefficient at `k ≠ 0` by
`−|k|²`, and zero on the zero mode. `NS.rhs` does not use it — its coupling
carries `Δ⁻¹` already — and `transport_eq_jacobian` is the tie. -/
noncomputable def laplacianInv (P : TrigPoly) : TrigPoly :=
  Finsupp.onFinset P.support (fun k => if k = 0 then 0 else -(P k / lam k)) fun k h => by
    rw [Finsupp.mem_support_iff]
    intro zero
    simp [zero] at h

@[simp] theorem laplacianInv_apply (P : TrigPoly) (k : Wave) :
    laplacianInv P k = if k = 0 then 0 else -(P k / lam k) := Finsupp.onFinset_apply

theorem laplacian_add (P Q : TrigPoly) : laplacian (P + Q) = laplacian P + laplacian Q := by
  ext k; simp; ring

theorem laplacian_zero : laplacian 0 = 0 := by ext k; simp

theorem laplacian_single (k : Wave) (a : ℚ) :
    laplacian (Finsupp.single k a) = Finsupp.single k (-(lam k : ℚ) * a) := by
  ext m
  simp only [laplacian_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem laplacian_laplacianInv {P : TrigPoly} (h : MeanZero P) :
    laplacian (laplacianInv P) = P := by
  ext k
  simp only [laplacian_apply, laplacianInv_apply]
  split_ifs with zero
  · subst zero; simpa [MeanZero] using h.symm
  · field_simp [lam_ne_zero zero]

theorem laplacianInv_laplacian {P : TrigPoly} (h : MeanZero P) :
    laplacianInv (laplacian P) = P := by
  ext k
  simp only [laplacian_apply, laplacianInv_apply]
  split_ifs with zero
  · subst zero; simpa [MeanZero] using h.symm
  · field_simp [lam_ne_zero zero]

theorem meanZero_laplacian (P : TrigPoly) : MeanZero (laplacian P) := by
  simp [MeanZero]

theorem meanZero_laplacianInv (P : TrigPoly) : MeanZero (laplacianInv P) := by
  simp [MeanZero]

theorem isEven_laplacian {P : TrigPoly} (h : IsEven P) : IsEven (laplacian P) := by
  intro k; simp [h k]

theorem isEven_laplacianInv {P : TrigPoly} (h : IsEven P) : IsEven (laplacianInv P) := by
  intro k; simp [h k, neg_eq_zero]

/-! ## Transport -/

/-- The coupling `(p × q)/|p|²`: the coefficient on `e^{i (p+q)·x}` of `u·∇Q`
contributed by `P_p Q_q`, for `u = ∇⊥ψ`, `Δψ = P`, `∇⊥ = (−∂_y, ∂_x)` (a
paper derivation; see the module header). At `p = 0` it is `0/0 = 0` by
Lean's division: a convention, since a nonzero mean has no periodic stream
function and the equation lives on `MeanZero`. -/
def coupling (p q : Wave) : ℚ := (cross p q : ℚ) / (lam p : ℚ)

@[simp] theorem coupling_neg_neg (p q : Wave) : coupling (-p) (-q) = coupling p q := by
  simp [coupling]

theorem coupling_neg_left (p q : Wave) : coupling (-p) q = -coupling p q := by
  simp [coupling, neg_div]

theorem coupling_neg_right (p q : Wave) : coupling p (-q) = -coupling p q := by
  simp [coupling, neg_div]

@[simp] theorem coupling_neg_self (p : Wave) : coupling p (-p) = 0 := by
  simp [coupling]

/-- The bilinear transport term as a linear map in each argument: on single
modes, `transport (e_p) (e_q) = coupling p q · e_{p+q}`. -/
noncomputable def transportₗ : TrigPoly →ₗ[ℚ] TrigPoly →ₗ[ℚ] TrigPoly :=
  Finsupp.lsum ℚ fun p => LinearMap.toSpanSingleton ℚ _
    (Finsupp.lsum ℚ fun q => LinearMap.toSpanSingleton ℚ _ (Finsupp.single (p + q) (coupling p q)))

/-- `transport P Q`: the bilinear form with the coupling `(p × q)/|p|²` on
`p + q = k`, the Fourier side of `u·∇Q` for `u = ∇⊥Δ⁻¹P`. -/
noncomputable def transport (P Q : TrigPoly) : TrigPoly := transportₗ P Q

theorem transport_eq_sum (P Q : TrigPoly) :
    transport P Q = P.sum fun p a => a • Q.sum fun q b => b • Finsupp.single (p + q) (coupling p q) := by
  simp only [transport, transportₗ, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.toSpanSingleton_apply]

theorem transport_add_left (P P' Q : TrigPoly) :
    transport (P + P') Q = transport P Q + transport P' Q := by
  simp [transport, map_add]

theorem transport_add_right (P Q Q' : TrigPoly) :
    transport P (Q + Q') = transport P Q + transport P Q' := by
  simp [transport, map_add]

theorem transport_zero_left (Q : TrigPoly) : transport 0 Q = 0 := by simp [transport]

theorem transport_zero_right (P : TrigPoly) : transport P 0 = 0 := by simp [transport]

/-- On single modes the transport is the coupling on the sum of the modes. -/
theorem transport_single_single (p q : Wave) (a b : ℚ) :
    transport (Finsupp.single p a) (Finsupp.single q b) =
      Finsupp.single (p + q) (coupling p q * a * b) := by
  rw [transport_eq_sum, Finsupp.sum_single_index, Finsupp.sum_single_index]
  · rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
    congr 1; ring
  · simp
  · simp

/-- The coefficient at `k`: a double sum over the supports with `p + q = k`. -/
theorem transport_apply (P Q : TrigPoly) (k : Wave) :
    transport P Q k = ∑ p ∈ P.support, ∑ q ∈ Q.support,
      if p + q = k then coupling p q * P p * Q q else 0 := by
  rw [transport_eq_sum, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- What Lean ties together: for mean-zero `P` the coupling is `−(p × q)`
against `Δ⁻¹P`, the symbol of the Jacobian `−Σ (p × q) ψ̂_p Q_q` with
`ψ = Δ⁻¹P`. -/
theorem transport_eq_jacobian {P : TrigPoly} (hP : MeanZero P) (Q : TrigPoly) (k : Wave) :
    transport P Q k = ∑ p ∈ P.support, ∑ q ∈ Q.support,
      if p + q = k then -(cross p q : ℚ) * laplacianInv P p * Q q else 0 := by
  rw [transport_apply]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q _ => ?_
  have p0 : p ≠ 0 := fun e => by
    rw [Finsupp.mem_support_iff] at hp
    exact hp (e ▸ hP)
  split_ifs
  · rw [laplacianInv_apply, if_neg p0, coupling]
    field_simp [lam_ne_zero p0]
  · rfl

/-- The transport has no zero mode: `p × (−p) = 0`. -/
theorem meanZero_transport (P Q : TrigPoly) : MeanZero (transport P Q) := by
  unfold MeanZero
  rw [transport_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  split_ifs with h
  · have : q = -p := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    subst this
    simp
  · rfl

/-- Even factors give an even transport: negate both summation indices. -/
theorem isEven_transport {P Q : TrigPoly} (hP : IsEven P) (hQ : IsEven Q) :
    IsEven (transport P Q) := by
  intro k
  rw [transport_apply, transport_apply]
  have memP : ∀ p, p ∈ P.support ↔ -p ∈ P.support := fun p => by
    simp [Finsupp.mem_support_iff, hP p]
  have memQ : ∀ q, q ∈ Q.support ↔ -q ∈ Q.support := fun q => by
    simp [Finsupp.mem_support_iff, hQ q]
  refine Finset.sum_nbij' (fun p => -p) (fun p => -p) (fun p hp => (memP p).mp hp)
    (fun p hp => (memP (-p)).mpr (by simpa using hp)) (fun _ _ => neg_neg _)
    (fun _ _ => neg_neg _) fun p _ => ?_
  refine Finset.sum_nbij' (fun q => -q) (fun q => -q) (fun q hq => (memQ q).mp hq)
    (fun q hq => (memQ (-q)).mpr (by simpa using hq)) (fun _ _ => neg_neg _)
    (fun _ _ => neg_neg _) fun q _ => ?_
  have cond : p + q = -k ↔ -p + -q = k := by
    rw [← neg_add, neg_eq_iff_eq_neg, eq_comm]
  simp only [cond, coupling_neg_neg, hP p, hQ q]

/-! ## Modes of bounded size -/

/-- `|k₁| + |k₂|`, the ℓ¹ size of a wavevector. -/
def size (k : Wave) : ℕ := k.1.natAbs + k.2.natAbs

theorem size_add_le (p q : Wave) : size (p + q) ≤ size p + size q := by
  simp only [size, Prod.fst_add, Prod.snd_add]
  have h1 := Int.natAbs_add_le p.1 q.1
  have h2 := Int.natAbs_add_le p.2 q.2
  omega

@[simp] theorem size_neg (k : Wave) : size (-k) = size k := by simp [size]

/-- Every mode of `P` has size at most `K`. -/
def SizeLE (K : ℕ) (P : TrigPoly) : Prop := ∀ k ∈ P.support, size k ≤ K

theorem SizeLE.mono {K K' : ℕ} (h : K ≤ K') {P : TrigPoly} (hP : SizeLE K P) : SizeLE K' P :=
  fun k hk => (hP k hk).trans h

theorem sizeLE_zero (K : ℕ) : SizeLE K (0 : TrigPoly) := fun k hk => by simp at hk

theorem sizeLE_add {K : ℕ} {P Q : TrigPoly} (hP : SizeLE K P) (hQ : SizeLE K Q) :
    SizeLE K (P + Q) := fun k hk => by
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h | h
  · exact hP k h
  · exact hQ k h

theorem sizeLE_neg {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) : SizeLE K (-P) := fun k hk =>
  hP k (by simpa using hk)

theorem sizeLE_sub {K : ℕ} {P Q : TrigPoly} (hP : SizeLE K P) (hQ : SizeLE K Q) :
    SizeLE K (P - Q) := by
  rw [sub_eq_add_neg]; exact sizeLE_add hP (sizeLE_neg hQ)

theorem sizeLE_smul {K : ℕ} (c : ℚ) {P : TrigPoly} (hP : SizeLE K P) : SizeLE K (c • P) :=
  fun k hk => hP k (Finsupp.support_smul hk)

theorem sizeLE_sum {ι : Type*} {K : ℕ} (s : Finset ι) {f : ι → TrigPoly}
    (h : ∀ i ∈ s, SizeLE K (f i)) : SizeLE K (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sizeLE_zero K
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact sizeLE_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sizeLE_laplacian {K : ℕ} {P : TrigPoly} (hP : SizeLE K P) : SizeLE K (laplacian P) :=
  fun k hk => hP k (by
    rw [Finsupp.mem_support_iff] at hk ⊢
    rw [laplacian_apply] at hk
    exact right_ne_zero_of_mul hk)

/-- The modes of a transport are sums of modes of the factors. -/
theorem sizeLE_transport {K K' : ℕ} {P Q : TrigPoly} (hP : SizeLE K P) (hQ : SizeLE K' Q) :
    SizeLE (K + K') (transport P Q) := by
  intro k hk
  rw [Finsupp.mem_support_iff, transport_apply] at hk
  obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  obtain ⟨q, hq, hq'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
  split_ifs at hq' with e
  · subst e
    exact (size_add_le p q).trans (add_le_add (hP p hp) (hQ q hq))
  · exact absurd rfl hq'

/-! ## The cosine-basis coupling of the Galerkin family -/

/-- `[p − q = ±k] − [p + q = ±k]`: how `2 sin(p·x) sin(q·x) = cos((p − q)·x) − cos((p + q)·x)`
lands on `cos(k·x)`. Named as in forseti-lean's `GalerkinNS/Family.lean`. -/
def S (p q k : Wave) : ℤ :=
  (if p - q = k ∨ p - q = -k then 1 else 0) - (if p + q = k ∨ p + q = -k then 1 else 0)

/-- The ordered-pair coupling `(p × q)/(2|p|²) · S(p, q, k)`: the coefficient
of `a_p a_q` in `a_k'` for a vorticity `Σ a_q cos(q·x)` over modes taken one
per `±` pair. A restatement over `ℚ` of forseti-lean's
`GalerkinNS.Family.coefficient`, which is over `ℝ` and cannot be imported
here; the cast identity between the two is one line in forseti-lean, not a
statement of this repository. -/
def cosineCoupling (p q k : Wave) : ℚ := (cross p q : ℚ) / (2 * lam p) * S p q k

/-- **Agreement with the cosine coupling.** For even polynomials supported on
`±H`, with `H` free of `0` and of `±` pairs, the exponential-basis transport
at any nonzero mode `k` is `−2 Σ_{p, q ∈ H} c(p, q, k) P_p Q_q`: on the cosine
amplitudes `a = 2P`, the quadratic form `Σ c a_p a_q` of the Galerkin family
is exactly `−transport` of the vorticity equation, at the modes `k ∈ H` the
member keeps and at the modes outside `H` it discards alike (at `k = 0` both
sides vanish, `meanZero_transport`). -/
theorem transport_eq_cosine (H : Finset Wave) (hz : (0 : Wave) ∉ H)
    (hneg : ∀ p ∈ H, -p ∉ H) {P Q : TrigPoly} (hP : IsEven P) (hQ : IsEven Q)
    (sP : ∀ p, P p ≠ 0 → p ∈ H ∨ -p ∈ H) (sQ : ∀ q, Q q ≠ 0 → q ∈ H ∨ -q ∈ H)
    {k : Wave} (hk : k ≠ 0) :
    transport P Q k = -2 * ∑ p ∈ H, ∑ q ∈ H, cosineCoupling p q k * P p * Q q := by
  classical
  set g : Wave → Wave → ℚ := fun p q => if p + q = k then coupling p q * P p * Q q else 0 with hg
  have inner_zero : ∀ p, P p = 0 → ∀ (s : Finset Wave), ∑ q ∈ s, g p q = 0 := by
    intro p hp s
    exact Finset.sum_eq_zero fun q _ => by simp [hg, hp]
  have outer_zero : ∀ p q, Q q = 0 → g p q = 0 := by
    intro p q hq
    simp [hg, hq]
  -- the double sum over the supports is the double sum over `H ∪ −H`
  let H₂ : Finset Wave := H ∪ H.image Neg.neg
  have subP : P.support ⊆ H₂ := fun p hp => by
    rw [Finsupp.mem_support_iff] at hp
    rcases sP p hp with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-p, h, neg_neg p⟩)
  have subQ : Q.support ⊆ H₂ := fun q hq => by
    rw [Finsupp.mem_support_iff] at hq
    rcases sQ q hq with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-q, h, neg_neg q⟩)
  have step1 : transport P Q k = ∑ p ∈ H₂, ∑ q ∈ H₂, g p q := by
    rw [transport_apply]
    rw [Finset.sum_subset subP fun p _ hp => inner_zero p (Finsupp.notMem_support_iff.mp hp) _]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Finset.sum_subset subQ fun q _ hq => outer_zero p q (Finsupp.notMem_support_iff.mp hq)
  have disj : Disjoint H (H.image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨p', mem, e⟩ := Finset.mem_image.mp hp'
    subst e
    exact hneg p' mem hp
  have negInj : ∀ x ∈ H, ∀ y ∈ H, -x = -y → x = y := fun _ _ _ _ h => neg_inj.mp h
  have split : ∀ F : Wave → ℚ, ∑ p ∈ H₂, F p = ∑ p ∈ H, (F p + F (-p)) := by
    intro F
    rw [Finset.sum_union disj, Finset.sum_image negInj, ← Finset.sum_add_distrib]
  rw [step1, split]
  simp_rw [split]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  -- termwise: the four signed placements against the cosine coupling
  have hp0 : p ≠ 0 := fun e => hz (e ▸ hp)
  have hq0 : q ≠ 0 := fun e => hz (e ▸ hq)
  have lam_ne : (lam p : ℚ) ≠ 0 := lam_ne_zero hp0
  simp only [hg, coupling_neg_left, coupling_neg_right, hP p, hQ q, cosineCoupling, S]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨k1, k2⟩ := k
  simp only [coupling]
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_sub,
    Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, ne_eq, not_and_or] at hp0 hq0 hk ⊢
  push_cast
  split_ifs <;> first | (exfalso; omega) | (field_simp; done) | (field_simp; ring)

#print axioms laplacian_laplacianInv
#print axioms laplacianInv_laplacian
#print axioms transport_single_single
#print axioms transport_eq_jacobian
#print axioms meanZero_transport
#print axioms isEven_transport
#print axioms transport_eq_cosine
#print axioms sizeLE_transport
end Gimle.Asgard.Streams.Torus
