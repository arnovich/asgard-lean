import Gimle.Asgard.Streams.TrigStream

/-! # The formal vorticity stream on the torus

The two-dimensional Navier–Stokes equations on the `2π`-periodic square, in
vorticity form with the velocity recovered from the stream function,

  `D_t ω = ν Δω − u·∇ω`,  `u = ∇⊥ψ = (−∂_y ψ, ∂_x ψ)`,  `Δψ = ω`,

as a formal `t`-series with trigonometric-polynomial coefficients. On the
Fourier side `Δ` is a multiplier and `u·∇ω` is the bilinear `transport` of
`Streams.Torus`, so the right-hand side at `t`-degree `n` is

  `ν Δ ω_n − Σ_{m ≤ n} transport ω_m ω_{n−m}`

(binomially weighted in EGF), which reads no higher degree than it writes.
`Causal` then gives, for every initial vorticity, exactly one formal solution:
`stream basis ν b`, with `stream_pde`, `stream_slice`, `formal_unique` and
`eq_stream` the instances of the generic lemma. The mean-zero and even
subspaces propagate from the initial coefficient to every coefficient
(`stream_meanZero`, `stream_isEven`): an even start, the cosine data that
stands for a real-valued field, gives an even series. `rhs_eq_family` is the
agreement with the Galerkin family's unforced field on cosine amplitudes.

`ν = 0` is the Euler equation. Nothing here concerns convergence: the series
is exact and unique whatever its radius, and that is all this module claims.
This module states the equation directly. `Streams.VorticityCircuit` assembles
its Fourier operators and time integration into a typed feedback circuit, and
proves that its relation has exactly this stream as output. -/
namespace Gimle.Asgard.Streams.NS

open Torus TrigStream Causal

/-- The right-hand side `ν Δω − u·∇ω`, coefficientwise in `t` for the viscous
term and a Cauchy product in `t` for the transport. -/
noncomputable def rhs (basis : Basis) (ν : ℚ) (ω : TrigStream) : TrigStream :=
  fun n => ν • laplacian (ω n) - convolve basis transport ω ω n

/-- The right-hand side reads no higher `t`-degree than it writes. -/
theorem rhs_causal (basis : Basis) (ν : ℚ) : (trigAxis basis).IsCausal (rhs basis ν) := by
  intro k a b h
  exact sub_causal (map_causal (g := fun _ P => ν • laplacian P) h)
    (convolve_causal basis transport h h)

/-- The formal vorticity stream from a boundary stream: its `t⁰` coefficient
is the initial vorticity, and nothing else of the boundary matters
(`stream_congr_slice`). -/
noncomputable def stream (basis : Basis) (ν : ℚ) (boundary : TrigStream) : TrigStream :=
  (trigAxis basis).solution (rhs basis ν) boundary

/-- The stream satisfies the equation on every coefficient. -/
theorem stream_pde (basis : Basis) (ν : ℚ) (boundary : TrigStream) :
    TrigStream.derivative basis (stream basis ν boundary) = rhs basis ν (stream basis ν boundary) :=
  Axis.solution_pde (rhs_causal basis ν)

/-- At `t⁰` the stream is the initial vorticity. -/
theorem stream_slice (basis : Basis) (ν : ℚ) (boundary : TrigStream) :
    stream basis ν boundary 0 = boundary 0 :=
  (TrigStream.agreeBelow_zero_iff _ _).mp (Axis.solution_slice (rhs_causal basis ν))

/-- Integrating the stream's own right-hand side from the boundary returns it. -/
theorem stream_reconstructs (basis : Basis) (ν : ℚ) (boundary : TrigStream) :
    TrigStream.integral basis (rhs basis ν (stream basis ν boundary)) boundary = stream basis ν boundary :=
  Axis.solution_reconstructs (rhs_causal basis ν)

/-- **Uniqueness** among all formal streams, for every initial vorticity. -/
theorem formal_unique (basis : Basis) (ν : ℚ) (a b : TrigStream)
    (ha : TrigStream.derivative basis a = rhs basis ν a) (hb : TrigStream.derivative basis b = rhs basis ν b)
    (slice : a 0 = b 0) : a = b :=
  Axis.formal_unique (rhs_causal basis ν) a b ha hb ((TrigStream.agreeBelow_zero_iff _ _).mpr slice)

/-- Every solution with the given initial vorticity is the constructed stream. -/
theorem eq_stream (basis : Basis) (ν : ℚ) (boundary a : TrigStream)
    (ha : TrigStream.derivative basis a = rhs basis ν a) (slice : a 0 = boundary 0) :
    a = stream basis ν boundary :=
  Axis.eq_solution (rhs_causal basis ν) a ha ((TrigStream.agreeBelow_zero_iff _ _).mpr slice)

/-- Only the boundary's `t⁰` coefficient enters the stream. -/
theorem stream_congr_slice (basis : Basis) (ν : ℚ) (boundary boundary' : TrigStream)
    (slice : boundary 0 = boundary' 0) :
    stream basis ν boundary = stream basis ν boundary' :=
  Axis.solution_congr_slice (rhs_causal basis ν) boundary' ((TrigStream.agreeBelow_zero_iff _ _).mpr slice)

/-- Reconstruction by integration is exactly the equation plus the slice. -/
theorem reconstructs_iff (basis : Basis) (ν : ℚ) (a b : TrigStream) :
    TrigStream.integral basis (rhs basis ν a) b = a ↔
      TrigStream.derivative basis a = rhs basis ν a ∧ a 0 = b 0 := by
  rw [← TrigStream.agreeBelow_zero_iff]
  exact (trigAxis basis).reconstructs_iff (rhs basis ν) a b

/-- The `t`-degree-`n` coefficient is read from the `n`-th Picard iterate. -/
theorem stream_apply (basis : Basis) (ν : ℚ) (boundary : TrigStream) (n : ℕ) :
    stream basis ν boundary n = (trigAxis basis).approx (rhs basis ν) boundary n n := rfl

/-- The OGF recursion: `ω_{n+1} = (n+1)⁻¹ (ν Δω_n − Σ_{m ≤ n} transport ω_m ω_{n−m})`. -/
theorem stream_succ_ogf (ν : ℚ) (b : TrigStream) (n : ℕ) :
    stream .ogf ν b (n + 1) = ((n : ℚ) + 1)⁻¹ • (ν • laplacian (stream .ogf ν b n) -
      ∑ m ∈ Finset.range (n + 1), transport (stream .ogf ν b m) (stream .ogf ν b (n - m))) := by
  have pde := congrFun (stream_pde .ogf ν b) n
  simp only [TrigStream.derivative, rhs, convolve_ogf_apply] at pde
  have ne : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [← pde, smul_smul, inv_mul_cancel₀ ne, one_smul]

/-! ## The invariant subspaces -/

/-- Every coefficient of the right-hand side is mean zero: `Δ` kills the zero
mode and the transport has none. -/
theorem meanZero_rhs (basis : Basis) (ν : ℚ) (ω : TrigStream) (n : ℕ) :
    MeanZero (rhs basis ν ω n) := by
  unfold rhs convolve
  refine meanZero_sub (meanZero_smul ν (meanZero_laplacian _)) ?_
  cases basis with
  | ogf => exact meanZero_sum _ fun m _ => meanZero_transport _ _
  | egf =>
      exact meanZero_smul _ (meanZero_sum _ fun m _ => meanZero_transport _ _)

/-- Even coefficients up to degree `n` give an even right-hand side at `n`. -/
theorem isEven_rhs (basis : Basis) (ν : ℚ) (ω : TrigStream) (n : ℕ)
    (h : ∀ m ≤ n, IsEven (ω m)) : IsEven (rhs basis ν ω n) := by
  unfold rhs convolve
  refine isEven_sub (isEven_smul ν (isEven_laplacian (h n le_rfl))) ?_
  have inner : ∀ m ∈ Finset.range (n + 1),
      IsEven (transport (TrigStream.decode basis ω m) (TrigStream.decode basis ω (n - m))) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : IsEven (TrigStream.decode basis ω m) := by
      cases basis with
      | ogf => exact h m (by omega)
      | egf => exact isEven_smul _ (h m (by omega))
    have hn' : IsEven (TrigStream.decode basis ω (n - m)) := by
      cases basis with
      | ogf => exact h (n - m) (by omega)
      | egf => exact isEven_smul _ (h (n - m) (by omega))
    exact isEven_transport hm' hn'
  cases basis with
  | ogf => exact isEven_sum _ inner
  | egf => exact isEven_smul _ (isEven_sum _ inner)

/-- Integration keeps a coefficientwise property from the boundary's `t⁰`
coefficient and the integrand's lower degrees. -/
theorem integral_prop (basis : Basis) (prop : TrigPoly → Prop)
    (smul : ∀ (c : ℚ) {P}, prop P → prop (c • P)) {a b : TrigStream} {n : ℕ}
    (hb : prop (b 0)) (ha : ∀ m < n, prop (a m)) : prop (TrigStream.integral basis a b n) := by
  cases n with
  | zero => simpa using hb
  | succ m =>
      cases basis with
      | ogf => rw [integral_ogf_succ]; exact smul _ (ha m (Nat.lt_succ_self m))
      | egf => rw [integral_egf_succ]; exact ha m (Nat.lt_succ_self m)

/-- The Picard iterates are mean zero wherever they are right. -/
theorem meanZero_approx (basis : Basis) (ν : ℚ) {boundary : TrigStream}
    (hb : MeanZero (boundary 0)) :
    ∀ n, ∀ m ≤ n, MeanZero ((trigAxis basis).approx (rhs basis ν) boundary n m) := by
  intro n
  induction n with
  | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm]
      simpa using hb
  | succ n _ =>
      intro m _
      rw [Axis.approx_succ, trigAxis_integral]
      exact integral_prop basis MeanZero (fun c _ h => meanZero_smul c h) hb
        fun k _ => meanZero_rhs basis ν _ k

/-- The Picard iterates are even wherever they are right. -/
theorem isEven_approx (basis : Basis) (ν : ℚ) {boundary : TrigStream}
    (hb : IsEven (boundary 0)) :
    ∀ n, ∀ m ≤ n, IsEven ((trigAxis basis).approx (rhs basis ν) boundary n m) := by
  intro n
  induction n with
  | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm]
      simpa using hb
  | succ n ih =>
      intro m hm
      rw [Axis.approx_succ, trigAxis_integral]
      exact integral_prop basis IsEven (fun c _ h => isEven_smul c h) hb
        fun k hk => isEven_rhs basis ν _ k fun j hj => ih j (by omega)

/-- A mean-zero start gives a mean-zero series. -/
theorem stream_meanZero (basis : Basis) (ν : ℚ) {boundary : TrigStream}
    (hb : MeanZero (boundary 0)) (n : ℕ) : MeanZero (stream basis ν boundary n) := by
  rw [stream_apply]
  exact meanZero_approx basis ν hb n n le_rfl

/-- An even start gives an even series. -/
theorem stream_isEven (basis : Basis) (ν : ℚ) {boundary : TrigStream}
    (hb : IsEven (boundary 0)) (n : ℕ) : IsEven (stream basis ν boundary n) := by
  rw [stream_apply]
  exact isEven_approx basis ν hb n n le_rfl

/-! ## The Galerkin family's field -/

/-- **Agreement with the Galerkin family.** For an even start `P` supported on
`±H` (`H` free of `0` and of `±` pairs), the `t⁰` right-hand side on the
cosine amplitudes `a = 2P` is the unforced field of forseti-lean's
`GalerkinNS.Family` at every nonzero mode:
`2 (rhs ω)₀(k) = −ν |k|² a_k + Σ_{p, q ∈ H} c(p, q, k) a_p a_q`. -/
theorem rhs_eq_family (ν : ℚ) (H : Finset Wave) (hz : (0 : Wave) ∉ H)
    (hneg : ∀ p ∈ H, -p ∉ H) {P : TrigPoly} (hP : IsEven P)
    (sP : ∀ p, P p ≠ 0 → p ∈ H ∨ -p ∈ H) {k : Wave} (hk : k ≠ 0) :
    2 * rhs .ogf ν (fun _ => P) 0 k =
      -ν * lam k * (2 * P k) + ∑ p ∈ H, ∑ q ∈ H, cosineCoupling p q k * (2 * P p) * (2 * P q) := by
  have h4 : ∀ p q, cosineCoupling p q k * (2 * P p) * (2 * P q) =
      4 * (cosineCoupling p q k * P p * P q) := by
    intros; ring
  simp only [rhs, convolve_ogf_apply, zero_add, Finset.sum_range_one, Finsupp.sub_apply,
    Finsupp.smul_apply, laplacian_apply, smul_eq_mul]
  rw [transport_eq_cosine H hz hneg hP hP sP sP hk]
  simp only [h4, ← Finset.mul_sum]
  ring

#print axioms rhs_causal
#print axioms rhs_eq_family
#print axioms stream_pde
#print axioms stream_succ_ogf
#print axioms formal_unique
#print axioms eq_stream
#print axioms stream_congr_slice
#print axioms stream_meanZero
#print axioms stream_isEven
end Gimle.Asgard.Streams.NS
