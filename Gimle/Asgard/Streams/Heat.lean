import Gimle.Asgard.Streams.Realization
import Mathlib.Algebra.Polynomial.Derivation

/-! # Heat evolution of a finite polynomial profile

Axes are ordered `[t, x]` (`0` is time, `1` is space). For any rational
polynomial profile `p(x)` the heat polynomial

`u(t,x) = Σ_{k ≤ cutoff p} t^k/k! · (D_x^(2k) p)(x)`,  `cutoff p = natDegree p / 2`

is a finite sum: every later term has `D^(2k) p = 0`. Constants and the zero
profile have cutoff 0 and are fixed (`solution_of_natDegree_le_one`).

What is proved, and for which object:

* **Constructed family** (`solution p`, `stream basis p`, both bases): the
  stream satisfies the original derivative/integration heat circuit with the
  full initial profile (`circuit_solution`), and its evaluated real field
  satisfies `∂_t u = ∂_x² u` and `u(0,x) = p(x)` at every real `t, x`
  (`solution_pde`, `solution_initial`).
* **Supplied candidate stream** `a`: if the heat circuit relates
  `[a, boundary basis p, _]` to `[_, a]`, then `a = stream basis p`
  (`candidate_stream`). Uniqueness is proved from the coefficient recurrence
  among *all formal streams* (`formal_unique`), hence in particular within the
  finite bivariate polynomial class.
* **Supplied candidate polynomial field** `q`: if the real field of `q`
  satisfies the PDE and the initial profile everywhere, then `q = solution p`
  (`field_unique`). Nothing is claimed about arbitrary smooth real fields. -/
namespace Gimle.Asgard.Streams.Heat

/-- A rational spatial profile `p(x)`. -/
abbrev Profile := _root_.Polynomial ℚ

/-- The profile as a polynomial on axes `[t, x]`, constant in `t`. -/
noncomputable def lift (p : Profile) : Poly 2 :=
  _root_.Polynomial.aeval (MvPolynomial.X 1 : Poly 2) p

/-- Degree cutoff derived from `p`: `D^(2k) p = 0` for every `k > cutoff p`. -/
def cutoff (p : Profile) : ℕ := p.natDegree / 2

/-- The `k`-th heat term `t^k/k! · (D_x^(2k) p)(x)`. -/
noncomputable def term (p : Profile) (k : ℕ) : Poly 2 :=
  MvPolynomial.C (1 / (k.factorial : ℚ)) * MvPolynomial.X 0 ^ k *
    lift (_root_.Polynomial.derivative^[2 * k] p)

/-- The heat polynomial of `p`. -/
noncomputable def solution (p : Profile) : Poly 2 :=
  ∑ k ∈ Finset.range (cutoff p + 1), term p k

/-- The constructed stream in either basis. -/
noncomputable def stream (basis : Basis) (p : Profile) : Stream 2 := ofPoly basis (solution p)

/-- The full initial profile, as the circuit's boundary input. -/
noncomputable def boundary (basis : Basis) (p : Profile) : Stream 2 := ofPoly basis (lift p)

/-! ## Cutoff -/

theorem term_eq_zero (p : Profile) {k : ℕ} (after : cutoff p < k) : term p k = 0 := by
  have : p.natDegree < 2 * k := by unfold cutoff at after; omega
  simp [term, _root_.Polynomial.iterate_derivative_eq_zero this, lift]

/-- The cutoff only stops a sum whose later terms vanish. -/
theorem solution_eq_sum (p : Profile) {M : ℕ} (large : cutoff p ≤ M) :
    solution p = ∑ k ∈ Finset.range (M + 1), term p k := by
  unfold solution
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    exact term_eq_zero p (by omega)

theorem term_zero (p : Profile) : term p 0 = lift p := by
  simp [term]

/-- Affine, constant and zero profiles are stationary. -/
theorem solution_of_natDegree_le_one (p : Profile) (affine : p.natDegree ≤ 1) :
    solution p = lift p := by
  have : cutoff p = 0 := by unfold cutoff; omega
  simp [solution, this, term_zero]

/-! ## Polynomial identities -/

theorem pderiv_time_lift (q : Profile) : MvPolynomial.pderiv 0 (lift q) = 0 := by
  unfold lift
  rw [Derivation.comp_aeval_eq, MvPolynomial.pderiv_X_of_ne (by decide), smul_zero]

theorem pderiv_space_lift (q : Profile) :
    MvPolynomial.pderiv 1 (lift q) = lift (_root_.Polynomial.derivative q) := by
  unfold lift
  rw [Derivation.comp_aeval_eq, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one]

private theorem pderiv_space_mono (c : ℚ) (k : ℕ) (L : Poly 2) :
    MvPolynomial.pderiv 1 (MvPolynomial.C c * MvPolynomial.X 0 ^ k * L) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ k * MvPolynomial.pderiv 1 L := by
  simp [MvPolynomial.pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]

private theorem iterate_two (p : Profile) (k : ℕ) :
    _root_.Polynomial.derivative (_root_.Polynomial.derivative
      (_root_.Polynomial.derivative^[2 * k] p)) =
      _root_.Polynomial.derivative^[2 * k + 2] p := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']

/-- The shifted heat term `t^k/k! · (D^(2k+2) p)(x)`. -/
private noncomputable def shifted (p : Profile) (k : ℕ) : Poly 2 :=
  MvPolynomial.C (1 / (k.factorial : ℚ)) * MvPolynomial.X 0 ^ k *
    lift (_root_.Polynomial.derivative^[2 * k + 2] p)

private theorem pderiv_space_term (p : Profile) (k : ℕ) :
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (term p k)) = shifted p k := by
  rw [term, pderiv_space_mono, pderiv_space_mono, pderiv_space_lift, pderiv_space_lift,
    iterate_two, shifted]

private theorem pderiv_time_term_zero (p : Profile) : MvPolynomial.pderiv 0 (term p 0) = 0 := by
  rw [term_zero, pderiv_time_lift]

private theorem pderiv_time_term_succ (p : Profile) (k : ℕ) :
    MvPolynomial.pderiv 0 (term p (k + 1)) = shifted p k := by
  have scale : MvPolynomial.C (1 / ((k + 1).factorial : ℚ)) * ((k + 1 : ℕ) : Poly 2) =
      MvPolynomial.C (1 / (k.factorial : ℚ)) := by
    rw [← map_natCast (MvPolynomial.C (σ := Fin 2) (R := ℚ)), ← map_mul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  have shift : 2 * (k + 1) = 2 * k + 2 := by ring
  simp only [term, shifted, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X_self, pderiv_time_lift, shift, Nat.add_sub_cancel]
  rw [← scale]
  ring

/-- The heat polynomial satisfies `∂_t u = ∂_x² u` as a polynomial identity. -/
theorem pde_poly (p : Profile) :
    MvPolynomial.pderiv 0 (solution p) =
      MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (solution p)) := by
  unfold solution
  simp only [map_sum, pderiv_space_term]
  rw [Finset.sum_range_succ', Finset.sum_range_succ, pderiv_time_term_zero, add_zero]
  simp only [pderiv_time_term_succ]
  have last : shifted p (cutoff p) = 0 := by
    have : p.natDegree < 2 * cutoff p + 2 := by unfold cutoff; omega
    simp [shifted, _root_.Polynomial.iterate_derivative_eq_zero this, lift]
  rw [last, add_zero]

/-- On `t`-degree zero the heat polynomial has exactly the profile's coefficients. -/
theorem coeff_solution_slice (p : Profile) (n : Index 2) (zero : n 0 = 0) :
    MvPolynomial.coeff n (solution p) = MvPolynomial.coeff n (lift p) := by
  classical
  unfold solution
  rw [Finset.sum_range_succ', MvPolynomial.coeff_add, MvPolynomial.coeff_sum, term_zero]
  have later : ∀ k, MvPolynomial.coeff n (term p (k + 1)) = 0 := by
    intro k
    have : term p (k + 1) = MvPolynomial.X 0 * (MvPolynomial.C (1 / ((k + 1).factorial : ℚ)) *
        MvPolynomial.X 0 ^ k * lift (_root_.Polynomial.derivative^[2 * (k + 1)] p)) := by
      rw [term]; ring
    rw [this, MvPolynomial.coeff_X_mul', if_neg (by simpa using zero)]
  simp [later]

/-! ## Real fields -/

theorem field_lift (q : Profile) (x : Fin 2 → ℝ) :
    field (lift q) x = _root_.Polynomial.aeval (x 1) q := by
  unfold field lift
  rw [← _root_.Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]

/-- The explicit finite heat sum, evaluated. -/
theorem field_solution (p : Profile) (t x : ℝ) :
    field (solution p) ![t, x] = ∑ k ∈ Finset.range (cutoff p + 1),
      t ^ k / (k.factorial : ℝ) *
        _root_.Polynomial.aeval x (_root_.Polynomial.derivative^[2 * k] p) := by
  unfold solution
  rw [field, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← field, term, field_mul, field_mul, field_lift]
  simp [div_eq_inv_mul]

private theorem update_time (t x s : ℝ) : Function.update ![t, x] 0 s = ![s, x] := by
  funext j; fin_cases j <;> rfl

private theorem update_space (t x s : ℝ) : Function.update ![t, x] 1 s = ![t, s] := by
  funext j; fin_cases j <;> rfl

private theorem vec_eta (y : Fin 2 → ℝ) : y = ![y 0, y 1] := by
  funext j; fin_cases j <;> rfl

theorem hasDerivAt_time (q : Poly 2) (t x : ℝ) :
    HasDerivAt (fun s => field q ![s, x]) (field (MvPolynomial.pderiv 0 q) ![t, x]) t := by
  have h := hasDerivAt_field q 0 ![t, x]
  simp only [update_time] at h
  exact h

theorem hasDerivAt_space (q : Poly 2) (t x : ℝ) :
    HasDerivAt (fun y => field q ![t, y]) (field (MvPolynomial.pderiv 1 q) ![t, x]) x := by
  have h := hasDerivAt_field q 1 ![t, x]
  simp only [update_space] at h
  exact h

private theorem deriv_space_space (q : Poly 2) (t x : ℝ) :
    deriv (fun y => deriv (fun z => field q ![t, z]) y) x =
      field (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 q)) ![t, x] := by
  have inner : (fun y => deriv (fun z => field q ![t, z]) y) =
      fun y => field (MvPolynomial.pderiv 1 q) ![t, y] :=
    funext fun y => (hasDerivAt_space q t y).deriv
  rw [inner]
  exact (hasDerivAt_space _ t x).deriv

/-- The analytic heat equation for a polynomial field is the polynomial identity. -/
theorem field_pde_iff (q : Poly 2) :
    (∀ t x : ℝ, deriv (fun s => field q ![s, x]) t =
      deriv (fun y => deriv (fun z => field q ![t, z]) y) x) ↔
    MvPolynomial.pderiv 0 q = MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 q) := by
  simp only [deriv_space_space, fun t x => (hasDerivAt_time q t x).deriv]
  constructor
  · intro h
    apply field_injective
    intro y
    rw [vec_eta y]
    exact h (y 0) (y 1)
  · intro h t x
    rw [h]

/-- The analytic initial condition for a polynomial field is the coefficient
condition on the whole `t = 0` slice. -/
theorem field_initial_iff (q : Poly 2) (p : Profile) :
    (∀ x : ℝ, field q ![0, x] = _root_.Polynomial.aeval x p) ↔
    ∀ n : Index 2, n 0 = 0 → MvPolynomial.coeff n q = MvPolynomial.coeff n (lift p) := by
  rw [slice_iff]
  have slice : ∀ y : Fin 2 → ℝ, Function.update y 0 0 = ![0, y 1] := by
    intro y; funext j; fin_cases j <;> rfl
  simp only [slice, field_lift]
  constructor
  · intro h y; simpa using h (y 1)
  · intro h x; simpa using h ![0, x]

/-- **Constructed family:** `∂_t u = ∂_x² u` at every real `(t, x)`. -/
theorem solution_pde (p : Profile) (t x : ℝ) :
    deriv (fun s => field (solution p) ![s, x]) t =
      deriv (fun y => deriv (fun z => field (solution p) ![t, z]) y) x :=
  (field_pde_iff (solution p)).mpr (pde_poly p) t x

/-- **Constructed family:** `u(0, x) = p(x)` at every real `x`. -/
theorem solution_initial (p : Profile) (x : ℝ) :
    field (solution p) ![0, x] = _root_.Polynomial.aeval x p :=
  (field_initial_iff (solution p) p).mpr (coeff_solution_slice p) x

/-! ## The formal stream and the original heat circuit -/

theorem stream_pde (basis : Basis) (p : Profile) :
    derivative basis 0 (stream basis p) =
      derivative basis 1 (derivative basis 1 (stream basis p)) := by
  simp only [stream, derivative_ofPoly, pde_poly]

theorem stream_boundary (basis : Basis) (p : Profile) (n : Index 2) (zero : n 0 = 0) :
    stream basis p n = boundary basis p n := by
  cases basis with
  | ogf => rw [stream, boundary, ofPoly_ogf_apply, ofPoly_ogf_apply, coeff_solution_slice p n zero]
  | egf => rw [stream, boundary, ofPoly_egf_apply, ofPoly_egf_apply, coeff_solution_slice p n zero]

/-- `D_x² u` on axes `[t, x]`; inputs are `[u, boundary, unused]`. -/
def rhs (basis : Basis) : Expr basis 2 3 :=
  .unary (.derivative 1) (.unary (.derivative 1) (.input 0))

/-- Integrate the right-hand side along `t` with the full boundary profile. -/
def rebuilt (basis : Basis) : Expr basis 2 3 := .binary (.integral 0) (rhs basis) (.input 1)

/-- The heat circuit, returning `[D_x² u, I_t(D_x² u, boundary)]`. -/
def circuit (basis : Basis) : Streams.Circuit basis 2 3 2 :=
  (rhs basis).compile.pair (rebuilt basis).compile

theorem circuit_rel_iff (basis : Basis) (a b unused : Stream 2) (y : StreamPoint 2 2) :
    (circuit basis).Rel ![a, b, unused] y ↔
      y = ![derivative basis 1 (derivative basis 1 a),
        integral basis 0 (derivative basis 1 (derivative basis 1 a)) b] := by
  rw [Streams.Circuit.rel_iff]
  have defined : (circuit basis).Defined ![a, b, unused] := by
    simp [circuit, Streams.Circuit.pair_defined, Expr.compile_defined, rhs, rebuilt,
      Expr.Defined, Binary.Domain]
  simp only [defined, true_and]
  simp [circuit, Streams.Circuit.pair_value, Expr.compile_value, rhs, rebuilt, Expr.value,
    Unary.value, Binary.value]

/-- Reconstruction by integration is exactly the formal PDE plus the whole
initial slice. -/
theorem reconstructs_iff (basis : Basis) (a b : Stream 2) :
    integral basis 0 (derivative basis 1 (derivative basis 1 a)) b = a ↔
      derivative basis 0 a = derivative basis 1 (derivative basis 1 a) ∧
        ∀ n : Index 2, n 0 = 0 → a n = b n := by
  constructor
  · intro h
    refine ⟨?_, fun n zero => ?_⟩
    · conv_lhs => rw [← h]
      exact derivative_integral basis 0 _ _
    · rw [← h, integral_boundary _ _ _ _ _ zero]
  · rintro ⟨pde, slice⟩
    rw [← pde]
    calc integral basis 0 (derivative basis 0 a) b =
        integral basis 0 (derivative basis 0 a) a := by
          funext n
          by_cases zero : n 0 = 0
          · rw [integral_boundary _ _ _ _ _ zero, integral_boundary _ _ _ _ _ zero, slice n zero]
          · simp [integral, zero]
      _ = a := integral_derivative basis 0 a

/-- **Constructed family:** the original derivative/integration heat circuit
returns `[D_x² u, u]` on `[u, p, unused]`, for any `p` and either basis. -/
theorem circuit_solution (basis : Basis) (p : Profile) (unused : Stream 2) :
    (circuit basis).Rel ![stream basis p, boundary basis p, unused]
      ![derivative basis 1 (derivative basis 1 (stream basis p)), stream basis p] := by
  rw [circuit_rel_iff, (reconstructs_iff basis _ _).mpr
    ⟨stream_pde basis p, stream_boundary basis p⟩]

/-! ## Uniqueness from the coefficient recurrence -/

/-- Two formal streams with the same `t = 0` slice that both satisfy
`D_t u = D_x² u` are equal. The `t`-degree `k+1` coefficients are determined by
those at `t`-degree `k`. This holds among all formal streams, not only
polynomials; it says nothing about non-analytic real fields. -/
theorem formal_unique (basis : Basis) (a b : Stream 2)
    (ha : derivative basis 0 a = derivative basis 1 (derivative basis 1 a))
    (hb : derivative basis 0 b = derivative basis 1 (derivative basis 1 b))
    (slice : ∀ n : Index 2, n 0 = 0 → a n = b n) : a = b := by
  suffices ∀ k (n : Index 2), n 0 = k → a n = b n from funext fun n => this _ n rfl
  intro k
  induction k with
  | zero => exact slice
  | succ k ih =>
    intro n hn
    have same : ∀ m : Index 2, m 0 = k → derivative basis 1 (derivative basis 1 a) m =
        derivative basis 1 (derivative basis 1 b) m := by
      intro m hm
      have keep : ∀ (m : Index 2) (j : ℕ), (m.update 1 j) 0 = m 0 := by
        intro m j; simp [Finsupp.update_apply]
      cases basis <;> simp only [derivative] <;> rw [ih _ (by rw [keep, keep, hm])]
    have ea := congrFun (integral_derivative basis 0 a) n
    have eb := congrFun (integral_derivative basis 0 b) n
    rw [ha] at ea
    rw [hb] at eb
    have pos : n 0 ≠ 0 := by omega
    have prev : (n.update 0 (n 0 - 1)) 0 = k := by simp; omega
    rw [← ea, ← eb]
    cases basis <;> simp only [integral, pos, if_false] <;> rw [same _ prev]

/-- Uniqueness within the finite bivariate polynomial class. -/
theorem poly_unique (p : Profile) (q : Poly 2)
    (pde : MvPolynomial.pderiv 0 q = MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 q))
    (slice : ∀ n : Index 2, n 0 = 0 → MvPolynomial.coeff n q = MvPolynomial.coeff n (lift p)) :
    q = solution p := by
  apply ofPoly_injective .ogf
  apply formal_unique .ogf
  · simp only [derivative_ofPoly, pde]
  · simp only [derivative_ofPoly, pde_poly]
  · intro n zero
    rw [ofPoly_ogf_apply, ofPoly_ogf_apply, slice n zero, coeff_solution_slice p n zero]

/-- **Supplied polynomial field:** a rational polynomial whose real field
satisfies the heat equation and the initial profile everywhere is the
constructed solution. Not a claim about arbitrary smooth fields. -/
theorem field_unique (p : Profile) (q : Poly 2)
    (pde : ∀ t x : ℝ, deriv (fun s => field q ![s, x]) t =
      deriv (fun y => deriv (fun z => field q ![t, z]) y) x)
    (initial : ∀ x : ℝ, field q ![0, x] = _root_.Polynomial.aeval x p) :
    q = solution p :=
  poly_unique p q ((field_pde_iff q).mp pde) ((field_initial_iff q p).mp initial)

/-- **Supplied candidate stream:** any stream the original heat circuit
reconstructs from the polynomial profile is the constructed stream, so it is
realized by `solution p` and its field satisfies `solution_pde`/`solution_initial`. -/
theorem candidate_stream (basis : Basis) (p : Profile) (a unused v : Stream 2)
    (rel : (circuit basis).Rel ![a, boundary basis p, unused] ![v, a]) :
    a = stream basis p := by
  rw [circuit_rel_iff] at rel
  have reconstructed := congrFun rel 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at reconstructed
  obtain ⟨pde, slice⟩ := (reconstructs_iff basis a _).mp reconstructed.symm
  exact formal_unique basis a _ pde (stream_pde basis p)
    (fun n zero => by rw [slice n zero, stream_boundary basis p n zero])

theorem candidate_realizes (basis : Basis) (p : Profile) (a unused v : Stream 2)
    (rel : (circuit basis).Rel ![a, boundary basis p, unused] ![v, a]) :
    Realizes basis a (solution p) :=
  candidate_stream basis p a unused v rel

end Gimle.Asgard.Streams.Heat
