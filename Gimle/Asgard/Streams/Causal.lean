import Gimle.Asgard.Streams.Core

/-! # Causal stream equations: existence and uniqueness degree by degree

A right-hand side `F` is *causal* along an axis when the coefficients of `F a`
up to degree `k` on that axis depend only on the coefficients of `a` up to
degree `k`. Derivatives along the other axes and Cauchy products are causal,
so every polynomial right-hand side in the unknown and its spatial
derivatives is. For a causal `F`, the equation `D_axis u = F u` with a
prescribed zero slice has exactly one formal solution: Picard iteration along
the axis constructs it, and strong induction on the degree shows there is no
other. This is the formal Cauchy–Kowalevski lemma; nothing here concerns
convergence, and the series it builds may well diverge. -/
namespace Gimle.Asgard.Streams.Causal

/-- `a` and `b` have the same coefficient at every index whose degree along
`axis` is at most `k`. -/
def AgreeBelow {d : Nat} (axis : Fin d) (k : ℕ) (a b : Stream d) : Prop :=
  ∀ m : Index d, m axis ≤ k → a m = b m

theorem AgreeBelow.refl {d : Nat} (axis : Fin d) (k : ℕ) (a : Stream d) :
    AgreeBelow axis k a a := fun _ _ => rfl

theorem AgreeBelow.symm {d : Nat} {axis : Fin d} {k : ℕ} {a b : Stream d}
    (h : AgreeBelow axis k a b) : AgreeBelow axis k b a := fun m hm => (h m hm).symm

theorem AgreeBelow.trans {d : Nat} {axis : Fin d} {k : ℕ} {a b c : Stream d}
    (hab : AgreeBelow axis k a b) (hbc : AgreeBelow axis k b c) : AgreeBelow axis k a c :=
  fun m hm => (hab m hm).trans (hbc m hm)

theorem AgreeBelow.mono {d : Nat} {axis : Fin d} {k k' : ℕ} {a b : Stream d}
    (le : k' ≤ k) (h : AgreeBelow axis k a b) : AgreeBelow axis k' a b :=
  fun m hm => h m (hm.trans le)

/-- Agreement at every degree is equality. -/
theorem AgreeBelow.eq {d : Nat} {axis : Fin d} {a b : Stream d}
    (h : ∀ k, AgreeBelow axis k a b) : a = b :=
  funext fun m => h (m axis) m le_rfl

/-- A right-hand side whose degree-`k` output reads only degree-`≤ k` input. -/
def IsCausal {d : Nat} (axis : Fin d) (F : Stream d → Stream d) : Prop :=
  ∀ k (a b : Stream d), AgreeBelow axis k a b → AgreeBelow axis k (F a) (F b)

/-! ## The primitives are causal -/

theorem add_causal {d : Nat} {axis : Fin d} {k : ℕ} {a a' b b' : Stream d}
    (ha : AgreeBelow axis k a a') (hb : AgreeBelow axis k b b') :
    AgreeBelow axis k (a + b) (a' + b') := by
  intro m hm
  change a m + b m = a' m + b' m
  rw [ha m hm, hb m hm]

theorem decode_agree {d : Nat} (basis : Basis) {axis : Fin d} {k : ℕ} {a b : Stream d}
    (h : AgreeBelow axis k a b) : AgreeBelow axis k (decode basis a) (decode basis b) := by
  intro m hm
  cases basis <;> simp [decode, h m hm]

theorem encode_agree {d : Nat} (basis : Basis) {axis : Fin d} {k : ℕ} {a b : Stream d}
    (h : AgreeBelow axis k a b) : AgreeBelow axis k (encode basis a) (encode basis b) := by
  intro m hm
  cases basis <;> simp [encode, h m hm]

/-- Both factors of a Cauchy product read degrees at most that of the output. -/
theorem mul_agree {d : Nat} {axis : Fin d} {k : ℕ} {a a' b b' : Stream d}
    (ha : AgreeBelow axis k a a') (hb : AgreeBelow axis k b b') :
    AgreeBelow axis k (a * b) (a' * b') := by
  intro m hm
  change MvPowerSeries.coeff m (a * b) = MvPowerSeries.coeff m (a' * b')
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  have split := congrArg (fun q : Index d => q axis) hp
  simp only [Finsupp.coe_add, Pi.add_apply] at split
  exact congrArg₂ (· * ·) (ha p.1 (by omega)) (hb p.2 (by omega))

theorem product_causal {d : Nat} (basis : Basis) {axis : Fin d} {k : ℕ} {a a' b b' : Stream d}
    (ha : AgreeBelow axis k a a') (hb : AgreeBelow axis k b b') :
    AgreeBelow axis k (product basis a b) (product basis a' b') :=
  encode_agree basis (mul_agree (decode_agree basis ha) (decode_agree basis hb))

/-- A derivative along another axis keeps the degree along `axis`. -/
theorem derivative_causal {d : Nat} (basis : Basis) {axis other : Fin d} (ne : other ≠ axis)
    {k : ℕ} {a b : Stream d} (h : AgreeBelow axis k a b) :
    AgreeBelow axis k (derivative basis other a) (derivative basis other b) := by
  intro m hm
  have keep : (m.update other (m other + 1)) axis = m axis := by
    simp [Finsupp.update_apply, ne.symm]
  cases basis <;> simp only [derivative] <;> rw [h _ (by rw [keep]; exact hm)]

/-- Integration along `axis` raises the degree it reads by one, and reads the
boundary only on the zero slice. -/
theorem integral_agree {d : Nat} (basis : Basis) {axis : Fin d} {k : ℕ} {a b c c' : Stream d}
    (h : AgreeBelow axis k a b) (slice : ∀ m : Index d, m axis = 0 → c m = c' m) :
    AgreeBelow axis (k + 1) (integral basis axis a c) (integral basis axis b c') := by
  intro m hm
  by_cases zero : m axis = 0
  · rw [integral_boundary _ _ _ _ _ zero, integral_boundary _ _ _ _ _ zero, slice m zero]
  · have prev : (m.update axis (m axis - 1)) axis = m axis - 1 := by simp
    cases basis <;> simp only [integral, zero, if_false] <;> rw [h _ (by rw [prev]; omega)]

/-! ## Reconstruction by integration is the equation plus its slice -/

/-- `I_axis (F a) b = a` says exactly `D_axis a = F a` on every coefficient and
`a = b` on the zero slice. -/
theorem reconstructs_iff {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (a b : Stream d) :
    integral basis axis (F a) b = a ↔
      derivative basis axis a = F a ∧ ∀ m : Index d, m axis = 0 → a m = b m := by
  constructor
  · intro h
    refine ⟨?_, fun m zero => ?_⟩
    · conv_lhs => rw [← h]
      exact derivative_integral basis axis _ _
    · rw [← h, integral_boundary _ _ _ _ _ zero]
  · rintro ⟨pde, slice⟩
    rw [← pde]
    calc integral basis axis (derivative basis axis a) b =
        integral basis axis (derivative basis axis a) a := by
          funext m
          by_cases zero : m axis = 0
          · rw [integral_boundary _ _ _ _ _ zero, integral_boundary _ _ _ _ _ zero, slice m zero]
          · simp [integral, zero]
      _ = a := integral_derivative basis axis a

/-! ## Existence by Picard iteration along the axis -/

/-- The `n`-th Picard iterate: integrate the right-hand side of the previous
one from the boundary. Its coefficients are right up to degree `n`. -/
noncomputable def approx {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) : ℕ → Stream d
  | 0 => boundary
  | n + 1 => integral basis axis (F (approx basis axis F boundary n)) boundary

/-- The formal solution: coefficient `m` is read from the iterate of its own
degree, which never changes afterwards. -/
noncomputable def solution {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) : Stream d :=
  fun m => approx basis axis F boundary (m axis) m

variable {d : Nat} {basis : Basis} {axis : Fin d} {F : Stream d → Stream d} {boundary : Stream d}

theorem approx_succ_agree (causal : IsCausal axis F) (n : ℕ) :
    AgreeBelow axis n (approx basis axis F boundary n) (approx basis axis F boundary (n + 1)) := by
  induction n with
  | zero =>
      intro m hm
      have zero : m axis = 0 := Nat.le_zero.mp hm
      simp only [approx]
      rw [integral_boundary _ _ _ _ _ zero]
  | succ n ih =>
      simp only [approx]
      exact integral_agree basis (causal n _ _ ih) fun _ _ => rfl

/-- Later iterates keep every coefficient an earlier one got right. -/
theorem approx_agree (causal : IsCausal axis F) {n n' : ℕ} (le : n ≤ n') :
    AgreeBelow axis n (approx basis axis F boundary n) (approx basis axis F boundary n') := by
  induction n', le using Nat.le_induction with
  | base => exact AgreeBelow.refl _ _ _
  | succ n' le ih => exact ih.trans ((approx_succ_agree causal n').mono le)

/-- The `n`-th iterate is the solution up to degree `n`. -/
theorem solution_agree (causal : IsCausal axis F) (n : ℕ) :
    AgreeBelow axis n (approx basis axis F boundary n) (solution basis axis F boundary) := by
  intro m hm
  exact ((approx_agree (boundary := boundary) causal hm) m le_rfl).symm

/-- On the zero slice the solution is the boundary. -/
theorem solution_slice (m : Index d) (zero : m axis = 0) :
    solution basis axis F boundary m = boundary m := by
  simp [solution, zero, approx]

/-- **Existence.** The constructed stream is reconstructed by integrating its
own right-hand side from the boundary. -/
theorem solution_reconstructs (causal : IsCausal axis F) :
    integral basis axis (F (solution basis axis F boundary)) boundary =
      solution basis axis F boundary := by
  funext m
  by_cases zero : m axis = 0
  · rw [integral_boundary _ _ _ _ _ zero, solution_slice m zero]
  · obtain ⟨n, hn⟩ : ∃ n, m axis = n + 1 := ⟨m axis - 1, by omega⟩
    have step : AgreeBelow axis (n + 1)
        (integral basis axis (F (approx basis axis F boundary n)) boundary)
        (integral basis axis (F (solution basis axis F boundary)) boundary) :=
      integral_agree basis (causal n _ _ (solution_agree causal n)) fun _ _ => rfl
    rw [← step m hn.le]
    simp only [solution, hn, approx]

/-- The constructed stream satisfies `D_axis u = F u` on every coefficient. -/
theorem solution_pde (causal : IsCausal axis F) :
    derivative basis axis (solution basis axis F boundary) = F (solution basis axis F boundary) :=
  ((reconstructs_iff basis axis F _ _).mp (solution_reconstructs causal)).1

/-! ## Uniqueness by strong induction on the degree -/

/-- **Uniqueness.** Two formal solutions of `D_axis u = F u` with the same zero
slice are equal: the coefficients of degree `k + 1` are integrals of `F`'s
coefficients of degree `k`, which the causal `F` reads from degrees `≤ k`. -/
theorem formal_unique (causal : IsCausal axis F) (a b : Stream d)
    (ha : derivative basis axis a = F a) (hb : derivative basis axis b = F b)
    (slice : ∀ m : Index d, m axis = 0 → a m = b m) : a = b := by
  refine AgreeBelow.eq (axis := axis) fun k => ?_
  induction k with
  | zero => exact fun m hm => slice m (Nat.le_zero.mp hm)
  | succ k ih =>
      have step := integral_agree basis (causal k a b ih) slice
      rwa [← ha, ← hb, integral_derivative, integral_derivative] at step

/-- Every solution of the equation with the given slice is the constructed one. -/
theorem eq_solution (causal : IsCausal axis F) (a : Stream d)
    (ha : derivative basis axis a = F a)
    (slice : ∀ m : Index d, m axis = 0 → a m = boundary m) :
    a = solution basis axis F boundary :=
  formal_unique causal a _ ha (solution_pde causal) fun m zero => by
    rw [slice m zero, solution_slice m zero]

/-- The solution reads only the boundary's zero slice: two boundaries that
agree there give the same stream, although the iterates carry the rest of
the boundary along. -/
theorem solution_congr_slice (causal : IsCausal axis F) (boundary' : Stream d)
    (slice : ∀ m : Index d, m axis = 0 → boundary m = boundary' m) :
    solution basis axis F boundary = solution basis axis F boundary' :=
  eq_solution causal _ (solution_pde causal) fun m zero => by
    rw [solution_slice m zero, slice m zero]

#print axioms solution_reconstructs
#print axioms formal_unique
#print axioms solution_congr_slice
end Gimle.Asgard.Streams.Causal
