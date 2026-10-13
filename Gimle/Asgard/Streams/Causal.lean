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
convergence, and the series it builds may well diverge.

The lemma is stated once, for an abstract `Axis` on any carrier: a graded
agreement relation, a derivative and an integral along the axis with the
shift laws, and a way to glue a coherent sequence of approximants into one
element. `Stream d` with any of its axes is an instance (`streamAxis`), and
the statements below the instance keep their original form; a carrier whose
coefficients are not rationals but, say, trigonometric polynomials
(`Streams.TrigStream`) is another. -/
namespace Gimle.Asgard.Streams.Causal

/-! ## The abstract axis -/

/-- An axis of a carrier `S`: `Agree k a b` says `a` and `b` have the same
coefficients up to degree `k` along it; `derivative` and `integral` shift
along it, the integral reading its boundary only at degree zero
(`integral_slice`, `integral_agree`); `glue f` assembles one element whose
degree-`n` coefficients are those of `f n`, for a chain `f` in which later
members keep every coefficient an earlier one fixed. -/
structure Axis (S : Type*) where
  /-- Agreement of all coefficients of degree at most `k` along the axis. -/
  Agree : ℕ → S → S → Prop
  agree_refl : ∀ (k : ℕ) (a : S), Agree k a a
  agree_symm : ∀ {k : ℕ} {a b : S}, Agree k a b → Agree k b a
  agree_trans : ∀ {k : ℕ} {a b c : S}, Agree k a b → Agree k b c → Agree k a c
  agree_mono : ∀ {k k' : ℕ} {a b : S}, k' ≤ k → Agree k a b → Agree k' a b
  /-- Agreement at every degree is equality. -/
  agree_eq : ∀ {a b : S}, (∀ k, Agree k a b) → a = b
  derivative : S → S
  /-- `integral a boundary`: the antiderivative of `a` along the axis whose
  degree-zero coefficients are the boundary's. -/
  integral : S → S → S
  derivative_integral : ∀ (a b : S), derivative (integral a b) = a
  integral_derivative : ∀ (a : S), integral (derivative a) a = a
  /-- At degree zero the integral is the boundary. -/
  integral_slice : ∀ (a b : S), Agree 0 (integral a b) b
  /-- Integration raises the degree it reads by one, and reads the boundary
  only at degree zero. -/
  integral_agree : ∀ {k : ℕ} {a b c c' : S},
    Agree k a b → Agree 0 c c' → Agree (k + 1) (integral a c) (integral b c')
  glue : (ℕ → S) → S
  /-- The glued element agrees with `f n` up to degree `n`, for a chain whose
  later members agree with earlier ones up to the earlier degree. -/
  glue_agree : ∀ {f : ℕ → S}, (∀ n n', n ≤ n' → Agree n (f n) (f n')) →
    ∀ n, Agree n (f n) (glue f)

namespace Axis

variable {S : Type*} (X : Axis S)

/-- A right-hand side whose degree-`k` output reads only degree-`≤ k` input. -/
def IsCausal (F : S → S) : Prop :=
  ∀ k (a b : S), X.Agree k a b → X.Agree k (F a) (F b)

/-- On a chain the glued element is determined: anything agreeing with every
member at its own degree is `glue f`. -/
theorem glue_unique {f : ℕ → S} (chain : ∀ n n', n ≤ n' → X.Agree n (f n) (f n')) {g : S}
    (hg : ∀ n, X.Agree n (f n) g) : g = X.glue f :=
  X.agree_eq fun n => X.agree_trans (X.agree_symm (hg n)) (X.glue_agree chain n)

/-- The integral reads its boundary only at degree zero. -/
theorem integral_congr_slice (a : S) {b b' : S} (slice : X.Agree 0 b b') :
    X.integral a b = X.integral a b' := by
  refine X.agree_eq fun k => ?_
  cases k with
  | zero =>
      exact X.agree_trans (X.integral_slice a b)
        (X.agree_trans slice (X.agree_symm (X.integral_slice a b')))
  | succ k => exact X.integral_agree (X.agree_refl k a) slice

/-! ### Reconstruction by integration is the equation plus its slice -/

/-- `I (F a) b = a` says exactly `D a = F a` and `a = b` at degree zero. -/
theorem reconstructs_iff (F : S → S) (a b : S) :
    X.integral (F a) b = a ↔ X.derivative a = F a ∧ X.Agree 0 a b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← h]
      exact X.derivative_integral _ _
    · have := X.integral_slice (F a) b
      rwa [h] at this
  · rintro ⟨pde, slice⟩
    rw [← pde, X.integral_congr_slice _ (X.agree_symm slice), X.integral_derivative]

/-! ### Existence by Picard iteration along the axis -/

/-- The `n`-th Picard iterate: integrate the right-hand side of the previous
one from the boundary. Its coefficients are right up to degree `n`. -/
def approx (F : S → S) (boundary : S) : ℕ → S
  | 0 => boundary
  | n + 1 => X.integral (F (approx F boundary n)) boundary

@[simp] theorem approx_zero (F : S → S) (boundary : S) : X.approx F boundary 0 = boundary := rfl

@[simp] theorem approx_succ (F : S → S) (boundary : S) (n : ℕ) :
    X.approx F boundary (n + 1) = X.integral (F (X.approx F boundary n)) boundary := rfl

/-- The formal solution: the iterates glued, each read at its own degree. -/
def solution (F : S → S) (boundary : S) : S := X.glue (X.approx F boundary)

variable {X} {F : S → S} {boundary : S}

theorem approx_succ_agree (causal : X.IsCausal F) (n : ℕ) :
    X.Agree n (X.approx F boundary n) (X.approx F boundary (n + 1)) := by
  induction n with
  | zero => exact X.agree_symm (X.integral_slice _ _)
  | succ n ih => exact X.integral_agree (causal n _ _ ih) (X.agree_refl 0 boundary)

/-- Later iterates keep every coefficient an earlier one got right. -/
theorem approx_agree (causal : X.IsCausal F) {n n' : ℕ} (le : n ≤ n') :
    X.Agree n (X.approx F boundary n) (X.approx F boundary n') := by
  induction n', le using Nat.le_induction with
  | base => exact X.agree_refl _ _
  | succ n' le ih => exact X.agree_trans ih (X.agree_mono le (approx_succ_agree causal n'))

/-- The `n`-th iterate is the solution up to degree `n`. -/
theorem solution_agree (causal : X.IsCausal F) (n : ℕ) :
    X.Agree n (X.approx F boundary n) (X.solution F boundary) :=
  X.glue_agree (fun _ _ le => approx_agree causal le) n

/-- At degree zero the solution is the boundary. -/
theorem solution_slice (causal : X.IsCausal F) :
    X.Agree 0 (X.solution F boundary) boundary :=
  X.agree_symm (solution_agree causal 0)

/-- **Existence.** The constructed element is reconstructed by integrating its
own right-hand side from the boundary. -/
theorem solution_reconstructs (causal : X.IsCausal F) :
    X.integral (F (X.solution F boundary)) boundary = X.solution F boundary := by
  refine X.agree_eq fun k => ?_
  cases k with
  | zero => exact X.agree_trans (X.integral_slice _ _) (X.agree_symm (solution_slice causal))
  | succ n =>
      have step : X.Agree (n + 1) (X.approx F boundary (n + 1))
          (X.integral (F (X.solution F boundary)) boundary) :=
        X.integral_agree (causal n _ _ (solution_agree causal n)) (X.agree_refl 0 boundary)
      exact X.agree_trans (X.agree_symm step) (solution_agree causal (n + 1))

/-- The constructed element satisfies `D u = F u` on every coefficient. -/
theorem solution_pde (causal : X.IsCausal F) :
    X.derivative (X.solution F boundary) = F (X.solution F boundary) :=
  ((X.reconstructs_iff F _ _).mp (solution_reconstructs causal)).1

/-! ### Uniqueness by strong induction on the degree -/

/-- **Uniqueness.** Two formal solutions of `D u = F u` that agree at degree
zero are equal: the coefficients of degree `k + 1` are integrals of `F`'s
coefficients of degree `k`, which the causal `F` reads from degrees `≤ k`. -/
theorem formal_unique (causal : X.IsCausal F) (a b : S)
    (ha : X.derivative a = F a) (hb : X.derivative b = F b) (slice : X.Agree 0 a b) : a = b := by
  refine X.agree_eq fun k => ?_
  induction k with
  | zero => exact slice
  | succ k ih =>
      have step := X.integral_agree (causal k a b ih) slice
      rwa [← ha, ← hb, X.integral_derivative, X.integral_derivative] at step

/-- Every solution of the equation with the given slice is the constructed one. -/
theorem eq_solution (causal : X.IsCausal F) (a : S) (ha : X.derivative a = F a)
    (slice : X.Agree 0 a boundary) : a = X.solution F boundary :=
  formal_unique causal a _ ha (solution_pde causal)
    (X.agree_trans slice (X.agree_symm (solution_slice causal)))

/-- The solution reads only the boundary's zero slice: two boundaries that
agree there give the same element, although the iterates carry the rest of
the boundary along. -/
theorem solution_congr_slice (causal : X.IsCausal F) (boundary' : S)
    (slice : X.Agree 0 boundary boundary') :
    X.solution F boundary = X.solution F boundary' :=
  eq_solution causal _ (solution_pde causal) (X.agree_trans (solution_slice causal) slice)

end Axis

/-! ## Streams: every axis of `MvPowerSeries (Fin d) ℚ` -/

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

/-- Agreement at degree zero is agreement on the zero slice. -/
theorem agreeBelow_zero_iff {d : Nat} (axis : Fin d) (a b : Stream d) :
    AgreeBelow axis 0 a b ↔ ∀ m : Index d, m axis = 0 → a m = b m :=
  ⟨fun h m zero => h m zero.le, fun h m hm => h m (Nat.le_zero.mp hm)⟩

/-- A right-hand side whose degree-`k` output reads only degree-`≤ k` input. -/
def IsCausal {d : Nat} (axis : Fin d) (F : Stream d → Stream d) : Prop :=
  ∀ k (a b : Stream d), AgreeBelow axis k a b → AgreeBelow axis k (F a) (F b)

/-! ### The primitives are causal -/

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

/-- The axis `axis` of `Stream d` in the given basis: agreement below a degree,
the stream derivative and integral, and gluing by reading each coefficient
from the member of its own degree. -/
noncomputable def streamAxis {d : Nat} (basis : Basis) (axis : Fin d) : Axis (Stream d) where
  Agree := AgreeBelow axis
  agree_refl := AgreeBelow.refl axis
  agree_symm := AgreeBelow.symm
  agree_trans := AgreeBelow.trans
  agree_mono := AgreeBelow.mono
  agree_eq := AgreeBelow.eq
  derivative := derivative basis axis
  integral := integral basis axis
  derivative_integral := derivative_integral basis axis
  integral_derivative := integral_derivative basis axis
  integral_slice a b m hm := integral_boundary basis axis a b m (Nat.le_zero.mp hm)
  integral_agree h slice := integral_agree basis h ((agreeBelow_zero_iff axis _ _).mp slice)
  glue f := fun m => f (m axis) m
  glue_agree chain n m hm := (chain (m axis) n hm m le_rfl).symm

@[simp] theorem streamAxis_agree {d : Nat} (basis : Basis) (axis : Fin d) (k : ℕ)
    (a b : Stream d) : (streamAxis basis axis).Agree k a b ↔ AgreeBelow axis k a b := Iff.rfl

@[simp] theorem streamAxis_derivative {d : Nat} (basis : Basis) (axis : Fin d) (a : Stream d) :
    (streamAxis basis axis).derivative a = derivative basis axis a := rfl

@[simp] theorem streamAxis_integral {d : Nat} (basis : Basis) (axis : Fin d) (a b : Stream d) :
    (streamAxis basis axis).integral a b = integral basis axis a b := rfl

/-! ### Reconstruction by integration is the equation plus its slice -/

/-- `I_axis (F a) b = a` says exactly `D_axis a = F a` on every coefficient and
`a = b` on the zero slice. -/
theorem reconstructs_iff {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (a b : Stream d) :
    integral basis axis (F a) b = a ↔
      derivative basis axis a = F a ∧ ∀ m : Index d, m axis = 0 → a m = b m := by
  rw [← agreeBelow_zero_iff]
  exact (streamAxis basis axis).reconstructs_iff F a b

/-! ### Existence by Picard iteration along the axis -/

/-- The `n`-th Picard iterate: integrate the right-hand side of the previous
one from the boundary. Its coefficients are right up to degree `n`. -/
noncomputable def approx {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) : ℕ → Stream d :=
  (streamAxis basis axis).approx F boundary

@[simp] theorem approx_zero {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) : approx basis axis F boundary 0 = boundary := rfl

@[simp] theorem approx_succ {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) (n : ℕ) :
    approx basis axis F boundary (n + 1) =
      integral basis axis (F (approx basis axis F boundary n)) boundary := rfl

/-- The formal solution: coefficient `m` is read from the iterate of its own
degree, which never changes afterwards. -/
noncomputable def solution {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) : Stream d :=
  (streamAxis basis axis).solution F boundary

@[simp] theorem solution_apply {d : Nat} (basis : Basis) (axis : Fin d) (F : Stream d → Stream d)
    (boundary : Stream d) (m : Index d) :
    solution basis axis F boundary m = approx basis axis F boundary (m axis) m := rfl

variable {d : Nat} {basis : Basis} {axis : Fin d} {F : Stream d → Stream d} {boundary : Stream d}

theorem approx_succ_agree (causal : IsCausal axis F) (n : ℕ) :
    AgreeBelow axis n (approx basis axis F boundary n) (approx basis axis F boundary (n + 1)) :=
  Axis.approx_succ_agree (X := streamAxis basis axis) causal n

/-- Later iterates keep every coefficient an earlier one got right. -/
theorem approx_agree (causal : IsCausal axis F) {n n' : ℕ} (le : n ≤ n') :
    AgreeBelow axis n (approx basis axis F boundary n) (approx basis axis F boundary n') :=
  Axis.approx_agree (X := streamAxis basis axis) causal le

/-- The `n`-th iterate is the solution up to degree `n`. -/
theorem solution_agree (causal : IsCausal axis F) (n : ℕ) :
    AgreeBelow axis n (approx basis axis F boundary n) (solution basis axis F boundary) :=
  Axis.solution_agree (X := streamAxis basis axis) causal n

/-- On the zero slice the solution is the boundary. -/
theorem solution_slice (m : Index d) (zero : m axis = 0) :
    solution basis axis F boundary m = boundary m := by
  simp [solution_apply, zero]

/-- **Existence.** The constructed stream is reconstructed by integrating its
own right-hand side from the boundary. -/
theorem solution_reconstructs (causal : IsCausal axis F) :
    integral basis axis (F (solution basis axis F boundary)) boundary =
      solution basis axis F boundary :=
  Axis.solution_reconstructs (X := streamAxis basis axis) causal

/-- The constructed stream satisfies `D_axis u = F u` on every coefficient. -/
theorem solution_pde (causal : IsCausal axis F) :
    derivative basis axis (solution basis axis F boundary) = F (solution basis axis F boundary) :=
  Axis.solution_pde (X := streamAxis basis axis) causal

/-! ### Uniqueness by strong induction on the degree -/

/-- **Uniqueness.** Two formal solutions of `D_axis u = F u` with the same zero
slice are equal: the coefficients of degree `k + 1` are integrals of `F`'s
coefficients of degree `k`, which the causal `F` reads from degrees `≤ k`. -/
theorem formal_unique (causal : IsCausal axis F) (a b : Stream d)
    (ha : derivative basis axis a = F a) (hb : derivative basis axis b = F b)
    (slice : ∀ m : Index d, m axis = 0 → a m = b m) : a = b :=
  Axis.formal_unique (X := streamAxis basis axis) causal a b ha hb
    ((agreeBelow_zero_iff axis a b).mpr slice)

/-- Every solution of the equation with the given slice is the constructed one. -/
theorem eq_solution (causal : IsCausal axis F) (a : Stream d)
    (ha : derivative basis axis a = F a)
    (slice : ∀ m : Index d, m axis = 0 → a m = boundary m) :
    a = solution basis axis F boundary :=
  Axis.eq_solution (X := streamAxis basis axis) causal a ha
    ((agreeBelow_zero_iff axis a boundary).mpr slice)

/-- The solution reads only the boundary's zero slice: two boundaries that
agree there give the same stream, although the iterates carry the rest of
the boundary along. -/
theorem solution_congr_slice (causal : IsCausal axis F) (boundary' : Stream d)
    (slice : ∀ m : Index d, m axis = 0 → boundary m = boundary' m) :
    solution basis axis F boundary = solution basis axis F boundary' :=
  Axis.solution_congr_slice (X := streamAxis basis axis) causal boundary'
    ((agreeBelow_zero_iff axis boundary boundary').mpr slice)

#print axioms Axis.solution_reconstructs
#print axioms Axis.formal_unique
#print axioms solution_reconstructs
#print axioms formal_unique
#print axioms solution_congr_slice
end Gimle.Asgard.Streams.Causal
