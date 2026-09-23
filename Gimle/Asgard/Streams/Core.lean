import Gimle.Asgard.Compile.Named
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! Exact formal rational coefficients on an arbitrary finite ordered product
of axes. No analytic function, numerical truncation or raw shift is implicit. -/
namespace Gimle.Asgard.Streams

abbrev Index (d : Nat) := Fin d →₀ ℕ
abbrev Stream (d : Nat) := MvPowerSeries (Fin d) ℚ
abbrev StreamPoint (d n : Nat) := Fin n → Stream d

inductive Basis where
  | ogf | egf
  deriving Repr, DecidableEq, BEq

def semanticVersion (basis : Basis) : String :=
  match basis with
  | .ogf => "asgard.formal-product-stream.ogf/v1"
  | .egf => "asgard.formal-product-stream.egf/v1"

/-- EGF raw coefficients multiply the ordinary coefficients by α₁!⋯α_d!. -/
def factorial {d : Nat} (a : Index d) : ℚ := ∏ i, (a i).factorial

theorem factorial_ne_zero {d : Nat} (a : Index d) : factorial a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (a i)

noncomputable def encode {d : Nat} (basis : Basis) (a : Stream d) : Stream d :=
  match basis with
  | .ogf => a
  | .egf => fun n => factorial n * a n

noncomputable def decode {d : Nat} (basis : Basis) (a : Stream d) : Stream d :=
  match basis with
  | .ogf => a
  | .egf => fun n => a n / factorial n

@[simp] theorem decode_encode {d : Nat} (basis : Basis) (a : Stream d) :
    decode basis (encode basis a) = a := by
  cases basis with
  | ogf => rfl
  | egf => funext n; simp [decode, encode, factorial_ne_zero]

@[simp] theorem encode_decode {d : Nat} (basis : Basis) (a : Stream d) :
    encode basis (decode basis a) = a := by
  cases basis with
  | ogf => rfl
  | egf =>
      funext n
      dsimp [decode, encode]
      field_simp [factorial_ne_zero]

noncomputable def constant {d : Nat} (basis : Basis) (q : ℚ) : Stream d :=
  encode basis (MvPowerSeries.C q)

noncomputable def axisVariable {d : Nat} (basis : Basis) (axis : Fin d) : Stream d :=
  encode basis (MvPowerSeries.X axis)

/-- Full componentwise Cauchy convolution, factorial-conjugated for EGF.
This is not coefficientwise multiplication or a flattened one-axis product. -/
noncomputable def product {d : Nat} (basis : Basis) (a b : Stream d) : Stream d :=
  encode basis (decode basis a * decode basis b)

@[simp] theorem decode_product {d : Nat} (basis : Basis) (a b : Stream d) :
    decode basis (product basis a b) = decode basis a * decode basis b := by
  simp [product]

/-- Formal differentiation: EGF is a shift; OGF additionally scales by degree. -/
noncomputable def derivative {d : Nat} (basis : Basis) (axis : Fin d) (a : Stream d) : Stream d :=
  fun n => match basis with
  | .ogf => (n axis + 1 : ℚ) * a (n.update axis (n axis + 1))
  | .egf => a (n.update axis (n axis + 1))

/-- The entire zero-axis slice is boundary data. Positive degrees on that axis
in the supplied boundary argument are explicitly projected away. -/
noncomputable def integral {d : Nat} (basis : Basis) (axis : Fin d)
    (a boundary : Stream d) : Stream d :=
  fun n => if n axis = 0 then boundary n else
    match basis with
    | .ogf => a (n.update axis (n axis - 1)) / (n axis : ℚ)
    | .egf => a (n.update axis (n axis - 1))

theorem integral_boundary {d : Nat} (basis : Basis) (axis : Fin d)
    (a boundary : Stream d) (n : Index d) (zero : n axis = 0) :
    integral basis axis a boundary n = boundary n := by simp [integral, zero]

theorem derivative_integral {d : Nat} (basis : Basis) (axis : Fin d)
    (a boundary : Stream d) : derivative basis axis (integral basis axis a boundary) = a := by
  funext n
  cases basis with
  | ogf =>
      have nonzero : (n axis : ℚ) + 1 ≠ 0 := by positivity
      simp [derivative, integral]
      field_simp
  | egf => simp [derivative, integral]

theorem integral_derivative {d : Nat} (basis : Basis) (axis : Fin d) (a : Stream d) :
    integral basis axis (derivative basis axis a) a = a := by
  funext n
  by_cases zero : n axis = 0
  · simp [integral, zero]
  · have pos : 0 < n axis := Nat.pos_of_ne_zero zero
    have cast_ne : (n axis : ℚ) ≠ 0 := by exact_mod_cast zero
    have cast : (↑(n axis - 1) : ℚ) + 1 = ↑(n axis) := by
      exact_mod_cast Nat.sub_add_cancel pos
    cases basis with
    | ogf =>
        simp [integral, derivative, zero, Nat.sub_add_cancel pos, cast, cast_ne]
    | egf => simp [integral, derivative, zero, Nat.sub_add_cancel pos]

/-- Only one formal variable is replaced; all other axes retain their identity. -/
noncomputable def substitution {d : Nat} (axis : Fin d) (inner : Stream d) :
    Fin d → Stream d := fun i => if i = axis then inner else MvPowerSeries.X i

/-- Conservative domain for arbitrary infinite outer series. Zero is the whole
multivariate constant, not the entire boundary slice on the selected axis. -/
def CanCompose {d : Nat} (basis : Basis) (inner : Stream d) : Prop :=
  MvPowerSeries.constantCoeff (decode basis inner) = 0

noncomputable def seriesCompose {d : Nat} (basis : Basis) (axis : Fin d)
    (outer inner : Stream d) : Stream d :=
  encode basis (MvPowerSeries.subst (substitution axis (decode basis inner)) (decode basis outer))

/-- Finite rectangular observation of an exact stream. No equality to a finite
numerical simulation or stability under differentiation is asserted. -/
noncomputable def truncate {d : Nat} (window : Fin d → Nat) (a : Stream d) : Stream d :=
  fun n => if ∀ i, n i < window i then a n else 0

theorem truncate_inside {d : Nat} (window : Fin d → Nat) (a : Stream d) (n : Index d)
    (inside : ∀ i, n i < window i) : truncate window a n = a n := by
  simp [truncate, inside]

#print axioms decode_encode
#print axioms encode_decode
#print axioms derivative_integral
#print axioms integral_derivative
end Gimle.Asgard.Streams
