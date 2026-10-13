import Gimle.Asgard.Streams.Causal
import Gimle.Asgard.Streams.Torus

/-! # Streams of trigonometric polynomials

A `TrigStream` is a formal power series in one variable `t` whose coefficients
are trigonometric polynomials on the torus: `Σ_n ω_n(x) tⁿ`, the shape of a
time series for a periodic field. The `t`-axis mirrors the stream derivative
and integral of `Streams.Core` in either basis (OGF scales by the degree, EGF
is a shift), and `trigAxis basis` packages them as a `Causal.Axis`, so the
formal Cauchy–Kowalevski lemma applies to any causal right-hand side here.
Coefficientwise operators are causal trivially, and `convolve` is the Cauchy
product in `t` of a bilinear operator on the coefficients, factorial-conjugated
in EGF as `Streams.product` is. -/
namespace Gimle.Asgard.Streams

open Torus

/-- A formal `t`-series with trigonometric-polynomial coefficients. -/
abbrev TrigStream := ℕ → TrigPoly

namespace TrigStream

/-- EGF raw coefficients multiply the ordinary ones by `n!`. -/
noncomputable def encode (basis : Basis) (a : TrigStream) : TrigStream :=
  match basis with
  | .ogf => a
  | .egf => fun n => (n.factorial : ℚ) • a n

noncomputable def decode (basis : Basis) (a : TrigStream) : TrigStream :=
  match basis with
  | .ogf => a
  | .egf => fun n => (n.factorial : ℚ)⁻¹ • a n

@[simp] theorem decode_encode (basis : Basis) (a : TrigStream) : decode basis (encode basis a) = a := by
  cases basis with
  | ogf => rfl
  | egf =>
      funext n
      simp [decode, encode, smul_smul, Nat.factorial_ne_zero]

@[simp] theorem encode_decode (basis : Basis) (a : TrigStream) : encode basis (decode basis a) = a := by
  cases basis with
  | ogf => rfl
  | egf =>
      funext n
      simp [decode, encode, smul_smul, Nat.factorial_ne_zero]

/-- Formal differentiation in `t`: EGF is a shift; OGF additionally scales by
the degree. -/
noncomputable def derivative (basis : Basis) (a : TrigStream) : TrigStream :=
  fun n => match basis with
  | .ogf => ((n : ℚ) + 1) • a (n + 1)
  | .egf => a (n + 1)

/-- Integration in `t` from a boundary: degree zero is the boundary's degree
zero, and nothing else of the boundary enters. -/
noncomputable def integral (basis : Basis) (a boundary : TrigStream) : TrigStream :=
  fun n => if n = 0 then boundary 0 else
    match basis with
    | .ogf => (n : ℚ)⁻¹ • a (n - 1)
    | .egf => a (n - 1)

@[simp] theorem integral_zero (basis : Basis) (a boundary : TrigStream) :
    integral basis a boundary 0 = boundary 0 := by simp [integral]

theorem integral_ogf_succ (a boundary : TrigStream) (n : ℕ) :
    integral .ogf a boundary (n + 1) = ((n : ℚ) + 1)⁻¹ • a n := by
  simp [integral]

theorem integral_egf_succ (a boundary : TrigStream) (n : ℕ) :
    integral .egf a boundary (n + 1) = a n := by
  simp [integral]

theorem derivative_integral (basis : Basis) (a boundary : TrigStream) :
    derivative basis (integral basis a boundary) = a := by
  funext n
  cases basis with
  | ogf =>
      have nonzero : (n : ℚ) + 1 ≠ 0 := by positivity
      simp [derivative, integral_ogf_succ, smul_smul, nonzero]
  | egf => simp [derivative, integral_egf_succ]

theorem integral_derivative (basis : Basis) (a : TrigStream) :
    integral basis (derivative basis a) a = a := by
  funext n
  cases n with
  | zero => simp
  | succ k =>
      cases basis with
      | ogf =>
          have nonzero : (k : ℚ) + 1 ≠ 0 := by positivity
          simp [derivative, integral_ogf_succ, smul_smul, nonzero]
      | egf => simp [derivative, integral_egf_succ]

/-! ## Agreement below a degree -/

/-- `a` and `b` have the same coefficient at every degree at most `k`. -/
def AgreeBelow (k : ℕ) (a b : TrigStream) : Prop := ∀ n, n ≤ k → a n = b n

theorem AgreeBelow.refl (k : ℕ) (a : TrigStream) : AgreeBelow k a a := fun _ _ => rfl

theorem AgreeBelow.symm {k : ℕ} {a b : TrigStream} (h : AgreeBelow k a b) : AgreeBelow k b a :=
  fun n hn => (h n hn).symm

theorem AgreeBelow.trans {k : ℕ} {a b c : TrigStream} (hab : AgreeBelow k a b)
    (hbc : AgreeBelow k b c) : AgreeBelow k a c :=
  fun n hn => (hab n hn).trans (hbc n hn)

theorem AgreeBelow.mono {k k' : ℕ} {a b : TrigStream} (le : k' ≤ k) (h : AgreeBelow k a b) :
    AgreeBelow k' a b :=
  fun n hn => h n (hn.trans le)

theorem AgreeBelow.eq {a b : TrigStream} (h : ∀ k, AgreeBelow k a b) : a = b :=
  funext fun n => h n n le_rfl

theorem agreeBelow_zero_iff (a b : TrigStream) : AgreeBelow 0 a b ↔ a 0 = b 0 :=
  ⟨fun h => h 0 le_rfl, fun h n hn => by rw [Nat.le_zero.mp hn]; exact h⟩

/-- Integration raises the degree it reads by one and reads the boundary only
at degree zero. -/
theorem integral_agree (basis : Basis) {k : ℕ} {a b c c' : TrigStream} (h : AgreeBelow k a b)
    (slice : c 0 = c' 0) :
    AgreeBelow (k + 1) (integral basis a c) (integral basis b c') := by
  intro n hn
  cases n with
  | zero => simp [slice]
  | succ m =>
      cases basis with
      | ogf => rw [integral_ogf_succ, integral_ogf_succ, h m (by omega)]
      | egf => rw [integral_egf_succ, integral_egf_succ, h m (by omega)]

/-- The `t`-axis of trigonometric streams, as an abstract causal axis. -/
noncomputable def trigAxis (basis : Basis) : Causal.Axis TrigStream where
  Agree := AgreeBelow
  agree_refl := AgreeBelow.refl
  agree_symm := AgreeBelow.symm
  agree_trans := AgreeBelow.trans
  agree_mono := AgreeBelow.mono
  agree_eq := AgreeBelow.eq
  derivative := derivative basis
  integral := integral basis
  derivative_integral := derivative_integral basis
  integral_derivative := integral_derivative basis
  integral_slice a b := (agreeBelow_zero_iff _ _).mpr (integral_zero basis a b)
  integral_agree h slice := integral_agree basis h ((agreeBelow_zero_iff _ _).mp slice)
  glue f := fun n => f n n
  glue_agree chain n m hm := (chain m n hm m le_rfl).symm

@[simp] theorem trigAxis_agree (basis : Basis) (k : ℕ) (a b : TrigStream) :
    (trigAxis basis).Agree k a b ↔ AgreeBelow k a b := Iff.rfl

@[simp] theorem trigAxis_derivative (basis : Basis) (a : TrigStream) :
    (trigAxis basis).derivative a = derivative basis a := rfl

@[simp] theorem trigAxis_integral (basis : Basis) (a b : TrigStream) :
    (trigAxis basis).integral a b = integral basis a b := rfl

/-! ## Causal primitives -/

/-- A coefficientwise operator is causal. -/
theorem map_causal {g : ℕ → TrigPoly → TrigPoly} {k : ℕ} {a b : TrigStream}
    (h : AgreeBelow k a b) : AgreeBelow k (fun n => g n (a n)) (fun n => g n (b n)) :=
  fun n hn => by simp only [h n hn]

theorem sub_causal {k : ℕ} {a a' b b' : TrigStream} (ha : AgreeBelow k a a')
    (hb : AgreeBelow k b b') : AgreeBelow k (a - b) (a' - b') :=
  fun n hn => by simp only [Pi.sub_apply, ha n hn, hb n hn]

theorem encode_agree (basis : Basis) {k : ℕ} {a b : TrigStream} (h : AgreeBelow k a b) :
    AgreeBelow k (encode basis a) (encode basis b) := by
  intro n hn
  cases basis <;> simp [encode, h n hn]

theorem decode_agree (basis : Basis) {k : ℕ} {a b : TrigStream} (h : AgreeBelow k a b) :
    AgreeBelow k (decode basis a) (decode basis b) := by
  intro n hn
  cases basis <;> simp [decode, h n hn]

/-- The Cauchy product in `t` of a bilinear operator `B` on the coefficients,
factorial-conjugated in EGF: the `t`-series of `B(a(t), b(t))`. -/
noncomputable def convolve (basis : Basis) (B : TrigPoly → TrigPoly → TrigPoly)
    (a b : TrigStream) : TrigStream :=
  encode basis fun n => ∑ m ∈ Finset.range (n + 1), B (decode basis a m) (decode basis b (n - m))

/-- Both factors of a Cauchy product read degrees at most that of the output. -/
theorem convolve_causal (basis : Basis) (B : TrigPoly → TrigPoly → TrigPoly) {k : ℕ}
    {a a' b b' : TrigStream} (ha : AgreeBelow k a a') (hb : AgreeBelow k b b') :
    AgreeBelow k (convolve basis B a b) (convolve basis B a' b') := by
  unfold convolve
  refine encode_agree basis fun n hn => ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [decode_agree basis ha m (by omega), decode_agree basis hb (n - m) (by omega)]

theorem convolve_ogf_apply (B : TrigPoly → TrigPoly → TrigPoly) (a b : TrigStream) (n : ℕ) :
    convolve .ogf B a b n = ∑ m ∈ Finset.range (n + 1), B (a m) (b (n - m)) := rfl

#print axioms derivative_integral
#print axioms integral_derivative
#print axioms convolve_causal
end TrigStream
end Gimle.Asgard.Streams
