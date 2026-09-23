import Gimle.Asgard.Compile.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! A separate pointwise partial-real circuit interpretation. Values outside a
domain are auxiliary totalized mathlib expressions, never admitted behavior. -/
namespace Gimle.Asgard.RealAtomics

def semanticVersion : String := "asgard.partial-real-atomics/v1"

inductive Unary where
  | neg | abs | sqrt | log | exp | sin | cos | sinh | cosh | tanh
  | naturalPower (exponent : Nat)
  | rationalPower (exponent : ℚ)
  deriving Repr, DecidableEq

inductive Binary where
  | add | mul | division | realPower
  deriving Repr, DecidableEq

def Unary.Domain : Unary → ℝ → Prop
  | .sqrt, x => 0 ≤ x
  | .log, x => 0 < x
  | .rationalPower _, x => 0 < x
  | _, _ => True

noncomputable def Unary.value : Unary → ℝ → ℝ
  | .neg, x => -x
  | .abs, x => |x|
  | .sqrt, x => Real.sqrt x
  | .log, x => Real.log x
  | .exp, x => Real.exp x
  | .sin, x => Real.sin x
  | .cos, x => Real.cos x
  | .sinh, x => Real.sinh x
  | .cosh, x => Real.cosh x
  | .tanh, x => Real.tanh x
  | .naturalPower n, x => x ^ n
  | .rationalPower q, x => Real.rpow x (q : ℝ)

def Binary.Domain : Binary → ℝ → ℝ → Prop
  | .division, _, y => y ≠ 0
  | .realPower, x, _ => 0 < x
  | _, _, _ => True

noncomputable def Binary.value : Binary → ℝ → ℝ → ℝ
  | .add, x, y => x + y
  | .mul, x, y => x * y
  | .division, x, y => x / y
  | .realPower, x, y => Real.rpow x y

/-- The ordered axis context is explicit and shared throughout a circuit.
A generator reads an axis, not an ordinary input wire. This is not a coefficient
stream and has no truncation-degree parameter. -/
inductive Circuit (axes : Nat) : Nat → Nat → Type where
  | embed {n m} (circuit : Gimle.Asgard.Circuit n m) : Circuit axes n m
  | unary (op : Unary) : Circuit axes 1 1
  | binary (op : Binary) : Circuit axes 2 1
  | generator (op : Unary) (axis : Fin axes) : Circuit axes 0 1
  | compose {n m o} (first : Circuit axes n m) (second : Circuit axes m o) : Circuit axes n o
  | parallel {n m d o} (left : Circuit axes n m) (right : Circuit axes d o) :
      Circuit axes (n + d) (m + o)

/-- Auxiliary value only. `Rel`, not this function alone, denotes admitted
behavior; every intermediate domain must also hold. -/
noncomputable def Circuit.value {k n m : Nat} (axes : Point k) : Circuit k n m → Point n → Point m
  | .embed c, x => c.run x
  | .unary op, x => ![op.value (x 0)]
  | .binary op, x => ![op.value (x 0) (x 1)]
  | .generator op axis, _ => ![op.value (axes axis)]
  | .compose c d, x => d.value axes (c.value axes x)
  | .parallel c d, x => pointAppend (c.value axes (pointLeft x)) (d.value axes (pointRight x))

def Circuit.Defined {k n m : Nat} (axes : Point k) : Circuit k n m → Point n → Prop
  | .embed _, _ => True
  | .unary op, x => op.Domain (x 0)
  | .binary op, x => op.Domain (x 0) (x 1)
  | .generator op axis, _ => op.Domain (axes axis)
  | .compose c d, x => c.Defined axes x ∧ d.Defined axes (c.value axes x)
  | .parallel c d, x => c.Defined axes (pointLeft x) ∧ d.Defined axes (pointRight x)

/-- Operational relation: composition must supply an admitted intermediate
valuation. Parallel branches both have to be defined, even if later discarded. -/
def Circuit.Rel {k n m : Nat} (axes : Point k) : Circuit k n m → Point n → Point m → Prop
  | .embed c, x, y => y = c.run x
  | .unary op, x, y => op.Domain (x 0) ∧ y = ![op.value (x 0)]
  | .binary op, x, y => op.Domain (x 0) (x 1) ∧ y = ![op.value (x 0) (x 1)]
  | .generator op axis, _, y => op.Domain (axes axis) ∧ y = ![op.value (axes axis)]
  | .compose c d, x, y => ∃ z, c.Rel axes x z ∧ d.Rel axes z y
  | .parallel c d, x, y => ∃ a b,
      c.Rel axes (pointLeft x) a ∧ d.Rel axes (pointRight x) b ∧ y = pointAppend a b

theorem Circuit.rel_iff {k n m : Nat} (c : Circuit k n m) (axes : Point k)
    (x : Point n) (y : Point m) : c.Rel axes x y ↔ c.Defined axes x ∧ y = c.value axes x := by
  induction c with
  | embed c => simp [Rel, Defined, value]
  | unary op => rfl
  | binary op => rfl
  | generator op axis => rfl
  | compose c d hc hd =>
      simp only [Rel, Defined, value, hc, hd]
      constructor
      · rintro ⟨z, ⟨hcx, rfl⟩, hdy⟩
        exact ⟨⟨hcx, hdy.1⟩, hdy.2⟩
      · rintro ⟨⟨hcx, hdx⟩, hy⟩
        exact ⟨c.value axes x, ⟨hcx, rfl⟩, hdx, hy⟩
  | parallel c d hc hd =>
      simp only [Rel, Defined, value, hc, hd]
      constructor
      · rintro ⟨a, b, ⟨ha, rfl⟩, ⟨hb, rfl⟩, hy⟩
        exact ⟨⟨ha, hb⟩, hy⟩
      · rintro ⟨⟨ha, hb⟩, hy⟩
        exact ⟨_, _, ⟨ha, rfl⟩, ⟨hb, rfl⟩, hy⟩

theorem Circuit.deterministic {k n m : Nat} (c : Circuit k n m) (axes : Point k)
    (x : Point n) (a b : Point m) (ha : c.Rel axes x a) (hb : c.Rel axes x b) : a = b := by
  rw [c.rel_iff] at ha hb
  exact ha.2.trans hb.2.symm

/-- Parallel evaluation with one shared input vector, implemented by explicit
legacy polynomial duplication and ordinary monoidal composition. -/
def Circuit.pair {k n m o : Nat} (c : Circuit k n m) (d : Circuit k n o) : Circuit k n (m + o) :=
  .compose (.embed (Polynomial.compileOutputs (Fin.addCases Polynomial.Expr.var Polynomial.Expr.var)))
    (.parallel c d)

@[simp] theorem Circuit.pair_value {k n m o : Nat} (c : Circuit k n m) (d : Circuit k n o)
    (axes : Point k) (x : Point n) :
    (c.pair d).value axes x = pointAppend (c.value axes x) (d.value axes x) := by
  have dup : (fun i : Fin (n + n) => Polynomial.Expr.eval x (Fin.addCases Polynomial.Expr.var Polynomial.Expr.var i)) =
      pointAppend x x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Fin.addCases_left]
      simp [Polynomial.Expr.eval, pointAppend]
    · intro j
      rw [Fin.addCases_right]
      simp [Polynomial.Expr.eval, pointAppend]
  simp only [pair, value, Polynomial.compileOutputs_correct, dup,
    pointLeft_pointAppend, pointRight_pointAppend]

@[simp] theorem Circuit.pair_defined {k n m o : Nat} (c : Circuit k n m) (d : Circuit k n o)
    (axes : Point k) (x : Point n) :
    (c.pair d).Defined axes x ↔ c.Defined axes x ∧ d.Defined axes x := by
  have dup : (fun i : Fin (n + n) => Polynomial.Expr.eval x (Fin.addCases Polynomial.Expr.var Polynomial.Expr.var i)) =
      pointAppend x x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Fin.addCases_left]
      simp [Polynomial.Expr.eval, pointAppend]
    · intro j
      rw [Fin.addCases_right]
      simp [Polynomial.Expr.eval, pointAppend]
  simp only [pair, Defined, value, Polynomial.compileOutputs_correct, dup,
    pointLeft_pointAppend, pointRight_pointAppend, true_and]

#print axioms Circuit.rel_iff
#print axioms Circuit.deterministic
#print axioms Circuit.pair_value
#print axioms Circuit.pair_defined
end Gimle.Asgard.RealAtomics
