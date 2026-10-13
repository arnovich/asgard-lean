import Gimle.Asgard.RealAtomics.Circuit

/-! Independent scalar source expressions and compilation with explicit shared
input wiring. Definedness is strict in all children, even for zero multipliers. -/
namespace Gimle.Asgard.RealAtomics

inductive Expr (axes inputs : Nat) where
  | input (coordinate : Fin inputs)
  | constant (value : ℚ)
  | unary (op : Unary) (argument : Expr axes inputs)
  | binary (op : Binary) (left right : Expr axes inputs)
  | generated (op : Unary) (axis : Fin axes)
  deriving Repr, DecidableEq

noncomputable def Expr.value {k n : Nat} (axes : Point k) (x : Point n) : Expr k n → ℝ
  | .input i => x i
  | .constant q => q
  | .unary op e => op.value (e.value axes x)
  | .binary op a b => op.value (a.value axes x) (b.value axes x)
  | .generated op axis => op.value (axes axis)

def Expr.Defined {k n : Nat} (axes : Point k) (x : Point n) : Expr k n → Prop
  | .input _ => True
  | .constant _ => True
  | .unary op e => e.Defined axes x ∧ op.Domain (e.value axes x)
  | .binary op a b => (a.Defined axes x ∧ b.Defined axes x) ∧
      op.Domain (a.value axes x) (b.value axes x)
  | .generated op axis => op.Domain (axes axis)

def Expr.compile {k n : Nat} : Expr k n → Circuit k n 1
  | .input i => .embed (Polynomial.Expr.var i).compile
  | .constant q => .embed (Polynomial.Expr.constant q).compile
  | .unary op e => .compose e.compile (.unary op)
  | .binary op a b => .compose (a.compile.pair b.compile) (.binary op)
  | .generated op axis => .compose (.embed (Wiring.discard n)) (.generator op axis)

@[simp] theorem Expr.compile_value {k n : Nat} (e : Expr k n) (axes : Point k) (x : Point n) :
    e.compile.value axes x = ![e.value axes x] := by
  induction e with
  | input i =>
      funext j
      fin_cases j
      simp [compile, Circuit.value, value, Polynomial.Expr.eval]
  | constant q =>
      funext j
      fin_cases j
      simp [compile, Circuit.value, value, Polynomial.Expr.eval]
  | unary op e he => simp [compile, Circuit.value, he, value]
  | binary op a b ha hb =>
      simp [compile, Circuit.value, Circuit.pair_value, ha, hb, value, pointAppend]
  | generated op axis => simp [compile, Circuit.value, value]

@[simp] theorem Expr.compile_defined {k n : Nat} (e : Expr k n) (axes : Point k) (x : Point n) :
    e.compile.Defined axes x ↔ e.Defined axes x := by
  induction e with
  | input i => rfl
  | constant q => rfl
  | unary op e he => simp [compile, Circuit.Defined, compile_value, he, Defined]
  | binary op a b ha hb =>
      simp [compile, Circuit.Defined, Circuit.pair_defined, Circuit.pair_value,
        compile_value, ha, hb, Defined, pointAppend]
  | generated op axis => simp [compile, Circuit.Defined, Defined]

/-- Both source definedness and exact value are necessary and sufficient for
the compiled circuit's operational relation; a value equality alone is weaker. -/
theorem Expr.compile_rel {k n : Nat} (e : Expr k n) (axes : Point k) (x : Point n) (y : Point 1) :
    e.compile.Rel axes x y ↔ e.Defined axes x ∧ y = ![e.value axes x] := by
  rw [Circuit.rel_iff, compile_defined, compile_value]

/-- A scalar output presentation of the same full partial relation. -/
theorem Expr.compile_scalar {k n : Nat} (e : Expr k n) (axes : Point k) (x : Point n) (y : ℝ) :
    e.compile.Rel axes x ![y] ↔ e.Defined axes x ∧ y = e.value axes x := by
  rw [compile_rel]
  simp only [Matrix.vecCons_inj, and_true]

#print axioms Expr.compile_value
#print axioms Expr.compile_defined
#print axioms Expr.compile_rel
end Gimle.Asgard.RealAtomics
