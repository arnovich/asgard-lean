import Gimle.Asgard.Compile.Polynomial

/-! Scoped polynomial normalization. A lambda occurs at its unary application
site; first-class/higher-order functions are outside this source fragment. -/
namespace Gimle.Asgard.Normalization
open Polynomial

def semanticVersion : String := "asgard.scoped-polynomial-normalization/v1"

/-- Simultaneous substitution in a binder-free polynomial target. -/
def substitute {n m : Nat} (env : Fin n → Expr m) : Expr n → Expr m
  | .var i => env i
  | .constant q => .constant q
  | .add a b => .add (substitute env a) (substitute env b)
  | .mul a b => .mul (substitute env a) (substitute env b)
  | .neg a => .neg (substitute env a)

theorem substitute_correct {n m : Nat} (e : Expr n) (env : Fin n → Expr m)
    (x : Point m) : (substitute env e).eval x = e.eval (fun i => (env i).eval x) := by
  induction e <;> simp_all [substitute, Expr.eval]

/-- Exact rational folding and elementary identities, without claiming a
canonical polynomial normal form or reordering source variables. -/
def add (a b : Expr n) : Expr n :=
  match a, b with
  | .constant p, .constant q => .constant (p + q)
  | .constant 0, e => e
  | e, .constant 0 => e
  | a, b => .add a b

def mul (a b : Expr n) : Expr n :=
  match a, b with
  | .constant p, .constant q => .constant (p * q)
  | .constant 0, _ => .constant 0
  | _, .constant 0 => .constant 0
  | .constant 1, e => e
  | e, .constant 1 => e
  | a, b => .mul a b

def neg (a : Expr n) : Expr n :=
  match a with
  | .constant q => .constant (-q)
  | .neg e => e
  | e => .neg e

@[simp] theorem add_correct (a b : Expr n) (x : Point n) :
    (add a b).eval x = a.eval x + b.eval x := by
  unfold add
  split <;> simp_all [Expr.eval]

@[simp] theorem mul_correct (a b : Expr n) (x : Point n) :
    (mul a b).eval x = a.eval x * b.eval x := by
  unfold mul
  split <;> simp_all [Expr.eval]

@[simp] theorem neg_correct (a : Expr n) (x : Point n) :
    (neg a).eval x = -a.eval x := by
  unfold neg
  split <;> simp_all [Expr.eval]

def simplify : Expr n → Expr n
  | .var i => .var i
  | .constant q => .constant q
  | .add a b => add (simplify a) (simplify b)
  | .mul a b => mul (simplify a) (simplify b)
  | .neg a => neg (simplify a)

@[simp] theorem simplify_correct (e : Expr n) (x : Point n) :
    (simplify e).eval x = e.eval x := by
  induction e <;> simp_all [simplify, Expr.eval]

/-- In an application body, coordinate zero is the bound scalar and successor
coordinates refer to the enclosing scope. Finite indices rule out dangling
variables. The argument is evaluated in the enclosing scope. -/
inductive Source : Nat → Type where
  | var {n} (coordinate : Fin n) : Source n
  | constant {n} (value : ℚ) : Source n
  | add {n} (left right : Source n) : Source n
  | mul {n} (left right : Source n) : Source n
  | neg {n} (argument : Source n) : Source n
  | apply {n} (body : Source (n + 1)) (argument : Source n) : Source n
  deriving Repr

/-- Independent source evaluation, including lexical binding. -/
noncomputable def Source.eval {n : Nat} (x : Point n) : Source n → ℝ
  | .var i => x i
  | .constant q => q
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x
  | .neg a => -a.eval x
  | .apply body arg => body.eval (Fin.cons (arg.eval x) x)

/-- Normalize inner binders first. Substitution then acts only on binder-free
polynomials: bound zero receives the argument and successors retain their
enclosing coordinate. No textual name can capture an external variable. -/
def Source.normalize {n : Nat} : Source n → Expr n
  | .var i => .var i
  | .constant q => .constant q
  | .add a b => Normalization.add a.normalize b.normalize
  | .mul a b => Normalization.mul a.normalize b.normalize
  | .neg a => Normalization.neg a.normalize
  | .apply body arg => simplify (substitute (Fin.cons arg.normalize Expr.var) body.normalize)

@[simp] theorem Source.normalize_correct {n : Nat} (e : Source n) (x : Point n) :
    e.normalize.eval x = e.eval x := by
  induction e with
  | var i => rfl
  | constant q => rfl
  | add a b ha hb => simp_all [normalize, eval]
  | mul a b ha hb => simp_all [normalize, eval]
  | neg a ha => simp_all [normalize, eval]
  | @apply k body arg hb ha =>
      simp only [normalize, simplify_correct, substitute_correct, eval]
      have env : (fun i : Fin (k + 1) => Expr.eval x ((Fin.cons (α := fun _ => Expr k) arg.normalize Expr.var) i)) =
          Fin.cons (arg.eval x) x := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [ha]
        · simp [Expr.eval]
      rw [env, hb]

def Source.compile (e : Source n) : Circuit n 1 := e.normalize.compile

@[simp] theorem Source.compile_correct (e : Source n) (x : Point n) :
    e.compile.run x 0 = e.eval x := by simp [compile]

#print axioms substitute_correct
#print axioms Source.normalize_correct
#print axioms Source.compile_correct
end Gimle.Asgard.Normalization
