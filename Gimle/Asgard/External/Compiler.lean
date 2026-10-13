import Gimle.Asgard.External.Core

namespace Gimle.Asgard.External

private def duplicate (n : Nat) : Gimle.Asgard.Circuit n (n+n) :=
  Polynomial.compileOutputs (Fin.addCases Polynomial.Expr.var Polynomial.Expr.var)

private theorem duplicate_run {n : Nat} (x : Point n) : (duplicate n).run x = pointAppend x x := by
  simp only [duplicate, Polynomial.compileOutputs_correct]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; rw [Fin.addCases_left]; simp [Polynomial.Expr.eval, pointAppend]
  · intro j; rw [Fin.addCases_right]; simp [Polynomial.Expr.eval, pointAppend]

def Circuit.pair {n m k : Nat} (a : Circuit n m) (b : Circuit n k) : Circuit n (m+k) :=
  .compose (.embed (duplicate n)) (.parallel a b)

@[simp] theorem Circuit.pair_value {n m k : Nat} (a : Circuit n m) (b : Circuit n k)
    (env : Environment) (x : Point n) :
    (a.pair b).value env x = pointAppend (a.value env x) (b.value env x) := by
  simp [pair, value, duplicate_run]

@[simp] theorem Circuit.pair_defined {n m k : Nat} (a : Circuit n m) (b : Circuit n k)
    (env : Environment) (x : Point n) :
    (a.pair b).Defined env x ↔ a.Defined env x ∧ b.Defined env x := by
  simp [pair, Defined, value, duplicate_run]

/-- Independent vector source expressions; weighted/add branches share inputs.
The target contains no weighted/add source constructors. -/
inductive Source : Nat → Nat → Type where
  | polynomial {n m} (outputs : Fin m → Polynomial.Expr n) : Source n m
  | external {n m} (s : Symbol n m) : Source n m
  | compose {n m k} (a : Source n m) (b : Source m k) : Source n k
  | parallel {n m k l} (a : Source n m) (b : Source k l) : Source (n+k) (m+l)
  | weighted {n m} (gate : Source n 1) (body : Source n m) : Source n m
  | add {n m} (a b : Source n m) : Source n m

noncomputable def Source.value (env : Environment) {n m : Nat} : Source n m → Point n → Point m
  | .polynomial es, x => fun i => (es i).eval x
  | .external s, x => externalValue env s x
  | .compose a b, x => b.value env (a.value env x)
  | .parallel a b, x => pointAppend (a.value env (pointLeft x)) (b.value env (pointRight x))
  | .weighted g b, x => fun i => g.value env x 0 * b.value env x i
  | .add a b, x => a.value env x + b.value env x

def Source.Defined (env : Environment) {n m : Nat} : Source n m → Point n → Prop
  | .polynomial _, _ => True
  | .external s, x => admitted env s x
  | .compose a b, x => a.Defined env x ∧ b.Defined env (a.value env x)
  | .parallel a b, x => a.Defined env (pointLeft x) ∧ b.Defined env (pointRight x)
  | .weighted g b, x => g.Defined env x ∧ b.Defined env x
  | .add a b, x => a.Defined env x ∧ b.Defined env x

def Source.compile {n m : Nat} : Source n m → Circuit n m
  | .polynomial es => .embed (Polynomial.compileOutputs es)
  | .external s => .external s
  | .compose a b => .compose a.compile b.compile
  | .parallel a b => .parallel a.compile b.compile
  | .weighted g b => .compose (g.compile.pair b.compile)
      (.embed (Polynomial.compileOutputs (fun i =>
        .mul (.var ⟨0, by omega⟩) (.var (i.natAdd 1)))))
  | .add a b => .compose (a.compile.pair b.compile)
      (.embed (Polynomial.compileOutputs (fun i =>
        .add (.var (i.castAdd _)) (.var (i.natAdd _)))))

@[simp] theorem Source.compile_value {n m : Nat} (s : Source n m) (env : Environment)
    (x : Point n) : s.compile.value env x = s.value env x := by
  induction s with
  | polynomial es => simp [compile, Circuit.value, value]
  | external s => rfl
  | compose a b ha hb => simp [compile, Circuit.value, value, ha, hb]
  | parallel a b ha hb => simp [compile, Circuit.value, value, ha, hb]
  | weighted g b hg hb =>
    funext i
    simp [compile, Circuit.value, value, hg, hb, Polynomial.Expr.eval, pointAppend]
  | add a b ha hb =>
    funext i
    simp [compile, Circuit.value, value, ha, hb, Polynomial.Expr.eval, pointAppend]

@[simp] theorem Source.compile_defined {n m : Nat} (s : Source n m) (env : Environment)
    (x : Point n) : s.compile.Defined env x ↔ s.Defined env x := by
  induction s with
  | polynomial es => rfl
  | external s => rfl
  | compose a b ha hb => simp [compile, Circuit.Defined, Defined, ha, hb]
  | parallel a b ha hb => simp [compile, Circuit.Defined, Defined, ha, hb]
  | weighted g b hg hb => simp [compile, Circuit.Defined, Defined, hg, hb]
  | add a b ha hb => simp [compile, Circuit.Defined, Defined, ha, hb]

theorem Source.compile_rel {n m : Nat} (s : Source n m) (env : Environment)
    (x : Point n) (y : Point m) : s.compile.Rel env x y ↔ s.Defined env x ∧ y = s.value env x := by
  rw [Circuit.rel_iff, compile_value, compile_defined]

/-- Constant gates and sources use explicit discard of the original inputs. -/
def Source.lift {n m : Nat} (s : Source 0 m) : Source n m :=
  .compose (.polynomial Fin.elim0) s

def Source.constant {n : Nat} (q : ℚ) : Source n 1 :=
  (Source.polynomial (fun _ => .constant q) : Source 0 1).lift

@[simp] theorem Source.constant_value {n : Nat} (q : ℚ) (env : Environment) (x : Point n) :
    (Source.constant q).value env x = ![(q : ℝ)] := by
  funext i; fin_cases i; rfl

@[simp] theorem Source.constant_defined {n : Nat} (q : ℚ) (env : Environment) (x : Point n) :
    (Source.constant q).Defined env x := ⟨trivial,trivial⟩

/-- Unit collapse uses a total constant gate, preserving the body's domain. -/
theorem Source.unit_weight {n m : Nat} (s : Source n m) (env : Environment) :
    (Source.weighted (Source.constant 1) s).compile.Equivalent env s.compile := by
  intro x y
  simp [compile_rel, Defined, value, constant, lift, Polynomial.Expr.eval]

#print axioms Source.compile_value
#print axioms Source.compile_defined
#print axioms Source.compile_rel
#print axioms Source.unit_weight
end Gimle.Asgard.External
