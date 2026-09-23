import Gimle.Asgard.Compile.Wiring

/-! Total polynomial compilation over arbitrary finite input contexts.
The independent source evaluator never invokes a circuit. -/
namespace Gimle.Asgard.Polynomial

inductive Expr (n : Nat) where
  | var (coordinate : Fin n)
  | constant (value : ℚ)
  | add (left right : Expr n)
  | mul (left right : Expr n)
  | neg (argument : Expr n)
  deriving Repr, DecidableEq

noncomputable def Expr.eval {n : Nat} (x : Point n) : Expr n → ℝ
  | .var i => x i
  | .constant q => q
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x
  | .neg a => -a.eval x

/-- Retain inputs while computing one result. Binary branches share the original
environment; neither receives a fresh unrelated set of source values. -/
def Expr.compileKeep {n : Nat} : Expr n → Circuit n (n + 1)
  | .var i => Wiring.copyWire n i
  | .constant q => @Circuit.parallel n n 0 1 (Wiring.identity n) (.const q)
  | .add a b => .compose b.compileKeep
      (.compose (.parallel a.compileKeep .id) (@Circuit.parallel n n 2 1 (Wiring.identity n) .add))
  | .mul a b => .compose b.compileKeep
      (.compose (.parallel a.compileKeep .id) (@Circuit.parallel n n 2 1 (Wiring.identity n) .multiplication))
  | .neg a => .compose a.compileKeep (.parallel (Wiring.identity n) (.scalar (-1)))

def Expr.compile {n : Nat} (e : Expr n) : Circuit n 1 :=
  .compose e.compileKeep (.parallel (Wiring.discard n) .id)

theorem Expr.compileKeep_correct {n : Nat} (e : Expr n) (x : Point n) :
    e.compileKeep.run x = pointAppend x ![e.eval x] := by
  induction e with
  | var i => simp [compileKeep, eval]
  | constant q =>
      simp only [compileKeep, Circuit.run, Wiring.identity_run, eval]
      rfl
  | add a b ha hb =>
      simp only [compileKeep, Circuit.run, ha, hb, Wiring.identity_run,
        pointLeft_pointAppend, pointRight_pointAppend]
      funext i
      by_cases h : i.val < n
      · simp [pointAppend, pointLeft, h, Nat.le_of_lt h]
      · simp [pointAppend, pointRight, eval, h]
  | mul a b ha hb =>
      simp only [compileKeep, Circuit.run, ha, hb, Wiring.identity_run,
        pointLeft_pointAppend, pointRight_pointAppend]
      funext i
      by_cases h : i.val < n
      · simp [pointAppend, pointLeft, h, Nat.le_of_lt h]
      · simp [pointAppend, pointRight, eval, h]
  | neg a ha => simp [compileKeep, eval, ha]

@[simp] theorem Expr.compile_correct {n : Nat} (e : Expr n) (x : Point n) :
    e.compile.run x 0 = e.eval x := by
  simp [compile, compileKeep_correct]

/-- Equation satisfaction is preserved; this theorem does not solve an equation. -/
theorem equation_correct {n : Nat} (a b : Expr n) (x : Point n) :
    a.compile.run x 0 = b.compile.run x 0 ↔ a.eval x = b.eval x := by
  simp

/-- Change only a propositionally equal wire count. -/
def castOutput {n m k : Nat} (h : m = k) (c : Circuit n m) : Circuit n k := h ▸ c

@[simp] theorem castOutput_run {n m k : Nat} (h : m = k) (c : Circuit n m)
    (x : Point n) (i : Fin k) :
    (castOutput h c).run x i = c.run x (Fin.cast h.symm i) := by
  subst k
  rfl

/-- Compute ordered outputs, retaining the original input prefix. -/
def compileOutputsKeep {n : Nat} : (m : Nat) → (Fin m → Expr n) → Circuit n (n + m)
  | 0, _ => Wiring.identity n
  | m + 1, es => castOutput (Nat.add_assoc n m 1)
      (.compose (es (Fin.last m)).compileKeep
        (@Circuit.parallel n (n + m) 1 1
          (compileOutputsKeep m (fun i => es i.castSucc)) .id))

theorem compileOutputsKeep_correct {n m : Nat} (es : Fin m → Expr n) (x : Point n) :
    (compileOutputsKeep m es).run x = pointAppend x (fun i => (es i).eval x) := by
  induction m with
  | zero =>
      funext i
      simp [compileOutputsKeep, pointAppend]
  | succ m ih =>
      funext i
      simp only [compileOutputsKeep, castOutput_run, Circuit.run, Expr.compileKeep_correct,
        pointLeft_pointAppend, pointRight_pointAppend, ih]
      by_cases h : i.val < n
      · simp [pointAppend, h, Nat.lt_of_lt_of_le h (Nat.le_add_right n m)]
      · by_cases h' : i.val < n + m
        · simp [pointAppend, h, h']
        · have last : i.val = n + m := by omega
          simp [pointAppend, last]
          rfl

def compileOutputs {n m : Nat} (es : Fin m → Expr n) : Circuit n m :=
  castOutput (Nat.zero_add m)
    (.compose (compileOutputsKeep m es) (.parallel (Wiring.discard n) (Wiring.identity m)))

@[simp] theorem compileOutputs_correct {n m : Nat} (es : Fin m → Expr n) (x : Point n) :
    (compileOutputs es).run x = fun i => (es i).eval x := by
  funext i
  simp only [compileOutputs, castOutput_run, Circuit.run, compileOutputsKeep_correct,
    pointLeft_pointAppend, pointRight_pointAppend, Wiring.identity_run, Wiring.discard_run]
  simp [pointAppend]

/-- Arbitrary routing includes permutations, duplication and omission of inputs. -/
def route {n m : Nat} (indices : Fin m → Fin n) : Circuit n m :=
  compileOutputs (fun i => .var (indices i))

@[simp] theorem route_correct {n m : Nat} (indices : Fin m → Fin n) (x : Point n) :
    (route indices).run x = fun i => x (indices i) := by
  simp [route, Expr.eval]

#print axioms Expr.compile_correct
#print axioms compileOutputs_correct
#print axioms route_correct

end Gimle.Asgard.Polynomial
