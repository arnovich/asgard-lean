import Gimle.Asgard.Streams.TrigStream

/-! Typed circuits on formal time streams of Fourier polynomials.

This interpretation uses `TrigStream` wires, not pointwise real numbers or
multivariate Taylor streams. Laplacian and transport reuse the exact Fourier
operators of `Torus`; transport includes the zero-mode convention of that
module. Interpreting an output as a real Euler field requires the separate
mean-zero, evenness and convergence hypotheses.

Feedback is relational: it asserts a fixed point without assuming existence
or uniqueness. Only the vorticity circuit's subsequent theorem provides those.
There is no opaque primitive for the Euler solution.
-/
namespace Gimle.Asgard.Streams.Fourier

/-- A bank of Fourier time streams. -/
abbrev Point (n : Nat) := Fin n → TrigStream

/-- Append two banks, preserving their port order. -/
def append {n m : Nat} (x : Point n) (y : Point m) : Point (n + m) := Fin.addCases x y

@[simp] theorem append_single (a b : TrigStream) : append ![a] ![b] = ![a, b] := by
  ext i
  fin_cases i <;> rfl

/-- Fourier operators and typed wiring, with arbitrary relational feedback. -/
inductive Circuit (basis : Basis) : Nat → Nat → Type where
  | route {n m} (ports : Fin m → Fin n) : Circuit basis n m
  | scale (q : ℚ) : Circuit basis 1 1
  | laplacian : Circuit basis 1 1
  | add : Circuit basis 2 1
  | transport : Circuit basis 2 1
  | integralFrom : Circuit basis 2 1
  | compose {n m k} (first : Circuit basis n m) (second : Circuit basis m k) : Circuit basis n k
  | pair {n m k} (first : Circuit basis n m) (second : Circuit basis n k) : Circuit basis n (m + k)
  | trace {n m} (k : Nat) (body : Circuit basis (n + k) (m + k)) : Circuit basis n m

/-- Exact whole-stream behavior. A trace neither constructs nor chooses a solution. -/
def Circuit.Rel {basis : Basis} {n m : Nat} : Circuit basis n m → Point n → Point m → Prop
  | .route ports, x, y => y = x ∘ ports
  | .scale q, x, y => y = ![fun degree => q • x 0 degree]
  | .laplacian, x, y => y = ![fun degree => Torus.laplacian (x 0 degree)]
  | .add, x, y => y = ![x 0 + x 1]
  | .transport, x, y => y = ![TrigStream.convolve basis Torus.transport (x 0) (x 1)]
  | .integralFrom, x, y => y = ![TrigStream.integral basis (x 0) (x 1)]
  | .compose first second, x, y => ∃ middle, first.Rel x middle ∧ second.Rel middle y
  | .pair first second, x, y => ∃ a b, first.Rel x a ∧ second.Rel x b ∧ y = append a b
  | .trace _ body, x, y => ∃ feedback, body.Rel (append x feedback) (append y feedback)

/-- Feedforward expressions compile to the same wiring primitives. -/
inductive Expr (n : Nat) where
  | input (port : Fin n)
  | scale (q : ℚ) (arg : Expr n)
  | laplacian (arg : Expr n)
  | add (left right : Expr n)
  | transport (left right : Expr n)
  | integralFrom (rate boundary : Expr n)

/-- Mathematical interpretation before compilation. -/
noncomputable def Expr.value {n : Nat} (basis : Basis) (x : Point n) : Expr n → TrigStream
  | .input port => x port
  | .scale q arg => fun degree => q • arg.value basis x degree
  | .laplacian arg => fun degree => Torus.laplacian (arg.value basis x degree)
  | .add left right => left.value basis x + right.value basis x
  | .transport left right => TrigStream.convolve basis Torus.transport (left.value basis x) (right.value basis x)
  | .integralFrom rate boundary => TrigStream.integral basis (rate.value basis x) (boundary.value basis x)

/-- Compilation introduces only operators, port routing, pairing and composition. -/
def Expr.compile {n : Nat} (basis : Basis) : Expr n → Circuit basis n 1
  | .input port => .route ![port]
  | .scale q arg => .compose (arg.compile basis) (.scale q)
  | .laplacian arg => .compose (arg.compile basis) .laplacian
  | .add left right => .compose (.pair (left.compile basis) (right.compile basis)) .add
  | .transport left right => .compose (.pair (left.compile basis) (right.compile basis)) .transport
  | .integralFrom rate boundary => .compose (.pair (rate.compile basis) (boundary.compile basis)) .integralFrom

/-- Compiled expressions are total and deterministic, with the specified value. -/
theorem Expr.compile_rel {n : Nat} (basis : Basis) (e : Expr n) (x : Point n) (y : Point 1) :
    (e.compile basis).Rel x y ↔ y = ![e.value basis x] := by
  induction e generalizing y with
  | input port =>
      have h : x ∘ ![port] = ![x port] := by ext i; fin_cases i; rfl
      exact congrArg (fun z => y = z) h ▸ Iff.rfl
  | scale q arg ih => simp [compile, Circuit.Rel, ih, value]
  | laplacian arg ih => simp [compile, Circuit.Rel, ih, value]
  | add left right ih₁ ih₂ => simp [compile, Circuit.Rel, ih₁, ih₂, value]
  | transport left right ih₁ ih₂ => simp [compile, Circuit.Rel, ih₁, ih₂, value]
  | integralFrom rate boundary ih₁ ih₂ => simp [compile, Circuit.Rel, ih₁, ih₂, value]

end Gimle.Asgard.Streams.Fourier
