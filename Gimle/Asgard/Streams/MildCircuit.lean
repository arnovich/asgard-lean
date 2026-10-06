import Gimle.Asgard.Streams.Mild

/-! Typed circuits on the exact mild interaction stream.

Heat, Duhamel integration and the degree shift are explicit primitives.
Relational trace asserts a fixed point; the specific circuit theorem proves
existence and uniqueness from the boundary's initial slice.
-/
namespace Gimle.Asgard.Streams.Mild

/-- The unweighted convolution in interaction degree. -/
noncomputable def convolve (a b : Stream) : Stream := fun n =>
  ∑ m ∈ Finset.range (n + 1), transport (a m) (b (n - m))

/-- A bank of mild interaction streams. -/
abbrev Point (n : Nat) := Fin n → Stream

/-- Append two banks, preserving their port order. -/
def append {n m : Nat} (x : Point n) (y : Point m) : Point (n + m) := Fin.addCases x y

@[simp] theorem append_single (a b : Stream) : append ![a] ![b] = ![a, b] := by
  ext i
  fin_cases i <;> rfl

/-- Mild operators and typed wiring, with arbitrary relational feedback. -/
inductive Circuit (ν : ℚ) : Nat → Nat → Type where
  | route {n m} (ports : Fin m → Fin n) : Circuit ν n m
  | scale (q : ℚ) : Circuit ν 1 1
  | heat : Circuit ν 1 1
  | duhamel : Circuit ν 1 1
  | add : Circuit ν 2 1
  | transport : Circuit ν 2 1
  | shiftFrom : Circuit ν 2 1
  | compose {n m k} (first : Circuit ν n m) (second : Circuit ν m k) : Circuit ν n k
  | pair {n m k} (first : Circuit ν n m) (second : Circuit ν n k) : Circuit ν n (m + k)
  | trace {n m} (k : Nat) (body : Circuit ν (n + k) (m + k)) : Circuit ν n m

/-- Exact whole-stream behavior. A trace neither constructs nor chooses a solution. -/
def Circuit.Rel {ν : ℚ} {n m : Nat} : Circuit ν n m → Point n → Point m → Prop
  | .route ports, x, y => y = x ∘ ports
  | .scale q, x, y => y = ![fun degree => q • x 0 degree]
  | .heat, x, y => y = ![fun degree => Mild.heat (x 0 degree)]
  | .duhamel, x, y => y = ![fun degree => Mild.duhamel ν (x 0 degree)]
  | .add, x, y => y = ![x 0 + x 1]
  | .transport, x, y => y = ![convolve (x 0) (x 1)]
  | .shiftFrom, x, y => y = ![Streams.shiftFrom (x 0) (x 1)]
  | .compose first second, x, y => ∃ middle, first.Rel x middle ∧ second.Rel middle y
  | .pair first second, x, y => ∃ a b, first.Rel x a ∧ second.Rel x b ∧ y = append a b
  | .trace _ body, x, y => ∃ feedback, body.Rel (append x feedback) (append y feedback)

/-- Feedforward expressions compile to the same wiring primitives. -/
inductive Expr (n : Nat) where
  | input (port : Fin n)
  | scale (q : ℚ) (arg : Expr n)
  | heat (arg : Expr n)
  | duhamel (arg : Expr n)
  | add (left right : Expr n)
  | transport (left right : Expr n)
  | shiftFrom (rate boundary : Expr n)

/-- Mathematical interpretation before compilation. -/
noncomputable def Expr.value {n : Nat} (ν : ℚ) (x : Point n) : Expr n → Stream
  | .input port => x port
  | .scale q arg => fun degree => q • arg.value ν x degree
  | .heat arg => fun degree => Mild.heat (arg.value ν x degree)
  | .duhamel arg => fun degree => Mild.duhamel ν (arg.value ν x degree)
  | .add left right => left.value ν x + right.value ν x
  | .transport left right => convolve (left.value ν x) (right.value ν x)
  | .shiftFrom rate boundary => Streams.shiftFrom (rate.value ν x) (boundary.value ν x)

/-- Compilation introduces only operators, port routing, pairing and composition. -/
def Expr.compile {n : Nat} (ν : ℚ) : Expr n → Circuit ν n 1
  | .input port => .route ![port]
  | .scale q arg => .compose (arg.compile ν) (.scale q)
  | .heat arg => .compose (arg.compile ν) .heat
  | .duhamel arg => .compose (arg.compile ν) .duhamel
  | .add left right => .compose (.pair (left.compile ν) (right.compile ν)) .add
  | .transport left right => .compose (.pair (left.compile ν) (right.compile ν)) .transport
  | .shiftFrom rate boundary => .compose (.pair (rate.compile ν) (boundary.compile ν)) .shiftFrom

/-- Compiled expressions are total and deterministic, with the specified value. -/
theorem Expr.compile_rel {n : Nat} (ν : ℚ) (e : Expr n) (x : Point n) (y : Point 1) :
    (e.compile ν).Rel x y ↔ y = ![e.value ν x] := by
  induction e generalizing y with
  | input port =>
      have h : x ∘ ![port] = ![x port] := by ext i; fin_cases i; rfl
      exact congrArg (fun z => y = z) h ▸ Iff.rfl
  | scale q arg ih => simp [compile, Circuit.Rel, ih, value]
  | heat arg ih => simp [compile, Circuit.Rel, ih, value]
  | duhamel arg ih => simp [compile, Circuit.Rel, ih, value]
  | add left right ih₁ ih₂ => simp [compile, Circuit.Rel, ih₁, ih₂, value]
  | transport left right ih₁ ih₂ => simp [compile, Circuit.Rel, ih₁, ih₂, value]
  | shiftFrom rate boundary ih₁ ih₂ => simp [compile, Circuit.Rel, ih₁, ih₂, value]

/-- The only external port is the boundary; port 1 is the internal feedback. -/
def rhsExpr : Expr 2 := .scale (-1) (.duhamel (.transport (.input 1) (.input 1)))

/-- Heat the initial slice, then shift the integrated nonlinear forcing. -/
def rebuiltExpr : Expr 2 := .shiftFrom rhsExpr (.heat (.input 0))

/-- Expose the feedback state and wire its reconstruction back into the loop. -/
def mildBody (ν : ℚ) : Circuit ν 2 2 :=
  .pair ((Expr.input 1).compile ν) (rebuiltExpr.compile ν)

/-- The viscous mild circuit contains one integrated interaction-degree loop. -/
def mildCircuit (ν : ℚ) : Circuit ν 1 1 := .trace 1 (mildBody ν)

theorem rhsExpr_value (ν : ℚ) (boundary state : Stream) :
    rhsExpr.value ν ![boundary, state] = rhs ν state := by
  funext degree
  apply Finsupp.ext
  intro k
  simp [rhsExpr, Expr.value, rhs, convolve]

/-- The actual loop relation is precisely the Wild reconstruction equation. -/
theorem mildCircuit_rel_iff_reconstructs (ν : ℚ) (boundary candidate : Stream) :
    (mildCircuit ν).Rel ![boundary] ![candidate] ↔
      Streams.shiftFrom (rhs ν candidate) (fun n => heat (boundary n)) = candidate := by
  simp only [mildCircuit, Circuit.Rel, mildBody, Expr.compile_rel]
  constructor
  · rintro ⟨feedback, a, b, ha, hb, h⟩
    change a = ![feedback 0] at ha
    subst a
    subst b
    have output : candidate = feedback 0 := congrArg (fun p => p 0) h
    have loop : feedback 0 = rebuiltExpr.value ν (append ![boundary] feedback) :=
      congrArg (fun p => p 1) h
    have input_eq : append ![boundary] feedback = ![boundary, candidate] := by
      funext i
      fin_cases i
      · rfl
      · exact output.symm
    rw [input_eq] at loop
    change feedback 0 = Streams.shiftFrom
      (rhsExpr.value ν ![boundary, candidate]) (fun n => heat (boundary n)) at loop
    rw [rhsExpr_value, ← output] at loop
    exact loop.symm
  · intro h
    refine ⟨![candidate], ![candidate], ![candidate], rfl, ?_, rfl⟩
    change ![candidate] = ![Streams.shiftFrom (rhsExpr.value ν ![boundary, candidate])
      (fun n => heat (boundary n))]
    rw [rhsExpr_value, h]

/-- The circuit is total and has exactly the constructed Wild stream as output. -/
theorem mildCircuit_rel_iff (ν : ℚ) (boundary : Stream) (output : Point 1) :
    (mildCircuit ν).Rel ![boundary] output ↔ output = ![wild ν boundary] := by
  have eta : output = ![output 0] := by ext i; fin_cases i; rfl
  rw [eta, mildCircuit_rel_iff_reconstructs]
  constructor
  · intro h
    have h0 : output 0 0 = heat (boundary 0) :=
      (congrFun h 0).symm
    have hs : ∀ n, output 0 (n + 1) = rhs ν (output 0) n :=
      fun n => (congrFun h (n + 1)).symm
    rw [wild_recursion_unique ν boundary (output 0) h0 hs]
  · intro h
    have value := congrArg (fun p => p 0) h
    simp only [Matrix.cons_val_zero] at value
    rw [value]
    exact wild_reconstructs ν boundary

/-- Every boundary has a related output; no proposed solution is an input. -/
theorem mildCircuit_solution (ν : ℚ) (boundary : Stream) :
    (mildCircuit ν).Rel ![boundary] ![wild ν boundary] :=
  (mildCircuit_rel_iff ν boundary _).mpr rfl

#print axioms Expr.compile_rel
#print axioms mildCircuit_rel_iff
#print axioms mildCircuit_solution

end Gimle.Asgard.Streams.Mild
