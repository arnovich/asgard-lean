import Gimle.Asgard.Compile.Polynomial

/-! Named source semantics and checked resolution. Assignments are explicit and
ordered: a right-hand side can use inputs and preceding assignments only. -/
namespace Gimle.Asgard.Polynomial

inductive PortRole where
  | input | parameter | state | driver | initial | boundary | output
  deriving Repr, DecidableEq, BEq

structure Port where
  id : String
  name : String
  role : PortRole
  deriving Repr, DecidableEq, BEq

/-- Stable IDs and source names are separately unique; position is list order. -/
def validPorts (ports : List Port) : Bool :=
  decide ((ports.map Port.id).Nodup ∧ (ports.map Port.name).Nodup) &&
    ports.all (fun p => !p.id.isEmpty && !p.name.isEmpty)

inductive NamedExpr where
  | var (name : String)
  | constant (value : ℚ)
  | add (left right : NamedExpr)
  | mul (left right : NamedExpr)
  | neg (argument : NamedExpr)
  deriving Repr, DecidableEq

/-- Independent partial source semantics: unbound names have no value. -/
noncomputable def NamedExpr.eval (env : String → Option ℝ) : NamedExpr → Option ℝ
  | .var name => env name
  | .constant q => some q
  | .add a b => do return (← a.eval env) + (← b.eval env)
  | .mul a b => do return (← a.eval env) * (← b.eval env)
  | .neg a => do return -(← a.eval env)

/-- Resolution substitutes already resolved assignments as indexed expressions. -/
def NamedExpr.resolve {n : Nat} (env : String → Option (Expr n)) : NamedExpr → Option (Expr n)
  | .var name => env name
  | .constant q => some (.constant q)
  | .add a b => do return .add (← a.resolve env) (← b.resolve env)
  | .mul a b => do return .mul (← a.resolve env) (← b.resolve env)
  | .neg a => do return .neg (← a.resolve env)

theorem NamedExpr.resolve_correct {n : Nat} (e : NamedExpr)
    (env : String → Option (Expr n)) (x : Point n) :
    (e.resolve env).map (Expr.eval x) =
      e.eval (fun name => (env name).map (Expr.eval x)) := by
  induction e with
  | var name => rfl
  | constant q => rfl
  | add a b ha hb =>
      simp only [resolve, eval]
      rw [← ha, ← hb]
      cases a.resolve env <;> cases b.resolve env <;> rfl
  | mul a b ha hb =>
      simp only [resolve, eval]
      rw [← ha, ← hb]
      cases a.resolve env <;> cases b.resolve env <;> rfl
  | neg a ha =>
      simp only [resolve, eval]
      rw [← ha]
      cases a.resolve env <;> rfl

/-- Ordered lookup; no first-occurrence context inference or role inference. -/
def lookupIndex : (names : List String) → String → Option (Fin names.length)
  | [], _ => none
  | head :: tail, name =>
      if name = head then some 0 else (lookupIndex tail name).map Fin.succ

/-- Successful name resolution selects a coordinate carrying that exact name. -/
theorem lookupIndex_sound (names : List String) (name : String) (i : Fin names.length)
    (found : lookupIndex names name = some i) : names[i] = name := by
  induction names with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      by_cases same : name = head
      · simp [lookupIndex, same] at found
        subst i
        simp [same]
      · cases rest : lookupIndex tail name with
        | none => simp [lookupIndex, same, rest] at found
        | some j =>
            simp [lookupIndex, same, rest] at found
            subst i
            simpa using ih j rest

def inputBindings (ports : List Port) (name : String) : Option (Expr ports.length) :=
  ((lookupIndex (ports.map Port.name) name).map fun i =>
    Expr.var (Fin.cast (List.length_map ..) i))

noncomputable def inputValues (ports : List Port) (x : Point ports.length)
    (name : String) : Option ℝ :=
  (lookupIndex (ports.map Port.name) name).map fun i => x (Fin.cast (List.length_map ..) i)

theorem inputBindings_correct (ports : List Port) (x : Point ports.length) (name : String) :
    (inputBindings ports name).map (Expr.eval x) = inputValues ports x name := by
  simp only [inputBindings, inputValues, Option.map_map]
  rfl

structure Assignment where
  output : Port
  rhs : NamedExpr
  deriving Repr, DecidableEq

def bind {α : Type} (env : String → Option α) (name : String) (value : α) :
    String → Option α := fun key => if key = name then some value else env key

/-- Duplicate names (including input shadowing) and unresolved dependencies fail. -/
def resolveAssignments {n : Nat} (env : String → Option (Expr n)) :
    List Assignment → Option (List (Expr n))
  | [] => some []
  | a :: rest => do
      if (env a.output.name).isSome then none else do
        let e ← a.rhs.resolve env
        let es ← resolveAssignments (bind env a.output.name e) rest
        return e :: es

/-- Source assignment evaluation uses real values, not compiled expressions. -/
noncomputable def evalAssignments (env : String → Option ℝ) :
    List Assignment → Option (List ℝ)
  | [] => some []
  | a :: rest => do
      if (env a.output.name).isSome then none else do
        let value ← a.rhs.eval env
        let values ← evalAssignments (bind env a.output.name value) rest
        return value :: values

theorem resolveAssignments_correct {n : Nat} (as : List Assignment)
    (env : String → Option (Expr n)) (x : Point n) :
    (resolveAssignments env as).map (List.map (Expr.eval x)) =
      evalAssignments (fun name => (env name).map (Expr.eval x)) as := by
  induction as generalizing env with
  | nil => rfl
  | cons a rest ih =>
      simp only [resolveAssignments, evalAssignments, Option.isSome_map]
      split_ifs with h
      · rfl
      · rw [← NamedExpr.resolve_correct]
        cases he : a.rhs.resolve env with
        | none => simp
        | some e =>
            simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
            have hb : (fun name => ((bind env a.output.name e) name).map (Expr.eval x)) =
                bind (fun name => (env name).map (Expr.eval x)) a.output.name (e.eval x) := by
              funext name
              simp [bind]
              split <;> rfl
            rw [← hb, ← ih]
            cases resolveAssignments (bind env a.output.name e) rest <;> rfl

structure Program where
  inputs : List Port
  assignments : List Assignment
  deriving Repr, DecidableEq

/-- Input and output IDs are globally distinct in this explicit-assignment fragment. -/
def Program.valid (p : Program) : Bool :=
  validPorts (p.inputs ++ p.assignments.map Assignment.output) &&
    p.inputs.all (fun p => p.role != .output) &&
    p.assignments.all (fun a => a.output.role == .output)

def Program.resolve (p : Program) : Option (List (Expr p.inputs.length)) :=
  if p.valid then resolveAssignments (inputBindings p.inputs) p.assignments else none

/-- Named satisfaction stays a relation to proposed output values. -/
def Program.Satisfies (p : Program) (x : Point p.inputs.length) (values : List ℝ) : Prop :=
  p.valid = true ∧ evalAssignments (inputValues p.inputs x) p.assignments = some values

theorem Program.resolve_correct (p : Program) (x : Point p.inputs.length) :
    (p.resolve).map (List.map (Expr.eval x)) =
      if p.valid then evalAssignments (inputValues p.inputs x) p.assignments else none := by
  simp only [resolve]
  split <;> simp_all [resolveAssignments_correct, inputBindings_correct]

def compileList {n : Nat} (es : List (Expr n)) : Circuit n es.length :=
  compileOutputs (fun i => es[i])

@[simp] theorem compileList_correct {n : Nat} (es : List (Expr n)) (x : Point n) :
    List.ofFn ((compileList es).run x) = es.map (Expr.eval x) := by
  simp [compileList, compileOutputs_correct]

/-- Every accepted program compiles to exactly its independent named assignment
relation, including all intermediate assignment outputs in declaration order. -/
theorem Program.satisfies_iff_compiled (p : Program) (es : List (Expr p.inputs.length))
    (accepted : p.resolve = some es) (x : Point p.inputs.length) (values : List ℝ) :
    p.Satisfies x values ↔ List.ofFn ((compileList es).run x) = values := by
  have valid : p.valid = true := by
    by_contra h
    simp [Program.resolve, h] at accepted
  have correct := p.resolve_correct x
  rw [accepted] at correct
  simp only [Option.map_some, valid, ite_true] at correct
  simp [Satisfies, valid, ← correct, compileList_correct]

def Program.compile (p : Program) : Option ((m : Nat) × Circuit p.inputs.length m) :=
  p.resolve.map (fun es => ⟨es.length, compileList es⟩)

#print axioms NamedExpr.resolve_correct
#print axioms resolveAssignments_correct
#print axioms Program.satisfies_iff_compiled

end Gimle.Asgard.Polynomial
