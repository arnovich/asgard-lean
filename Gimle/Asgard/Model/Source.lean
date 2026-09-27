import Gimle.Asgard.Model.Differential
import Gimle.Asgard.Model.Continuous

/-! Common source declarations with applied lambdas and implicit first-order
differential equations.

A `SourceBody` is lowered to an ordinary `Body`: every explicit assignment is
beta-normalized, and every differential equation is isolated into an assignment
to its state's derivative port. The lowered body then goes through the existing
verified compiler unchanged. Inputs, parameters and observations are copied,
and the `Evolution` (axis, start, states and initial values) is used as given.

`SourceBody.Solves` is independent of lowering and of every circuit. There
`D_t(x)` is the value of `x`'s declared derivative port, and that value is
required to be the derivative of `x` on the forward domain
(`Solves.derivative_denotes`). The main results are `solves_iff_lowered` and
the composed `SourceContinuousModel.solves_iff_realizes`. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- An explicit named assignment. Its right-hand side may contain applied
lambdas, but no derivative. -/
structure SourceAssignment where
  output : Port
  rhs : Term
  deriving Repr, DecidableEq

/-- An implicit first-order equation `lhs = rhs` defining the derivative port
`output`. A `StateBinding` names `output.id` as its state's derivative. -/
structure DifferentialEquation where
  output : Port
  lhs : Term
  rhs : Term
  deriving Repr, DecidableEq

structure SourceBody where
  inputs : List Port
  assignments : List SourceAssignment
  differentials : List DifferentialEquation := []
  parameters : List RationalBinding := []
  observations : List Observation := []
  deriving Repr, DecidableEq

/-- Assignment outputs, then differential outputs, in declaration order. -/
def SourceBody.outputs (sb : SourceBody) : List Port :=
  sb.assignments.map (·.output) ++ sb.differentials.map (·.output)

/-- The body with the same interface and the given explicit assignments. -/
def SourceBody.withAssignments (sb : SourceBody) (as : List Assignment) : Body where
  program := ⟨sb.inputs, as⟩
  parameters := sb.parameters
  observations := sb.observations

/-- The display name of the port with a stable ID, found as `Body.value` does. -/
def SourceBody.portName (sb : SourceBody) (id : String) : Option String :=
  ((sb.inputs ++ sb.outputs).find? (·.id == id)).map Port.name

/-- `x` names a state port; its derivative port is the one its binding names. -/
def SourceBody.context (sb : SourceBody) (e : Evolution) : Context where
  axis := e.axis.name
  locate state := do
    let p ← sb.inputs.find? (fun p => p.name == state && p.role == .state)
    let i ← index e.stateIds p.id
    sb.portName (e.derivativeIds i)

/-! ## Source semantics -/

/-- Every original equation, explicit and differential, with defined outputs. -/
def SourceBody.Equations (sb : SourceBody) (c : Context) (env : String → Option ℝ) :
    Prop :=
  (∀ a ∈ sb.assignments, env a.output.name ≠ none ∧
    a.rhs.eval env (c.rates env) = env a.output.name) ∧
  (∀ d ∈ sb.differentials, env d.output.name ≠ none ∧
    ∃ v, d.lhs.eval env (c.rates env) = some v ∧ d.rhs.eval env (c.rates env) = some v)

noncomputable def SourceBody.inputEnvironment {n : Nat} (sb : SourceBody)
    (ids : Fin n → String) (x : Point n) : String → Option ℝ :=
  (sb.withAssignments []).inputEnvironment ids x

def SourceBody.Source {n : Nat} (sb : SourceBody) (c : Context) (ids : Fin n → String)
    (x : Point n) (env : String → Option ℝ) : Prop :=
  Agrees (sb.inputEnvironment ids x) env ∧ sb.Equations c env

def SourceBody.value {α : Type} (sb : SourceBody) (env : String → Option α) (id : String) :
    Option α :=
  ((sb.inputs ++ sb.outputs).find? (·.id == id)).bind (fun p => env p.name)

theorem SourceBody.value_eq {α : Type} (sb : SourceBody) (env : String → Option α)
    (id : String) : sb.value env id = (sb.portName id).bind env := by
  unfold SourceBody.value SourceBody.portName
  cases (sb.inputs ++ sb.outputs).find? (·.id == id) <;> rfl

/-- Initial conditions and the original source equations on the forward domain,
with each derivative atom read from the state's actual derivative. -/
def SourceBody.Solves (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) : Prop :=
  (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
    some (state e.time.start i)) ∧
  ∀ t ∈ e.time.domain, ∃ env, sb.Source (sb.context e) e.stateIds (state t) env ∧
    ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t

/-- In a solution, `D_t(x)` denotes the derivative of the state coordinate
whose stable ID is the ID of the state port named `x`. -/
theorem SourceBody.Solves.derivative_denotes {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} {t : ℝ} {env : String → Option ℝ}
    (rates : ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t)
    (x : String) (r : ℝ) (h : (sb.context e).rates env e.axis.name x = some r) :
    ∃ p i, sb.inputs.find? (fun p => p.name == x && p.role == .state) = some p ∧
      e.stateIds i = p.id ∧ HasDerivWithinAt (fun t => state t i) r e.time.domain t := by
  simp only [Context.rates, context, if_true] at h
  cases hp : sb.inputs.find? (fun p => p.name == x && p.role == .state) with
  | none => simp [hp] at h
  | some p =>
    cases hi : index e.stateIds p.id with
    | none => simp [hp, hi] at h
    | some i =>
      refine ⟨p, i, rfl, ?_, ?_⟩
      · have := List.find?_some hi
        simpa using this
      · obtain ⟨rate, hv, hd⟩ := rates i
        have hr : sb.value env (e.derivativeIds i) = some r := by
          simp only [hp, hi, Option.bind_eq_bind, Option.bind_some] at h
          rw [SourceBody.value_eq]
          exact h
        rw [hr, Option.some.injEq] at hv
        exact hv ▸ hd

/-! ## Lowering -/

/-- A lowered body, with the source/target correspondence of its equations. -/
structure Lowered (sb : SourceBody) (c : Context) where
  assignments : List Assignment
  outputs : assignments.map (·.output) = sb.outputs
  equations : ∀ env, sb.Equations c env ↔ Equations assignments env

def Lowered.body {sb : SourceBody} {c : Context} (l : Lowered sb c) : Body :=
  sb.withAssignments l.assignments

private def lowerAssignment (c : Context) (a : SourceAssignment) :
    Except Diagnostic {out : Assignment // out.output = a.output ∧ ∀ env,
      (env a.output.name ≠ none ∧ a.rhs.eval env (c.rates env) = env a.output.name) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name)} :=
  match h : a.rhs.beta with
  | none => .error ⟨.unsupportedDerivative, a.output.id, "derivative in an explicit assignment"⟩
  | some e => .ok ⟨⟨a.output, e⟩, rfl, fun env => by
      rw [a.rhs.beta_correct e h env (c.rates env)]⟩

private def lowerDifferential (c : Context) (d : DifferentialEquation) :
    Except Diagnostic {out : Assignment // out.output = d.output ∧ ∀ env,
      (env d.output.name ≠ none ∧ ∃ v, d.lhs.eval env (c.rates env) = some v ∧
          d.rhs.eval env (c.rates env) = some v) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name)} :=
  match isolate c d.output.name d.lhs d.rhs with
  | .error code => .error ⟨code, d.output.id, d.output.name⟩
  | .ok i => .ok ⟨⟨d.output, i.expr⟩, rfl, fun env => i.correct env⟩

private def lowerList {α : Type} (P : α → (String → Option ℝ) → Prop) (port : α → Port)
    (f : (a : α) → Except Diagnostic {out : Assignment // out.output = port a ∧ ∀ env,
      P a env ↔ (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name)}) :
    (as : List α) → Except Diagnostic {out : List Assignment //
      out.map (·.output) = as.map port ∧ ∀ env, (∀ a ∈ as, P a env) ↔ Equations out env}
  | [] => .ok ⟨[], rfl, fun env => by simp [Equations]⟩
  | a :: rest => do
      let ⟨x, hx, px⟩ ← f a
      let ⟨xs, hxs, pxs⟩ ← lowerList P port f rest
      return ⟨x :: xs, by simp [hx, hxs], fun env => by
        simp only [List.forall_mem_cons, Equations] at *
        rw [px env, pxs env]⟩

/-- Check scopes, beta-normalize explicit assignments and isolate differentials. -/
def SourceBody.lower (sb : SourceBody) (c : Context) : Except Diagnostic (Lowered sb c) := do
  let names := (sb.inputs ++ sb.outputs).map Port.name
  for a in sb.assignments do
    match a.rhs.checkScope names with
    | .error name => throw ⟨.unknownReference, a.output.id, name⟩
    | .ok () => pure ()
  for d in sb.differentials do
    match d.lhs.checkScope names, d.rhs.checkScope names with
    | .error name, _ | _, .error name => throw ⟨.unknownReference, d.output.id, name⟩
    | .ok (), .ok () => pure ()
  let ⟨as, has, pas⟩ ← lowerList _ (·.output) (lowerAssignment c) sb.assignments
  let ⟨ds, hds, pds⟩ ← lowerList _ (·.output) (lowerDifferential c) sb.differentials
  return ⟨as ++ ds, by simp [SourceBody.outputs, has, hds], fun env => by
    rw [SourceBody.Equations, pas env, pds env]
    exact ⟨fun ⟨h1, h2⟩ a ha => (List.mem_append.mp ha).elim (h1 a) (h2 a),
      fun h => ⟨fun a ha => h a (List.mem_append_left _ ha),
        fun a ha => h a (List.mem_append_right _ ha)⟩⟩⟩

/-! ## Correspondence with the lowered body -/

theorem Lowered.value {sb : SourceBody} {c : Context} (l : Lowered sb c)
    {α : Type} (env : String → Option α) (id : String) :
    l.body.value env id = sb.value env id := by
  simp [Body.value, SourceBody.value, Lowered.body, SourceBody.withAssignments, l.outputs]

theorem Lowered.source {sb : SourceBody} {c : Context} (l : Lowered sb c) {n : Nat}
    (ids : Fin n → String) (x : Point n) (env : String → Option ℝ) :
    sb.Source c ids x env ↔ l.body.Source ids x env := by
  simp only [SourceBody.Source, Body.Source, l.equations]
  rfl

/-- The original differential equations and the lowered explicit body have the
same solutions: same states, axis, start, forward domain and initial values. -/
theorem Lowered.solves_iff {sb : SourceBody} {e : Evolution} (l : Lowered sb (sb.context e))
    (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ l.body.Solves e state := by
  simp only [SourceBody.Solves, Body.Solves, l.source, l.value]

/-- Hidden states and auxiliaries are existential, as in `Body.Observes`. -/
def SourceBody.Observes {n m : Nat} (sb : SourceBody) (c : Context) (ids : Fin n → String)
    (refs : Fin m → String) (x : Point n) (y : Point m) : Prop :=
  ∃ env, sb.Source c ids x env ∧ ∀ i, sb.value env (refs i) = some (y i)

theorem Lowered.observes {sb : SourceBody} {c : Context} (l : Lowered sb c) {n m : Nat}
    (ids : Fin n → String) (refs : Fin m → String) (x : Point n) (y : Point m) :
    sb.Observes c ids refs x y ↔ l.body.Observes ids refs x y := by
  simp only [SourceBody.Observes, Body.Observes, l.source, l.value]

def SourceBody.observationIds (sb : SourceBody) (i : Fin sb.observations.length) : String :=
  sb.observations[i].sourceId

def SourceBody.ObservedSolution (sb : SourceBody) (e : Evolution)
    (output : Dynamics.Signal sb.observations.length) : Prop :=
  ∃ state, sb.Solves e state ∧ ∀ t ∈ e.time.domain,
    sb.Observes (sb.context e) e.stateIds sb.observationIds (state t) (output t)

/-! ## Compilation -/

structure SourcePolynomialModel (sb : SourceBody) where
  lowered : Lowered sb Context.empty
  model : PolynomialModel lowered.body

/-- A polynomial declaration has no evolution axis, so every derivative atom and
every differential equation is rejected. -/
def compileSourcePolynomial (sb : SourceBody) :
    Except Diagnostic (SourcePolynomialModel sb) := do
  if let some d := sb.differentials.head? then
    throw ⟨.unsupportedDerivative, d.output.id, "differential equation without an evolution axis"⟩
  let lowered ← sb.lower Context.empty
  let model ← compilePolynomial lowered.body
  return ⟨lowered, model⟩

/-- Original source equations, including lambdas, against the compiled outputs. -/
theorem SourcePolynomialModel.correct {sb : SourceBody} (p : SourcePolynomialModel sb)
    (x : Point p.lowered.body.runtimePorts.length) (y : Point sb.observations.length) :
    sb.Observes Context.empty p.lowered.body.runtimeIds sb.observationIds x y ↔
      p.model.outputs.circuit.run x = y := by
  rw [p.lowered.observes]
  exact p.model.outputs.correct x y

structure SourceContinuousModel (sb : SourceBody) (e : Evolution) where
  lowered : Lowered sb (sb.context e)
  model : ContinuousModel lowered.body e

def compileSourceContinuous (sb : SourceBody) (e : Evolution) :
    Except Diagnostic (SourceContinuousModel sb e) := do
  let lowered ← sb.lower (sb.context e)
  let model ← compileContinuous lowered.body e
  return ⟨lowered, model⟩

/-- The original implicit differential equations and initial conditions against
the initialized feedback of the compiled isolated RHS, on the same domain. -/
theorem SourceContinuousModel.solves_iff_realizes {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ p.model.Realizes state := by
  rw [p.lowered.solves_iff, p.model.solves_iff_realizes]

/-- Any further obligation on the whole trajectory, such as a boundary or
terminal condition, is carried unchanged: the trajectory itself is not
transformed by isolation. -/
theorem SourceContinuousModel.constrained_iff {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (constraint : Dynamics.Signal e.states.length → Prop)
    (state : Dynamics.Signal e.states.length) :
    (sb.Solves e state ∧ constraint state) ↔ (p.model.Realizes state ∧ constraint state) := by
  rw [p.solves_iff_realizes]

theorem SourceContinuousModel.observations_correct {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (output : Dynamics.Signal sb.observations.length) :
    sb.ObservedSolution e output ↔ p.model.ObservedRealization output := by
  rw [← p.model.observations_correct]
  simp only [SourceBody.ObservedSolution, Body.ObservedSolution, p.lowered.solves_iff,
    p.lowered.observes]
  rfl

#print axioms SourceBody.Solves.derivative_denotes
#print axioms Lowered.solves_iff
#print axioms SourcePolynomialModel.correct
#print axioms SourceContinuousModel.solves_iff_realizes
#print axioms SourceContinuousModel.constrained_iff
#print axioms SourceContinuousModel.observations_correct
end Gimle.Asgard.Model
