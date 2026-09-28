import Gimle.Asgard.Model.Integral
import Gimle.Asgard.Model.Continuous

/-! Common source declarations with applied lambdas, implicit first-order
differential equations and higher-order equations over declared velocities.

A `SourceBody` is lowered to an ordinary `Body`: every explicit assignment is
beta-normalized, and every differential equation is isolated into an assignment
to its state's derivative port. A velocity declaration `dx : D_t(x) = v` is
itself such an equation, lowered to `dx := v`; it also licenses the chain
`D_t(D_t(x))`, which isolation reads as `D_t(v)`. A higher-order equation is
thus lowered to a first-order system over explicitly declared states: the velocity
`v` is an ordinary state with its own `StateBinding` and initial value, and
nothing about it is inferred from names. A lower-order atom `D_t(x)` beside the
chain is read as `v`; that reading needs the velocity equations, which the
declarations themselves supply for the whole system (`SourceBody.velocitiesHold`).
Before isolation, the three inverse rewrites of `Model.Integral` remove
integrals: `D_t(I_t(X))` becomes `X`, `D_t(D_t(I_t(x)))` becomes `D_t(x)`, and
`I_t(D_t(x))` becomes `x - x0`, with the declared initial value `x0` of `x`.
An integral declaration `dF : F = I_t(X)` names a state `F`, whose derivative
port is `dF` and whose declared initial value must be `0`; it is read as the
equation `D_t(F) = X`, lowered to `dF := X`, and every other occurrence of
`I_t(X)` is read as `F`. Any other integral is rejected.
The lowered body then goes through the existing verified compiler unchanged.
Inputs, parameters and observations are copied, and the `Evolution` (axis,
start, states and initial values) is used as given.

`SourceBody.Solves` is independent of lowering and of every circuit. There
`D_t(x)` is the value of `x`'s declared derivative port, and that value is
required to be the derivative of `x` on the forward domain
(`Solves.derivative_denotes`). A chain of `k + 1` derivatives denotes the
`k + 1`-th derivative of `x` on the forward domain, and a declared velocity's
initial value is the initial derivative (`Solves.chain_denotes`,
`Solves.initial_iterated`). Integrals, and derivatives of anything but a chain,
are read along the whole trajectory (`SourceBody.atoms`): an integral is the
antiderivative from the declared start, never a totalized integral. A declared
integral state is not read into `Solves`; in every solution it equals that
reading of its integral (`Solves.integral_state`). The main
results are `Lowered.solves_iff` and the composed
`SourceContinuousModel.solves_iff_realizes`. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- An explicit named assignment. Its right-hand side may contain applied
lambdas, but no derivative. -/
structure SourceAssignment where
  output : Port
  rhs : Term
  deriving Repr, DecidableEq

/-- An implicit equation `lhs = rhs` with one derivative atom, or one chain over
declared velocities, defining the derivative port `output` (of the top state,
for a chain). A `StateBinding` names `output.id` as its state's derivative. -/
structure DifferentialEquation where
  output : Port
  lhs : Term
  rhs : Term
  deriving Repr, DecidableEq

/-- `output : D_axis(state) = velocity` declares the state named `velocity` as
the first derivative of the state named `state`, whose derivative port is
`output`. It is the only way to write a higher-order chain: `D_t(D_t(state))`
then reads as `D_t(velocity)`. -/
structure VelocityDeclaration where
  output : Port
  axis : String
  state : String
  velocity : String
  deriving Repr, DecidableEq

/-- A velocity declaration is the first-order equation it states. -/
def VelocityDeclaration.equation (v : VelocityDeclaration) : DifferentialEquation :=
  ⟨v.output, .derivative v.axis (.var v.state), .var v.velocity⟩

/-- `output : state = I_axis(integrand)` declares the state named `state`, whose
derivative port is `output`, as the integral of `integrand` from the declared
start. It is read as `D_t(state) = integrand`; lowering requires the declared
initial value `0`, under which that is `state = I_axis(integrand)`. It is the
only way to keep an integral that no inverse rewrite removes: `I_axis(integrand)`
then reads as `state` wherever it occurs at an atom position. -/
structure IntegralDeclaration where
  output : Port
  axis : String
  state : String
  integrand : Term
  deriving Repr, DecidableEq

/-- An integral declaration is read as the first-order equation
`D_axis(state) = integrand`; with the initial value `0` this is `state =
I_axis(integrand)` along the trajectory (`primitiveFrom_iff`). -/
def IntegralDeclaration.equation (d : IntegralDeclaration) : DifferentialEquation :=
  ⟨d.output, .derivative d.axis (.var d.state), d.integrand⟩

structure SourceBody where
  inputs : List Port
  assignments : List SourceAssignment
  differentials : List DifferentialEquation := []
  velocities : List VelocityDeclaration := []
  integrals : List IntegralDeclaration := []
  parameters : List RationalBinding := []
  observations : List Observation := []
  deriving Repr, DecidableEq

/-- Differential equations, then the equations of the velocity declarations,
then those of the integral declarations. -/
def SourceBody.equations (sb : SourceBody) : List DifferentialEquation :=
  sb.differentials ++ sb.velocities.map VelocityDeclaration.equation ++
    sb.integrals.map IntegralDeclaration.equation

/-- Assignment outputs, then differential, velocity and integral declaration
outputs, in declaration order. -/
def SourceBody.outputs (sb : SourceBody) : List Port :=
  sb.assignments.map (·.output) ++ sb.equations.map (·.output)

/-- The body with the same interface and the given explicit assignments. -/
def SourceBody.withAssignments (sb : SourceBody) (as : List Assignment) : Body where
  program := ⟨sb.inputs, as⟩
  parameters := sb.parameters
  observations := sb.observations

/-- The display name of the port with a stable ID, found as `Body.value` does. -/
def SourceBody.portName (sb : SourceBody) (id : String) : Option String :=
  ((sb.inputs ++ sb.outputs).find? (·.id == id)).map Port.name

/-- The coordinate of the first state port named `x`. -/
def SourceBody.coordinate (sb : SourceBody) (e : Evolution) (x : String) :
    Option (Fin e.states.length) :=
  (sb.inputs.find? (fun p => p.name == x && p.role == .state)).bind (index e.stateIds ·.id)

/-- A name is an input when it is read from a state coordinate or a bound
parameter. The initial value of `x` is declared when the first source input
named `x` is a state. -/
def SourceBody.stateBoundary (sb : SourceBody) (e : Evolution) : Boundary where
  input name := ((sb.withAssignments []).seed e.stateIds name).isSome
  initial x := (sb.inputs.find? (·.name == x)).bind fun p =>
    if p.role == .state then (index e.stateIds p.id).bind fun i =>
      e.initialValue e.states[i].initialId
    else none

/-- `stateBoundary`, with the integral declarations the rewrites read: `I_t(X)`
is the state of the first declaration of `X` on the evolution axis whose
integrand is a polynomial in inputs and whose state's declared initial value is
`0`. Lowering rejects every other declaration. -/
def SourceBody.boundary (sb : SourceBody) (e : Evolution) : Boundary :=
  { sb.stateBoundary e with
    integral := fun X => (sb.integrals.find? fun d =>
      d.axis == e.axis.name && d.integrand == X && X.continuous (sb.stateBoundary e) &&
        (sb.stateBoundary e).initial d.state == some 0).map (·.state) }

/-- `x` names a state port; its derivative port is the one its binding names,
and its velocity the one its first velocity declaration on the evolution axis
names. -/
def SourceBody.context (sb : SourceBody) (e : Evolution) : Context where
  axis := e.axis.name
  locate state := do
    let p ← sb.inputs.find? (fun p => p.name == state && p.role == .state)
    let i ← index e.stateIds p.id
    sb.portName (e.derivativeIds i)
  velocity state :=
    (sb.velocities.find? (fun v => v.state == state && v.axis == e.axis.name)).map (·.velocity)
  boundary := some (sb.boundary e)

/-! ## Source semantics -/

/-- Every original equation, explicit and differential, with defined outputs;
`atoms` reads integrals and derivatives of non-chains. -/
def SourceBody.Equations (sb : SourceBody) (c : Context) (atoms : Term → Option ℝ)
    (env : String → Option ℝ) : Prop :=
  (∀ a ∈ sb.assignments, env a.output.name ≠ none ∧
    a.rhs.eval env (c.rates env) atoms = env a.output.name) ∧
  (∀ d ∈ sb.equations, env d.output.name ≠ none ∧
    ∃ v, d.lhs.eval env (c.rates env) atoms = some v ∧
      d.rhs.eval env (c.rates env) atoms = some v)

noncomputable def SourceBody.inputEnvironment {n : Nat} (sb : SourceBody)
    (ids : Fin n → String) (x : Point n) : String → Option ℝ :=
  (sb.withAssignments []).inputEnvironment ids x

def SourceBody.Source {n : Nat} (sb : SourceBody) (c : Context) (atoms : Term → Option ℝ)
    (ids : Fin n → String) (x : Point n) (env : String → Option ℝ) : Prop :=
  Agrees (sb.inputEnvironment ids x) env ∧ sb.Equations c atoms env

def SourceBody.value {α : Type} (sb : SourceBody) (env : String → Option α) (id : String) :
    Option α :=
  ((sb.inputs ++ sb.outputs).find? (·.id == id)).bind (fun p => env p.name)

theorem SourceBody.value_eq {α : Type} (sb : SourceBody) (env : String → Option α)
    (id : String) : sb.value env id = (sb.portName id).bind env := by
  unfold SourceBody.value SourceBody.portName
  cases (sb.inputs ++ sb.outputs).find? (·.id == id) <;> rfl

/-- A chain of `k` evolution derivatives of `x`, admitted by the same declared
velocities as `Context.rates`, read as the `k`-th derivative of `x` at `t`. -/
noncomputable def SourceBody.classicalRates (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) (t : ℝ) : List String → String → Option ℝ :=
  fun axes x => if axes ≠ [] ∧ axes.all (· == (sb.context e).axis) then
    (((sb.context e).lift (axes.length - 1) x).bind (sb.context e).locate).bind fun _ =>
      (sb.coordinate e x).map fun i =>
        iteratedDerivWithin axes.length (fun s => state s i) e.time.domain t
  else none

/-- The signal as the source reads it along the forward domain: inputs by name,
and chains as actual iterated derivatives. Only states and bound parameters are
read, so an integrand naming an auxiliary or a derivative port has no value here;
lowering rejects such integrands. -/
noncomputable def SourceBody.trajectory (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) : Trajectory where
  axis := e.axis.name
  start := e.time.start
  base s := sb.inputEnvironment e.stateIds (state s)
  rates s := sb.classicalRates e state s

/-- Integrals, and derivatives of non-chains, read at `t` along the signal. -/
noncomputable def SourceBody.atoms (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) (t : ℝ) : Term → Option ℝ :=
  (sb.trajectory e state).atoms t

/-- Initial conditions and the original source equations on the forward domain,
with each derivative atom read from the state's actual derivative, and each
integral and derivative of a non-chain read along the signal. -/
def SourceBody.Solves (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) : Prop :=
  (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
    some (state e.time.start i)) ∧
  ∀ t ∈ e.time.domain, ∃ env, sb.Source (sb.context e) (sb.atoms e state t) e.stateIds
    (state t) env ∧
    ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t

/-- In a solution, `D_t(x)` denotes the derivative of the state coordinate
whose stable ID is the ID of the state port named `x`. -/
theorem SourceBody.Solves.derivative_denotes {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} {t : ℝ} {env : String → Option ℝ}
    (rates : ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t)
    (x : String) (r : ℝ) (h : (sb.context e).rates env [e.axis.name] x = some r) :
    ∃ p i, sb.inputs.find? (fun p => p.name == x && p.role == .state) = some p ∧
      e.stateIds i = p.id ∧ HasDerivWithinAt (fun t => state t i) r e.time.domain t := by
  simp only [Context.rates, context, Context.lift, ne_eq, List.cons_ne_nil,
    not_false_eq_true, List.all_cons, beq_self_eq_true, List.all_nil, Bool.and_self, and_self,
    if_true, List.length_cons, List.length_nil, Nat.sub_self, Option.bind_some] at h
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

/-- The same fact stated from a solution: at every time in the domain, the
environment that witnesses the source equations reads each atom `D_t(x)` as the
derivative of the state named `x`. -/
theorem SourceBody.Solves.derivative_at {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state) {t : ℝ}
    (ht : t ∈ e.time.domain) :
    ∃ env, sb.Source (sb.context e) (sb.atoms e state t) e.stateIds (state t) env ∧
      ∀ x r, (sb.context e).rates env [e.axis.name] x = some r →
        ∃ p i, sb.inputs.find? (fun p => p.name == x && p.role == .state) = some p ∧
          e.stateIds i = p.id ∧ HasDerivWithinAt (fun t => state t i) r e.time.domain t := by
  obtain ⟨env, source, rates⟩ := h.2 t ht
  exact ⟨env, source, fun x r hr => derivative_denotes rates x r hr⟩

/-! ## Higher-order chains

A chain is read through declared velocities (`Context.rates`). In a solution
each velocity equation `D_t(x) = v` makes the coordinate of `v` the actual
derivative of the coordinate of `x`, so a chain of `k + 1` derivatives of `x`
denotes the derivative of the `k`-th iterated derivative of `x` on the forward
domain, and the declared initial value of the state `k` velocities above `x`
is the `k`-th derivative of `x` at the start. -/

/-- Every declared velocity names an input port, the first of its name, and
that port is a state. -/
def SourceBody.VelocityStates (sb : SourceBody) : Prop :=
  ∀ v ∈ sb.velocities, (sb.inputs.find? (·.name == v.velocity)).any (·.role == .state) = true

instance : DecidablePred SourceBody.VelocityStates := fun sb =>
  inferInstanceAs (Decidable (∀ v ∈ sb.velocities,
    (sb.inputs.find? (·.name == v.velocity)).any (·.role == .state) = true))

theorem SourceBody.context_locate (sb : SourceBody) (e : Evolution) (x : String) :
    (sb.context e).locate x =
      (sb.coordinate e x).bind (fun i => sb.portName (e.derivativeIds i)) := by
  simp only [context, coordinate, Option.bind_eq_bind, Option.bind_assoc]

private theorem find?_and {α : Type} {p q : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) (hq : q a = true) :
    l.find? (fun x => p x && q x) = some a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
      by_cases hb : p b = true
      · rw [List.find?_cons_of_pos hb] at h
        cases h
        exact List.find?_cons_of_pos (by simp [hb, hq])
      · rw [List.find?_cons_of_neg hb] at h
        rw [List.find?_cons_of_neg (by simp [hb])]
        exact ih h

private theorem role_beq {r q : PortRole} : (r == q) = true ↔ r = q := by
  cases r <;> cases q <;> decide

/-- The first velocity declaration of `x` is one of the declarations. -/
private theorem velocity_declared {sb : SourceBody} {e : Evolution} {x y : String}
    (h : (sb.context e).velocity x = some y) :
    ∃ d ∈ sb.velocities, d.state = x ∧ d.velocity = y := by
  simp only [SourceBody.context, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  have named := List.find?_some hd
  simp only [Bool.and_eq_true, beq_iff_eq] at named
  exact ⟨d, List.mem_of_find?_eq_some hd, named.1, rfl⟩

/-- A velocity equation holds in every environment satisfying the source: the
derivative port of `x` and the velocity carry the same value. -/
theorem SourceBody.velocity_equation {sb : SourceBody} {e : Evolution}
    {atoms : Term → Option ℝ} {env : String → Option ℝ}
    (equations : sb.Equations (sb.context e) atoms env) {x y : String}
    (h : (sb.context e).velocity x = some y) :
    ∃ w, ((sb.context e).locate x).bind env = some w ∧ env y = some w := by
  obtain ⟨d, hd, rfl, rfl⟩ := velocity_declared h
  have mem : d.equation ∈ sb.equations :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hd))
  obtain ⟨_, w, hl, hr⟩ := equations.2 _ mem
  refine ⟨w, ?_, hr⟩
  simp only [VelocityDeclaration.equation, Term.eval, Term.chain, Context.rates] at hl
  split_ifs at hl
  · simpa [Context.lift] using hl

/-- A declared velocity reads its own state coordinate. -/
theorem SourceBody.velocity_value {sb : SourceBody} {e : Evolution} {x0 : Point e.states.length}
    {env : String → Option ℝ} (states : sb.VelocityStates)
    (agrees : Agrees (sb.inputEnvironment e.stateIds x0) env) {x y : String}
    (h : (sb.context e).velocity x = some y) {j : Fin e.states.length}
    (hj : sb.coordinate e y = some j) : env y = some (x0 j) := by
  obtain ⟨d, hd, -, rfl⟩ := velocity_declared h
  have hs := states d hd
  cases hp : sb.inputs.find? (·.name == d.velocity) with
  | none => simp [hp] at hs
  | some p =>
    have role : p.role = .state := role_beq.mp (by simpa [hp] using hs)
    have named := find?_and (q := fun p => p.role == .state) hp (role_beq.mpr role)
    have index_eq : index e.stateIds p.id = some j := by
      simpa [coordinate, named] using hj
    apply agrees
    have notParameter : (p.role == .parameter) = false := by rw [role]; decide
    simp [SourceBody.inputEnvironment, SourceBody.withAssignments, Body.inputEnvironment,
      hp, Body.inputValue, notParameter, index_eq]

private theorem lift_succ {c : Context} :
    ∀ (k : Nat) (x y : String), c.lift (k + 1) x = some y → ∃ z, c.velocity x = some z
  | 0, x, y, h => ⟨y, by simpa [Context.lift] using h⟩
  | k + 1, x, y, h => by
      simp only [Context.lift] at h
      cases hk : c.lift k x with
      | none => simp [hk] at h
      | some w =>
        cases hw : c.velocity w with
        | none => simp [hk, hw] at h
        | some u =>
          exact lift_succ k x u (by simp [Context.lift, hk, hw])

private theorem start_mem (e : Evolution) : e.time.start ∈ e.time.domain :=
  Set.self_mem_Ici

/-- A located derivative port has a coordinate. -/
private theorem coordinate_of_locate {sb : SourceBody} {e : Evolution} {x port : String}
    (h : (sb.context e).locate x = some port) :
    ∃ j, sb.coordinate e x = some j ∧ sb.portName (e.derivativeIds j) = some port := by
  rw [SourceBody.context_locate] at h
  cases hx : sb.coordinate e x with
  | none => simp [hx] at h
  | some j => exact ⟨j, rfl, by simpa [hx] using h⟩

/-- In a solution, climbing `k` declared velocities from `x` reaches the `k`-th
derivative of `x` on the whole forward domain. -/
theorem SourceBody.Solves.lift_eqOn {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state)
    (states : sb.VelocityStates) (k : Nat) {x y : String} {i j : Fin e.states.length}
    (hy : (sb.context e).lift k x = some y) (hi : sb.coordinate e x = some i)
    (hj : sb.coordinate e y = some j) :
    Set.EqOn (iteratedDerivWithin k (fun s => state s i) e.time.domain)
      (fun s => state s j) e.time.domain := by
  induction k generalizing y j with
  | zero =>
      simp only [Context.lift, Option.some.injEq] at hy
      subst hy
      rw [hi, Option.some.injEq] at hj
      subst hj
      simp only [iteratedDerivWithin_zero]
      exact Set.eqOn_refl _ _
  | succ k ih =>
      simp only [Context.lift] at hy
      cases hz : (sb.context e).lift k x with
      | none => simp [hz] at hy
      | some z =>
        rw [hz, Option.bind_some] at hy
        obtain ⟨env0, source0, -⟩ := h.2 _ (start_mem e)
        obtain ⟨w0, hl0, -⟩ := SourceBody.velocity_equation source0.2 hy
        cases hloc : (sb.context e).locate z with
        | none => simp [hloc] at hl0
        | some port =>
          obtain ⟨jz, hjz, hport⟩ := coordinate_of_locate hloc
          have eq := ih hz hjz
          intro s hs
          rw [iteratedDerivWithin_succ, derivWithin_congr eq (eq hs)]
          obtain ⟨env, source, rates⟩ := h.2 s hs
          obtain ⟨rate, hv, hd⟩ := rates jz
          obtain ⟨w, hl, hw⟩ := SourceBody.velocity_equation source.2 hy
          have hvel := SourceBody.velocity_value states source.1 hy hj
          rw [SourceBody.value_eq, hport, Option.bind_some] at hv
          rw [hloc, Option.bind_some, hv, Option.some.injEq] at hl
          rw [hvel, Option.some.injEq] at hw
          rw [hd.derivWithin (uniqueDiffOn_Ici _ s hs), hl]
          exact hw.symm

/-- The declared initial value of the state `k` velocities above `x` is the
`k`-th derivative of `x` at the start. -/
theorem SourceBody.Solves.initial_iterated {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state)
    (states : sb.VelocityStates) (k : Nat) {x y : String} {i j : Fin e.states.length}
    (hy : (sb.context e).lift k x = some y) (hi : sb.coordinate e x = some i)
    (hj : sb.coordinate e y = some j) :
    (e.initialValue e.states[j].initialId).map (fun q : ℚ => (q : ℝ)) =
      some (iteratedDerivWithin k (fun s => state s i) e.time.domain e.time.start) := by
  rw [h.1 j, h.lift_eqOn states k hy hi hj (start_mem e)]

/-- In a solution, a chain of `n` derivatives of `x` denotes the derivative of
the `n - 1`-th iterated derivative of `x`, within the forward domain, for every
environment witnessing the source equations at `t`. -/
theorem SourceBody.Solves.chain_denotes {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state)
    (states : sb.VelocityStates) {t : ℝ} (ht : t ∈ e.time.domain) {env : String → Option ℝ}
    (source : sb.Source (sb.context e) (sb.atoms e state t) e.stateIds (state t) env)
    (rates : ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t)
    (axes : List String) (x : String) (r : ℝ)
    (hr : (sb.context e).rates env axes x = some r) :
    ∃ i, sb.coordinate e x = some i ∧
      HasDerivWithinAt (iteratedDerivWithin (axes.length - 1) (fun s => state s i)
        e.time.domain) r e.time.domain t := by
  simp only [Context.rates] at hr
  split_ifs at hr
  cases hy : (sb.context e).lift (axes.length - 1) x with
  | none => simp [hy] at hr
  | some y =>
    cases hloc : (sb.context e).locate y with
    | none => simp [hy, hloc] at hr
    | some port =>
      simp only [hy, hloc, Option.bind_some] at hr
      obtain ⟨j, hj, hport⟩ := coordinate_of_locate hloc
      have hi : ∃ i, sb.coordinate e x = some i := by
        cases hk : axes.length - 1 with
        | zero =>
            rw [hk] at hy
            simp only [Context.lift, Option.some.injEq] at hy
            exact ⟨j, hy ▸ hj⟩
        | succ k =>
            rw [hk] at hy
            obtain ⟨z, hz⟩ := lift_succ k x y hy
            obtain ⟨w, hl, -⟩ := SourceBody.velocity_equation source.2 hz
            cases hx : (sb.context e).locate x with
            | none => simp [hx] at hl
            | some px =>
              obtain ⟨i, hi, -⟩ := coordinate_of_locate hx
              exact ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hi
      refine ⟨i, hi, ?_⟩
      obtain ⟨rate, hv, hd⟩ := rates j
      rw [SourceBody.value_eq, hport, Option.bind_some, hr, Option.some.injEq] at hv
      subst hv
      exact hd.congr_of_mem (fun s hs => h.lift_eqOn states _ hy hi hj hs) ht

/-- The same fact stated from a solution, as `Solves.derivative_at` is. -/
theorem SourceBody.Solves.chain_at {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state)
    (states : sb.VelocityStates) {t : ℝ} (ht : t ∈ e.time.domain) :
    ∃ env, sb.Source (sb.context e) (sb.atoms e state t) e.stateIds (state t) env ∧
      ∀ axes x r, (sb.context e).rates env axes x = some r →
        ∃ i, sb.coordinate e x = some i ∧
          HasDerivWithinAt (iteratedDerivWithin (axes.length - 1) (fun s => state s i)
            e.time.domain) r e.time.domain t := by
  obtain ⟨env, source, rates⟩ := h.2 t ht
  exact ⟨env, source, fun axes x r hr => h.chain_denotes states ht source rates axes x r hr⟩

/-! ## The classical reading

`SourceBody.Solves` reads an atom through derivative ports and pins each port
to the actual derivative. `SolvesClassical` reads every chain of `k` evolution
derivatives of `x` directly as `iteratedDerivWithin k x` on the forward domain,
with no velocity value in between; the declared velocities only decide which
chains are in the fragment, exactly as in `Context.rates`. The two relations
coincide (`Solves_iff_classical`). -/

/-- The source equations under an arbitrary reading of derivative chains. -/
def SourceBody.EquationsUnder (sb : SourceBody) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) (env : String → Option ℝ) : Prop :=
  (∀ a ∈ sb.assignments, env a.output.name ≠ none ∧
    a.rhs.eval env rates atoms = env a.output.name) ∧
  (∀ d ∈ sb.equations, env d.output.name ≠ none ∧
    ∃ v, d.lhs.eval env rates atoms = some v ∧ d.rhs.eval env rates atoms = some v)

theorem SourceBody.equations_eq (sb : SourceBody) (c : Context) (atoms : Term → Option ℝ)
    (env : String → Option ℝ) :
    sb.Equations c atoms env = sb.EquationsUnder (c.rates env) atoms env :=
  rfl

/-- At `t`, `env` extends the inputs and every derivative port carries the
actual derivative of its differentiable state. -/
def SourceBody.PortsAt (sb : SourceBody) (e : Evolution) (state : Dynamics.Signal e.states.length)
    (t : ℝ) (env : String → Option ℝ) : Prop :=
  Agrees (sb.inputEnvironment e.stateIds (state t)) env ∧
    ∀ i, DifferentiableWithinAt ℝ (fun s => state s i) e.time.domain t ∧
      sb.value env (e.derivativeIds i) = some (derivWithin (fun s => state s i) e.time.domain t)

/-- The original equations with every chain read as an actual iterated
derivative, the initial conditions, and actual derivatives in the ports. -/
def SourceBody.SolvesClassical (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) : Prop :=
  (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
    some (state e.time.start i)) ∧
  ∀ t ∈ e.time.domain, ∃ env, sb.PortsAt e state t env ∧
    sb.EquationsUnder (sb.classicalRates e state t) (sb.atoms e state t) env

/-- The velocity equations under a reading. -/
private def velocityEquations (sb : SourceBody) (rates : List String → String → Option ℝ)
    (env : String → Option ℝ) : Prop :=
  ∀ d ∈ sb.velocities, ∃ w, rates [d.axis] d.state = some w ∧ env d.velocity = some w

private theorem velocityEquations_of {sb : SourceBody} {rates : List String → String → Option ℝ}
    {atoms : Term → Option ℝ} {env : String → Option ℝ} (h : sb.EquationsUnder rates atoms env) :
    velocityEquations sb rates env := by
  intro d hd
  obtain ⟨_, w, hl, hr⟩ :=
    h.2 _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hd)))
  exact ⟨w, by simpa [VelocityDeclaration.equation, Term.eval, Term.chain] using hl, hr⟩

/-- On first-order atoms the two readings agree wherever the ports are actual. -/
private theorem rates_single {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} {t : ℝ} {env : String → Option ℝ}
    (ports : sb.PortsAt e state t env) (a z : String) :
    (sb.context e).rates env [a] z = sb.classicalRates e state t [a] z := by
  simp only [Context.rates, SourceBody.classicalRates]
  split_ifs with hc
  · simp only [List.length_singleton, Nat.sub_self, Context.lift, Option.bind_some]
    cases hl : (sb.context e).locate z with
    | none => simp
    | some port =>
      obtain ⟨j, hj, hport⟩ := coordinate_of_locate hl
      have hv := (ports.2 j).2
      rw [SourceBody.value_eq, hport, Option.bind_some] at hv
      simp [hv, hj, iteratedDerivWithin_one]
  · rfl

/-- Port values that are actual derivatives make `env` read ports as actual. -/
private theorem ports_of {sb : SourceBody} {e : Evolution} {state : Dynamics.Signal e.states.length}
    {t : ℝ} (ht : t ∈ e.time.domain) {env : String → Option ℝ}
    (agrees : Agrees (sb.inputEnvironment e.stateIds (state t)) env)
    (rates : ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t) :
    sb.PortsAt e state t env := by
  refine ⟨agrees, fun i => ?_⟩
  obtain ⟨rate, hv, hd⟩ := rates i
  exact ⟨hd.differentiableWithinAt, by rw [hv, hd.derivWithin (uniqueDiffOn_Ici _ t ht)]⟩

/-! ## Integrals along a signal

The inverse rewrites of `Model.Integral` are exact wherever the atoms are read
along a regular trajectory, at a time where the ports are actual derivatives.
Every signal with differentiable states and its declared initial values is
regular, so both a source solution and a lowered solution discharge the premise
at every time. -/

private theorem seed_shape {b : Body} {n : Nat} {ids : Fin n → String} {name : String}
    {expr : Expr n} (h : b.seed ids name = some expr) :
    (∃ q, expr = .constant q) ∨ ∃ i, expr = .var i := by
  simp only [Body.seed, Body.inputTerm, Option.bind_eq_some_iff] at h
  obtain ⟨p, -, hp⟩ := h
  split at hp
  · obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact .inl ⟨q, rfl⟩
  · obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact .inr ⟨i, rfl⟩

/-- The first input named `x` is the state port the context locates. -/
private theorem initial_coordinate {sb : SourceBody} {e : Evolution} {x : String} {q : ℚ}
    (h : (sb.boundary e).initial x = some q) :
    ∃ i, sb.coordinate e x = some i ∧ e.initialValue e.states[i].initialId = some q ∧
      ∀ y : Point e.states.length, sb.inputEnvironment e.stateIds y x = some (y i) := by
  simp only [SourceBody.boundary, SourceBody.stateBoundary, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, hq⟩ := h
  split at hq
  · rename_i role
    obtain ⟨i, hi, hv⟩ := Option.bind_eq_some_iff.mp hq
    have role' : p.role = .state := role_beq.mp role
    refine ⟨i, ?_, hv, fun y => ?_⟩
    · have := find?_and (q := fun p => p.role == .state) hp role
      simp [SourceBody.coordinate, this, hi]
    · have notParameter : (p.role == .parameter) = false := by rw [role']; decide
      simp [SourceBody.inputEnvironment, SourceBody.withAssignments, Body.inputEnvironment, hp,
        Body.inputValue, notParameter, hi]
  · simp at hq

/-- A located state is read as its coordinate's derivative by the classical chains. -/
private theorem classical_single {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} {y port : String}
    (hl : (sb.context e).locate y = some port) {j : Fin e.states.length}
    (hj : sb.coordinate e y = some j) (s : ℝ) :
    sb.classicalRates e state s [(sb.context e).axis] y =
      some (derivWithin (fun s => state s j) e.time.domain s) := by
  simp [SourceBody.classicalRates, Context.lift, hl, hj, iteratedDerivWithin_one]

/-- An input is read from a state coordinate or a constant. -/
private theorem input_value {sb : SourceBody} {e : Evolution} {n : String}
    (h : (sb.boundary e).input n = true) :
    ∃ expr : Expr e.states.length, ((∃ q, expr = .constant q) ∨ ∃ i, expr = .var i) ∧
      ∀ y, sb.inputEnvironment e.stateIds y n = some (expr.eval y) := by
  obtain ⟨expr, hexpr⟩ := Option.isSome_iff_exists.mp h
  refine ⟨expr, seed_shape hexpr, fun y => ?_⟩
  have := congrFun ((sb.withAssignments []).seed_correct e.stateIds y) n
  simp only [Evaluated, hexpr, Option.map_some] at this
  exact this.symm

/-- An integral state the boundary reads comes from a declaration on the
evolution axis, with a continuous integrand and the declared initial value `0`. -/
private theorem integral_declared {sb : SourceBody} {e : Evolution} {X : Term} {F : String}
    (h : (sb.boundary e).integral X = some F) :
    ∃ d ∈ sb.integrals, d.axis = e.axis.name ∧ d.integrand = X ∧ d.state = F ∧
      X.continuous (sb.boundary e) = true ∧ (sb.boundary e).initial F = some 0 := by
  simp only [SourceBody.boundary, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  have named := List.find?_some hd
  simp only [Bool.and_eq_true, beq_iff_eq] at named
  obtain ⟨⟨⟨haxis, hX⟩, hc⟩, hq⟩ := named
  exact ⟨d, List.mem_of_find?_eq_some hd, haxis, hX, rfl,
    (Term.continuous_congr (bd := sb.boundary e) (bd' := sb.stateBoundary e) rfl X).trans hc, hq⟩

/-- At every time of the forward domain, an environment that reads the signal
with actual ports satisfies each integral declaration `D_t(F) = X`. Every solution
of the source (`Solves.integralsAlong`) and of the lowered body
(`Lowered.integralsAlong`) has it. -/
def SourceBody.IntegralsAlong (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) : Prop :=
  ∀ s ∈ e.time.domain, ∃ env, sb.PortsAt e state s env ∧ ∀ d ∈ sb.integrals,
    ∃ v, d.equation.lhs.eval env ((sb.context e).rates env) (sb.atoms e state s) = some v ∧
      d.equation.rhs.eval env ((sb.context e).rates env) (sb.atoms e state s) = some v

/-- A signal with differentiable states, its declared initial values and its
integral declarations is a regular trajectory for the integral rewrites. -/
theorem SourceBody.regular {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length}
    (init : ∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
      some (state e.time.start i))
    (diff : ∀ s ∈ e.time.domain, ∀ i,
      DifferentiableWithinAt ℝ (fun s => state s i) e.time.domain s)
    (integrals : sb.IntegralsAlong e state) :
    (sb.trajectory e state).Regular (sb.context e) (sb.boundary e) where
  axis := rfl
  input n h := by
    obtain ⟨expr, shape, base⟩ := input_value h
    refine ⟨fun s => expr.eval (state s), ?_, fun s _ => base (state s)⟩
    rcases shape with ⟨q, rfl⟩ | ⟨i, rfl⟩
    · exact continuousOn_const
    · exact fun s hs => (diff s hs i).continuousWithinAt
  integral X F h := by
    obtain ⟨d, hd, haxis, rfl, rfl, hc, hq⟩ := integral_declared h
    obtain ⟨i, hi, hv, hbase⟩ := initial_coordinate hq
    have start := init i
    rw [hv, Option.map_some, Option.some.injEq] at start
    refine ⟨fun s => state s i, by exact_mod_cast start.symm, fun s hs => ⟨hbase (state s), ?_⟩⟩
    obtain ⟨env, ports, holds⟩ := integrals s hs
    obtain ⟨v, hl, hr⟩ := holds d hd
    have hax : (sb.context e).axis = e.axis.name := rfl
    have hl' : ((sb.context e).locate d.state).bind env = some v := by
      simpa [IntegralDeclaration.equation, Term.eval, Term.chain, Context.rates, Context.lift,
        haxis, hax] using hl
    cases hloc : (sb.context e).locate d.state with
    | none => simp [hloc] at hl'
    | some port =>
      obtain ⟨j, hj, hport⟩ := coordinate_of_locate hloc
      rw [hi, Option.some.injEq] at hj
      subst hj
      have hval := (ports.2 i).2
      rw [SourceBody.value_eq, hport, Option.bind_some] at hval
      rw [hloc, Option.bind_some, hval, Option.some.injEq] at hl'
      refine ⟨v, ?_, hl' ▸ (ports.2 i).1.hasDerivWithinAt⟩
      rw [← Term.continuous_agrees_at hc (fun n hn => by
        obtain ⟨expr, -, base⟩ := input_value hn
        simp [SourceBody.trajectory, base]) ports.1 ((sb.context e).rates env) (sb.atoms e state s)]
      exact hr
  rate y h := by
    obtain ⟨port, hl⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨j, hj, -⟩ := coordinate_of_locate hl
    exact ⟨fun s => state s j, fun s hs => ⟨diff s hs j, classical_single hl hj s⟩⟩
  initial x q h hq := by
    obtain ⟨port, hl⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨i, hi, hv, hbase⟩ := initial_coordinate hq
    have start := init i
    rw [hv, Option.map_some, Option.some.injEq] at start
    exact ⟨fun s => state s i, start.symm, fun s hs =>
      ⟨diff s hs i, hbase (state s), classical_single hl hi s⟩⟩

/-- Where the ports carry actual derivatives, `env` reads the signal. -/
theorem SourceBody.at_of {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} {t : ℝ} (ht : t ∈ e.time.domain)
    {env : String → Option ℝ} (ports : sb.PortsAt e state t env) :
    (sb.trajectory e state).At (sb.context e) t env where
  mem := ht
  base := ports.1
  rate y _ := rates_single ports _ y

/-- The premise of the integral rewrites holds at every time of a signal with
differentiable states, its declared initial values, its integral declarations
and actual ports. -/
theorem SourceBody.cancels_at {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length}
    (init : ∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
      some (state e.time.start i))
    (diff : ∀ s ∈ e.time.domain, ∀ i,
      DifferentiableWithinAt ℝ (fun s => state s i) e.time.domain s)
    (integrals : sb.IntegralsAlong e state)
    {t : ℝ} (ht : t ∈ e.time.domain) {env : String → Option ℝ}
    (ports : sb.PortsAt e state t env) : (sb.context e).Cancels (sb.atoms e state t) env :=
  Context.cancels rfl (sb.regular init diff integrals) (sb.at_of ht ports)

/-- An integral declaration is one of the source equations. -/
private theorem integral_mem {sb : SourceBody} {d : IntegralDeclaration} (hd : d ∈ sb.integrals) :
    d.equation ∈ sb.equations :=
  List.mem_append_right _ (List.mem_map_of_mem hd)

/-- Every solution of the source satisfies its integral declarations along the signal. -/
theorem SourceBody.Solves.integralsAlong {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state) :
    sb.IntegralsAlong e state := by
  intro s hs
  obtain ⟨env, source, rates⟩ := h.2 s hs
  exact ⟨env, ports_of hs source.1 rates, fun d hd => (source.2.2 _ (integral_mem hd)).2⟩

/-- At `s`, each declared velocity is the actual derivative of its state. -/
private def velocityHolds (sb : SourceBody) (e : Evolution)
    (state : Dynamics.Signal e.states.length) (s : ℝ) : Prop :=
  ∀ z y, (sb.context e).velocity z = some y → ∃ jz, sb.coordinate e z = some jz ∧
    ∀ jy, sb.coordinate e y = some jy →
      state s jy = derivWithin (fun s => state s jz) e.time.domain s

private theorem velocityHolds_of {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} {s : ℝ} {env : String → Option ℝ}
    (states : sb.VelocityStates) (ports : sb.PortsAt e state s env)
    (h : velocityEquations sb ((sb.context e).rates env) env) : velocityHolds sb e state s := by
  intro z y hzy
  obtain ⟨d, hd, rfl, rfl⟩ := velocity_declared hzy
  obtain ⟨w, hl, hw⟩ := h d hd
  simp only [Context.rates] at hl
  split_ifs at hl
  simp only [List.length_singleton, Nat.sub_self, Context.lift, Option.bind_some] at hl
  cases hloc : (sb.context e).locate d.state with
  | none => simp [hloc] at hl
  | some port =>
    obtain ⟨jz, hjz, hport⟩ := coordinate_of_locate hloc
    refine ⟨jz, hjz, fun jy hjy => ?_⟩
    have hvel := SourceBody.velocity_value states ports.1 hzy hjy
    have hv := (ports.2 jz).2
    rw [SourceBody.value_eq, hport, Option.bind_some] at hv
    rw [hloc, Option.bind_some, hv, Option.some.injEq] at hl
    rw [hvel, Option.some.injEq] at hw
    rw [hw, hl]

private theorem eqOn_of_holds {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length}
    (holds : ∀ s ∈ e.time.domain, velocityHolds sb e state s) (k : Nat) {x y : String}
    {i j : Fin e.states.length} (hy : (sb.context e).lift k x = some y)
    (hi : sb.coordinate e x = some i) (hj : sb.coordinate e y = some j) :
    Set.EqOn (iteratedDerivWithin k (fun s => state s i) e.time.domain)
      (fun s => state s j) e.time.domain := by
  induction k generalizing y j with
  | zero =>
      simp only [Context.lift, Option.some.injEq] at hy
      subst hy
      rw [hi, Option.some.injEq] at hj
      subst hj
      simp only [iteratedDerivWithin_zero]
      exact Set.eqOn_refl _ _
  | succ k ih =>
      simp only [Context.lift] at hy
      cases hz : (sb.context e).lift k x with
      | none => simp [hz] at hy
      | some z =>
        rw [hz, Option.bind_some] at hy
        obtain ⟨jz, hjz, -⟩ := holds _ (start_mem e) z y hy
        have eq := ih hz hjz
        intro s hs
        obtain ⟨jz', hjz', hval⟩ := holds s hs z y hy
        rw [hjz, Option.some.injEq] at hjz'
        subst hjz'
        rw [iteratedDerivWithin_succ, derivWithin_congr eq (eq hs)]
        exact (hval j hj).symm

/-- Where each velocity is the actual derivative at every time, the port
reading and the classical reading of every chain coincide at `t`. -/
private theorem rates_eq_classical {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length}
    (holds : ∀ s ∈ e.time.domain, velocityHolds sb e state s) {t : ℝ} (ht : t ∈ e.time.domain)
    {env : String → Option ℝ} (ports : sb.PortsAt e state t env) :
    (sb.context e).rates env = sb.classicalRates e state t := by
  funext axes x
  simp only [Context.rates, SourceBody.classicalRates]
  split_ifs with hc
  · cases hy : (sb.context e).lift (axes.length - 1) x with
    | none => simp
    | some y =>
      cases hloc : (sb.context e).locate y with
      | none => simp [hloc]
      | some port =>
        simp only [hloc, Option.bind_some]
        obtain ⟨j, hj, hport⟩ := coordinate_of_locate hloc
        have hv := (ports.2 j).2
        rw [SourceBody.value_eq, hport, Option.bind_some] at hv
        have hi : ∃ i, sb.coordinate e x = some i := by
          cases hk : axes.length - 1 with
          | zero =>
              rw [hk] at hy
              simp only [Context.lift, Option.some.injEq] at hy
              exact ⟨j, hy ▸ hj⟩
          | succ k =>
              rw [hk] at hy
              obtain ⟨z, hz⟩ := lift_succ k x y hy
              obtain ⟨i, hi, -⟩ := holds t ht x z hz
              exact ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hi
        have eq := eqOn_of_holds holds _ hy hi hj
        have hlen : axes.length = axes.length - 1 + 1 := by
          have : axes.length ≠ 0 := by simpa using hc.1
          omega
        rw [hv, hi, Option.map_some, hlen, iteratedDerivWithin_succ,
          derivWithin_congr eq (eq ht)]
  · rfl

/-- The port reading of `Solves` and the classical reading of every chain as
an iterated derivative have the same solutions, with the same initial data. -/
theorem SourceBody.solves_iff_classical {sb : SourceBody} {e : Evolution}
    (states : sb.VelocityStates) (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ sb.SolvesClassical e state := by
  constructor
  · intro h
    have holds : ∀ s ∈ e.time.domain, velocityHolds sb e state s := by
      intro s hs
      obtain ⟨env, source, rates⟩ := h.2 s hs
      exact velocityHolds_of states (ports_of hs source.1 rates)
        (velocityEquations_of source.2)
    refine ⟨h.1, fun t ht => ?_⟩
    obtain ⟨env, source, rates⟩ := h.2 t ht
    have ports := ports_of ht source.1 rates
    refine ⟨env, ports, ?_⟩
    rw [← rates_eq_classical holds ht ports]
    exact source.2
  · intro h
    have holds : ∀ s ∈ e.time.domain, velocityHolds sb e state s := by
      intro s hs
      obtain ⟨env, ports, equations⟩ := h.2 s hs
      refine velocityHolds_of states ports (fun d hd => ?_)
      obtain ⟨w, hl, hw⟩ := velocityEquations_of equations d hd
      exact ⟨w, by rw [rates_single ports]; exact hl, hw⟩
    refine ⟨h.1, fun t ht => ?_⟩
    obtain ⟨env, ports, equations⟩ := h.2 t ht
    refine ⟨env, ⟨ports.1, ?_⟩, fun i => ?_⟩
    · rw [SourceBody.equations_eq, rates_eq_classical holds ht ports]
      exact equations
    · obtain ⟨hdiff, hv⟩ := ports.2 i
      exact ⟨_, hv, hdiff.hasDerivWithinAt⟩

/-! ## Velocity equations as a premise

A lower-order atom `D_t(x)` beside a declared chain is read as the declared
velocity `v` of `x` (`Term.readVelocities`). That is exact only where the
velocity equation `D_t(x) = v` holds, so the per-equation correspondence of a
differential takes the velocity equations as a premise. Every velocity
declaration is itself a source equation, lowered with no premise, so the
premise is discharged for the whole system on both sides of `Lowered.equations`. -/

/-- Every velocity the context reads is declared in the body, on its axis. -/
def SourceBody.Declares (sb : SourceBody) (c : Context) : Prop :=
  ∀ x y, c.velocity x = some y →
    ∃ d ∈ sb.velocities, d.state = x ∧ d.velocity = y ∧ d.axis = c.axis

/-- The context of an evolution reads only the body's declarations on its axis;
`compileSourceContinuous` lowers with it. -/
theorem SourceBody.declares_context (sb : SourceBody) (e : Evolution) :
    sb.Declares (sb.context e) := by
  intro x y h
  simp only [SourceBody.context, Option.map_eq_some_iff] at h
  obtain ⟨d, hd, rfl⟩ := h
  have named := List.find?_some hd
  simp only [Bool.and_eq_true, beq_iff_eq] at named
  exact ⟨d, List.mem_of_find?_eq_some hd, named.1, rfl, named.2⟩

/-- The empty context reads no velocity; `compileSourcePolynomial` lowers with it. -/
theorem SourceBody.declares_empty (sb : SourceBody) : sb.Declares Context.empty := by
  intro x y h
  simp [Context.empty] at h

/-- The velocity equations of the source discharge the premise of
`Term.readVelocities_eval`. This is `SourceBody.velocity_equation` for any
context the body declares, taking only the velocity equations rather than all
of `SourceBody.Equations`, so the lowered side can supply them too. -/
theorem SourceBody.velocitiesHold {sb : SourceBody} {c : Context} (declares : sb.Declares c)
    {atoms : Term → Option ℝ} {env : String → Option ℝ}
    (h : ∀ d ∈ sb.velocities, env d.equation.output.name ≠ none ∧
      ∃ v, d.equation.lhs.eval env (c.rates env) atoms = some v ∧
        d.equation.rhs.eval env (c.rates env) atoms = some v) :
    c.VelocitiesHold env := by
  intro x y hxy
  obtain ⟨d, hd, rfl, rfl, haxis⟩ := declares x y hxy
  obtain ⟨-, w, hl, hr⟩ := h d hd
  simp only [VelocityDeclaration.equation, Term.eval, Term.chain, Context.rates, haxis] at hl hr
  simp [Context.lift] at hl
  rw [hl, hr]

/-! ## Lowering -/

/-- Every integral declaration is the one the context reads for its integrand. -/
def SourceBody.IntegralStates (sb : SourceBody) (c : Context) : Prop :=
  ∀ d ∈ sb.integrals, (c.boundary.bind fun bd => bd.integral d.integrand) = some d.state

instance (sb : SourceBody) (c : Context) : Decidable (sb.IntegralStates c) :=
  inferInstanceAs (Decidable (∀ d ∈ sb.integrals,
    (c.boundary.bind fun bd => bd.integral d.integrand) = some d.state))

/-- A lowered body, with the source/target correspondence of its equations and
the checked velocity and integral states. The correspondence is for the whole
system and in every environment, although a single differential's correspondence
may need the velocity equations: the system contains them on both sides. It holds
wherever the atoms read the integral rewrites as they are rewritten
(`Context.Cancels`), which `SourceBody.cancels_at` discharges at every time of a
signal. That discharge needs the integral declarations along the whole signal,
so their correspondence (`integrals`) holds with no premise. -/
structure Lowered (sb : SourceBody) (c : Context) where
  assignments : List Assignment
  outputs : assignments.map (·.output) = sb.outputs
  equations : ∀ atoms env, c.Cancels atoms env →
    (sb.Equations c atoms env ↔ Equations assignments env)
  integrals : ∀ atoms env, Equations assignments env → ∀ d ∈ sb.integrals,
    env d.equation.output.name ≠ none ∧ ∃ v, d.equation.lhs.eval env (c.rates env) atoms = some v ∧
      d.equation.rhs.eval env (c.rates env) atoms = some v
  velocityStates : sb.VelocityStates
  integralStates : sb.IntegralStates c

def Lowered.body {sb : SourceBody} {c : Context} (l : Lowered sb c) : Body :=
  sb.withAssignments l.assignments

/-- Lower an explicit assignment: apply the integral rewrites, then
beta-normalize. -/
private def lowerAssignment (c : Context) (a : SourceAssignment) :
    Except Diagnostic {out : Assignment // out.output = a.output ∧ ∀ atoms env,
      c.Cancels atoms env →
      ((env a.output.name ≠ none ∧ a.rhs.eval env (c.rates env) atoms = env a.output.name) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  if (a.rhs.cancel c).integrals ≠ 0 then
    .error ⟨.unsupportedIntegral, a.output.id, "integral in an explicit assignment"⟩
  else match h : (a.rhs.cancel c).beta with
  | none => .error ⟨.unsupportedDerivative, a.output.id, "derivative in an explicit assignment"⟩
  | some e => .ok ⟨⟨a.output, e⟩, rfl, fun atoms env hc => by
      rw [(a.rhs.cancel c).beta_correct e h env (c.rates env) atoms,
        a.rhs.cancel_eval c env atoms hc]⟩

/-- Lower a differential equation: apply the integral rewrites, collapse
declared chains, read lower-order atoms as their declared velocities, then
isolate. The correspondence holds wherever the velocity equations hold and the
atoms read the rewrites. -/
private def lowerDifferential (c : Context) (d : DifferentialEquation) :
    Except Diagnostic {out : Assignment // out.output = d.output ∧ ∀ atoms env,
      c.VelocitiesHold env ∧ c.Cancels atoms env →
      ((env d.output.name ≠ none ∧ ∃ v, d.lhs.eval env (c.rates env) atoms = some v ∧
          d.rhs.eval env (c.rates env) atoms = some v) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  if d.lhs.mentions d.output.name || d.rhs.mentions d.output.name then
    .error ⟨.repeatedDerivative, d.output.id, "derivative port named in its own equation"⟩
  else if (d.lhs.cancel c).integrals + (d.rhs.cancel c).integrals ≠ 0 then
    .error ⟨.unsupportedIntegral, d.output.id, d.output.name⟩
  else match isolate c d.output.name (((d.lhs.cancel c).collapse c).readVelocities c d.output.name)
      (((d.rhs.cancel c).collapse c).readVelocities c d.output.name) with
  | .error code => .error ⟨code, d.output.id, d.output.name⟩
  | .ok i => .ok ⟨⟨d.output, i.expr⟩, rfl, fun atoms env ⟨hold, hc⟩ => by
      rw [← i.correct env atoms, Term.readVelocities_eval c _ _ env atoms hold,
        Term.readVelocities_eval c _ _ env atoms hold, Term.collapse_eval, Term.collapse_eval,
        Term.cancel_eval c _ env atoms hc, Term.cancel_eval c _ env atoms hc]⟩

/-- Lower a velocity declaration as the first-order equation it states, with no
premise. It is kept apart from `lowerDifferential` so that a declaration is
never read through `Term.readVelocities`: its correspondence must hold in every
environment, because it is what discharges that reading for the system. -/
private def lowerVelocity (c : Context) (v : VelocityDeclaration) :
    Except Diagnostic {out : Assignment // out.output = v.output ∧ ∀ (atoms : Term → Option ℝ) env,
      True →
      ((env v.equation.output.name ≠ none ∧
          ∃ w, v.equation.lhs.eval env (c.rates env) atoms = some w ∧
            v.equation.rhs.eval env (c.rates env) atoms = some w) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  let d := v.equation
  if d.lhs.mentions d.output.name || d.rhs.mentions d.output.name then
    .error ⟨.repeatedDerivative, d.output.id, "derivative port named in its own equation"⟩
  else match isolate c d.output.name d.lhs d.rhs with
  | .error code => .error ⟨code, d.output.id, d.output.name⟩
  | .ok i => .ok ⟨⟨d.output, i.expr⟩, rfl, fun atoms env _ => i.correct env atoms⟩

/-- Lower an integral declaration as the first-order equation `D_t(F) = X` it
states, with no premise, after checking that the context reads it: the axis is
the evolution axis, `X` is a polynomial in inputs, and `F` is a state whose
declared initial value is `0`. -/
private def lowerIntegral (c : Context) (d : IntegralDeclaration) :
    Except Diagnostic {out : Assignment // out.output = d.output ∧ ∀ (atoms : Term → Option ℝ) env,
      True →
      ((env d.equation.output.name ≠ none ∧
          ∃ w, d.equation.lhs.eval env (c.rates env) atoms = some w ∧
            d.equation.rhs.eval env (c.rates env) atoms = some w) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  match c.boundary with
  | none => .error ⟨.unsupportedIntegral, d.output.id, "integral without an evolution axis"⟩
  | some bd =>
    if d.axis ≠ c.axis then .error ⟨.unsupportedIntegral, d.output.id, d.axis⟩
    else if d.equation.lhs.mentions d.output.name || d.equation.rhs.mentions d.output.name then
      .error ⟨.repeatedDerivative, d.output.id, "derivative port named in its own equation"⟩
    else if !d.integrand.continuous bd then
      .error ⟨.unsupportedIntegral, d.output.id, "integrand"⟩
    else match bd.initial d.state with
    | none => .error ⟨.unsupportedRole, d.output.id, d.state⟩
    | some q =>
      if q ≠ 0 then .error ⟨.nonzeroInitial, d.output.id, d.state⟩
      else match isolate c d.output.name d.equation.lhs d.equation.rhs with
      | .error code => .error ⟨code, d.output.id, d.output.name⟩
      | .ok i => .ok ⟨⟨d.output, i.expr⟩, rfl, fun atoms env _ => i.correct env atoms⟩

private def lowerList {α : Type} (H : (Term → Option ℝ) → (String → Option ℝ) → Prop)
    (P : α → (Term → Option ℝ) → (String → Option ℝ) → Prop) (port : α → Port)
    (f : (a : α) → Except Diagnostic {out : Assignment // out.output = port a ∧ ∀ atoms env,
      H atoms env →
      (P a atoms env ↔ (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))}) :
    (as : List α) → Except Diagnostic {out : List Assignment //
      out.map (·.output) = as.map port ∧ ∀ atoms env, H atoms env →
        ((∀ a ∈ as, P a atoms env) ↔ Equations out env)}
  | [] => .ok ⟨[], rfl, fun _ _ _ => by simp [Equations]⟩
  | a :: rest => do
      let ⟨x, hx, px⟩ ← f a
      let ⟨xs, hxs, pxs⟩ ← lowerList H P port f rest
      return ⟨x :: xs, by simp [hx, hxs], fun atoms env hold => by
        have h1 := px atoms env hold
        have h2 := pxs atoms env hold
        simp only [List.forall_mem_cons, Equations] at *
        rw [h1, h2]⟩

private theorem equations_append (l r : List Assignment) (env : String → Option ℝ) :
    Equations (l ++ r) env ↔ Equations l env ∧ Equations r env := by
  simp only [Equations, List.forall_mem_append]

/-- Check scopes and velocity states, isolate integral declarations, apply the
integral rewrites and beta-normalize explicit assignments, isolate differentials
after the integral rewrites with lower-order atoms read as declared velocities,
isolate velocity declarations, and check that the context reads every integral
declaration. The lowered assignments keep source order: explicit assignments,
differentials, velocity declarations, integral declarations. `declares` ties the
velocities `c` reads to the body's declarations, whose equations discharge that
reading. -/
def SourceBody.lower (sb : SourceBody) (c : Context) (declares : sb.Declares c) :
    Except Diagnostic (Lowered sb c) := do
  let names := (sb.inputs ++ sb.outputs).map Port.name
  for a in sb.assignments do
    match a.rhs.checkScope names with
    | .error name => throw ⟨.unknownReference, a.output.id, name⟩
    | .ok () => pure ()
  for d in sb.equations do
    match d.lhs.checkScope names, d.rhs.checkScope names with
    | .error name, _ | _, .error name => throw ⟨.unknownReference, d.output.id, name⟩
    | .ok (), .ok () => pure ()
  if states : sb.VelocityStates then
    -- Integral declarations first: an equation using a rejected declaration's
    -- integral would otherwise be reported instead of the declaration.
    let ⟨is, his, pis⟩ ← lowerList (fun _ _ => True) _ (·.output) (lowerIntegral c) sb.integrals
    let ⟨as, has, pas⟩ ← lowerList c.Cancels _ (·.output) (lowerAssignment c) sb.assignments
    let ⟨ds, hds, pds⟩ ← lowerList (fun atoms env => c.VelocitiesHold env ∧ c.Cancels atoms env)
      _ (·.output) (lowerDifferential c) sb.differentials
    let ⟨vs, hvs, pvs⟩ ← lowerList (fun _ _ => True) _ (·.output) (lowerVelocity c) sb.velocities
    if reads : sb.IntegralStates c then
      return ⟨as ++ ds ++ vs ++ is, by
        simp [SourceBody.outputs, SourceBody.equations, has, hds, hvs, his, Function.comp_def,
          VelocityDeclaration.equation, IntegralDeclaration.equation], fun atoms env hc => by
        simp only [SourceBody.Equations, SourceBody.equations, List.forall_mem_append,
          List.forall_mem_map, equations_append]
        rw [← pas atoms env hc, ← pvs atoms env trivial, ← pis atoms env trivial]
        constructor
        · rintro ⟨ha, ⟨hd, hv⟩, hi⟩
          exact ⟨⟨⟨ha, (pds atoms env ⟨velocitiesHold declares hv, hc⟩).mp hd⟩, hv⟩, hi⟩
        · rintro ⟨⟨⟨ha, hd⟩, hv⟩, hi⟩
          exact ⟨ha, ⟨(pds atoms env ⟨velocitiesHold declares hv, hc⟩).mpr hd, hv⟩, hi⟩,
        fun atoms env h => (pis atoms env trivial).mpr ((equations_append _ _ env).mp h).2,
        states, reads⟩
    else
      -- Each declaration passed `lowerIntegral`, so the context fails to read one
      -- only when an earlier declaration names the same integral.
      match sb.integrals.find? (fun d =>
          (c.boundary.bind fun bd => bd.integral d.integrand) != some d.state) with
      | some d => throw ⟨.duplicateId, d.output.id, d.state⟩
      -- Unreachable: `IntegralStates` fails only through a declaration `find?` returns.
      | none => throw ⟨.duplicateId, "integrals", "declared integral state"⟩
  else
    match sb.velocities.find? (fun v =>
        !(sb.inputs.find? (·.name == v.velocity)).any (·.role == .state)) with
    | some v => throw ⟨.unsupportedRole, v.output.id, v.velocity⟩
    -- Unreachable: `VelocityStates` fails only through a declaration `find?` returns.
    | none => throw ⟨.unsupportedRole, "velocities", "declared velocity state"⟩

/-! ## Correspondence with the lowered body -/

theorem Lowered.value {sb : SourceBody} {c : Context} (l : Lowered sb c)
    {α : Type} (env : String → Option α) (id : String) :
    l.body.value env id = sb.value env id := by
  simp [Body.value, SourceBody.value, Lowered.body, SourceBody.withAssignments, l.outputs]

theorem Lowered.source {sb : SourceBody} {c : Context} (l : Lowered sb c) {n : Nat}
    (ids : Fin n → String) (x : Point n) {atoms : Term → Option ℝ} (env : String → Option ℝ)
    (h : c.Cancels atoms env) :
    sb.Source c atoms ids x env ↔ l.body.Source ids x env := by
  simp only [SourceBody.Source, Body.Source, l.equations atoms env h]
  rfl

/-- In a solution of the source or of the lowered body, every state is
differentiable on the forward domain. -/
private theorem differentiable_of {e : Evolution} {state : Dynamics.Signal e.states.length}
    {value : (String → Option ℝ) → String → Option ℝ} {Source : ℝ → (String → Option ℝ) → Prop}
    (h : ∀ t ∈ e.time.domain, ∃ env, Source t env ∧ ∀ i, ∃ rate,
      value env (e.derivativeIds i) = some rate ∧
        HasDerivWithinAt (fun t => state t i) rate e.time.domain t) :
    ∀ s ∈ e.time.domain, ∀ i, DifferentiableWithinAt ℝ (fun s => state s i) e.time.domain s := by
  intro s hs i
  obtain ⟨env, -, rates⟩ := h s hs
  obtain ⟨rate, -, hd⟩ := rates i
  exact hd.differentiableWithinAt

/-- Every solution of the lowered body satisfies the source's integral
declarations along the signal: their correspondence needs no premise. -/
theorem Lowered.integralsAlong {sb : SourceBody} {e : Evolution} (l : Lowered sb (sb.context e))
    {state : Dynamics.Signal e.states.length} (h : l.body.Solves e state) :
    sb.IntegralsAlong e state := by
  intro s hs
  obtain ⟨env, source, rates⟩ := h.2 s hs
  have rates' : ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain s := fun i => by
    rw [← l.value]; exact rates i
  exact ⟨env, ports_of hs source.1 rates', fun d hd => (l.integrals _ env source.2 d hd).2⟩

/-- The original differential equations and the lowered explicit body have the
same solutions: same states, axis, start, forward domain and initial values. -/
theorem Lowered.solves_iff {sb : SourceBody} {e : Evolution} (l : Lowered sb (sb.context e))
    (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ l.body.Solves e state := by
  constructor
  · intro hs
    obtain ⟨init, h⟩ := hs
    have diff := differentiable_of h
    have integrals := SourceBody.Solves.integralsAlong ⟨init, h⟩
    refine ⟨init, fun t ht => ?_⟩
    obtain ⟨env, source, rates⟩ := h t ht
    have hc := sb.cancels_at init diff integrals ht (ports_of ht source.1 rates)
    exact ⟨env, (l.source _ _ env hc).mp source, fun i => by rw [l.value]; exact rates i⟩
  · intro hs
    have integrals := l.integralsAlong hs
    obtain ⟨init, h⟩ := hs
    have diff := differentiable_of h
    refine ⟨init, fun t ht => ?_⟩
    obtain ⟨env, source, rates⟩ := h t ht
    have rates' : ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
        HasDerivWithinAt (fun t => state t i) rate e.time.domain t := fun i => by
      rw [← l.value]; exact rates i
    have hc := sb.cancels_at init diff integrals ht (ports_of ht source.1 rates')
    exact ⟨env, (l.source _ _ env hc).mpr source, rates'⟩

/-- In a solution, `I_t(D_t(x))` reads `x - x0` at every time, with the declared
initial value `x0` of the state `x`: the boundary term is part of the meaning. -/
theorem SourceBody.Solves.integral_derivative {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state) {x : String} {q : ℚ}
    (hl : ((sb.context e).locate x).isSome = true) (hq : (sb.boundary e).initial x = some q) :
    ∃ i, sb.coordinate e x = some i ∧ ∀ t ∈ e.time.domain,
      sb.atoms e state t (.integral e.axis.name (.derivative e.axis.name (.var x))) =
        some (state t i - q) := by
  obtain ⟨port, hport⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨i, hi, hv, -⟩ := initial_coordinate hq
  have start := h.1 i
  rw [hv, Option.map_some, Option.some.injEq] at start
  have diff := differentiable_of h.2
  refine ⟨i, hi, fun t ht => ?_⟩
  have := Term.along_integral_derivative (T := sb.trajectory e state) (x := x)
    (g := fun s => state s i) (fun s hs => ⟨diff s hs i, classical_single hport hi s⟩) ht
  rw [SourceBody.atoms, Trajectory.atoms]
  exact this.trans (by rw [start]; rfl)

/-- In a solution, `D_t(I_t(X))` reads as `X` along the solution, for a tame
integrand `X`: the derivative of the integral is the integrand. -/
theorem SourceBody.Solves.derivative_integral {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state) {X : Term}
    (hX : X.tame (sb.context e) (sb.boundary e) = true) {t : ℝ} (ht : t ∈ e.time.domain) :
    sb.atoms e state t (.derivative e.axis.name (.integral e.axis.name X)) =
      X.along (sb.trajectory e state) t := by
  obtain ⟨F, g, h0, hF⟩ :=
    Term.tame_primitive hX (sb.regular h.1 (differentiable_of h.2) h.integralsAlong)
  exact Term.along_derivative_integral (T := sb.trajectory e state) h0 (fun s hs => (hF s hs).1)
    (fun s hs => (hF s hs).2) ht

/-- In a solution, a declared integral state is the source's integral: wherever
the context reads `I_t(X)` as `F`, the antiderivative of `X` from the start reads
`F` at every time. The declaration's own equation is only `D_t(F) = X`; the
declared initial value `0` and the uniqueness of the antiderivative give the
rest (`primitiveFrom_iff`). -/
theorem SourceBody.Solves.integral_state {sb : SourceBody} {e : Evolution}
    {state : Dynamics.Signal e.states.length} (h : sb.Solves e state) {X : Term} {F : String}
    (hF : (sb.boundary e).integral X = some F) :
    ∃ j, sb.coordinate e F = some j ∧ ∀ t ∈ e.time.domain,
      sb.atoms e state t (.integral e.axis.name X) = some (state t j) := by
  obtain ⟨-, -, -, -, -, -, hq⟩ := integral_declared hF
  obtain ⟨i, hi, -, hbase⟩ := initial_coordinate hq
  obtain ⟨g, g0, hg⟩ := (sb.regular h.1 (differentiable_of h.2) h.integralsAlong).integral X F hF
  refine ⟨i, hi, fun t ht => ?_⟩
  have hI := primitiveFrom_iff.mpr ⟨g0, fun s hs => (hg s hs).2⟩ t ht
  have hgt : g t = state t i := by
    have := (hg t ht).1
    rw [show (sb.trajectory e state).base t F = sb.inputEnvironment e.stateIds (state t) F from rfl,
      hbase (state t), Option.some.injEq] at this
    exact this.symm
  rw [SourceBody.atoms, Trajectory.atoms, ← hgt]
  simpa [Term.along, SourceBody.trajectory] using hI

/-- Hidden states and auxiliaries are existential, as in `Body.Observes`. There
is no trajectory, so no integral or derivative of a non-chain has a value. -/
def SourceBody.Observes {n m : Nat} (sb : SourceBody) (c : Context) (ids : Fin n → String)
    (refs : Fin m → String) (x : Point n) (y : Point m) : Prop :=
  ∃ env, sb.Source c (fun _ => none) ids x env ∧ ∀ i, sb.value env (refs i) = some (y i)

/-- Without a trajectory, only a context that rewrites no integral, such as the
polynomial one, relates the observations. -/
theorem Lowered.observes {sb : SourceBody} {c : Context} (l : Lowered sb c) {n m : Nat}
    (ids : Fin n → String) (refs : Fin m → String) (x : Point n) (y : Point m)
    (h : c.boundary = none) :
    sb.Observes c ids refs x y ↔ l.body.Observes ids refs x y := by
  simp only [SourceBody.Observes, Body.Observes, l.value]
  exact exists_congr fun env => and_congr_left fun _ =>
    l.source ids x env (Context.cancels_none h _ env)

def SourceBody.observationIds (sb : SourceBody) (i : Fin sb.observations.length) : String :=
  sb.observations[i].sourceId

/-- Observed outputs of a solution, read at each time from an environment whose
ports carry the actual derivatives, as in `Solves`. -/
def SourceBody.ObservedSolution (sb : SourceBody) (e : Evolution)
    (output : Dynamics.Signal sb.observations.length) : Prop :=
  ∃ state, sb.Solves e state ∧ ∀ t ∈ e.time.domain, ∃ env, sb.PortsAt e state t env ∧
    sb.Equations (sb.context e) (sb.atoms e state t) env ∧
      ∀ i, sb.value env (sb.observationIds i) = some (output t i)

/-! ## Compilation -/

/-- The declared interface with every right-hand side erased. Validating it
first reports malformed ports, bindings and axes before any source term is read. -/
def SourceBody.interface (sb : SourceBody) : Body :=
  sb.withAssignments (sb.outputs.map fun p => ⟨p, .constant 0⟩)

structure SourcePolynomialModel (sb : SourceBody) where
  lowered : Lowered sb Context.empty
  model : PolynomialModel lowered.body

/-- A polynomial declaration has no evolution axis, so every derivative atom,
integral, differential equation, velocity declaration and integral declaration is
rejected. -/
def compileSourcePolynomial (sb : SourceBody) :
    Except Diagnostic (SourcePolynomialModel sb) := do
  if let some d := sb.integrals.head? then
    throw ⟨.unsupportedIntegral, d.output.id, "integral without an evolution axis"⟩
  if let some d := sb.equations.head? then
    throw ⟨.unsupportedDerivative, d.output.id, "differential equation without an evolution axis"⟩
  if let some a := sb.assignments.find? (·.rhs.integrals ≠ 0) then
    throw ⟨.unsupportedIntegral, a.output.id, "integral without an evolution axis"⟩
  (Declaration.polynomial sb.interface).validate
  let lowered ← sb.lower Context.empty sb.declares_empty
  let model ← compilePolynomial lowered.body
  return ⟨lowered, model⟩

/-- Original source equations, including lambdas, against the compiled outputs. -/
theorem SourcePolynomialModel.correct {sb : SourceBody} (p : SourcePolynomialModel sb)
    (x : Point p.lowered.body.runtimePorts.length) (y : Point sb.observations.length) :
    sb.Observes Context.empty p.lowered.body.runtimeIds sb.observationIds x y ↔
      p.model.outputs.circuit.run x = y := by
  rw [p.lowered.observes _ _ _ _ rfl]
  exact p.model.outputs.correct x y

structure SourceContinuousModel (sb : SourceBody) (e : Evolution) where
  lowered : Lowered sb (sb.context e)
  model : ContinuousModel lowered.body e

def compileSourceContinuous (sb : SourceBody) (e : Evolution) :
    Except Diagnostic (SourceContinuousModel sb e) := do
  (Declaration.continuous sb.interface e).validate
  let lowered ← sb.lower (sb.context e) (sb.declares_context e)
  let model ← compileContinuous lowered.body e
  return ⟨lowered, model⟩

/-- The original implicit differential equations and initial conditions against
the initialized feedback of the compiled isolated RHS, on the same domain. -/
theorem SourceContinuousModel.solves_iff_realizes {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ p.model.Realizes state := by
  rw [p.lowered.solves_iff, p.model.solves_iff_realizes]

/-- A corollary of `solves_iff_realizes`, stated because isolation must not
lose obligations: the solution sets coincide and the trajectory is not
transformed, so any further predicate on it, such as a terminal condition, is
preserved. This fragment itself is an initial-value problem; it has no
boundary-condition semantics of its own. -/
theorem SourceContinuousModel.constrained_iff {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (constraint : Dynamics.Signal e.states.length → Prop)
    (state : Dynamics.Signal e.states.length) :
    (sb.Solves e state ∧ constraint state) ↔ (p.model.Realizes state ∧ constraint state) := by
  rw [p.solves_iff_realizes]

theorem SourceContinuousModel.observations_correct {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (output : Dynamics.Signal sb.observations.length) :
    sb.ObservedSolution e output ↔ p.model.ObservedRealization output := by
  rw [← p.model.observations_correct]
  refine exists_congr fun state => ?_
  rw [p.lowered.solves_iff]
  refine and_congr_right fun hs => ?_
  have init := hs.1
  have diff := differentiable_of hs.2
  have integrals := p.lowered.integralsAlong hs
  have field := ((p.model.solves_iff_field state).mp hs).2
  refine forall₂_congr fun t ht => ?_
  constructor
  · rintro ⟨env, ports, equations, observed⟩
    have hc := sb.cancels_at init diff integrals ht ports
    exact ⟨env, (p.lowered.source _ _ env hc).mp ⟨ports.1, equations⟩,
      fun i => by rw [p.lowered.value]; exact observed i⟩
  · rintro ⟨env, source, observed⟩
    have ports : sb.PortsAt e state t env := by
      refine ⟨source.1, fun i => ⟨(field t ht i).differentiableWithinAt, ?_⟩⟩
      have forced := p.lowered.body.value_agrees (p.model.prepared.forced (state t) env source)
        (e.derivativeIds i) _ (p.model.rates.value_correct (state t) i)
      rw [← p.lowered.value, forced, (field t ht i).derivWithin (uniqueDiffOn_Ici _ t ht)]
    have hc := sb.cancels_at init diff integrals ht ports
    exact ⟨env, ports, ((p.lowered.source _ _ env hc).mpr source).2,
      fun i => by rw [← p.lowered.value]; exact observed i⟩

/-- Every realization of a compiled model is a solution in which each chain of
derivatives denotes the iterated derivative on the forward domain, each state
reached through declared velocities is that iterated derivative, and its
declared initial value is the iterated derivative at the start.
`classical_iff_realizes` states the equations themselves under that reading. -/
theorem SourceContinuousModel.realizes_iterated {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) {state : Dynamics.Signal e.states.length}
    (h : p.model.Realizes state) :
    (∀ t ∈ e.time.domain, ∃ env, sb.Source (sb.context e) (sb.atoms e state t) e.stateIds
      (state t) env ∧
      ∀ axes x r, (sb.context e).rates env axes x = some r →
        ∃ i, sb.coordinate e x = some i ∧
          HasDerivWithinAt (iteratedDerivWithin (axes.length - 1) (fun s => state s i)
            e.time.domain) r e.time.domain t) ∧
    ∀ k x y i j, (sb.context e).lift k x = some y → sb.coordinate e x = some i →
      sb.coordinate e y = some j →
        Set.EqOn (iteratedDerivWithin k (fun s => state s i) e.time.domain)
          (fun s => state s j) e.time.domain ∧
        (e.initialValue e.states[j].initialId).map (fun q : ℚ => (q : ℝ)) =
          some (iteratedDerivWithin k (fun s => state s i) e.time.domain e.time.start) := by
  have hs := (p.solves_iff_realizes state).mpr h
  have states := p.lowered.velocityStates
  exact ⟨fun t ht => hs.chain_at states ht, fun k _ _ _ _ hy hi hj =>
    ⟨hs.lift_eqOn states k hy hi hj, hs.initial_iterated states k hy hi hj⟩⟩

/-- In every realization of a compiled model, each integral declaration's
state is the source's integral of its integrand, from the declared start, at
every time of the forward domain. -/
theorem SourceContinuousModel.integral_states {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) {state : Dynamics.Signal e.states.length}
    (h : p.model.Realizes state) :
    ∀ d ∈ sb.integrals, ∃ j, sb.coordinate e d.state = some j ∧ ∀ t ∈ e.time.domain,
      sb.atoms e state t (.integral e.axis.name d.integrand) = some (state t j) := by
  intro d hd
  exact ((p.solves_iff_realizes state).mpr h).integral_state (p.lowered.integralStates d hd)

/-- The original higher-order source, read with actual iterated derivatives,
has exactly the realizations of the compiled first-order system as solutions:
same states, start, forward domain and initial data. -/
theorem SourceContinuousModel.classical_iff_realizes {sb : SourceBody} {e : Evolution}
    (p : SourceContinuousModel sb e) (state : Dynamics.Signal e.states.length) :
    sb.SolvesClassical e state ↔ p.model.Realizes state := by
  rw [← sb.solves_iff_classical p.lowered.velocityStates, p.solves_iff_realizes]

#print axioms SourceBody.velocitiesHold
#print axioms SourceBody.declares_context
#print axioms SourceBody.solves_iff_classical
#print axioms SourceContinuousModel.classical_iff_realizes
#print axioms SourceBody.Solves.derivative_denotes
#print axioms SourceBody.Solves.lift_eqOn
#print axioms SourceBody.Solves.initial_iterated
#print axioms SourceBody.Solves.chain_denotes
#print axioms SourceContinuousModel.realizes_iterated
#print axioms Lowered.solves_iff
#print axioms SourceBody.Solves.integral_derivative
#print axioms SourceBody.regular
#print axioms SourceBody.cancels_at
#print axioms SourceBody.Solves.derivative_integral
#print axioms SourcePolynomialModel.correct
#print axioms SourceContinuousModel.solves_iff_realizes
#print axioms SourceContinuousModel.constrained_iff
#print axioms SourceContinuousModel.observations_correct
#print axioms SourceBody.Solves.integral_state
#print axioms SourceContinuousModel.integral_states
#print axioms Lowered.integralsAlong
#print axioms SourceBody.Solves.integralsAlong
end Gimle.Asgard.Model
