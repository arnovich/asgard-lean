import Gimle.Asgard.Model.Driven
import Gimle.Asgard.Model.Source

/-! Source declarations with declared time-varying drivers.

A driven source is a `SourceBody` whose inputs include `.driver` ports, each
declared by a `DriverBinding`, compiled against an `Evolution` as a continuous
source is. A driver is read as a value in residuals and explicit assignments.
`D_t(z)` of a driver `z` has a value only when `z` is declared differentiable,
and then it is the value of `z`'s declared derivative port
(`SourceBody.drivenContext`), which the relation binds to the actual derivative
of the driver signal (`Evolution.Admitted`). Nothing is inferred from a name or
a `$` prefix: an undeclared `.driver` port is rejected by validation, and the
derivative of a driver without a derivative port, of a parameter, of an
auxiliary or of a derivative port stays rejected by isolation, as does a driver
derivative inside a lambda application, as for states.

Before the unchanged lowering of `Model.Source`, every first-order evolution
atom `D_t(z)` of a differentiable driver is read as the name of its derivative
port (`Term.readRates`). That is exact in every environment
(`Term.readRates_eval`): the context reads the atom as that port. It leaves the
state atom as the only derivative in an equation such as `D_t(a) = D_t(z)`, so
isolation solves it for the state.

This fragment has no integrals: the context has no boundary, so an integral
declaration or an integral anywhere is rejected, and the relation reads every
non-local atom as undefined. Velocity declarations and higher-order chains of
states are lowered as in `Model.Source`; a chain of a driver is rejected. The
main result is `SourceDrivenModel.solves_iff_realizes`. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- The display name of the derivative port of the first `.driver` input named
`y`, when that driver is declared differentiable. -/
def SourceBody.driverRate (sb : SourceBody) (ds : List DriverBinding) (y : String) :
    Option String := do
  let p ← sb.inputs.find? (fun p => p.name == y && p.role == .driver)
  let d ← ds.find? (·.driverId == p.id)
  let port ← d.derivativeId
  sb.portName port

/-- `D_t(x)` of a state is its derivative port, as in `SourceBody.context`;
`D_t(z)` of a differentiable driver is its declared derivative port. There is no
boundary, so no integral is rewritten. -/
def SourceBody.drivenContext (sb : SourceBody) (e : Evolution) (ds : List DriverBinding) :
    Context where
  axis := e.axis.name
  locate y := (sb.driverRate ds y).orElse fun _ => sb.locate e y
  velocity := (sb.context e).velocity
  boundary := none

/-- Read each first-order `axis` atom `D_axis(y)` for which `rate y` names a port
as that port. Lambda applications are left untouched, as in `Term.readPorts`. -/
def Term.readRates (axis : String) (rate : String → Option String) : Term → Term
  | .add a b => .add (a.readRates axis rate) (b.readRates axis rate)
  | .mul a b => .mul (a.readRates axis rate) (b.readRates axis rate)
  | .neg a => .neg (a.readRates axis rate)
  | .derivative a (.var y) =>
      if a = axis then
        match rate y with
        | some port => .var port
        | none => .derivative a (.var y)
      else .derivative a (.var y)
  | t => t

/-- Reading atoms as ports the context also locates them at preserves meaning in
every environment. -/
theorem Term.readRates_eval (c : Context) (rate : String → Option String)
    (h : ∀ y port, rate y = some port → c.locate y = some port) (t : Term)
    (env : String → Option ℝ) (atoms : Term → Option ℝ) :
    (t.readRates c.axis rate).eval env (c.rates env) atoms = t.eval env (c.rates env) atoms := by
  induction t with
  | var _ | constant _ | apply _ _ _ | integral _ _ _ | unary _ _ _ | binary _ _ _ _ _ => rfl
  | add a b ha hb => simp only [readRates, Term.eval, ha, hb]
  | mul a b ha hb => simp only [readRates, Term.eval, ha, hb]
  | neg a ha => simp only [readRates, Term.eval, ha]
  | derivative axis operand _ =>
      cases operand with
      | var y =>
          by_cases hc : axis = c.axis
          · cases hl : rate y with
            | none => simp only [readRates, if_pos hc, hl]
            | some port =>
                simp only [readRates, if_pos hc, hl, Term.eval, Term.chain, Context.rates]
                simp [Context.lift, hc, h y port hl]
          · simp only [readRates, if_neg hc]
      | _ => rfl

/-- The same source with every explicit assignment and differential equation read
through `Term.readRates`. Ports, velocity and integral declarations, parameters
and observations are unchanged. -/
def SourceBody.readRates (sb : SourceBody) (axis : String) (rate : String → Option String) :
    SourceBody :=
  { sb with
    assignments := sb.assignments.map fun a => ⟨a.output, a.rhs.readRates axis rate⟩
    differentials := sb.differentials.map fun d =>
      ⟨d.output, d.lhs.readRates axis rate, d.rhs.readRates axis rate⟩ }

theorem SourceBody.readRates_outputs (sb : SourceBody) (axis : String)
    (rate : String → Option String) : (sb.readRates axis rate).outputs = sb.outputs := by
  simp [SourceBody.outputs, SourceBody.equations, SourceBody.readRates, Function.comp_def]

theorem SourceBody.readRates_value {α : Type} (sb : SourceBody) (axis : String)
    (rate : String → Option String) (env : String → Option α) (id : String) :
    (sb.readRates axis rate).value env id = sb.value env id := by
  simp only [SourceBody.value, sb.readRates_outputs]
  rfl

theorem SourceBody.readRates_equations (sb : SourceBody) (c : Context)
    (rate : String → Option String) (h : ∀ y port, rate y = some port → c.locate y = some port)
    (atoms : Term → Option ℝ) (env : String → Option ℝ) :
    (sb.readRates c.axis rate).Equations c atoms env ↔ sb.Equations c atoms env := by
  simp only [SourceBody.Equations, SourceBody.equations, SourceBody.readRates,
    List.forall_mem_append, List.forall_mem_map, Term.readRates_eval c rate h]

theorem SourceBody.readRates_source (sb : SourceBody) (c : Context)
    (rate : String → Option String) (h : ∀ y port, rate y = some port → c.locate y = some port)
    (atoms : Term → Option ℝ) {n : Nat} (ids : Fin n → String) (x : Point n)
    (env : String → Option ℝ) :
    (sb.readRates c.axis rate).Source c atoms ids x env ↔ sb.Source c atoms ids x env := by
  simp only [SourceBody.Source, sb.readRates_equations c rate h]
  rfl

theorem SourceBody.driverRate_located (sb : SourceBody) (e : Evolution)
    (ds : List DriverBinding) (y port : String) (h : sb.driverRate ds y = some port) :
    (sb.drivenContext e ds).locate y = some port := by
  simp [SourceBody.drivenContext, h]

/-- The source with its driver atoms read as their ports. -/
def SourceBody.drivenSource (sb : SourceBody) (e : Evolution) (ds : List DriverBinding) :
    SourceBody :=
  sb.readRates e.axis.name (sb.driverRate ds)

theorem SourceBody.declares_driven (sb : SourceBody) (e : Evolution) (ds : List DriverBinding) :
    (sb.drivenSource e ds).Declares (sb.drivenContext e ds) :=
  sb.declares_context e

/-- An admitted driver signal, initial conditions and the original source
equations on the forward domain: each state's derivative atom is its actual
derivative, and each driver and derivative port is read from the signal at the
same time. Non-local atoms have no value in this fragment. -/
def SourceBody.SolvesDriven (sb : SourceBody) (e : Evolution) (ds : List DriverBinding)
    (drivers : Dynamics.Signal (DriverBinding.width ds))
    (state : Dynamics.Signal e.states.length) : Prop :=
  e.Admitted ds drivers ∧
  (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
    some (state e.time.start i)) ∧
  ∀ t ∈ e.time.domain, ∃ env, sb.Source (sb.drivenContext e ds) (fun _ => none)
    (e.drivenIds ds) (pointAppend (drivers t) (state t)) env ∧
    ∀ i, ∃ rate, sb.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t

structure SourceDrivenModel (sb : SourceBody) (e : Evolution) (ds : List DriverBinding) where
  lowered : Lowered (sb.drivenSource e ds) (sb.drivenContext e ds)
  model : DrivenModel lowered.body e ds

/-- Reject integrals, validate the declared interface and drivers, read driver
atoms as their ports, lower, and compile the driven body. -/
def compileSourceDriven (sb : SourceBody) (e : Evolution) (ds : List DriverBinding) :
    Except Diagnostic (SourceDrivenModel sb e ds) := do
  if let some d := sb.integrals.head? then
    throw ⟨.unsupportedIntegral, d.output.id, "integral in a driven declaration"⟩
  if let some a := sb.assignments.find? (·.rhs.integrals ≠ 0) then
    throw ⟨.unsupportedIntegral, a.output.id, "integral in a driven declaration"⟩
  if let some d := sb.differentials.find? (fun d => d.lhs.integrals + d.rhs.integrals ≠ 0) then
    throw ⟨.unsupportedIntegral, d.output.id, "integral in a driven declaration"⟩
  (Declaration.driven sb.interface e ds).validate
  let lowered ← (sb.drivenSource e ds).lower (sb.drivenContext e ds) (sb.declares_driven e ds)
  let model ← compileDriven lowered.body e ds
  return ⟨lowered, model⟩

/-- The original driven source equations and initial conditions, for an
admitted driver signal, against the initialized driven feedback of the compiled
isolated right-hand side, on the same domain. -/
theorem SourceDrivenModel.solves_iff_realizes {sb : SourceBody} {e : Evolution}
    {ds : List DriverBinding} (p : SourceDrivenModel sb e ds)
    (drivers : Dynamics.Signal (DriverBinding.width ds))
    (state : Dynamics.Signal e.states.length) :
    sb.SolvesDriven e ds drivers state ↔ p.model.Realizes drivers state := by
  rw [← p.model.solves_iff_realizes]
  unfold SourceBody.SolvesDriven Body.SolvesDriven
  refine and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun t _ => exists_congr fun env => ?_
  have hval : ∀ id, p.lowered.body.value env id = sb.value env id := fun id => by
    rw [p.lowered.value]
    exact sb.readRates_value _ _ env id
  simp only [hval]
  rw [← p.lowered.source _ _ env (Context.cancels_none rfl (fun _ => none) env)]
  exact and_congr_left' (sb.readRates_source (sb.drivenContext e ds) _
    (sb.driverRate_located e ds) _ _ _ env).symm

/-- Hidden state is existential; observations read the drivers at the same time,
with no value for a non-local atom, as in `SourceBody.Observes`. -/
def SourceBody.ObservedDriven (sb : SourceBody) (e : Evolution) (ds : List DriverBinding)
    (drivers : Dynamics.Signal (DriverBinding.width ds))
    (output : Dynamics.Signal sb.observations.length) : Prop :=
  ∃ state, sb.SolvesDriven e ds drivers state ∧ ∀ t ∈ e.time.domain,
    sb.Observes (sb.drivenContext e ds) (e.drivenIds ds) sb.observationIds
      (pointAppend (drivers t) (state t)) (output t)

theorem SourceDrivenModel.observations_correct {sb : SourceBody} {e : Evolution}
    {ds : List DriverBinding} (p : SourceDrivenModel sb e ds)
    (drivers : Dynamics.Signal (DriverBinding.width ds))
    (output : Dynamics.Signal sb.observations.length) :
    sb.ObservedDriven e ds drivers output ↔ p.model.ObservedRealization drivers output := by
  rw [← p.model.observations_correct]
  refine exists_congr fun state => and_congr
    ((p.solves_iff_realizes drivers state).trans (p.model.solves_iff_realizes drivers state).symm)
    (forall₂_congr fun t _ => ?_)
  rw [← p.lowered.observes _ _ _ _ rfl]
  simp only [SourceBody.Observes, SourceBody.drivenSource, sb.readRates_value]
  exact exists_congr fun env => and_congr_left fun _ =>
    (sb.readRates_source (sb.drivenContext e ds) _ (sb.driverRate_located e ds) _ _ _ env).symm

/-- For an admitted signal, a source solution is exactly a realization of the
compiled driven feedback. -/
theorem SourceDrivenModel.solves_iff_rel {sb : SourceBody} {e : Evolution}
    {ds : List DriverBinding} (p : SourceDrivenModel sb e ds)
    {drivers : Dynamics.Signal (DriverBinding.width ds)} (admitted : e.Admitted ds drivers)
    (state : Dynamics.Signal e.states.length) :
    sb.SolvesDriven e ds drivers state ↔
      p.model.feedback.Rel e.time (Dynamics.signalAppend drivers (fun _ => p.model.initial)) state := by
  rw [p.solves_iff_realizes, DrivenModel.Realizes, and_iff_right admitted]

#print axioms Term.readRates_eval
#print axioms SourceDrivenModel.solves_iff_rel
#print axioms SourceDrivenModel.observations_correct
#print axioms SourceDrivenModel.solves_iff_realizes
end Gimle.Asgard.Model
