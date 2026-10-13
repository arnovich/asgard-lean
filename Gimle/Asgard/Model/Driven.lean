import Gimle.Asgard.Model.Continuous

/-! Continuous declarations with declared time-varying drivers.

A driven declaration is a continuous one whose body may also read `.driver`
ports, each declared by a `DriverBinding`. The runtime coordinates are the
driver ports, in `DriverBinding.ports` order, followed by the states, so the
compiled right-hand side is a circuit on `[drivers, states]` and closes through
`Dynamics.close` with those drivers as its external input. Parameters stay fixed
rationals, specialized as in `Model.Continuous`.

The driver signal is part of the relation, not an argument beside it. A driven
solution is stated for a given signal on every driver port, and that signal
must be admitted (`Admitted`): each driver is continuous on the forward domain,
and a driver declared differentiable has, at every time of the domain, the value
of its derivative port as its actual derivative. A derivative port is therefore
never an unconstrained extra input. Continuity is the least regularity under
the relation requires; it is required, not inferred.
A derivative port need not be continuous: a contract that also needs existence
or uniqueness states whatever further regularity of the drivers it uses.

`DrivenModel.solves_iff_realizes` is an equivalence for each admitted driver
signal. It is not an existence or uniqueness claim, and it says nothing about
any other signal, such as a sampled or held one. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- The number of driver coordinates. -/
abbrev DriverBinding.width (ds : List DriverBinding) : Nat := (DriverBinding.ports ds).length

/-- The stable ID of each driver coordinate. -/
def DriverBinding.ids (ds : List DriverBinding) (i : Fin (DriverBinding.width ds)) : String :=
  (DriverBinding.ports ds)[i]

/-- Runtime coordinates: the driver ports, then the states. -/
def Evolution.drivenIds (e : Evolution) (ds : List DriverBinding) :
    Fin (DriverBinding.width ds + e.states.length) → String :=
  Fin.append (DriverBinding.ids ds) e.stateIds

/-- The driver signal is admitted: every declared driver is continuous on the
forward domain, and every declared derivative port carries its driver's actual
derivative there. Coordinates are found by stable ID, which is meaningful for
bindings that pass validation, where every port is declared once. -/
def Evolution.Admitted (e : Evolution) (ds : List DriverBinding)
    (drivers : Dynamics.Signal (DriverBinding.width ds)) : Prop :=
  ∀ d ∈ ds, ∃ i, index (DriverBinding.ids ds) d.driverId = some i ∧
    ContinuousOn (fun t => drivers t i) e.time.domain ∧
    ∀ port, d.derivativeId = some port → ∃ j, index (DriverBinding.ids ds) port = some j ∧
      ∀ t ∈ e.time.domain, HasDerivWithinAt (fun t => drivers t i) (drivers t j) e.time.domain t

/-- Initial conditions, an admitted driver signal, and the original equations
with every state's derivative on the forward domain, reading each driver port
from the signal at the same time. -/
def Body.SolvesDriven (b : Body) (e : Evolution) (ds : List DriverBinding)
    (drivers : Dynamics.Signal (DriverBinding.width ds))
    (state : Dynamics.Signal e.states.length) : Prop :=
  e.Admitted ds drivers ∧
  (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
    some (state e.time.start i)) ∧
  ∀ t ∈ e.time.domain, ∃ env, b.Source (e.drivenIds ds) (pointAppend (drivers t) (state t)) env ∧
    ∀ i, ∃ rate, b.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t

structure DrivenModel (b : Body) (e : Evolution) (ds : List DriverBinding) where
  valid : (Declaration.driven b e ds).validate = .ok ()
  prepared : Prepared b (e.drivenIds ds)
  rates : Selected prepared e.derivativeIds
  outputs : Selected prepared b.observationIds
  initials : Fin e.states.length → ℚ
  initialFound : ∀ i, e.initialValue e.states[i].initialId = some (initials i)

def compileDriven (b : Body) (e : Evolution) (ds : List DriverBinding) :
    Except Diagnostic (DrivenModel b e ds) :=
  match hv : (Declaration.driven b e ds).validate with
  | .error error => .error error
  | .ok () => do
      let prepared ← b.prepare (e.drivenIds ds)
      match prepared.select e.derivativeIds, prepared.select b.observationIds with
      | some rates, some outputs =>
        match hi : Dynamics.resolveTable (fun i => e.initialValue e.states[i].initialId) with
        | none => .error ⟨.missingBinding, "initialValues", "state initial ID"⟩
        | some initials => return ⟨hv, prepared, rates, outputs, initials,
            Dynamics.resolveTable_correct _ _ hi⟩
      | _, _ => .error ⟨.unknownReference, "outputs", "derivative or observation ID"⟩

noncomputable def DrivenModel.initial {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) : Point e.states.length := fun i => p.initials i

/-- The compiled right-hand side on `[drivers, states]`, unchanged. -/
def DrivenModel.field {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) :
    Gimle.Asgard.Circuit (DriverBinding.width ds + e.states.length) e.states.length :=
  p.rates.circuit

def DrivenModel.feedback {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) :
    Dynamics.Circuit (DriverBinding.width ds + e.states.length) e.states.length :=
  Dynamics.close e.axis.id p.field

/-- The initialized driven feedback, for an admitted driver signal. -/
def DrivenModel.Realizes {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (drivers : Dynamics.Signal (DriverBinding.width ds))
    (state : Dynamics.Signal e.states.length) : Prop :=
  e.Admitted ds drivers ∧
    p.feedback.Rel e.time (Dynamics.signalAppend drivers (fun _ => p.initial)) state

@[simp] theorem DrivenModel.field_correct {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (x : Point (DriverBinding.width ds + e.states.length)) :
    p.field.run x = fun i => (p.rates.expressions i).eval x := by
  simp [field, Selected.circuit]

theorem DrivenModel.solves_iff_field {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (drivers : Dynamics.Signal (DriverBinding.width ds))
    (state : Dynamics.Signal e.states.length) :
    b.SolvesDriven e ds drivers state ↔ e.Admitted ds drivers ∧ state e.time.start = p.initial ∧
      ∀ t ∈ e.time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        ((p.rates.expressions i).eval (pointAppend (drivers t) (state t))) e.time.domain t := by
  unfold Body.SolvesDriven
  apply and_congr_right
  intro _
  have initials : (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
      some (state e.time.start i)) ↔ state e.time.start = p.initial := by
    simp only [p.initialFound, Option.map_some, Option.some.injEq]
    exact ⟨fun h => funext (fun i => (h i).symm), fun h i => (congrFun h i).symm⟩
  rw [initials]
  apply and_congr_right
  intro _
  constructor
  · intro source t ht i
    obtain ⟨env, equations, rates⟩ := source t ht
    obtain ⟨rate, value, deriv⟩ := rates i
    have forced := b.value_agrees (p.prepared.forced _ env equations)
      (e.derivativeIds i) _ (p.rates.value_correct _ i)
    rw [value] at forced
    exact (Option.some.inj forced) ▸ deriv
  · intro deriv t ht
    refine ⟨p.prepared.environment _, p.prepared.source _, ?_⟩
    intro i
    exact ⟨_, p.rates.value_correct _ i, deriv t ht i⟩

/-- The original equations and initial conditions, for an admitted driver
signal, against the initialized driven feedback of the compiled right-hand side
on the same domain. -/
theorem DrivenModel.solves_iff_realizes {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (drivers : Dynamics.Signal (DriverBinding.width ds))
    (state : Dynamics.Signal e.states.length) :
    b.SolvesDriven e ds drivers state ↔ p.Realizes drivers state := by
  rw [p.solves_iff_field]
  simp only [Realizes, feedback, Dynamics.close_correct, field_correct, Evolution.time, true_and]

/-- For an admitted signal, a solution is exactly a realization of the driven
feedback: `Realizes` adds nothing beyond `Admitted` to the circuit relation. -/
theorem DrivenModel.solves_iff_rel {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) {drivers : Dynamics.Signal (DriverBinding.width ds)}
    (admitted : e.Admitted ds drivers) (state : Dynamics.Signal e.states.length) :
    b.SolvesDriven e ds drivers state ↔
      p.feedback.Rel e.time (Dynamics.signalAppend drivers (fun _ => p.initial)) state := by
  rw [p.solves_iff_realizes, Realizes, and_iff_right admitted]

/-- Hidden state is existential; observations read the drivers at the same time. -/
def Body.ObservedDriven (b : Body) (e : Evolution) (ds : List DriverBinding)
    (drivers : Dynamics.Signal (DriverBinding.width ds))
    (output : Dynamics.Signal b.observations.length) : Prop :=
  ∃ state, b.SolvesDriven e ds drivers state ∧ ∀ t ∈ e.time.domain,
    b.Observes (e.drivenIds ds) b.observationIds (pointAppend (drivers t) (state t)) (output t)

def DrivenModel.ObservedRealization {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (drivers : Dynamics.Signal (DriverBinding.width ds))
    (output : Dynamics.Signal b.observations.length) : Prop :=
  ∃ state, p.Realizes drivers state ∧ ∀ t ∈ e.time.domain,
    p.outputs.circuit.run (pointAppend (drivers t) (state t)) = output t

theorem DrivenModel.observations_correct {b : Body} {e : Evolution} {ds : List DriverBinding}
    (p : DrivenModel b e ds) (drivers : Dynamics.Signal (DriverBinding.width ds))
    (output : Dynamics.Signal b.observations.length) :
    b.ObservedDriven e ds drivers output ↔ p.ObservedRealization drivers output := by
  simp only [Body.ObservedDriven, ObservedRealization, p.solves_iff_realizes, p.outputs.correct]

#print axioms DrivenModel.solves_iff_realizes
#print axioms DrivenModel.observations_correct
#print axioms DrivenModel.solves_iff_rel
end Gimle.Asgard.Model
