import Gimle.Asgard.Model.Compiler
import Gimle.Asgard.Dynamics.Linear

namespace Gimle.Asgard.Model
open Polynomial

def Evolution.stateIds (e : Evolution) (i : Fin e.states.length) : String := e.states[i].stateId
def Evolution.derivativeIds (e : Evolution) (i : Fin e.states.length) : String :=
  e.states[i].derivativeId

def Evolution.initialValue (e : Evolution) (id : String) : Option ℚ :=
  (e.initialValues.find? (·.id == id)).map RationalBinding.value

noncomputable def Evolution.time (e : Evolution) : Dynamics.TimeDomain := ⟨e.axis.id, e.start⟩

/-- Initial conditions and original equations, with derivatives on the same
forward domain. Neither the scheduler nor a compiled circuit appears here. -/
def Body.Solves (b : Body) (e : Evolution) (state : Dynamics.Signal e.states.length) : Prop :=
  (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
    some (state e.time.start i)) ∧
  ∀ t ∈ e.time.domain, ∃ env, b.Source e.stateIds (state t) env ∧
    ∀ i, ∃ rate, b.value env (e.derivativeIds i) = some rate ∧
      HasDerivWithinAt (fun t => state t i) rate e.time.domain t

structure ContinuousModel (b : Body) (e : Evolution) where
  valid : (Declaration.continuous b e).validate = .ok ()
  prepared : Prepared b e.stateIds
  rates : Selected prepared e.derivativeIds
  outputs : Selected prepared b.observationIds
  initials : Fin e.states.length → ℚ
  initialFound : ∀ i, e.initialValue e.states[i].initialId = some (initials i)

def compileContinuous (b : Body) (e : Evolution) : Except Diagnostic (ContinuousModel b e) :=
  match hv : (Declaration.continuous b e).validate with
  | .error error => .error error
  | .ok () => do
      let prepared ← b.prepare e.stateIds
      match prepared.select e.derivativeIds, prepared.select b.observationIds with
      | some rates, some outputs =>
        match hi : Dynamics.resolveTable (fun i => e.initialValue e.states[i].initialId) with
        | none => .error ⟨.missingBinding, "initialValues", "state initial ID"⟩
        | some initials => return ⟨hv, prepared, rates, outputs, initials,
            Dynamics.resolveTable_correct _ _ hi⟩
      | _, _ => .error ⟨.unknownReference, "outputs", "derivative or observation ID"⟩

noncomputable def ContinuousModel.initial {b : Body} {e : Evolution} (p : ContinuousModel b e) :
    Point e.states.length := fun i => p.initials i

/-- This is the original compiled RHS, adapted only to the no-driver interface. -/
def ContinuousModel.field {b : Body} {e : Evolution} (p : ContinuousModel b e) :
    Gimle.Asgard.Circuit (0 + e.states.length) e.states.length :=
  .compose (route (fun i => Fin.natAdd 0 i)) p.rates.circuit

def ContinuousModel.feedback {b : Body} {e : Evolution} (p : ContinuousModel b e) :
    Dynamics.Circuit (0 + e.states.length) e.states.length :=
  Dynamics.close (d := 0) e.axis.id p.field

def noDrivers : Dynamics.Signal 0 := fun _ i => Fin.elim0 i

def ContinuousModel.Realizes {b : Body} {e : Evolution} (p : ContinuousModel b e)
    (state : Dynamics.Signal e.states.length) : Prop :=
  p.feedback.Rel e.time (Dynamics.signalAppend noDrivers (fun _ => p.initial)) state

@[simp] theorem ContinuousModel.field_correct {b : Body} {e : Evolution}
    (p : ContinuousModel b e) (u : Point 0) (x : Point e.states.length) :
    p.field.run (pointAppend u x) = fun i => (p.rates.expressions i).eval x := by
  simp [field, Selected.circuit, Gimle.Asgard.Circuit.run, pointAppend]

theorem ContinuousModel.solves_iff_field {b : Body} {e : Evolution}
    (p : ContinuousModel b e) (state : Dynamics.Signal e.states.length) :
    b.Solves e state ↔ state e.time.start = p.initial ∧
      ∀ t ∈ e.time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        ((p.rates.expressions i).eval (state t)) e.time.domain t := by
  unfold Body.Solves
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
    have forced := b.value_agrees (p.prepared.forced (state t) env equations)
      (e.derivativeIds i) _ (p.rates.value_correct (state t) i)
    rw [value] at forced
    exact (Option.some.inj forced) ▸ deriv
  · intro deriv t ht
    refine ⟨p.prepared.environment (state t), p.prepared.source (state t), ?_⟩
    intro i
    exact ⟨_, p.rates.value_correct (state t) i, deriv t ht i⟩

/-- Full original-source correspondence through actual initialized continuous
feedback. This is an equivalence, not a general existence or uniqueness claim. -/
theorem ContinuousModel.solves_iff_realizes {b : Body} {e : Evolution}
    (p : ContinuousModel b e) (state : Dynamics.Signal e.states.length) :
    b.Solves e state ↔ p.Realizes state := by
  rw [p.solves_iff_field]
  simp only [Realizes, feedback, Dynamics.close_correct, field_correct,
    Evolution.time, true_and]

/-- Hidden state is existential; observations constrain only the forward domain. -/
def Body.ObservedSolution (b : Body) (e : Evolution)
    (output : Dynamics.Signal b.observations.length) : Prop :=
  ∃ state, b.Solves e state ∧ ∀ t ∈ e.time.domain,
    b.Observes e.stateIds b.observationIds (state t) (output t)

def ContinuousModel.ObservedRealization {b : Body} {e : Evolution}
    (p : ContinuousModel b e) (output : Dynamics.Signal b.observations.length) : Prop :=
  ∃ state, p.Realizes state ∧ ∀ t ∈ e.time.domain,
    p.outputs.circuit.run (state t) = output t

theorem ContinuousModel.observations_correct {b : Body} {e : Evolution}
    (p : ContinuousModel b e) (output : Dynamics.Signal b.observations.length) :
    b.ObservedSolution e output ↔ p.ObservedRealization output := by
  simp only [Body.ObservedSolution, ObservedRealization, p.solves_iff_realizes,
    p.outputs.correct]

#print axioms ContinuousModel.solves_iff_realizes
#print axioms ContinuousModel.observations_correct
end Gimle.Asgard.Model
