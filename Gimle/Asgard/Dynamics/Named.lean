import Gimle.Asgard.Dynamics.Feedback
import Gimle.Asgard.Compile.Named

/-! Checked named interfaces for continuous feedback. The source Program may
interleave states and external inputs, and retain intermediate assignments.
Every state explicitly names its derivative output and its initial-value port. -/
namespace Gimle.Asgard.Dynamics
open Polynomial

structure Axis where
  id : String
  name : String
  deriving Repr, DecidableEq

structure StateBinding where
  stateId : String
  derivativeId : String
  initialId : String
  deriving Repr, DecidableEq

structure System where
  program : Program
  states : List StateBinding
  externalIds : List String
  initialPorts : List Port
  axis : Axis
  evolveAlong : String
  deriving Repr, DecidableEq

/-- The compiler accepts a single real time axis and explicit external roles.
State dependency cycles are allowed; assignment cycles still fail Program.resolve. -/
def System.valid (s : System) : Bool :=
  s.program.valid && validPorts (s.program.inputs ++
    s.program.assignments.map Assignment.output ++ s.initialPorts) &&
  !s.axis.id.isEmpty && !s.axis.name.isEmpty && s.evolveAlong == s.axis.id &&
  decide ((s.states.map StateBinding.stateId).Nodup ∧
    (s.states.map StateBinding.initialId).Nodup ∧
    (s.states.map StateBinding.derivativeId).Nodup ∧ s.externalIds.Nodup) &&
  s.initialPorts.all (fun p => p.role == .initial) &&
  s.program.inputs.all (fun p =>
    if p.role == .state then (s.states.map StateBinding.stateId).contains p.id
    else (p.role == .driver || p.role == .parameter) && s.externalIds.contains p.id) &&
  s.states.all (fun b => s.program.inputs.any (fun p => p.id == b.stateId && p.role == .state)) &&
  s.externalIds.all (fun id => s.program.inputs.any (fun p =>
    p.id == id && (p.role == .driver || p.role == .parameter))) &&
  decide (s.program.inputs.length = s.externalIds.length + s.states.length ∧
    s.initialPorts.length = s.states.length)

/-- Resolve a finite table without any default coordinate on lookup failure. -/
def resolveTable {α : Type} : {n : Nat} → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, f => do
      let head ← f 0
      let tail ← resolveTable (fun i : Fin n => f i.succ)
      return Fin.cases head tail

theorem resolveTable_correct {α : Type} {n : Nat} (f : Fin n → Option α)
    (g : Fin n → α) (h : resolveTable f = some g) : ∀ i, f i = some (g i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      cases hhead : f 0 with
      | none => simp [resolveTable, hhead] at h
      | some head =>
          cases htail : resolveTable (fun i : Fin n => f i.succ) with
          | none => simp [resolveTable, hhead, htail] at h
          | some tail =>
              simp [resolveTable, hhead, htail] at h
              subst g
              intro i
              refine Fin.cases ?_ ?_ i
              · exact hhead
              · exact ih _ _ htail

/-- Coordinate lookup by stable identity; display names belong to Program syntax. -/
def idIndex (ports : List Port) (id : String) : Option (Fin ports.length) :=
  (lookupIndex (ports.map Port.id) id).map (Fin.cast (List.length_map ..))

noncomputable def idValue (ids : List String) (values : Point ids.length)
    (id : String) : Option ℝ := (lookupIndex ids id).map values

/-- Resolution preserves the number and order of all intermediate outputs. -/
theorem assignment_count {n : Nat} (as : List Assignment)
    (env : String → Option (Expr n)) (es : List (Expr n))
    (h : resolveAssignments env as = some es) : es.length = as.length := by
  induction as generalizing env es with
  | nil => simp [resolveAssignments] at h; subst es; rfl
  | cons a rest ih =>
      simp only [resolveAssignments] at h
      split at h
      · simp at h
      · cases he : a.rhs.resolve env with
        | none => simp [he] at h
        | some e =>
            cases ht : resolveAssignments (bind env a.output.name e) rest with
            | none => simp [he, ht] at h
            | some tail =>
                simp [he, ht] at h
                subst es
                simp [ih _ _ ht]

theorem program_count (p : Program) (es : List (Expr p.inputs.length))
    (h : p.resolve = some es) : es.length = p.assignments.length := by
  unfold Program.resolve at h
  split at h
  · exact assignment_count _ _ _ h
  · simp at h

def System.inputIds (s : System) : List String :=
  s.externalIds ++ s.states.map StateBinding.stateId

/-- Successful preparation carries the lookup equations checked by the pure
compiler. These are evidence about declared IDs, not caller-supplied routing. -/
structure Prepared (s : System) where
  valid : s.valid = true
  expressions : List (Expr s.program.inputs.length)
  accepted : s.program.resolve = some expressions
  inputRoute : Fin s.program.inputs.length → Fin s.inputIds.length
  inputFound : ∀ i, lookupIndex s.inputIds s.program.inputs[i].id = some (inputRoute i)
  outputRoute : Fin s.states.length → Fin s.program.assignments.length
  outputFound : ∀ i, idIndex (s.program.assignments.map Assignment.output)
    s.states[i].derivativeId = some (Fin.cast (List.length_map ..).symm (outputRoute i))
  initialRoute : Fin s.states.length → Fin s.initialPorts.length
  initialFound : ∀ i, idIndex s.initialPorts s.states[i].initialId = some (initialRoute i)

def System.prepare (s : System) : Option (Prepared s) :=
  if hv : s.valid = true then
    match he : s.program.resolve with
    | none => none
    | some es =>
      match hi : resolveTable (fun i : Fin s.program.inputs.length =>
          lookupIndex s.inputIds s.program.inputs[i].id) with
      | none => none
      | some inputs =>
        match ho : resolveTable (fun i : Fin s.states.length =>
            idIndex (s.program.assignments.map Assignment.output) s.states[i].derivativeId) with
        | none => none
        | some outputs =>
          match hc : resolveTable (fun i : Fin s.states.length =>
              idIndex s.initialPorts s.states[i].initialId) with
          | none => none
          | some initials => some {
              valid := hv
              expressions := es
              accepted := he
              inputRoute := inputs
              inputFound := resolveTable_correct _ _ hi
              outputRoute := fun i => Fin.cast (List.length_map ..) (outputs i)
              outputFound := by simpa using resolveTable_correct _ _ ho
              initialRoute := initials
              initialFound := resolveTable_correct _ _ hc
            }
  else none

/-- Input routing normalizes arbitrary source port order to [external, state]. -/
def Prepared.field {s : System} (p : Prepared s) :
    Gimle.Asgard.Circuit (s.externalIds.length + s.states.length) s.states.length :=
  .compose (Polynomial.route (fun i =>
    Fin.cast (by simp [System.inputIds]) (p.inputRoute i)))
    (.compose (compileList p.expressions) (Polynomial.route (fun i =>
      Fin.cast (program_count _ _ p.accepted).symm (p.outputRoute i))))

/-- External initial inputs retain their declaration order, independently of
state order. The routing pass places each explicitly paired value on its bank wire. -/
def Prepared.circuit {s : System} (p : Prepared s) :
    Circuit (s.externalIds.length + s.initialPorts.length) s.states.length :=
  .compose (.lift (.parallel (Wiring.identity s.externalIds.length)
    (Polynomial.route p.initialRoute))) (close s.evolveAlong p.field)



noncomputable def System.environment (s : System) (external : Point s.externalIds.length)
    (state : Point s.states.length) : Point s.inputIds.length :=
  fun i => pointAppend external state (Fin.cast (by simp [System.inputIds]) i)

noncomputable def initialValue (s : System) (initial : Point s.initialPorts.length)
    (id : String) : Option ℝ := (idIndex s.initialPorts id).map initial

noncomputable def outputValue (s : System) (outputs : Point s.program.assignments.length)
    (id : String) : Option ℝ :=
  (idIndex (s.program.assignments.map Assignment.output) id).map
    (fun i => outputs (Fin.cast (List.length_map ..) i))

/-- Independent named source relation. Assignments use Program's source
interpreter; input, derivative and initial values are looked up by declared ID.
No target circuit is run in this definition. -/
def System.Solves (s : System) (time : TimeDomain) (external : Signal s.externalIds.length)
    (initial : Point s.initialPorts.length) (state : Signal s.states.length) : Prop :=
  s.valid = true ∧ s.evolveAlong = time.axis ∧
    ∃ inputs : Signal s.program.inputs.length,
    ∃ outputs : Signal s.program.assignments.length,
      (∀ t i, idValue s.inputIds (s.environment (external t) (state t))
        s.program.inputs[i].id = some (inputs t i)) ∧
      (∀ t, s.program.Satisfies (inputs t) (List.ofFn (outputs t))) ∧
      (∀ i, initialValue s initial s.states[i].initialId = some (state time.start i)) ∧
      ∀ t ∈ time.domain, ∀ i, ∃ rate,
        outputValue s (outputs t) s.states[i].derivativeId = some rate ∧
          HasDerivWithinAt (fun t => state t i) rate time.domain t

noncomputable def Prepared.inputPoint {s : System} (p : Prepared s)
    (external : Point s.externalIds.length) (state : Point s.states.length) :
    Point s.program.inputs.length :=
  fun i => s.environment external state (p.inputRoute i)

noncomputable def Prepared.outputPoint {s : System} (p : Prepared s)
    (x : Point s.program.inputs.length) : Point s.program.assignments.length :=
  fun i => (compileList p.expressions).run x (Fin.cast (program_count _ _ p.accepted).symm i)

@[simp] theorem Prepared.input_value {s : System} (p : Prepared s)
    (u : Point s.externalIds.length) (x : Point s.states.length) (i : Fin s.program.inputs.length) :
    idValue s.inputIds (s.environment u x) s.program.inputs[i].id =
      some (p.inputPoint u x i) := by
  rw [idValue, p.inputFound i]
  rfl

@[simp] theorem Prepared.initial_value {s : System} (p : Prepared s)
    (initial : Point s.initialPorts.length) (i : Fin s.states.length) :
    initialValue s initial s.states[i].initialId = some (initial (p.initialRoute i)) := by
  rw [initialValue, p.initialFound i]
  rfl

@[simp] theorem Prepared.output_value {s : System} (p : Prepared s)
    (outputs : Point s.program.assignments.length) (i : Fin s.states.length) :
    outputValue s outputs s.states[i].derivativeId = some (outputs (p.outputRoute i)) := by
  rw [outputValue, p.outputFound i]
  simp

@[simp] theorem Prepared.outputs_correct {s : System} (p : Prepared s)
    (x : Point s.program.inputs.length) (y : Point s.program.assignments.length) :
    s.program.Satisfies x (List.ofFn y) ↔ p.outputPoint x = y := by
  rw [s.program.satisfies_iff_compiled _ p.accepted]
  rw [List.ofFn_congr (program_count _ _ p.accepted)]
  exact List.ofFn_inj

@[simp] theorem Prepared.field_run {s : System} (p : Prepared s)
    (u : Point s.externalIds.length) (x : Point s.states.length) :
    p.field.run (pointAppend u x) =
      fun i => p.outputPoint (p.inputPoint u x) (p.outputRoute i) := by
  simp only [Prepared.field, Gimle.Asgard.Circuit.run, Polynomial.route_correct]
  rfl

/-- The source interpreter and independently resolved ID lookups reduce to the
same derivative/initial relation, for every successful preparation. -/
theorem Prepared.source_correct {s : System} (p : Prepared s) (time : TimeDomain)
    (external : Signal s.externalIds.length) (initial : Point s.initialPorts.length)
    (state : Signal s.states.length) :
    s.Solves time external initial state ↔
      s.evolveAlong = time.axis ∧ state time.start = (fun i => initial (p.initialRoute i)) ∧
      ∀ t ∈ time.domain, ∀ i,
        HasDerivWithinAt (fun t => state t i)
          (p.field.run (pointAppend (external t) (state t)) i) time.domain t := by
  simp only [System.Solves, p.valid, true_and, p.input_value, p.initial_value,
    p.output_value, p.outputs_correct, Option.some.injEq, p.field_run]
  constructor
  · rintro ⟨axis, inputs, outputs, hi, ho, hc, hd⟩
    have inputs_eq : inputs = fun t => p.inputPoint (external t) (state t) := by
      funext t i
      exact (hi t i).symm
    subst inputs
    have outputs_eq : outputs = fun t => p.outputPoint (p.inputPoint (external t) (state t)) := by
      funext t
      exact (ho t).symm
    subst outputs
    refine ⟨axis, ?_, ?_⟩
    · funext i
      exact (hc i).symm
    · intro t ht i
      obtain ⟨rate, hr, deriv⟩ := hd t ht i
      rwa [← hr] at deriv
  · rintro ⟨axis, hc, hd⟩
    refine ⟨axis, (fun t => p.inputPoint (external t) (state t)),
      (fun t => p.outputPoint (p.inputPoint (external t) (state t))),
      (fun _ _ => rfl), (fun _ => rfl), ?_, ?_⟩
    · intro i
      exact (congrFun hc i).symm
    · intro t ht i
      exact ⟨_, rfl, hd t ht i⟩

/-- Full named-source preservation through input/output/IC routing, the compiled
polynomial field, the integrator bank, and actual existential feedback trace. -/
theorem Prepared.solves_iff_circuit {s : System} (p : Prepared s) (time : TimeDomain)
    (external : Signal s.externalIds.length) (initial : Point s.initialPorts.length)
    (state : Signal s.states.length) :
    s.Solves time external initial state ↔
      p.circuit.Rel time (signalAppend external (fun _ => initial)) state := by
  rw [p.source_correct]
  simp only [Prepared.circuit, Circuit.Rel]
  have hroute : (fun t => (Gimle.Asgard.Circuit.parallel
      (Wiring.identity s.externalIds.length) (Polynomial.route p.initialRoute)).run
        (signalAppend external (fun _ => initial) t)) =
      signalAppend external (fun _ i => initial (p.initialRoute i)) := by
    funext t
    simp [signalAppend]
  rw [hroute]
  simp only [exists_eq_left, close_correct]

theorem Prepared.circuit_correct {s : System} (p : Prepared s) (time : TimeDomain)
    (external : Signal s.externalIds.length) (initial : Point s.initialPorts.length)
    (state : Signal s.states.length) :
    p.circuit.Rel time (signalAppend external (fun _ => initial)) state ↔
      s.evolveAlong = time.axis ∧ state time.start = (fun i => initial (p.initialRoute i)) ∧
      ∀ t ∈ time.domain, ∀ i,
        HasDerivWithinAt (fun t => state t i)
          (p.field.run (pointAppend (external t) (state t)) i) time.domain t :=
  (p.solves_iff_circuit time external initial state).symm.trans
    (p.source_correct time external initial state)

#print axioms Prepared.solves_iff_circuit

end Gimle.Asgard.Dynamics
