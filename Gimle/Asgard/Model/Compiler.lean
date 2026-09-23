import Gimle.Asgard.Model.Resolution

namespace Gimle.Asgard.Model
open Polynomial

/-- Runtime coordinates are explicit stable IDs, never inferred from name order. -/
def index {n : Nat} (ids : Fin n → String) (id : String) : Option (Fin n) :=
  (List.finRange n).find? (fun i => ids i == id)

def Body.parameter (b : Body) (id : String) : Option ℚ :=
  (b.parameters.find? (·.id == id)).map RationalBinding.value

def Body.inputTerm {n : Nat} (b : Body) (ids : Fin n → String) (p : Port) : Option (Expr n) :=
  if p.role == .parameter then (b.parameter p.id).map Expr.constant
  else (index ids p.id).map Expr.var

/-- Independent real input interpretation: constants for fixed parameters,
coordinates for runtime ports. It does not evaluate a compiled expression. -/
noncomputable def Body.inputValue {n : Nat} (b : Body) (ids : Fin n → String)
    (x : Point n) (p : Port) : Option ℝ :=
  if p.role == .parameter then (b.parameter p.id).map (fun q : ℚ => (q : ℝ))
  else (index ids p.id).map x

def Body.seed {n : Nat} (b : Body) (ids : Fin n → String) (name : String) : Option (Expr n) :=
  (b.program.inputs.find? (·.name == name)).bind (b.inputTerm ids)

noncomputable def Body.inputEnvironment {n : Nat} (b : Body) (ids : Fin n → String)
    (x : Point n) (name : String) : Option ℝ :=
  (b.program.inputs.find? (·.name == name)).bind (b.inputValue ids x)

theorem Body.seed_correct {n : Nat} (b : Body) (ids : Fin n → String) (x : Point n) :
    Evaluated (b.seed ids) x = b.inputEnvironment ids x := by
  funext name
  unfold Evaluated Body.seed Body.inputEnvironment
  cases hp : b.program.inputs.find? (·.name == name) with
  | none => rfl
  | some p =>
      simp only [Option.bind_some, Body.inputTerm, Body.inputValue]
      split
      · cases b.parameter p.id <;> rfl
      · cases index ids p.id <;> rfl

/-- Fused exact parameter specialization and runtime-variable substitution. Any
unresolved auxiliary stays unresolved until its assignment becomes ready. -/
theorem Body.parameter_substitution_correct {n : Nat} (b : Body) (ids : Fin n → String)
    (rhs : NamedExpr) (x : Point n) :
    (rhs.resolve (b.seed ids)).map (Expr.eval x) = rhs.eval (b.inputEnvironment ids x) := by
  rw [rhs.resolve_correct]
  change rhs.eval (Evaluated (b.seed ids) x) = _
  rw [b.seed_correct]

/-- Original simultaneous source equations, independent of scheduling and targets.
Unused assignments and fixed parameters remain requirements of this relation. -/
def Body.Source {n : Nat} (b : Body) (ids : Fin n → String) (x : Point n)
    (env : String → Option ℝ) : Prop :=
  Agrees (b.inputEnvironment ids x) env ∧ Equations b.program.assignments env

structure Prepared {n : Nat} (b : Body) (ids : Fin n → String) where
  resolution : Resolution b.program.assignments (b.seed ids)
  inputsComplete : ∀ p ∈ b.program.inputs, b.seed ids p.name ≠ none
  complete : Complete b.program.assignments resolution.env

/-- A successful result carries the final acceptance equations, not only a flag. -/
def Body.prepare {n : Nat} (b : Body) (ids : Fin n → String) : Except Diagnostic (Prepared b ids) :=
  if hi : ∀ p ∈ b.program.inputs, b.seed ids p.name ≠ none then
    let result := schedule b.program.assignments.length ⟨b.seed ids, .start⟩
    if hc : Complete b.program.assignments result.env then .ok ⟨result, hi, hc⟩
    else
      match b.program.assignments.find? (fun a => (result.env a.output.name).isNone) with
      | some a => .error ⟨.cyclicDependency, a.output.id, a.output.name⟩
      | none => .error ⟨.incompleteResolution, "equations", "final symbolic environment"⟩
  else .error ⟨.missingBinding, "inputs", "runtime coordinate or fixed parameter"⟩

noncomputable def Prepared.environment {n : Nat} {b : Body} {ids : Fin n → String}
    (p : Prepared b ids) (x : Point n) : String → Option ℝ :=
  Evaluated p.resolution.env x

theorem Prepared.source {n : Nat} {b : Body} {ids : Fin n → String}
    (p : Prepared b ids) (x : Point n) : b.Source ids x (p.environment x) := by
  refine ⟨?_, complete_equations _ _ p.complete x⟩
  rw [← b.seed_correct]
  intro name value h
  change ((b.seed ids) name).map (Expr.eval x) = some value at h
  cases hs : b.seed ids name with
  | none => simp [hs] at h
  | some e =>
      have extended := p.resolution.trace.extends name e hs
      have value_eq : e.eval x = value := by simpa [hs] using h
      simp [Prepared.environment, Evaluated, extended, value_eq]

theorem Prepared.forced {n : Nat} {b : Body} {ids : Fin n → String}
    (p : Prepared b ids) (x : Point n) (env : String → Option ℝ)
    (source : b.Source ids x env) : Agrees (p.environment x) env := by
  apply p.resolution.trace.forced x env
  · simpa [b.seed_correct] using source.1
  · exact source.2

/-- Source-value selection by original stable ID, independent of target routing. -/
def Body.value {α : Type} (b : Body) (env : String → Option α) (id : String) : Option α :=
  ((b.program.inputs ++ b.program.assignments.map Assignment.output).find?
    (·.id == id)).bind (fun p => env p.name)

theorem Body.value_agrees {α : Type} (b : Body) {a c : String → Option α}
    (h : Agrees a c) (id : String) (value : α) (found : b.value a id = some value) :
    b.value c id = some value := by
  unfold Body.value at *
  cases hp : (b.program.inputs ++ b.program.assignments.map Assignment.output).find?
    (·.id == id) with
  | none => simp [hp] at found
  | some p => simpa [hp] using h p.name value (by simpa [hp] using found)

theorem Body.value_evaluated {n : Nat} (b : Body) (env : String → Option (Expr n))
    (x : Point n) (id : String) :
    b.value (Evaluated env x) id = (b.value env id).map (Expr.eval x) := by
  unfold Body.value
  cases (b.program.inputs ++ b.program.assignments.map Assignment.output).find?
    (·.id == id) <;> rfl

structure Selected {n m : Nat} {b : Body} {ids : Fin n → String}
    (p : Prepared b ids) (refs : Fin m → String) where
  expressions : Fin m → Expr n
  found : ∀ i, b.value p.resolution.env (refs i) = some (expressions i)

def Prepared.select {n m : Nat} {b : Body} {ids : Fin n → String}
    (p : Prepared b ids) (refs : Fin m → String) : Option (Selected p refs) :=
  match h : Dynamics.resolveTable (fun i => b.value p.resolution.env (refs i)) with
  | none => none
  | some expressions => some ⟨expressions, Dynamics.resolveTable_correct _ _ h⟩

def Selected.circuit {n m : Nat} {b : Body} {ids : Fin n → String}
    {p : Prepared b ids} {refs : Fin m → String} (s : Selected p refs) :
    Gimle.Asgard.Circuit n m := compileOutputs s.expressions

/-- Observable source relation may quantify hidden named auxiliary values. -/
def Body.Observes {n m : Nat} (b : Body) (ids : Fin n → String) (refs : Fin m → String)
    (x : Point n) (y : Point m) : Prop :=
  ∃ env, b.Source ids x env ∧ ∀ i, b.value env (refs i) = some (y i)

theorem Selected.value_correct {n m : Nat} {b : Body} {ids : Fin n → String}
    {p : Prepared b ids} {refs : Fin m → String} (s : Selected p refs) (x : Point n) (i : Fin m) :
    b.value (p.environment x) (refs i) = some (s.expressions i |>.eval x) := by
  rw [Prepared.environment, b.value_evaluated, s.found]
  rfl

/-- Both directions relate the compiled outputs to the ORIGINAL equations. -/
theorem Selected.correct {n m : Nat} {b : Body} {ids : Fin n → String}
    {p : Prepared b ids} {refs : Fin m → String} (s : Selected p refs) (x : Point n) (y : Point m) :
    b.Observes ids refs x y ↔ s.circuit.run x = y := by
  rw [Selected.circuit, compileOutputs_correct]
  constructor
  · rintro ⟨env, source, outputs⟩
    funext i
    have value := b.value_agrees (p.forced x env source) (refs i) _ (s.value_correct x i)
    rw [outputs i] at value
    exact (Option.some.inj value).symm
  · intro outputs
    refine ⟨p.environment x, p.source x, ?_⟩
    intro i
    simpa [← outputs] using s.value_correct x i

def Body.runtimePorts (b : Body) : List Port := b.program.inputs.filter (·.role != .parameter)
def Body.runtimeIds (b : Body) (i : Fin b.runtimePorts.length) : String := b.runtimePorts[i].id
def Body.observationIds (b : Body) (i : Fin b.observations.length) : String :=
  b.observations[i].sourceId

structure PolynomialModel (b : Body) where
  valid : (Declaration.polynomial b).validate = .ok ()
  prepared : Prepared b b.runtimeIds
  outputs : Selected prepared b.observationIds

def compilePolynomial (b : Body) : Except Diagnostic (PolynomialModel b) :=
  match hv : (Declaration.polynomial b).validate with
  | .error error => .error error
  | .ok () => do
      let prepared ← b.prepare b.runtimeIds
      match prepared.select b.observationIds with
      | none => .error ⟨.unknownReference, "observations", "selected source ID"⟩
      | some outputs => return ⟨hv, prepared, outputs⟩

#print axioms Body.parameter_substitution_correct
#print axioms Prepared.source
#print axioms Selected.correct
end Gimle.Asgard.Model
