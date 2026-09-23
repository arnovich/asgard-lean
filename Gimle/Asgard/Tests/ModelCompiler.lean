import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Compile.Syntax

namespace Gimle.Asgard.Tests.ModelCompiler
open Polynomial Model

def forward : Body := {
  program := ⟨[⟨"x", "x", .input⟩, ⟨"a", "a", .parameter⟩],
    equations% { z := y + a*x; y := x*x; }⟩
  parameters := [⟨"a", 1 / 3⟩]
  observations := [⟨⟨"obs-z", "z", .output⟩, "z"⟩]
}
example : (compilePolynomial forward).isOk = true := by decide +kernel
example : (compilePolynomial { forward with program :=
    { forward.program with assignments := equations% { z := y; y := z; } } }).isOk = false := by decide +kernel


def polynomial : PolynomialModel forward :=
  (compilePolynomial forward).toOption.get (by decide +kernel)

example : polynomial.outputs.expressions =
    (![Expr.add (.mul (.var 0) (.var 0)) (.mul (.constant (1 / 3)) (.var 0))] : Fin 1 → Expr 1) := by
  decide +kernel

example : polynomial.outputs.circuit.run (![3] : Point 1) = ![(10 : ℝ)] := by
  rw [Selected.circuit, compileOutputs_correct]
  have terms : polynomial.outputs.expressions =
      (![Expr.add (.mul (.var 0) (.var 0)) (.mul (.constant (1 / 3)) (.var 0))] : Fin 1 → Expr 1) := by decide +kernel
  rw [terms]
  ext i
  change Fin 1 at i
  fin_cases i
  norm_num [Expr.eval]

example : forward.Observes forward.runtimeIds forward.observationIds (![3] : Point 1) ![10] := by
  apply (polynomial.outputs.correct _ _).mpr
  rw [Selected.circuit, compileOutputs_correct]
  have terms : polynomial.outputs.expressions =
      (![Expr.add (.mul (.var 0) (.var 0)) (.mul (.constant (1 / 3)) (.var 0))] : Fin 1 → Expr 1) := by decide +kernel
  rw [terms]
  ext i
  change Fin 1 at i
  fin_cases i
  norm_num [Expr.eval]

-- A valid changed coefficient must not inherit the old output claim.
def changed : Body := { forward with parameters := [⟨"a", 2 / 3⟩] }
def changedModel : PolynomialModel changed :=
  (compilePolynomial changed).toOption.get (by decide +kernel)
example : ¬ changed.Observes changed.runtimeIds changed.observationIds (![3] : Point 1) ![10] := by
  rw [changedModel.outputs.correct, Selected.circuit, compileOutputs_correct]
  have terms : changedModel.outputs.expressions =
      (![Expr.add (.mul (.var 0) (.var 0)) (.mul (.constant (2 / 3)) (.var 0))] : Fin 1 → Expr 1) := by decide +kernel
  rw [terms]
  intro bad
  have := congrFun bad (0 : Fin 1)
  norm_num [Expr.eval] at this

-- Empty interfaces, exact constants, repeated selection and unused inputs.
example : (compilePolynomial {
    program := ⟨[], equations% { c := rat(2, 7); }⟩
    observations := [⟨⟨"o", "c", .output⟩, "c"⟩] }).isOk = true := by decide +kernel
example : (compilePolynomial { forward with observations := [] }).isOk = true := by decide +kernel
example : (compilePolynomial { forward with observations :=
    [⟨⟨"o1", "first", .output⟩, "x"⟩, ⟨⟨"o2", "second", .output⟩, "x"⟩] }).isOk = true := by
  decide +kernel

def manyInputs : Body := {
  program := ⟨(List.range 7).map (fun i => ⟨s!"p{i}", s!"x{i}", .input⟩),
    equations% { y := x6 - x1; }⟩
  observations := [⟨⟨"o", "y", .output⟩, "y"⟩]
}
def manyModel : PolynomialModel manyInputs :=
  (compilePolynomial manyInputs).toOption.get (by decide +kernel)
example : manyModel.outputs.expressions = (![Expr.add (.var 6) (.neg (.var 1))] : Fin 1 → Expr 7) := by decide +kernel

-- Undefined values do not satisfy real equations, independently of scheduling.
example : ¬ Equations (equations% { x := x + 1; }) (fun _ => none) := by
  simp [Equations]

def constantBody : Body := {
  program := ⟨[], equations% { c := rat(2, 7); }⟩
  observations := [⟨⟨"o", "c", .output⟩, "c"⟩]
}
def constantModel : PolynomialModel constantBody :=
  (compilePolynomial constantBody).toOption.get (by decide +kernel)
example : constantModel.outputs.circuit.run ![] = ![(2/7 : ℝ)] := by
  rw [Selected.circuit, compileOutputs_correct]
  have terms : constantModel.outputs.expressions =
      (![Expr.constant (2/7)] : Fin 1 → Expr 0) := by decide +kernel
  rw [terms]
  ext i
  change Fin 1 at i
  fin_cases i
  norm_num [Expr.eval]

def repeated : Body := { forward with observations :=
  [⟨⟨"o1", "first", .output⟩, "x"⟩, ⟨⟨"o2", "second", .output⟩, "x"⟩] }
def repeatedModel : PolynomialModel repeated :=
  (compilePolynomial repeated).toOption.get (by decide +kernel)
example : repeatedModel.outputs.circuit.run (![3] : Point 1) = ![(3 : ℝ), 3] := by
  rw [Selected.circuit, compileOutputs_correct]
  have terms : repeatedModel.outputs.expressions =
      (![Expr.var 0, .var 0] : Fin 2 → Expr 1) := by decide +kernel
  rw [terms]
  ext i
  change Fin 2 at i
  fin_cases i <;> norm_num [Expr.eval]

-- An unused cycle still fails: selecting a good output does not discard bad equations.
example : (compilePolynomial {
    program := ⟨[], equations% { c := 1; u := v; v := u; }⟩
    observations := [⟨⟨"o", "c", .output⟩, "c"⟩] }).map (fun _ => ()) =
    .error ⟨.cyclicDependency, "u", "u"⟩ := by decide +kernel
example : (compilePolynomial { forward with parameters := [] }).map (fun _ => ()) =
    .error ⟨.missingBinding, "parameters", "a"⟩ := by decide +kernel
example : (compilePolynomial { forward with program :=
    { forward.program with assignments := equations% { z := missing; } } }).map (fun _ => ()) =
    .error ⟨.unknownReference, "z", "missing"⟩ := by decide +kernel

/-- dx = 2*a*y, dy = -a*x-y. State, input, assignment, IC and output orders
are different; helper is a shared forward reference. -/
def field : Body := {
  program := ⟨[⟨"state-y", "y", .state⟩, ⟨"param-a", "a", .parameter⟩,
    ⟨"state-x", "x", .state⟩, ⟨"param-unused", "unused", .parameter⟩],
    equations% { dy := -a*x - y; dx := helper + helper; helper := a*y; energy := x^2 + y^2; }⟩
  parameters := [⟨"param-unused", 7⟩, ⟨"param-a", 1 / 3⟩]
  observations := [⟨⟨"obs-y", "y", .output⟩, "state-y"⟩,
    ⟨⟨"obs-energy", "E", .output⟩, "energy"⟩,
    ⟨⟨"obs-x", "x", .output⟩, "state-x"⟩]
}
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩]
  initialPorts := [⟨"initial-y", "y0", .initial⟩, ⟨"initial-x", "x0", .initial⟩]
  initialValues := [⟨"initial-x", 1 / 2⟩, ⟨"initial-y", -2⟩]
  axis := ⟨"time-axis", "x"⟩
  evolveAlong := "time-axis"
  start := 2 / 3
}
def model : ContinuousModel field evolution :=
  (compileContinuous field evolution).toOption.get (by decide +kernel)
def linear : LinearView model := model.linear.get (by decide +kernel)

example : linear.matrix = ![![0, 2/3], ![-1/3, -1]] := by decide +kernel
example : model.initials = ![1/2, -2] := by decide +kernel
example : evolution.time.start = (2 / 3 : ℝ) := by norm_num [Evolution.time, evolution]

example : model.rates.circuit.run model.initial = ![(-4/3 : ℝ), 11/6] := by
  rw [Selected.circuit, compileOutputs_correct]
  have hx : model.initial = ![(1/2 : ℝ), -2] := by
    have h : model.initials = ![1/2, -2] := by decide +kernel
    change (fun i : Fin 2 => (model.initials i : ℝ)) = _
    rw [h]
    ext i
    fin_cases i <;> norm_num
  have matrix : linear.matrix = ![![0, 2/3], ![-1/3, -1]] := by decide +kernel
  ext i
  change Fin 2 at i
  rw [linear.rhs_correct, hx]
  rw [matrix]
  change (∑ j : Fin 2, ((![![0, 2/3], ![-1/3, -1]] : Fin 2 → Fin 2 → ℚ) i j : ℝ) * ![(1/2 : ℝ), -2] j) = ![(-4/3 : ℝ), 11/6] i
  fin_cases i <;> norm_num [Fin.sum_univ_two]

theorem initial_eq : model.initial = (![(1/2 : ℝ), -2] : Point 2) := by
  change (fun i : Fin 2 => (model.initials i : ℝ)) = _
  have values : model.initials = ![1/2, -2] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

theorem observed_initial : model.outputs.circuit.run model.initial =
    (![-2, 17/4, 1/2] : Point 3) := by
  rw [initial_eq, Selected.circuit, compileOutputs_correct]
  have terms : model.outputs.expressions =
      (![Expr.var 1, .add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)),
        .var 0] : Fin 3 → Expr 2) := by decide +kernel
  rw [terms]
  ext i
  change Fin 3 at i
  fin_cases i <;> norm_num [Expr.eval]

-- Changing only declaration order preserves ID-routed expressions and initial data.
def permuted : Body := { field with
  program := { field.program with
    inputs := field.program.inputs.reverse
    assignments := field.program.assignments.reverse }
  parameters := field.parameters.reverse }
def permutedEvolution : Evolution := { evolution with
  initialPorts := evolution.initialPorts.reverse,
  initialValues := evolution.initialValues.reverse }
def permutedModel : ContinuousModel permuted permutedEvolution :=
  (compileContinuous permuted permutedEvolution).toOption.get (by decide +kernel)
example : permutedModel.rates.expressions = model.rates.expressions := by decide +kernel
example : permutedModel.outputs.expressions = model.outputs.expressions := by decide +kernel
example : permutedModel.initials = model.initials := by decide +kernel

def reordered : Body := { field with observations := field.observations.reverse }
def reorderedModel : ContinuousModel reordered evolution :=
  (compileContinuous reordered evolution).toOption.get (by decide +kernel)
example : reorderedModel.rates.expressions = model.rates.expressions := by decide +kernel
example : reorderedModel.outputs.circuit.run model.initial ≠
    (![-2, 17/4, 1/2] : Point 3) := by
  rw [initial_eq, Selected.circuit, compileOutputs_correct]
  have terms : reorderedModel.outputs.expressions =
      (![Expr.var 0, .add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)),
        .var 1] : Fin 3 → Expr 2) := by decide +kernel
  rw [terms]
  intro bad
  have := congrFun bad (0 : Fin 3)
  norm_num [Expr.eval] at this

-- The original-source theorem composes with actual feedback for every trajectory.
example (state : Dynamics.Signal 2) : field.Solves evolution state ↔ model.Realizes state :=
  model.solves_iff_realizes state
example : ∃ state, model.Realizes state := linear.exists_realization
example {x y : Dynamics.Signal 2} (hx : model.Realizes x) (hy : model.Realizes y) :
    Set.EqOn x y evolution.time.domain := linear.unique_realization hx hy

example (state : Dynamics.Signal 2) (h : model.Realizes state) :
    state evolution.time.start ≠ ![(0 : ℝ), 0] := by
  have initial := ((model.solves_iff_field _).mp ((model.solves_iff_realizes _).mpr h)).1
  have values : model.initials = ![1/2, -2] := by decide +kernel
  intro bad
  have := congrFun initial 0
  norm_num [bad, ContinuousModel.initial, values] at this

-- Nonlinear translation remains available when linear recognition declines it.
def nonlinear : Body := { field with program := { field.program with assignments :=
  equations% { dy := -x; dx := y*y; energy := x^2 + y^2; } } }
def nonlinearModel : ContinuousModel nonlinear evolution :=
  (compileContinuous nonlinear evolution).toOption.get (by decide +kernel)
example : nonlinearModel.linear.isNone = true := by decide +kernel
example (state : Dynamics.Signal 2) :
    nonlinear.Solves evolution state ↔ nonlinearModel.Realizes state :=
  nonlinearModel.solves_iff_realizes state

-- IC and axis errors are caught before compilation.
example : (compileContinuous field { evolution with evolveAlong := "x" }).map (fun _ => ()) =
    .error ⟨.wrongAxis, "evolveAlong", "x"⟩ := by decide +kernel
example : (compileContinuous field { evolution with initialValues := [] }).map (fun _ => ()) =
    .error ⟨.missingBinding, "initialValues", "initial-y"⟩ := by decide +kernel

-- Output order and hiding do not change the state feedback or its domain.
def hidden : Body := { field with observations := [⟨⟨"obs-E", "E", .output⟩, "energy"⟩] }
def hiddenModel : ContinuousModel hidden evolution :=
  (compileContinuous hidden evolution).toOption.get (by decide +kernel)
example : hiddenModel.rates.expressions = model.rates.expressions := by decide +kernel
example (output : Dynamics.Signal 1) :
    hidden.ObservedSolution evolution output ↔ hiddenModel.ObservedRealization output :=
  hiddenModel.observations_correct output
example (x y : Dynamics.Signal 1) (same : Set.EqOn x y evolution.time.domain) :
    hiddenModel.ObservedRealization x ↔ hiddenModel.ObservedRealization y := by
  unfold ContinuousModel.ObservedRealization
  constructor
  · rintro ⟨state, solves, outputs⟩
    exact ⟨state, solves, fun t ht => (outputs t ht).trans (same ht)⟩
  · rintro ⟨state, solves, outputs⟩
    exact ⟨state, solves, fun t ht => (outputs t ht).trans (same ht).symm⟩

#print axioms Selected.correct
#print axioms ContinuousModel.solves_iff_realizes
#print axioms ContinuousModel.observations_correct
#print axioms LinearView.exists_realization
end Gimle.Asgard.Tests.ModelCompiler
