import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Visualization.Model
import Gimle.Asgard.Compile.Syntax

/-! A coupled three-state model with exact field and observation checks.

One declaration is the single source for the compiled field, its initialization,
and its observations. The definitions support downstream trajectory proofs;
no floating-point or worker result appears among the theorems.

This module deliberately does not import `Model.Execution`: that reaches the
Python process client, and a property proof must not pin a subprocess bridge to
obtain the model's mathematics. The requests are in
`Examples/ThreeStateExecution.lean`. -/
namespace Gimle.Asgard.Examples.ThreeState
open Polynomial Model

/-- x' = -a*x + y - z, y' = -x - b*y + z, z' = x - y - c*z, with the energy
V = x²+y²+z² and its exact rate as auxiliary assignments.

The coupling is skew-symmetric, so the cross terms cancel in V' and only the
damping survives; `dissipation` records that exact rate.

Input, derivative, observation and initial-condition orders deliberately differ,
`sqx`/`sqy`/`sqz` are shared by two assignments and declared after both uses, and
`param-unused` is bound but never read. None of this is silently reordered. -/
def body (a b c : ℚ) : Body := {
  program := ⟨[⟨"state-y", "y", .state⟩, ⟨"param-c", "c", .parameter⟩,
      ⟨"state-z", "z", .state⟩, ⟨"param-a", "a", .parameter⟩,
      ⟨"state-x", "x", .state⟩, ⟨"param-b", "b", .parameter⟩,
      ⟨"param-unused", "unused", .parameter⟩],
    equations% {
      dy := -x - b * y + z;
      V := sqx + sqy + sqz;
      dz := x - y - c * z;
      dissipation := -2 * (a * sqx + b * sqy + c * sqz);
      dx := -a * x + y - z;
      sqx := x ^ 2;
      sqy := y ^ 2;
      sqz := z ^ 2;
    }⟩
  parameters := [⟨"param-unused", 7⟩, ⟨"param-a", a⟩,
    ⟨"param-b", b⟩, ⟨"param-c", c⟩]
  observations := [⟨⟨"obs-z", "z", .output⟩, "state-z"⟩,
    ⟨⟨"obs-x", "x", .output⟩, "state-x"⟩,
    ⟨⟨"obs-y", "y", .output⟩, "state-y"⟩,
    ⟨⟨"obs-v", "V", .output⟩, "V"⟩]
}

/-- State order is [x,y,z] with initial state (1,2,-1) at t=2. The initial-port
and initial-value orders differ from it again; bindings are by stable ID. -/
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩,
    ⟨"state-z", "dz", "initial-z"⟩]
  initialPorts := [⟨"initial-z", "z0", .initial⟩, ⟨"initial-x", "x0", .initial⟩,
    ⟨"initial-y", "y0", .initial⟩]
  initialValues := [⟨"initial-y", 2⟩, ⟨"initial-z", -1⟩, ⟨"initial-x", 1⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 2
}

/-- The baseline instantiates (a,b,c)=(1/3,1/2,2). `body` stays parameterised
so downstream proofs can instantiate other exact triples without restating the
declaration; compilation itself is checked per instantiation. -/
def model : ContinuousModel (body (1 / 3) (1 / 2) 2) evolution :=
  (compileContinuous (body (1 / 3) (1 / 2) 2) evolution).toOption.get (by decide +kernel)

/-- The compiled RHS is the declared equations with the fixed parameters
substituted and `^` normalized into multiplication, routed to state order
[x,y,z]. Coordinates 0,1,2 are x,y,z. Private: it is compiler-internal
normalization, and `rates_formula` is the semantic statement to depend on. -/
private theorem rates_expressions : model.rates.expressions =
    (![.add (.add (.mul (.neg (.constant (1 / 3))) (.var 0)) (.var 1)) (.neg (.var 2)),
      .add (.add (.neg (.var 0)) (.neg (.mul (.constant (1 / 2)) (.var 1)))) (.var 2),
      .add (.add (.var 0) (.neg (.var 1))) (.neg (.mul (.constant 2) (.var 2)))] :
      Fin 3 → Expr 3) := by decide +kernel

/-- Observations keep their declared display order [z,x,y,V] over state order
[x,y,z]; the first three are pure selections and V is the shared auxiliary.
Private for the same reason as `rates_expressions`. -/
private theorem outputs_expressions : model.outputs.expressions =
    (![.var 2, .var 0, .var 1,
      .add (.add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)))
        (.mul (.mul (.constant 1) (.var 2)) (.var 2))] : Fin 4 → Expr 3) := by decide +kernel

theorem initial_eq : model.initial = (![1, 2, -1] : Point 3) := by
  change (fun i : Fin 3 => (model.initials i : ℝ)) = _
  have values : model.initials = ![1, 2, -1] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

/-- The exact field at the initial state: (8/3, -3, 1). -/
theorem rates_at_initial :
    model.rates.circuit.run model.initial = (![8 / 3, -3, 1] : Point 3) := by
  rw [initial_eq, Selected.circuit, compileOutputs_correct, rates_expressions]
  ext i
  change Fin 3 at i
  fin_cases i <;> norm_num [Expr.eval, Matrix.cons_val_two, Matrix.tail_cons]

/-- One exact simultaneous Euler step of the compiled field. Every coordinate
reads the same pre-step point, so this is the simultaneous update rather than a
sequential one, and it evaluates the actual compiled circuit rather than a
separately authored right-hand side. This is an exact oracle for comparison; it
is not a claim about the trajectory, and no numerical result appears here. -/
noncomputable def eulerStep (h : ℝ) (x : Point 3) : Point 3 :=
  fun i => x i + h * model.rates.circuit.run x i

/-- The exact Euler oracle at h=1/8 from (1,2,-1): (4/3, 13/8, -7/8). -/
theorem euler_step_at_initial :
    eulerStep (1 / 8) model.initial = (![4 / 3, 13 / 8, -7 / 8] : Point 3) := by
  funext i
  rw [eulerStep, rates_at_initial, initial_eq]
  fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- Observations at the initial state, in declared order [z,x,y,V]. V=6 there,
which supplies the initial value for a trajectory energy bound. -/
theorem observed_initial :
    model.outputs.circuit.run model.initial = (![-1, 1, 2, 6] : Point 4) := by
  rw [initial_eq, Selected.circuit, compileOutputs_correct, outputs_expressions]
  ext i
  change Fin 4 at i
  fin_cases i <;> norm_num [Expr.eval, Matrix.cons_val_two, Matrix.tail_cons]

/-- Observing the Euler oracle point through the same compiled observation
circuit gives energy 1493/288; V is never retyped downstream. -/
theorem observed_euler_step :
    model.outputs.circuit.run (eulerStep (1 / 8) model.initial) =
      (![-7 / 8, 4 / 3, 13 / 8, 1493 / 288] : Point 4) := by
  rw [euler_step_at_initial, Selected.circuit, compileOutputs_correct, outputs_expressions]
  ext i
  change Fin 4 at i
  fin_cases i <;> norm_num [Expr.eval, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## Definitions for downstream property proofs

These name the compiled field, its initialized feedback and its observations so
property proofs quantify over the objects the compiler produced. The
correspondence they rest on is `ContinuousModel.solves_iff_realizes` and
`ContinuousModel.observations_correct`; nothing here proves a property. -/

/-- The compiled field closed with integrators at the declared axis. The start
time is not part of `feedback`; it enters through `Realizes` via the evolution's
time domain. An `abbrev` so downstream proofs need no unfolding step. -/
abbrev feedback : Dynamics.Circuit 3 3 := model.feedback

/-- Trajectories of that initialized feedback, with initial state (1,2,-1) at
t=2. An `abbrev` so downstream proofs need no unfolding step. -/
abbrev Realizes (state : Dynamics.Signal 3) : Prop := model.Realizes state

/-- The original declared equations and initial conditions have exactly the
trajectories of the compiled feedback. -/
theorem solves_iff_realizes (state : Dynamics.Signal 3) :
    (body (1 / 3) (1 / 2) 2).Solves evolution state ↔ Realizes state := model.solves_iff_realizes state

/-- The compiled field in closed form, in state order [x,y,z]. -/
theorem rates_formula (x : Point 3) : model.rates.circuit.run x =
    (![-(1 / 3) * x 0 + x 1 - x 2, -x 0 - 1 / 2 * x 1 + x 2,
      x 0 - x 1 - 2 * x 2] : Point 3) := by
  rw [Selected.circuit, compileOutputs_correct, rates_expressions]
  ext i
  change Fin 3 at i
  fin_cases i <;> norm_num [Expr.eval, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- All four observations in declared order: the three state selections and the
energy V = x²+y²+z².

This pins V to the compiled observation circuit. The `energyIndex` and
`energy_at` definitions below select its value directly while retaining the
observation count from `body.observations.length`. -/
theorem observations_formula (x : Point 3) : model.outputs.circuit.run x =
    (![x 2, x 0, x 1, x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2] : Point 4) := by
  rw [Selected.circuit, compileOutputs_correct, outputs_expressions]
  ext i
  change Fin 4 at i
  fin_cases i <;> norm_num [Expr.eval, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The declared exact energy rate, selected from the same prepared source. -/
def energyRate : Selected model.prepared (fun _ : Fin 1 => "dissipation") :=
  (model.prepared.select _).get (by decide +kernel)

theorem energyRate_value (x : Point 3) : (energyRate.expressions 0).eval x =
    -2 * (1 / 3 * x 0 ^ 2 + 1 / 2 * x 1 ^ 2 + 2 * x 2 ^ 2) := by
  have terms : energyRate.expressions =
      (![.mul (.neg (.constant 2))
          (.add (.add (.mul (.constant (1 / 3))
              (.mul (.mul (.constant 1) (.var 0)) (.var 0)))
            (.mul (.constant (1 / 2)) (.mul (.mul (.constant 1) (.var 1)) (.var 1))))
            (.mul (.constant 2) (.mul (.mul (.constant 1) (.var 2)) (.var 2))))] :
        Fin 1 → Expr 3) := by decide +kernel
  rw [terms]
  norm_num [Expr.eval]
  ring

/-- The algebraic heart of the model: the coupling is skew-symmetric, so pairing
the state with the compiled field leaves only the damping, and the cancellation
is a fact about this compiled field rather than a retyped right-hand side.

With the chain rule this gives V' = -2(a*x²+b*y²+c*z²) along any trajectory.
That is one ingredient of a trajectory energy bound and not the whole
argument: reaching [0,6] for t≥2 also needs a,b,c ≥ 0 so the rate is nonpositive,
monotonicity on the forward half-line, and state 2 = initial from `Body.Solves`.
None of those is claimed here. -/
theorem energy_pairing (x : Point 3) :
    2 * ∑ i, x i * model.rates.circuit.run x i = (energyRate.expressions 0).eval x := by
  rw [energyRate_value, rates_formula]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The fourth selected observation is V. Indexing the compiled observation
circuit is what the routed `Circuit 3 1` selector could not express without the
observation count syntactically; `⟨3, by decide⟩` supplies it directly. -/
def energyIndex : Fin (body (1 / 3) (1 / 2) 2).observations.length := ⟨3, by decide⟩

/-- V read off the compiled observation circuit at its own index, the shape a
property proof consumes. -/
theorem energy_at (x : Point 3) :
    model.outputs.circuit.run x energyIndex = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [Selected.circuit, compileOutputs_correct]
  change (model.outputs.expressions energyIndex).eval x = _
  have expression : model.outputs.expressions energyIndex =
      (.add (.add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)))
        (.mul (.mul (.constant 1) (.var 2)) (.var 2)) : Expr 3) := by decide +kernel
  rw [expression]
  simp [Expr.eval, pow_two]

theorem energy_at_initial : model.outputs.circuit.run model.initial energyIndex = 6 := by
  rw [energy_at, initial_eq]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

theorem energy_at_euler_step :
    model.outputs.circuit.run (eulerStep (1 / 8) model.initial) energyIndex = 1493 / 288 := by
  rw [energy_at, euler_step_at_initial]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- Pairing the state with the field is the gradient of V against the field:
∇V = 2x, so `energy_pairing`'s left side is exactly ⟪∇V(x), f(x)⟫. This is the
step a reader would otherwise supply by eye. -/
theorem energy_gradient (x : Point 3) :
    ∑ i, (2 * x i) * model.rates.circuit.run x i =
      2 * ∑ i, x i * model.rates.circuit.run x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Linear analysis, for existence and forward uniqueness

A trajectory proof must establish existence and forward uniqueness independently
of the energy bound. The field is homogeneous linear, so the library's
recognizer applies; these expose it rather than restating a matrix. -/

/-- The accepted linear view of the compiled field. -/
noncomputable def linear : LinearView model := model.linear.get (by decide +kernel)

theorem linear_matrix : linear.matrix =
    ![![-(1 / 3), 1, -1], ![-1, -(1 / 2), 1], ![1, -1, -2]] := by decide +kernel

/-- Existence, from the linear view rather than from any energy argument. -/
theorem exists_realization : ∃ state, Realizes state := linear.exists_realization

/-- Forward uniqueness on the declared domain, likewise independent of energy. -/
theorem unique_realization {x y : Dynamics.Signal 3} (hx : Realizes x) (hy : Realizes y) :
    Set.EqOn x y evolution.time.domain := linear.unique_realization hx hy

/-! ## A checked viewer entry point

`#html` in the gallery renders a layout failure as a paragraph, so a broken
diagram cannot fail `lake build`. This returns the same overview as an `Except`,
which `Tests/ThreeState.lean` asserts is `ok`. -/

def overview : Except String Visualization.ModelOverview := Visualization.overview model

#print axioms initial_eq
#print axioms rates_formula
#print axioms observations_formula
#print axioms energyRate_value
#print axioms rates_at_initial
#print axioms euler_step_at_initial
#print axioms observed_initial
#print axioms observed_euler_step
#print axioms solves_iff_realizes
#print axioms energy_pairing
#print axioms energy_gradient
#print axioms exists_realization
#print axioms unique_realization

end Gimle.Asgard.Examples.ThreeState
