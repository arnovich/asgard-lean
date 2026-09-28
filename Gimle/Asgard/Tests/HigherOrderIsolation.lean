import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax
import Gimle.Asgard.Examples.DampedOscillator
import Gimle.Asgard.Examples.HigherOrderIsolation

/-! Acceptance fixtures for higher-order chains over declared velocity states.

Python cases restate `tests/unit/test_differential_side_context.py` and
`tests/unit/test_affine_differential_isolation.py` (gimle-asgard `abb428ad`;
the same outcomes at `fba931e`). Python's outcome is recorded beside each one;
it is a regression reference, not an oracle, and the cases where the fragments
deliberately differ are marked "differs". Outcomes marked "probed" are not
pinned test cases; they were observed with the compiler at `fba931e`. -/
namespace Gimle.Asgard.Tests.HigherOrderIsolation
open Polynomial Model

/-! ## Isolation of one equation

`f`, `v`, `a` and `g` are states with derivative ports `df`, `dv`, `da` and
`dg`. `v` is declared as the velocity of `f`, and `a` as the velocity of `v`. -/

def locate (s : String) : Option String :=
  if s = "f" then some "df" else if s = "v" then some "dv"
  else if s = "a" then some "da" else if s = "g" then some "dg" else none

def context : Context :=
  ⟨"t", locate, fun s => if s = "f" then some "v" else if s = "v" then some "a" else none⟩

/-- Only `f` has a declared velocity. -/
def secondOnly : Context := ⟨"t", locate, fun s => if s = "f" then some "v" else none⟩

/-- No velocity is declared. -/
def firstOnly : Context := ⟨"t", locate, fun _ => none⟩

/-- The side isolation reads, as `SourceBody.lower` prepares it: declared
chains collapsed, and lower-order atoms read as their declared velocities. -/
def read (c : Context) (output : String) (t : Term) : Term :=
  (t.collapse c).readVelocities c output

def solve (c : Context) (output : String) (lhs rhs : Term) : Option NamedExpr :=
  ((isolate c output (read c output lhs) (read c output rhs)).map Isolated.expr).toOption

def reject (c : Context) (output : String) (lhs rhs : Term) : Option ErrorCode :=
  match isolate c output (read c output lhs) (read c output rhs) with
  | .error code => some code
  | .ok _ => none

-- The chain is read as `D_t(v)` and defines `v`'s derivative port.
example : (term% diff(diff(f, t), t)).collapse context = term% diff(v, t) := by decide +kernel
example : (term% diff(diff(diff(f, t), t), t)).collapse context = term% diff(a, t) := by
  decide +kernel

-- Python: `diff(diff(f,t),t) = g` gives Form-A `f = int(int(g,t),t) + f0`.
-- Lean: `D_t(v) = g` beside the declared `D_t(f) = v`; see the declaration below.
example : solve context "dv" (term% diff(diff(f, t), t)) (term% g) = some (.var "g") := by
  decide +kernel
example : solve context "dv" (term% g) (term% diff(diff(f, t), t)) = some (.var "g") := by
  decide +kernel

-- Differs: Python rejects the scaled chain `2 * diff(diff(f,t),t) = f`.
example : solve context "dv" (term% 2 * diff(diff(f, t), t)) (term% f) =
    some (.mul (.constant (1 / 2)) (.var "f")) := by decide +kernel
-- The scaled and residual form in the top derivative; every residual term is kept.
example : solve context "dv" (term% 2 * diff(diff(f, t), t) + f) (term% g) =
    some (.mul (.constant (1 / 2)) (.add (.var "g") (.neg (.var "f")))) := by decide +kernel
example : solve context "dv" (term% f - diff(diff(f, t), t) / 4 + v) (term% 0) =
    some (.mul (.constant (-4))
      (.add (.constant 0) (.neg (.add (.var "f") (.var "v"))))) := by decide +kernel

-- A third-order chain climbs two declared velocities.
-- Python (probed): `f = int(int(int(g,t),t),t) + f0`.
example : solve context "da" (term% diff(diff(diff(f, t), t), t)) (term% g) =
    some (.var "g") := by decide +kernel

-- An undeclared velocity is rejected; Python accepts the bare chain.
example : reject firstOnly "dv" (term% diff(diff(f, t), t)) (term% g) =
    some .higherOrderDerivative := by decide +kernel
example : reject secondOnly "da" (term% diff(diff(diff(f, t), t), t)) (term% g) =
    some .higherOrderDerivative := by decide +kernel

-- Mixed-axis chains stay rejected even over a declared velocity; Python rejects
-- the scaled one (pinned) and the bare ones (probed).
example : reject context "dv" (term% diff(diff(f, x), t)) (term% g) =
    some .mixedDerivative := by decide +kernel
example : reject context "dv" (term% diff(diff(f, t), x)) (term% g) =
    some .mixedDerivative := by decide +kernel
example : reject context "dv" (term% 2 * diff(diff(f, x), t)) (term% f) =
    some .mixedDerivative := by decide +kernel
example : reject context "da" (term% diff(diff(diff(f, x), t), t)) (term% g) =
    some .mixedDerivative := by decide +kernel
-- Python rejects the scaled wave equation too (task 029).
example : reject context "dv" (term% 2 * diff(diff(f, t), t)) (term% diff(diff(f, x), x)) =
    some .mixedDerivative := by decide +kernel

-- The chain defines the velocity's port, not the state's.
example : reject context "df" (term% diff(diff(f, t), t)) (term% g) =
    some .missingDerivative := by decide +kernel

/-! ### Lower-order atoms beside a chain (task 032)

A lower-order atom whose state has a declared velocity is read as that velocity:
`D_t(f)` as `v`, and `D_t(D_t(f))`, collapsed to `D_t(v)`, as `a` when it is not
the atom being isolated. This is exact only where the velocity equations hold;
`SourceBody.lower` discharges them for the whole system. -/

-- Differs: Python rejects the lower-order atom beside the chain (probed at
-- `fba931e`: "cannot isolate 'f': unsupported differential-..."). Lean reads it
-- as the declared velocity and keeps the residual.
example : read context "dv" (term% diff(diff(f, t), t) + diff(f, t)) =
    term% diff(v, t) + v := by decide +kernel
example : solve context "dv" (term% diff(diff(f, t), t) + diff(f, t)) (term% g) =
    some (.add (.var "g") (.neg (.var "v"))) := by decide +kernel
-- The damped oscillator; Python rejects it with literal and with symbolic `c`
-- and `k` (probed). `c` multiplies the velocity, not a derivative, so it is
-- not a scale.
example : solve context "dv" (term% diff(diff(f, t), t) + c * diff(f, t) + k * f) (term% 0) =
    some (.add (.constant 0)
      (.neg (.add (.mul (.var "c") (.var "v")) (.mul (.var "k") (.var "f"))))) := by
  decide +kernel
-- The lower-order atom on the other side; Python reports a competing
-- derivative (probed).
example : solve context "dv" (term% diff(diff(f, t), t)) (term% -(3 * diff(f, t)) - 2 * f) =
    some (.add (.neg (.mul (.constant 3) (.var "v"))) (.neg (.mul (.constant 2) (.var "f")))) := by
  decide +kernel
-- The scale belongs to the top atom only.
example : solve context "dv" (term% 2 * diff(diff(f, t), t) + 3 * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 2)) (.add (.var "f") (.neg (.mul (.constant 3) (.var "v"))))) := by
  decide +kernel
-- Every lower order of a third-order chain, each read through its velocity.
example : solve context "da"
    (term% diff(diff(diff(f, t), t), t) + diff(diff(f, t), t) + diff(f, t)) (term% g) =
    some (.add (.var "g") (.neg (.add (.var "a") (.var "v")))) := by decide +kernel
-- A lower-order atom is a polynomial term like any state, so products are kept.
example : solve context "dv" (term% diff(diff(f, t), t) + diff(f, t) * diff(f, t)) (term% 0) =
    some (.add (.constant 0) (.neg (.mul (.var "v") (.var "v")))) := by decide +kernel
-- The atom of another state with a declared velocity is read the same way.
example : solve context "dg" (term% diff(g, t)) (term% diff(f, t)) = some (.var "v") := by
  decide +kernel

-- Still rejected, with the diagnostic they had before task 032.
-- A lower-order atom whose state has no declared velocity is a second atom.
example : reject context "dv" (term% diff(diff(f, t), t) + diff(g, t)) (term% 0) =
    some .repeatedDerivative := by decide +kernel
example : reject secondOnly "dv" (term% diff(diff(f, t), t) + diff(v, t)) (term% 0) =
    some .repeatedDerivative := by decide +kernel
-- Two atoms that both define the output are not lower-order.
example : reject context "dv" (term% diff(diff(f, t), t) + diff(v, t)) (term% 0) =
    some .repeatedDerivative := by decide +kernel
-- A lower-order atom on another axis.
example : reject context "dv" (term% diff(diff(f, t), t) + diff(f, x)) (term% 0) =
    some .mixedDerivative := by decide +kernel
-- A lower-order atom inside a lambda.
example : reject context "dv" (term% diff(diff(f, t), t) + (λ z => diff(f, t))(0)) (term% 0) =
    some .unsupportedDerivative := by decide +kernel
-- A lower-order atom that is only read is not the atom being isolated.
example : reject context "dv" (term% diff(f, t)) (term% g) = some .missingDerivative := by
  decide +kernel
example : reject context "dv" (term% diff(diff(f, t), t)) (term% diff(g, t)) =
    some .competingDerivative := by decide +kernel
example : reject context "dv" (term% (λ z => diff(diff(z, t), t))(f)) (term% g) =
    some .unsupportedDerivative := by decide +kernel
-- A chain over a non-state cannot be given a velocity.
example : reject context "dv" (term% diff(diff(f + g, t), t)) (term% g) =
    some .unsupportedDerivative := by decide +kernel
example : reject context "dv" (term% diff(diff(p, t), t)) (term% g) =
    some .unsupportedDerivative := by decide +kernel

/-! ## Declarations -/

/-- Python's `diff(diff(f,t),t) = g` with the driver `g = 3` as a parameter,
and the velocity `v` declared. -/
def bare : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-v", "v", .state⟩, ⟨"param-g", "g", .parameter⟩]
  assignments := []
  differentials := differentials% { dv : diff(diff(f, t), t) = g; }
  velocities := velocities% { df : diff(f, t) = v; }
  parameters := [⟨"param-g", 3⟩]
}

def bareEvolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-v", "dv", "initial-v"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-v", "v0", .initial⟩]
  initialValues := [⟨"initial-f", 1⟩, ⟨"initial-v", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def bareModel : SourceContinuousModel bare bareEvolution :=
  (compileSourceContinuous bare bareEvolution).toOption.get (by decide +kernel)

-- `D_t(v) = g` and `D_t(f) = v`, over state order [f, v].
example : bareModel.lowered.assignments =
    [⟨⟨"dv", "dv", .output⟩, .var "g"⟩, ⟨⟨"df", "df", .output⟩, .var "v"⟩] := by decide +kernel
example : bareModel.model.rates.expressions =
    (![.var 1, .constant 3] : Fin 2 → Expr 2) := by decide +kernel
-- Differs: Python declares only `f0` and fixes the velocity's initial value to
-- zero; Lean requires it declared, here as the same `0`.
example : bareModel.model.initials = ![1, 0] := by decide +kernel

private def code {α : Type} : Except Diagnostic α → Option Diagnostic
  | .error d => some d
  | .ok _ => none

private def continuous (sb : SourceBody) (e : Evolution := bareEvolution) : Option Diagnostic :=
  code (compileSourceContinuous sb e)

-- A missing velocity initial value.
example : continuous bare { bareEvolution with initialValues := [⟨"initial-f", 1⟩] } =
    some ⟨.missingBinding, "initialValues", "initial-v"⟩ := by decide +kernel
-- A velocity state without a binding in the evolution.
example : continuous bare { bareEvolution with
    states := [⟨"state-f", "df", "initial-f"⟩],
    initialPorts := [⟨"initial-f", "f0", .initial⟩],
    initialValues := [⟨"initial-f", 1⟩] } =
    some ⟨.missingBinding, "states", "state-v"⟩ := by decide +kernel
-- The same first-order equation written as an ordinary differential declares
-- no velocity, so the chain is rejected: nothing is inferred from its shape.
example : continuous { bare with
    differentials := differentials% { dv : diff(diff(f, t), t) = g; df : diff(f, t) = v; }
    velocities := [] } =
    some ⟨.higherOrderDerivative, "dv", "dv"⟩ := by decide +kernel
-- The velocity must be a state.
example : continuous { bare with velocities := velocities% { df : diff(f, t) = g; } } =
    some ⟨.unsupportedRole, "df", "g"⟩ := by decide +kernel
-- The velocity must be declared.
example : continuous { bare with velocities := velocities% { df : diff(f, t) = w; } } =
    some ⟨.unknownReference, "df", "w"⟩ := by decide +kernel
-- The declaration names its own state's derivative port, and differentiates a
-- state. Here `dv` is defined by a first-order equation, so no chain is read.
def firstOrder : SourceBody := { bare with differentials := differentials% { dv : diff(v, t) = g; } }
example : continuous firstOrder = none := by decide +kernel
example : continuous { firstOrder with velocities := velocities% { df : diff(v, t) = v; } } =
    some ⟨.missingDerivative, "df", "df"⟩ := by decide +kernel
example : continuous { firstOrder with velocities := velocities% { df : diff(g, t) = v; } } =
    some ⟨.unsupportedDerivative, "df", "df"⟩ := by decide +kernel
-- The velocity is declared on the evolution axis; a declaration on another axis
-- licenses no chain.
example : continuous { firstOrder with velocities := velocities% { df : diff(f, x) = v; } } =
    some ⟨.mixedDerivative, "df", "df"⟩ := by decide +kernel
example : continuous { bare with velocities := velocities% { df : diff(f, x) = v; } } =
    some ⟨.higherOrderDerivative, "dv", "dv"⟩ := by decide +kernel
-- The chain's equation defines the velocity's port; `df` is the declaration's.
example : continuous { bare with differentials := differentials% {
    df : diff(diff(f, t), t) = g; } } =
    some ⟨.duplicateId, "source", "df"⟩ := by decide +kernel
-- A velocity declared twice for one state defines its port twice.
example : continuous { bare with
    velocities := velocities% { df : diff(f, t) = v; df : diff(f, t) = v; } } =
    some ⟨.duplicateId, "source", "df"⟩ := by decide +kernel
-- A binder named like the velocity: the chain inside a lambda is rejected.
example : continuous { bare with differentials := differentials% {
    dv : (λ v => diff(diff(f, t), t) + v)(0) = g; } } =
    some ⟨.unsupportedDerivative, "dv", "dv"⟩ := by decide +kernel
-- A declared velocity whose own derivative port is never defined.
example : continuous { bare with differentials := [] } =
    some ⟨.unknownReference, "state-v", "dv"⟩ := by decide +kernel
-- A mixed-axis chain over a declared velocity, at the declaration level.
example : continuous { bare with differentials := differentials% {
    dv : diff(diff(f, x), t) = g; } } =
    some ⟨.mixedDerivative, "dv", "dv"⟩ := by decide +kernel
-- An initial port is not a source name, so it cannot be a velocity.
example : continuous { bare with velocities := velocities% { df : diff(f, t) = f0; } } =
    some ⟨.unknownReference, "df", "f0"⟩ := by decide +kernel
-- Velocity roles are checked before any equation is isolated.
example : continuous { bare with
    differentials := differentials% { dv : f * diff(diff(f, t), t) = g; }
    velocities := velocities% { df : diff(f, t) = g; } } =
    some ⟨.unsupportedRole, "df", "g"⟩ := by decide +kernel

/-! Accepted shapes that are sound but unusual: every velocity declaration is
its own equation, so sharing, cycles and self-velocities mean what they say. -/

def twoStates : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-h", "h", .state⟩, ⟨"state-v", "v", .state⟩]
  assignments := assignments% { dv := 1; }
  velocities := velocities% { df : diff(f, t) = v; dh : diff(h, t) = v; }
}

def threeEvolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-h", "dh", "initial-h"⟩,
    ⟨"state-v", "dv", "initial-v"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-h", "h0", .initial⟩,
    ⟨"initial-v", "v0", .initial⟩]
  initialValues := [⟨"initial-f", 0⟩, ⟨"initial-h", 1⟩, ⟨"initial-v", 2⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

-- Two states sharing one velocity: `f' = v` and `h' = v`.
example : ((compileSourceContinuous twoStates threeEvolution).map
    (·.lowered.assignments)).toOption =
    some [⟨⟨"dv", "dv", .output⟩, .constant 1⟩, ⟨⟨"df", "df", .output⟩, .var "v"⟩,
      ⟨⟨"dh", "dh", .output⟩, .var "v"⟩] := by decide +kernel

-- Two states sharing one velocity: `D_t(h)` beside `D_t(D_t(f))` is read as
-- `v`, which `h' = v` makes exact.
example : ((compileSourceContinuous { twoStates with
    assignments := []
    differentials := differentials% { dv : diff(diff(f, t), t) + diff(h, t) = 0; } }
    threeEvolution).map (·.lowered.assignments)).toOption =
    some [⟨⟨"dv", "dv", .output⟩, .add (.constant 0) (.neg (.var "v"))⟩,
      ⟨⟨"df", "df", .output⟩, .var "v"⟩, ⟨⟨"dh", "dh", .output⟩, .var "v"⟩] := by decide +kernel
-- Without `h`'s declaration, its atom is a second atom, as before task 032.
example : continuous { twoStates with
    assignments := []
    differentials := differentials% {
      dv : diff(diff(f, t), t) + diff(h, t) = 0; dh : diff(h, t) = v; }
    velocities := velocities% { df : diff(f, t) = v; } } threeEvolution =
    some ⟨.repeatedDerivative, "dv", "dv"⟩ := by decide +kernel

-- A velocity cycle `f' = v`, `v' = f` is the first-order system it states.
example : ((compileSourceContinuous { bare with
    differentials := [], velocities := velocities% { df : diff(f, t) = v; dv : diff(v, t) = f; } }
    bareEvolution).map (·.model.rates.expressions)).toOption =
    some (![.var 1, .var 0] : Fin 2 → Expr 2) := by decide +kernel

-- A self-velocity `f' = f` reads `D_t(D_t(f))` as `D_t(f)`, whose port is the
-- declaration's own, so no further equation can define it.
example : continuous { bare with
    differentials := differentials% { dv : diff(diff(f, t), t) = g; }
    velocities := velocities% { df : diff(f, t) = f; } } =
    some ⟨.missingDerivative, "dv", "dv"⟩ := by decide +kernel

/-! A third-order equation `D_t(D_t(D_t(f))) = g` over two declared velocities
and three initial values. -/

def third : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-v", "v", .state⟩, ⟨"state-a", "a", .state⟩,
    ⟨"param-g", "g", .parameter⟩]
  assignments := []
  differentials := differentials% { da : diff(diff(diff(f, t), t), t) = g; }
  velocities := velocities% { df : diff(f, t) = v; dv : diff(v, t) = a; }
  parameters := [⟨"param-g", 3⟩]
}

def thirdEvolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-v", "dv", "initial-v"⟩,
    ⟨"state-a", "da", "initial-a"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-v", "v0", .initial⟩,
    ⟨"initial-a", "a0", .initial⟩]
  initialValues := [⟨"initial-f", 1⟩, ⟨"initial-v", 2⟩, ⟨"initial-a", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def thirdModel : SourceContinuousModel third thirdEvolution :=
  (compileSourceContinuous third thirdEvolution).toOption.get (by decide +kernel)

example : thirdModel.model.rates.expressions =
    (![.var 1, .var 2, .constant 3] : Fin 3 → Expr 3) := by decide +kernel
example : thirdModel.model.initials = ![1, 2, 0] := by decide +kernel
-- With `v' = a` written as an ordinary equation, not a declaration, the chain
-- is rejected.
example : continuous { third with
    differentials := differentials% {
      da : diff(diff(diff(f, t), t), t) = g; dv : diff(v, t) = a; }
    velocities := velocities% { df : diff(f, t) = v; } }
    thirdEvolution = some ⟨.higherOrderDerivative, "da", "da"⟩ := by decide +kernel

/-! The damped oscillator `D_t(D_t(f)) + c*D_t(f) + k*f = 0` over the declared
velocity `v`; `Examples.DampedOscillator` solves it for `c = 3`, `k = 2`. -/

def damped : SourceBody := { bare with
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-v", "v", .state⟩,
    ⟨"param-c", "c", .parameter⟩, ⟨"param-k", "k", .parameter⟩]
  differentials := differentials% { dv : diff(diff(f, t), t) + c * diff(f, t) + k * f = 0; }
  parameters := [⟨"param-c", 3⟩, ⟨"param-k", 2⟩] }

-- Differs: Python rejects this equation (probed at `fba931e`).
example : ((compileSourceContinuous damped bareEvolution).map
    (·.lowered.assignments)).toOption =
    some [⟨⟨"dv", "dv", .output⟩, .add (.constant 0)
      (.neg (.add (.mul (.var "c") (.var "v")) (.mul (.var "k") (.var "f"))))⟩,
      ⟨⟨"df", "df", .output⟩, .var "v"⟩] := by decide +kernel
-- The same equation with `f' = v` written as an ordinary differential declares
-- no velocity: the chain is rejected first, as before task 032.
example : continuous { damped with
    differentials := differentials% {
      dv : diff(diff(f, t), t) + c * diff(f, t) + k * f = 0; df : diff(f, t) = v; }
    velocities := [] } =
    some ⟨.higherOrderDerivative, "dv", "dv"⟩ := by decide +kernel
-- In a first-order equation, the undeclared atom `D_t(f)` stays a second atom.
example : continuous { damped with
    differentials := differentials% { dv : diff(v, t) + c * diff(f, t) + k * f = 0; df : diff(f, t) = v; }
    velocities := [] } =
    some ⟨.repeatedDerivative, "dv", "dv"⟩ := by decide +kernel
-- With the declaration, it is read as `v`, the same system as the chain form.
example : ((compileSourceContinuous { damped with
    differentials := differentials% { dv : diff(v, t) + c * diff(f, t) + k * f = 0; } }
    bareEvolution).map (·.model.rates.expressions)).toOption =
    ((compileSourceContinuous damped bareEvolution).map (·.model.rates.expressions)).toOption := by
  decide +kernel
-- A velocity declared on another axis licenses neither the chain nor the atom.
example : continuous { damped with velocities := velocities% { df : diff(f, x) = v; } } =
    some ⟨.higherOrderDerivative, "dv", "dv"⟩ := by decide +kernel

-- A polynomial declaration has no evolution axis.
example : code (compileSourcePolynomial { bare with differentials := [] }) =
    some ⟨.unsupportedDerivative, "df", "differential equation without an evolution axis"⟩ := by
  decide +kernel

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Model.Term.collapse_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.collapse_eval
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.lift_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.lift_eqOn
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.initial_iterated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.initial_iterated
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.chain_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.chain_denotes
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.chain_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.chain_at
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.realizes_iterated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.realizes_iterated
/--
info: 'Gimle.Asgard.Model.SourceBody.solves_iff_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.solves_iff_classical
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.classical_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.classical_iff_realizes
/--
info: 'Gimle.Asgard.Model.Term.readVelocities_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.readVelocities_eval
/--
info: 'Gimle.Asgard.Model.SourceBody.velocitiesHold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.velocitiesHold
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.solves_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.solves_iff_realizes
/--
info: 'Gimle.Asgard.Examples.DampedOscillator.solution_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.DampedOscillator.solution_solves
/--
info: 'Gimle.Asgard.Examples.DampedOscillator.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.DampedOscillator.source_unique
/--
info: 'Gimle.Asgard.Examples.DampedOscillator.classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.DampedOscillator.classical
/--
info: 'Gimle.Asgard.Examples.HigherOrderIsolation.solution_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.HigherOrderIsolation.solution_solves
/--
info: 'Gimle.Asgard.Examples.HigherOrderIsolation.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.HigherOrderIsolation.source_unique
/--
info: 'Gimle.Asgard.Examples.HigherOrderIsolation.classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.HigherOrderIsolation.classical
/--
info: 'Gimle.Asgard.Examples.HigherOrderIsolation.changed_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.HigherOrderIsolation.changed_velocity

end Gimle.Asgard.Tests.HigherOrderIsolation
