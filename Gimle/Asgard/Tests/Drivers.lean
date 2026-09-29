import Gimle.Asgard.Examples.DrivenForcing

/-! Regression tests for declared time-varying drivers (task 031).

Python cases restate the driver fixtures of
`tests/unit/test_differential_side_context.py` and
`tests/unit/test_affine_differential_isolation.py` (gimle-asgard `fba931e`).
Python reads a `$`-prefixed or undeclared name as external forcing; Lean reads a
driver only from an explicit `.driver` port and `DriverBinding`, so each Python
source is restated with its driver declared. Each case records the Python
outcome and whether Lean agrees ("same") or deliberately differs.

The state `a` has derivative port `da` and initial value `1`, and `g` has `dg`
and `2`, on the axis `t` from `0`. `z` is a driver with derivative port `dz`, `f`
a driver without one, and `p = 3` a parameter. -/
namespace Gimle.Asgard.Tests.Drivers
open Polynomial Model

def inputs : List Port :=
  [⟨"state-a", "a", .state⟩, ⟨"state-g", "g", .state⟩, ⟨"driver-z", "z", .driver⟩,
   ⟨"driver-dz", "dz", .driver⟩, ⟨"driver-f", "f", .driver⟩, ⟨"param-p", "p", .parameter⟩]

def body (equations : List DifferentialEquation)
    (extra : List SourceAssignment := []) : SourceBody := {
  inputs := inputs
  assignments := extra
  differentials := equations
  parameters := [⟨"param-p", 3⟩]
}

def evolution : Evolution := {
  states := [⟨"state-a", "da", "initial-a"⟩, ⟨"state-g", "dg", "initial-g"⟩]
  initialPorts := [⟨"initial-a", "a0", .initial⟩, ⟨"initial-g", "g0", .initial⟩]
  initialValues := [⟨"initial-a", 1⟩, ⟨"initial-g", 2⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- `z` is differentiable with derivative port `dz`; `f` is not. -/
def drivers : List DriverBinding := [⟨"driver-z", some "driver-dz"⟩, ⟨"driver-f", none⟩]

def lowered (sb : SourceBody) (port : String) (ds : List DriverBinding := drivers) :
    Option NamedExpr :=
  (compileSourceDriven sb evolution ds).toOption.bind fun m =>
    (m.lowered.assignments.find? (·.output.id == port)).map (·.rhs)

def rejected (sb : SourceBody) (ds : List DriverBinding := drivers) : Option Diagnostic :=
  match compileSourceDriven sb evolution ds with
  | .error d => some d
  | .ok _ => none

/-! ## The listed Python fixtures -/

-- `diff(a,t) = diff($z,t)` (`test_parameter_derivative_can_remain_external_forcing`).
-- Python: accepted; with `z = t` and `a(0) = 1`, `a = 1 + t`. Same, with `z`
-- declared differentiable: `D_t(z)` is read as `dz`, so `a' = dz`, and the
-- relation makes `dz` the actual derivative of `z`.
example : lowered (body (differentials% { da : diff(a, t) = diff(z, t); dg : diff(g, t) = 0; }))
    "da" = some (.var "dz") := by decide +kernel
-- `f = 2 * diff(g,t)` (`test_rhs_affine_form_preserves_external_forcing_wire`).
-- Python: accepted; with `f = 3`, `g = 2 + 1.5 t`. Same: `g' = f/2`.
example : lowered (body (differentials% { da : diff(a, t) = 0; dg : f = 2 * diff(g, t); }))
    "dg" = some (.mul (.constant (1 / 2)) (.var "f")) := by decide +kernel
-- `f = diff(g,t) + g`. Python: accepted; with `f = 3`, `g = 3 - exp(-t)`. Same:
-- `g' = f - g`.
example : lowered (body (differentials% { da : diff(a, t) = 0; dg : f = diff(g, t) + g; }))
    "dg" = some (.add (.var "f") (.neg (.var "g"))) := by decide +kernel

/-! ## Drivers in residuals and assignments -/

-- A driver and a parameter in one residual, and a driver derivative in an
-- explicit assignment, read as its port.
example : lowered (body (differentials% { da : diff(a, t) + a = z * p; dg : diff(g, t) = h; })
    [⟨⟨"h", "h", .output⟩, term% diff(z, t) + f⟩]) "h" =
    some (.add (.var "dz") (.var "f")) := by decide +kernel
example : lowered (body (differentials% { da : diff(a, t) + a = z * p; dg : diff(g, t) = 0; }))
    "da" = some (.add (.mul (.var "z") (.var "p")) (.neg (.var "a"))) := by decide +kernel

/-- The compiled field over `[z, dz, f, a, g]`: `a' = dz`, `g' = f/2`. -/
def forced : SourceDrivenModel
    (body (differentials% { da : diff(a, t) = diff(z, t); dg : f = 2 * diff(g, t); }))
    evolution drivers :=
  (compileSourceDriven _ evolution drivers).toOption.get (by decide +kernel)

example : forced.model.rates.expressions =
    (![.var 1, .mul (.constant (1 / 2)) (.var 2)] : Fin 2 → Expr 5) := by decide +kernel

/-- The Python outcomes, checked: with `z = t`, `dz = 1` and `f = 3`, the
compiled model has `a = 1 + t` and `g = 2 + 3t/2`, as Python simulates. -/
noncomputable def pythonDrivers : Dynamics.Signal 3 := fun t => ![t, 1, 3]
noncomputable def pythonState : Dynamics.Signal 2 := fun t => ![1 + t, 2 + 3 / 2 * t]

theorem python_outcome :
    (body (differentials% { da : diff(a, t) = diff(z, t); dg : f = 2 * diff(g, t); })).SolvesDriven
      evolution drivers pythonDrivers pythonState := by
  rw [forced.solves_iff_realizes, ← forced.model.solves_iff_realizes,
    forced.model.solves_iff_field]
  refine ⟨?_, ?_, fun t _ i => ?_⟩
  · intro d hd
    simp only [drivers, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨⟨0, by decide⟩, by decide +kernel, continuous_id.continuousOn, fun port hp => ?_⟩
      simp only [Option.some.injEq] at hp
      subst hp
      refine ⟨⟨1, by decide⟩, by decide +kernel, fun t _ => ?_⟩
      exact (hasDerivAt_id' t).hasDerivWithinAt
    · refine ⟨⟨2, by decide⟩, by decide +kernel, continuousOn_const, fun port hp => ?_⟩
      simp at hp
  · have : forced.model.initials = ![1, 2] := by decide +kernel
    ext i
    fin_cases i <;> simp [DrivenModel.initial, this, pythonState, Evolution.time, evolution]
  · have rates : forced.model.rates.expressions =
        (![.var 1, .mul (.constant (1 / 2)) (.var 2)] : Fin 2 → Expr 5) := by decide +kernel
    rw [rates]
    fin_cases i
    · refine ((hasDerivAt_id' t).const_add 1).hasDerivWithinAt.congr_deriv ?_
      change (1 : ℝ) = Expr.eval (pointAppend (pythonDrivers t) (pythonState t)) (.var 1)
      simp [Expr.eval, pythonDrivers, pointAppend]
    · refine (((hasDerivAt_id' t).const_mul (3 / 2)).const_add 2).hasDerivWithinAt.congr_deriv ?_
      change (3 / 2 * 1 : ℝ) = Expr.eval (pointAppend (pythonDrivers t) (pythonState t))
        (.mul (.constant (1 / 2)) (.var 2))
      simp [Expr.eval, pythonDrivers, pointAppend]
      norm_num

/-! ## Rejected declarations -/

-- A `.driver` port without a `DriverBinding` is not a driver.
example : rejected (body (differentials% { da : diff(a, t) = 0; dg : diff(g, t) = 0; }))
    [⟨"driver-z", some "driver-dz"⟩] = some ⟨.missingBinding, "drivers", "driver-f"⟩ := by
  decide +kernel
-- A binding must name a `.driver` port.
example : rejected (body (differentials% { da : diff(a, t) = 0; dg : diff(g, t) = 0; }))
    (drivers ++ [⟨"state-a", none⟩]) = some ⟨.unknownReference, "drivers", "state-a"⟩ := by
  decide +kernel
-- A port is declared once, as a driver or as a derivative.
example : rejected (body (differentials% { da : diff(a, t) = 0; dg : diff(g, t) = 0; }))
    [⟨"driver-z", some "driver-dz"⟩, ⟨"driver-f", some "driver-dz"⟩] =
    some ⟨.duplicateBinding, "drivers", "driver-dz"⟩ := by decide +kernel
-- The derivative of a driver not declared differentiable stays rejected.
example : rejected (body (differentials% { da : diff(a, t) = diff(f, t); dg : diff(g, t) = 0; })) =
    some ⟨.unsupportedDerivative, "da", "da"⟩ := by decide +kernel
example : rejected (body (differentials% { da : diff(a, t) = diff(z, t); dg : diff(g, t) = 0; }))
    [⟨"driver-z", none⟩, ⟨"driver-dz", none⟩, ⟨"driver-f", none⟩] =
    some ⟨.unsupportedDerivative, "da", "da"⟩ := by decide +kernel
-- The derivative of a fixed parameter stays rejected.
example : rejected (body (differentials% { da : diff(a, t) = diff(p, t); dg : diff(g, t) = 0; })) =
    some ⟨.unsupportedDerivative, "da", "da"⟩ := by decide +kernel
-- A derivative port is not itself differentiable.
example : rejected (body (differentials% { da : diff(a, t) = diff(dz, t); dg : diff(g, t) = 0; })) =
    some ⟨.unsupportedDerivative, "da", "da"⟩ := by decide +kernel
-- A second derivative of a driver is not read as a port.
example : rejected (body
    (differentials% { da : diff(a, t) = diff(diff(z, t), t); dg : diff(g, t) = 0; })) =
    some ⟨.higherOrderDerivative, "da", "da"⟩ := by decide +kernel
-- Integrals are outside the driven fragment, in a declaration, an equation or
-- an explicit assignment.
example : rejected (body
    (differentials% { da : diff(a, t) = diff(int(z, t), t); dg : diff(g, t) = 0; })) =
    some ⟨.unsupportedIntegral, "da", "integral in a driven declaration"⟩ := by decide +kernel
example : rejected (body (differentials% { da : diff(a, t) = 0; dg : diff(g, t) = h; })
    [⟨⟨"h", "h", .output⟩, term% int(f, t)⟩]) =
    some ⟨.unsupportedIntegral, "h", "integral in a driven declaration"⟩ := by decide +kernel
example : rejected { body (differentials% { da : diff(a, t) = 0; })
    with integrals := integrals% { dg : g = int(f, t); } } =
    some ⟨.unsupportedIntegral, "dg", "integral in a driven declaration"⟩ := by decide +kernel
-- The undriven compilers still reject every `.driver` port.
example : (match compileSourceContinuous
    (body (differentials% { da : diff(a, t) = 0; dg : diff(g, t) = 0; })) evolution with
    | .error d => some d | .ok _ => none) = some ⟨.unsupportedRole, "driver-z", "z"⟩ := by
  decide +kernel

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Model.DrivenModel.solves_iff_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms DrivenModel.solves_iff_rel
/--
info: 'Gimle.Asgard.Model.SourceDrivenModel.solves_iff_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceDrivenModel.solves_iff_rel
/--
info: 'Gimle.Asgard.Model.DrivenModel.solves_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms DrivenModel.solves_iff_realizes
/--
info: 'Gimle.Asgard.Model.DrivenModel.observations_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms DrivenModel.observations_correct
/--
info: 'Gimle.Asgard.Model.SourceDrivenModel.solves_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceDrivenModel.solves_iff_realizes
/--
info: 'Gimle.Asgard.Model.SourceDrivenModel.observations_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceDrivenModel.observations_correct
/--
info: 'Gimle.Asgard.Model.Term.readRates_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.readRates_eval
/--
info: 'Gimle.Asgard.Examples.DrivenForcing.solution_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.DrivenForcing.solution_solves
/--
info: 'Gimle.Asgard.Examples.DrivenForcing.wrong_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.DrivenForcing.wrong_derivative
/--
info: 'Gimle.Asgard.Tests.Drivers.python_outcome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms python_outcome

end Gimle.Asgard.Tests.Drivers
