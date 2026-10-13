import Gimle.Asgard.Model.DrivenSource
import Gimle.Asgard.Model.SourceSyntax

/-! A source declaration forced by a declared, differentiable driver.

The source is `D_t(x) + x = D_t(u) + u` with `x(0) = 0`, where `u` is a
`.driver` port declared differentiable with derivative port `du`. Nothing about
`u` is inferred: without its `DriverBinding` the declaration is rejected, and
without a derivative port `D_t(u)` has no value. Lowering reads `D_t(u)` as `du`
and isolates `D_t(x) = (du + u) - x`, over the coordinates `[u, du, x]`.

The driver signal is an argument of the relation. For `u = sin` with its actual
derivative `du = cos`, `x = sin` is a solution. For `u = sin` with `du = 0`
the signal is not admitted, because `du` must be the actual derivative of `u`,
so no state solves the source with it: a derivative port is never an
unconstrained extra input. -/
namespace Gimle.Asgard.Examples.DrivenForcing
open Polynomial Model

def body : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"driver-u", "u", .driver⟩, ⟨"driver-du", "du", .driver⟩]
  assignments := []
  differentials := differentials% { dx : diff(x, t) + x = diff(u, t) + u; }
}

def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩]
  initialValues := [⟨"initial-x", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def drivers : List DriverBinding := [⟨"driver-u", some "driver-du"⟩]

def model : SourceDrivenModel body evolution drivers :=
  (compileSourceDriven body evolution drivers).toOption.get (by decide +kernel)

/-- `D_t(u)` is read as `du` and the equation isolated with its residual kept. -/
theorem lowered : model.lowered.assignments =
    [⟨⟨"dx", "dx", .output⟩, .add (.add (.var "du") (.var "u")) (.neg (.var "x"))⟩] := by
  decide +kernel

/-- The compiled field over `[u, du, x]`. -/
theorem rates_expressions : model.model.rates.expressions =
    (![.add (.add (.var 1) (.var 0)) (.neg (.var 2))] : Fin 1 → Expr 3) := by
  decide +kernel

/-- Without the binding, the `.driver` ports are not drivers. -/
theorem undeclared : (compileSourceDriven body evolution []).toOption.isNone := by
  decide +kernel

/-- Without a derivative port, `D_t(u)` has no value and is rejected. -/
theorem underived :
    (compileSourceDriven body evolution [⟨"driver-u", none⟩, ⟨"driver-du", none⟩]).toOption.isNone := by
  decide +kernel

noncomputable def forcing : Dynamics.Signal 2 := fun t => ![Real.sin t, Real.cos t]
noncomputable def wrongDerivative : Dynamics.Signal 2 := fun t => ![Real.sin t, 0]
noncomputable def solution : Dynamics.Signal 1 := fun t => ![Real.sin t]

private theorem domain : evolution.time.domain = Set.Ici 0 := by
  simp [Evolution.time, evolution, Dynamics.TimeDomain.domain]

private theorem width : DriverBinding.width drivers = 2 := rfl

private theorem index_u : index (DriverBinding.ids drivers) "driver-u" = some ⟨0, by decide⟩ := by
  decide +kernel

private theorem index_du :
    index (DriverBinding.ids drivers) "driver-du" = some ⟨1, by decide⟩ := by
  decide +kernel

theorem forcing_admitted : evolution.Admitted drivers forcing := by
  intro d hd
  simp only [drivers, List.mem_singleton] at hd
  subst hd
  refine ⟨_, index_u, ?_, fun port hp => ?_⟩
  · exact Real.continuous_sin.continuousOn
  · simp only [Option.some.injEq] at hp
    subst hp
    exact ⟨_, index_du, fun t _ => (Real.hasDerivAt_sin t).hasDerivWithinAt⟩

/-- `x = sin` solves the ORIGINAL source, driver and initial data included. -/
theorem solution_solves : body.SolvesDriven evolution drivers forcing solution := by
  rw [model.solves_iff_realizes, ← model.model.solves_iff_realizes, model.model.solves_iff_field]
  refine ⟨forcing_admitted, ?_, fun t _ i => ?_⟩
  · have : model.model.initials = ![0] := by decide +kernel
    ext i
    fin_cases i
    simp [DrivenModel.initial, this, solution, Evolution.time, evolution]
  · rw [rates_expressions]
    fin_cases i
    refine (Real.hasDerivAt_sin t).hasDerivWithinAt.congr_deriv ?_
    simp [Expr.eval, forcing, solution, pointAppend, width]

/-- A derivative port that is not the actual derivative is not admitted, so no
state solves the source under that signal. -/
theorem wrong_derivative (state : Dynamics.Signal 1) :
    ¬ body.SolvesDriven evolution drivers wrongDerivative state := by
  intro h
  obtain ⟨i, hi, -, hport⟩ := h.1 _ (List.mem_singleton_self _)
  rw [index_u, Option.some.injEq] at hi
  subst hi
  obtain ⟨j, hj, hd⟩ := hport "driver-du" rfl
  rw [index_du, Option.some.injEq] at hj
  subst hj
  have h0 : HasDerivWithinAt Real.sin 0 (Set.Ici 0) 0 := by
    have := hd 0 (by simp [domain])
    rw [domain] at this
    exact this
  have hsin : HasDerivWithinAt Real.sin (Real.cos 0) (Set.Ici 0) 0 :=
    (Real.hasDerivAt_sin 0).hasDerivWithinAt
  have := (uniqueDiffOn_Ici (0 : ℝ) 0 (by simp)).eq_deriv _ hsin h0
  simp at this

#print axioms solution_solves
#print axioms wrong_derivative
end Gimle.Asgard.Examples.DrivenForcing
