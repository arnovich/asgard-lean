import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax

/-! A second-order equation, lowered by an explicitly declared velocity state,
and solved.

The source is `4*D_t(D_t(x)) + x = 0` with `x(0) = 1` and `x'(0) = 0`. The
velocity is declared, not inferred: `dx : D_t(x) = v` makes the state `v` the
first derivative of `x`, with its own `StateBinding` and initial value `v(0) = 0`.
Lowering yields the first-order system `D_t(x) = v`, `D_t(v) = (0 - x)/4`, and
the compiled field is homogeneous linear, so the source has exactly one solution
on `t ≥ 0`: `x(t) = cos(t/2)` and `v(t) = -sin(t/2)/2`.

The pinned Python compiler rejects the scaled form `2 * diff(diff(f,t),t) = f`,
and accepts only the bare chain, whose velocity initial value it fixes to zero
without declaring it; see the regression file. Python is not used here as an
oracle. -/
namespace Gimle.Asgard.Examples.HigherOrderIsolation
open Polynomial Model

def body : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"state-v", "v", .state⟩]
  assignments := []
  differentials := differentials% { dv : 4 * diff(diff(x, t), t) + x = 0; }
  velocities := velocities% { dx : diff(x, t) = v; }
}

def evolution (x0 v0 : ℚ) : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-v", "dv", "initial-v"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-v", "v0", .initial⟩]
  initialValues := [⟨"initial-x", x0⟩, ⟨"initial-v", v0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def model : SourceContinuousModel body (evolution 1 0) :=
  (compileSourceContinuous body (evolution 1 0)).toOption.get (by decide +kernel)

/-- The chain is read as `D_t(v)` and isolated with its residual kept; the
velocity declaration becomes the assignment `dx := v`. -/
theorem lowered : model.lowered.assignments =
    [⟨⟨"dv", "dv", .output⟩, .mul (.constant (1 / 4)) (.add (.constant 0) (.neg (.var "x")))⟩,
     ⟨⟨"dx", "dx", .output⟩, .var "v"⟩] := by
  decide +kernel

/-- The compiled field over state order [x, v]. -/
theorem rates_expressions : model.model.rates.expressions =
    (![.var 1, .mul (.constant (1 / 4)) (.add (.constant 0) (.neg (.var 0)))] :
      Fin 2 → Expr 2) := by
  decide +kernel

/-- Both initial values, read from the unchanged evolution. -/
theorem initial_eq : model.model.initial = (![1, 0] : Point 2) := by
  change (fun i : Fin 2 => (model.model.initials i : ℝ)) = _
  have values : model.model.initials = ![1, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

noncomputable def solution : Dynamics.Signal 2 :=
  fun t => ![Real.cos (t / 2), -Real.sin (t / 2) / 2]

private theorem cos_deriv (t : ℝ) :
    HasDerivAt (fun t => Real.cos (t / 2)) (-Real.sin (t / 2) / 2) t := by
  have h := ((hasDerivAt_id' t).div_const 2).cos
  exact h.congr_deriv (by ring)

private theorem sin_deriv (t : ℝ) :
    HasDerivAt (fun t => -Real.sin (t / 2) / 2) (-Real.cos (t / 2) / 4) t := by
  have h := (((hasDerivAt_id' t).div_const 2).sin.neg).div_const 2
  exact h.congr_deriv (by ring)

/-- The explicit trajectory solves the ORIGINAL second-order source, velocity
declaration and initial data included. -/
theorem solution_solves : body.Solves (evolution 1 0) solution := by
  rw [model.lowered.solves_iff, model.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [initial_eq]
    ext i
    fin_cases i <;> norm_num [solution, Evolution.time, evolution]
  · rw [rates_expressions]
    change Fin 2 at i
    fin_cases i
    · exact (cos_deriv t).hasDerivWithinAt.congr_deriv (by simp [Expr.eval, solution])
    · refine (sin_deriv t).hasDerivWithinAt.congr_deriv ?_
      simp [Expr.eval, solution]
      ring

def linear : LinearView model.model := model.model.linear.get (by decide +kernel)

/-- Every solution of the source equals the explicit one on `t ≥ 0`, the
velocity coordinate included. -/
theorem source_unique (state : Dynamics.Signal 2) (h : body.Solves (evolution 1 0) state) :
    Set.EqOn state solution (Set.Ici 0) := by
  have hx := (model.solves_iff_realizes state).mp h
  have hs := (model.solves_iff_realizes solution).mp solution_solves
  have := linear.unique_realization hx hs
  simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using this

/-- Read with actual derivatives: in every solution the derivative of `x`'s
own derivative is `-x/4` on `t ≥ 0`, and `x'(0) = 0`, the declared initial
value of the velocity. The statement mentions only `body.Solves` and
`derivWithin`, not the lowered system or its field. -/
theorem classical (state : Dynamics.Signal 2) (h : body.Solves (evolution 1 0) state) :
    (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt
      (derivWithin (fun s => state s 0) (Set.Ici 0)) (-(state t 0) / 4) (Set.Ici 0) t) ∧
    derivWithin (fun s => state s 0) (Set.Ici 0) 0 = 0 := by
  have states := model.lowered.velocityStates
  have hdom : (evolution 1 0).time.domain = Set.Ici 0 := by
    simp [Evolution.time, evolution, Dynamics.TimeDomain.domain]
  have hy : (body.context (evolution 1 0)).lift 1 "x" = some "v" := by decide +kernel
  have hi : body.coordinate (evolution 1 0) "x" = some ⟨0, by decide⟩ := by decide +kernel
  have hj : body.coordinate (evolution 1 0) "v" = some ⟨1, by decide⟩ := by decide +kernel
  have eq : Set.EqOn (derivWithin (fun s => state s 0) (Set.Ici 0)) (fun s => state s 1)
      (Set.Ici 0) := by
    have := h.lift_eqOn states 1 hy hi hj
    rw [iteratedDerivWithin_one, hdom] at this
    exact this
  refine ⟨fun t ht => ?_, ?_⟩
  · have field := (model.lowered.solves_iff state).mp h
    rw [model.model.solves_iff_field, rates_expressions] at field
    have hd := field.2 t (hdom ▸ ht) ⟨1, by decide⟩
    rw [hdom] at hd
    have hd' : HasDerivWithinAt (fun t => state t 1) (1 / 4 * (0 + -state t 0)) (Set.Ici 0) t := by
      refine hd.congr_deriv ?_
      change Expr.eval (state t) (.mul (.constant (1 / 4)) (.add (.constant 0) (.neg (.var 0)))) = _
      simp [Expr.eval]
    refine (hd'.congr_of_mem (fun s hs => eq hs) ht).congr_deriv ?_
    ring
  · have init := h.initial_iterated states 1 hy hi hj
    have value : (evolution 1 0).initialValue
        ((evolution 1 0).states[(⟨1, by decide⟩ : Fin (evolution 1 0).states.length)]).initialId =
        some 0 := by decide +kernel
    rw [iteratedDerivWithin_one, value, hdom] at init
    have start : (evolution 1 0).time.start = 0 := by simp [Evolution.time, evolution]
    rw [start] at init
    have := init.symm
    simp only [Rat.cast_zero, Option.map_some, Option.some.injEq] at this
    exact this

/-- A changed velocity initial value is a valid model whose solutions differ. -/
theorem changed_velocity : ¬ body.Solves (evolution 1 1) solution := by
  intro h
  have := h.1 (1 : Fin 2)
  simp [Evolution.initialValue, Evolution.time, evolution, solution] at this

#print axioms solution_solves
#print axioms source_unique
#print axioms classical
end Gimle.Asgard.Examples.HigherOrderIsolation
