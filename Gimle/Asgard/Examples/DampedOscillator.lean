import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax

/-! A damped oscillator with a lower-order atom beside its declared chain, lowered
and solved.

The source is `D_t(D_t(x)) + c*D_t(x) + k*x = 0` with the parameters `c = 3` and
`k = 2`, `x(0) = 1` and `x'(0) = 0`. The velocity is declared, not inferred:
`dx : D_t(x) = v` makes the state `v` the first derivative of `x`, with its own
`StateBinding` and initial value. The chain `D_t(D_t(x))` is read as `D_t(v)`,
and the lower-order atom `D_t(x)` beside it as `v`; the non-literal factor `c`
then multiplies a state, not a derivative. Lowering yields the first-order system
`D_t(x) = v`, `D_t(v) = 0 - (c*v + k*x)`, with the residual in source order.

Reading `D_t(x)` as `v` is exact only where the velocity equation holds. Here
that equation is itself part of the source, so the source and the lowered
system have the same solutions, and the compiled field is homogeneous linear:
the source has exactly one solution on `t ≥ 0`, `x(t) = 2e^(-t) - e^(-2t)`.

The pinned Python compiler rejects this form; see the regression file. -/
namespace Gimle.Asgard.Examples.DampedOscillator
open Polynomial Model

def body : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"state-v", "v", .state⟩,
    ⟨"param-c", "c", .parameter⟩, ⟨"param-k", "k", .parameter⟩]
  assignments := []
  differentials := differentials% { dv : diff(diff(x, t), t) + c * diff(x, t) + k * x = 0; }
  velocities := velocities% { dx : diff(x, t) = v; }
  parameters := [⟨"param-c", 3⟩, ⟨"param-k", 2⟩]
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

/-- `dv := 0 - (c*v + k*x)`: the chain is read as `D_t(v)`, the lower-order atom
as `v`, and the residual is kept in source order. The velocity declaration
becomes `dx := v`. -/
theorem lowered : model.lowered.assignments =
    [⟨⟨"dv", "dv", .output⟩, .add (.constant 0)
      (.neg (.add (.mul (.var "c") (.var "v")) (.mul (.var "k") (.var "x"))))⟩,
     ⟨⟨"dx", "dx", .output⟩, .var "v"⟩] := by
  decide +kernel

/-- The compiled field over state order [x, v], with `c` and `k` specialized. -/
theorem rates_expressions : model.model.rates.expressions =
    (![.var 1, .add (.constant 0) (.neg (.add (.mul (.constant 3) (.var 1))
      (.mul (.constant 2) (.var 0))))] : Fin 2 → Expr 2) := by
  decide +kernel

theorem initial_eq : model.model.initial = (![1, 0] : Point 2) := by
  change (fun i : Fin 2 => (model.model.initials i : ℝ)) = _
  have values : model.model.initials = ![1, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

noncomputable def solution : Dynamics.Signal 2 :=
  fun t => ![2 * Real.exp (-t) - Real.exp (-2 * t), -2 * Real.exp (-t) + 2 * Real.exp (-2 * t)]

private theorem exp_deriv (a : ℝ) (t : ℝ) :
    HasDerivAt (fun t => Real.exp (a * t)) (a * Real.exp (a * t)) t := by
  have h := ((hasDerivAt_id' t).const_mul a).exp
  exact h.congr_deriv (by ring)

private theorem x_deriv (t : ℝ) :
    HasDerivAt (fun t => 2 * Real.exp (-t) - Real.exp (-2 * t))
      (-2 * Real.exp (-t) + 2 * Real.exp (-2 * t)) t := by
  have h := ((exp_deriv (-1) t).const_mul 2).sub (exp_deriv (-2) t)
  have e : (fun t => 2 * Real.exp (-t) - Real.exp (-2 * t)) =
      (fun t => 2 * Real.exp (-1 * t)) - fun t => Real.exp (-2 * t) := by
    funext s
    simp
  rw [e]
  exact h.congr_deriv (by simp only [neg_one_mul]; ring)

private theorem v_deriv (t : ℝ) :
    HasDerivAt (fun t => -2 * Real.exp (-t) + 2 * Real.exp (-2 * t))
      (2 * Real.exp (-t) - 4 * Real.exp (-2 * t)) t := by
  have h := ((exp_deriv (-1) t).const_mul (-2)).add ((exp_deriv (-2) t).const_mul 2)
  have e : (fun t => -2 * Real.exp (-t) + 2 * Real.exp (-2 * t)) =
      (fun t => -2 * Real.exp (-1 * t)) + fun t => 2 * Real.exp (-2 * t) := by
    funext s
    simp
  rw [e]
  exact h.congr_deriv (by simp only [neg_one_mul]; ring)

/-- The explicit trajectory solves the ORIGINAL source, with its lower-order
atom, velocity declaration and initial data. -/
theorem solution_solves : body.Solves (evolution 1 0) solution := by
  rw [model.lowered.solves_iff, model.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [initial_eq]
    ext i
    fin_cases i <;> norm_num [solution, Evolution.time, evolution]
  · rw [rates_expressions]
    change Fin 2 at i
    fin_cases i
    · exact (x_deriv t).hasDerivWithinAt.congr_deriv (by simp [Expr.eval, solution])
    · refine (v_deriv t).hasDerivWithinAt.congr_deriv ?_
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

/-- Read with actual derivatives: in every solution
`x'' = -(3*x' + 2*x)` on `t ≥ 0`, where both `x'` in the damping term and the
outer derivative are `derivWithin` of the state, and `x'(0) = 0`. The
statement mentions only `body.Solves` and `derivWithin`, not the lowered system. -/
theorem classical (state : Dynamics.Signal 2) (h : body.Solves (evolution 1 0) state) :
    (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt
      (derivWithin (fun s => state s 0) (Set.Ici 0))
      (-(3 * derivWithin (fun s => state s 0) (Set.Ici 0) t + 2 * state t 0)) (Set.Ici 0) t) ∧
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
    have hd' : HasDerivWithinAt (fun t => state t 1)
        (-(3 * state t 1 + 2 * state t 0)) (Set.Ici 0) t := by
      refine hd.congr_deriv ?_
      change Expr.eval (state t) (.add (.constant 0) (.neg (.add (.mul (.constant 3) (.var 1))
        (.mul (.constant 2) (.var 0))))) = _
      simp [Expr.eval]
    rw [eq ht]
    exact hd'.congr_of_mem (fun s hs => eq hs) ht
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

#print axioms solution_solves
#print axioms source_unique
#print axioms classical
end Gimle.Asgard.Examples.DampedOscillator
