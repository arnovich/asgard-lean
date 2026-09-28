import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! A nested integral kept through two declared integral states, and solved.

The source is `D_t(f) = I_t(I_t(f))` with `f(0) = 1`. Both integrals are
declared, not inferred: `dF : F = I_t(f)` and `dG : G = I_t(I_t(f))`, each state
with its own `StateBinding` and the declared initial value `0`. The outer
declaration's integrand `I_t(f)` is itself read through the inner declaration, so
lowering yields the first-order system `D_t(f) = G`, `D_t(G) = F`, `D_t(F) = f`.
The compiled field is homogeneous linear, so the source has exactly one solution
on `t ≥ 0`. With `ω = √3/2` it is

```text
f(t) = (eᵗ + 2e^(-t/2) cos ωt) / 3
F(t) = (eᵗ - e^(-t/2) cos ωt + √3 e^(-t/2) sin ωt) / 3
G(t) = (eᵗ - e^(-t/2) cos ωt - √3 e^(-t/2) sin ωt) / 3
```

In every solution the source's own readings of `I_t(f)` and `I_t(I_t(f))`, each
an antiderivative from the start, are the states `F` and `G`
(`integrals_read_states`).

The pinned Python compiler accepts the same source as Form-A
`f = int(int(int(f,t),t),t) + f0`, with two hidden states starting at zero; Lean
requires both declared, with their initial values written in the evolution. -/
namespace Gimle.Asgard.Examples.NestedIntegralStates
open Polynomial Model

def body : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-F", "F", .state⟩, ⟨"state-G", "G", .state⟩]
  assignments := []
  differentials := differentials% { df : diff(f, t) = int(int(f, t), t); }
  integrals := integrals% { dF : F = int(f, t); dG : G = int(int(f, t), t); }
}

def evolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-F", "dF", "initial-F"⟩,
    ⟨"state-G", "dG", "initial-G"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-F", "F0", .initial⟩,
    ⟨"initial-G", "G0", .initial⟩]
  initialValues := [⟨"initial-f", 1⟩, ⟨"initial-F", 0⟩, ⟨"initial-G", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def model : SourceContinuousModel body evolution :=
  (compileSourceContinuous body evolution).toOption.get (by decide +kernel)

/-- `I_t(I_t(f))` became `G`, and the outer declaration's integrand `I_t(f)`
became `F`. -/
theorem lowered : model.lowered.assignments =
    [⟨⟨"df", "df", .output⟩, .var "G"⟩, ⟨⟨"dF", "dF", .output⟩, .var "f"⟩,
     ⟨⟨"dG", "dG", .output⟩, .var "F"⟩] := by
  decide +kernel

/-- The compiled field over state order [f, F, G]. -/
theorem rates_expressions : model.model.rates.expressions =
    (![.var 2, .var 0, .var 1] : Fin 3 → Expr 3) := by
  decide +kernel

/-- All three initial values, read from the unchanged evolution: `F(0) = G(0) = 0`
are declared, not assumed. -/
theorem initial_eq : model.model.initial = (![1, 0, 0] : Point 3) := by
  change (fun i : Fin 3 => (model.model.initials i : ℝ)) = _
  have values : model.model.initials = ![1, 0, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

/-- The damped cosine part `e^(-t/2) cos ωt`, with `ω = √3/2`. -/
noncomputable def dampedCos (t : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * t) * Real.cos (Real.sqrt 3 / 2 * t)
/-- The damped sine part `e^(-t/2) sin ωt`. -/
noncomputable def dampedSin (t : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * t) * Real.sin (Real.sqrt 3 / 2 * t)

private theorem cos_deriv (t : ℝ) :
    HasDerivAt dampedCos (-(1 / 2) * dampedCos t - Real.sqrt 3 / 2 * dampedSin t) t := by
  have h := (((hasDerivAt_id' t).const_mul (-(1 / 2) : ℝ)).exp).mul
    (((hasDerivAt_id' t).const_mul (Real.sqrt 3 / 2)).cos)
  exact h.congr_deriv (by simp only [dampedCos, dampedSin]; ring)

private theorem sin_deriv (t : ℝ) :
    HasDerivAt dampedSin (-(1 / 2) * dampedSin t + Real.sqrt 3 / 2 * dampedCos t) t := by
  have h := (((hasDerivAt_id' t).const_mul (-(1 / 2) : ℝ)).exp).mul
    (((hasDerivAt_id' t).const_mul (Real.sqrt 3 / 2)).sin)
  exact h.congr_deriv (by simp only [dampedCos, dampedSin]; ring)

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

noncomputable def solution : Dynamics.Signal 3 := fun t =>
  ![(Real.exp t + 2 * dampedCos t) / 3,
    (Real.exp t - dampedCos t + Real.sqrt 3 * dampedSin t) / 3,
    (Real.exp t - dampedCos t - Real.sqrt 3 * dampedSin t) / 3]

/-- The explicit trajectory solves the ORIGINAL source, both integral
declarations and the initial data included. -/
theorem solution_solves : body.Solves evolution solution := by
  rw [model.lowered.solves_iff, model.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [initial_eq]
    ext i
    fin_cases i <;> norm_num [solution, Evolution.time, evolution, dampedCos, dampedSin]
  · rw [rates_expressions]
    change Fin 3 at i
    fin_cases i
    · refine (((Real.hasDerivAt_exp t).add ((cos_deriv t).const_mul 2)).div_const 3)
        |>.hasDerivWithinAt.congr_deriv ?_
      simp [Expr.eval, solution]
      ring
    · refine ((((Real.hasDerivAt_exp t).sub (cos_deriv t)).add
        ((sin_deriv t).const_mul (Real.sqrt 3))).div_const 3).hasDerivWithinAt.congr_deriv ?_
      simp [Expr.eval, solution]
      linear_combination (dampedCos t / 2) * sqrt_three_sq
    · refine ((((Real.hasDerivAt_exp t).sub (cos_deriv t)).sub
        ((sin_deriv t).const_mul (Real.sqrt 3))).div_const 3).hasDerivWithinAt.congr_deriv ?_
      simp [Expr.eval, solution]
      linear_combination (-(dampedCos t) / 2) * sqrt_three_sq

def linear : LinearView model.model := model.model.linear.get (by decide +kernel)

/-- Every solution of the source equals the explicit one on `t ≥ 0`, both
integral states included. -/
theorem source_unique (state : Dynamics.Signal 3) (h : body.Solves evolution state) :
    Set.EqOn state solution (Set.Ici 0) := by
  have hx := (model.solves_iff_realizes state).mp h
  have hs := (model.solves_iff_realizes solution).mp solution_solves
  have := linear.unique_realization hx hs
  simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using this

/-- In every solution, the source's reading of `I_t(f)` is the state `F` and its
reading of `I_t(I_t(f))` is the state `G`, each the antiderivative from the start.
The statement mentions only `body.Solves` and the trajectory reading, not the
lowered system. -/
theorem integrals_read_states (state : Dynamics.Signal 3) (h : body.Solves evolution state)
    (t : ℝ) (ht : 0 ≤ t) :
    body.atoms evolution state t (term% int(f, t)) = some (state t 1) ∧
      body.atoms evolution state t (term% int(int(f, t), t)) = some (state t 2) := by
  have ht' : t ∈ evolution.time.domain := by
    simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using ht
  have hF : (body.boundary evolution).integral (term% f) = some "F" := by decide +kernel
  have hG : (body.boundary evolution).integral (term% int(f, t)) = some "G" := by decide +kernel
  have cF : body.coordinate evolution "F" = some ⟨1, by decide⟩ := by decide +kernel
  have cG : body.coordinate evolution "G" = some ⟨2, by decide⟩ := by decide +kernel
  obtain ⟨j, hj, readsF⟩ := h.integral_state hF
  obtain ⟨k, hk, readsG⟩ := h.integral_state hG
  rw [cF, Option.some.injEq] at hj
  rw [cG, Option.some.injEq] at hk
  subst hj hk
  exact ⟨readsF t ht', readsG t ht'⟩

/-- Along the explicit solution, `I_t(I_t(f))` is `G(t)`. -/
theorem nested_integral_value (t : ℝ) (ht : 0 ≤ t) :
    body.atoms evolution solution t (term% int(int(f, t), t)) =
      some ((Real.exp t - dampedCos t - Real.sqrt 3 * dampedSin t) / 3) :=
  (integrals_read_states solution solution_solves t ht).2

/-- Declaring only the outer integral leaves its integrand `I_t(f)` unread. -/
theorem outer_only_rejected :
    (match compileSourceContinuous { body with
        integrals := integrals% { dG : G = int(int(f, t), t); }
        differentials := differentials% {
          df : diff(f, t) = int(int(f, t), t); dF : diff(F, t) = f; } } evolution with
      | .error d => some d | .ok _ => none) = some ⟨.unsupportedIntegral, "dG", "integrand"⟩ := by
  decide +kernel

#print axioms solution_solves
#print axioms source_unique
#print axioms integrals_read_states
#print axioms nested_integral_value
end Gimle.Asgard.Examples.NestedIntegralStates
