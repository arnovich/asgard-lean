import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! An integral that no inverse rewrite removes, kept through a declared
integral state, and solved.

The source is `D_t(f) = I_t(f)` with `f(0) = 1`. The integral is declared, not
inferred: `dF : F = I_t(f)` makes the state `F` the integral of `f` from the
start, with its own `StateBinding` and the declared initial value `F(0) = 0`.
Lowering reads `I_t(f)` as `F` and yields the first-order system `D_t(f) = F`,
`D_t(F) = f`. The compiled field is homogeneous linear, so the source has
exactly one solution on `t ≥ 0`: `f(t) = cosh t` and `F(t) = sinh t`.

Along that solution the source's own reading of `I_t(f)`, the antiderivative of
`f` from the start, is `sinh t`, which is `F` (`integral_reads_state`); for
`cosh` it is also the interval integral (`integral_is_interval_integral`).

The pinned Python compiler accepts the same source as Form-A
`f = int(int(f,t),t) + f0`, whose inner integral is a hidden state starting at
zero; Lean requires that state declared, with its initial value `0` written in
the evolution. A declared initial value other than `0` is rejected
(`nonzero_rejected`). -/
namespace Gimle.Asgard.Examples.IntegralStates
open Polynomial Model

def body : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-F", "F", .state⟩]
  assignments := []
  differentials := differentials% { df : diff(f, t) = int(f, t); }
  integrals := integrals% { dF : F = int(f, t); }
}

def evolution (f0 F0 : ℚ) : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-F", "dF", "initial-F"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-F", "F0", .initial⟩]
  initialValues := [⟨"initial-f", f0⟩, ⟨"initial-F", F0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def model : SourceContinuousModel body (evolution 1 0) :=
  (compileSourceContinuous body (evolution 1 0)).toOption.get (by decide +kernel)

/-- `I_t(f)` became `F`, and the declaration became `dF := f`. -/
theorem lowered : model.lowered.assignments =
    [⟨⟨"df", "df", .output⟩, .var "F"⟩, ⟨⟨"dF", "dF", .output⟩, .var "f"⟩] := by
  decide +kernel

/-- The compiled field over state order [f, F]. -/
theorem rates_expressions : model.model.rates.expressions =
    (![.var 1, .var 0] : Fin 2 → Expr 2) := by
  decide +kernel

/-- Both initial values, read from the unchanged evolution: `F(0) = 0` is
declared, not assumed. -/
theorem initial_eq : model.model.initial = (![1, 0] : Point 2) := by
  change (fun i : Fin 2 => (model.model.initials i : ℝ)) = _
  have values : model.model.initials = ![1, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

noncomputable def solution : Dynamics.Signal 2 := fun t => ![Real.cosh t, Real.sinh t]

/-- The explicit trajectory solves the ORIGINAL source, integral declaration and
initial data included. -/
theorem solution_solves : body.Solves (evolution 1 0) solution := by
  rw [model.lowered.solves_iff, model.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [initial_eq]
    ext i
    fin_cases i <;> norm_num [solution, Evolution.time, evolution]
  · rw [rates_expressions]
    change Fin 2 at i
    fin_cases i
    · exact (Real.hasDerivAt_cosh t).hasDerivWithinAt.congr_deriv (by simp [Expr.eval, solution])
    · exact (Real.hasDerivAt_sinh t).hasDerivWithinAt.congr_deriv (by simp [Expr.eval, solution])

def linear : LinearView model.model := model.model.linear.get (by decide +kernel)

/-- Every solution of the source equals the explicit one on `t ≥ 0`, the
integral state included. -/
theorem source_unique (state : Dynamics.Signal 2) (h : body.Solves (evolution 1 0) state) :
    Set.EqOn state solution (Set.Ici 0) := by
  have hx := (model.solves_iff_realizes state).mp h
  have hs := (model.solves_iff_realizes solution).mp solution_solves
  have := linear.unique_realization hx hs
  simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using this

/-- In every solution, the source's reading of `I_t(f)`, the antiderivative of
`f` from the start, is the state `F`. The statement mentions only `body.Solves`
and the trajectory reading, not the lowered system. -/
theorem integral_reads_state (state : Dynamics.Signal 2) (h : body.Solves (evolution 1 0) state)
    (t : ℝ) (ht : 0 ≤ t) :
    body.atoms (evolution 1 0) state t (term% int(f, t)) = some (state t 1) := by
  have hF : (body.boundary (evolution 1 0)).integral (term% f) = some "F" := by decide +kernel
  obtain ⟨j, hj, reads⟩ := h.integral_state hF
  have hj' : j = ⟨1, by decide⟩ := by
    have : body.coordinate (evolution 1 0) "F" = some ⟨1, by decide⟩ := by decide +kernel
    rw [this, Option.some.injEq] at hj
    exact hj.symm
  subst hj'
  exact reads t (by simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using ht)

/-- Along the solution the integral is `sinh t`, and for the continuous
integrand `cosh` that is the interval integral from `0`. -/
theorem integral_is_interval_integral (t : ℝ) (ht : 0 ≤ t) :
    body.atoms (evolution 1 0) solution t (term% int(f, t)) = some (Real.sinh t) ∧
      (∫ s in (0 : ℝ)..t, Real.cosh s) = Real.sinh t := by
  refine ⟨integral_reads_state solution solution_solves t ht, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => Real.hasDerivAt_sinh s)
    (Real.continuous_cosh.intervalIntegrable 0 t), Real.sinh_zero, sub_zero]

/-- A declared integral state must start at `0`: with `F(0) = 1` the state would
be `1 + I_t(f)`, not `I_t(f)`, so lowering refuses to read `I_t(f)` as `F`. -/
theorem nonzero_rejected :
    (match compileSourceContinuous body (evolution 1 1) with
      | .error d => some d | .ok _ => none) = some ⟨.nonzeroInitial, "dF", "F"⟩ := by
  decide +kernel

#print axioms solution_solves
#print axioms source_unique
#print axioms integral_reads_state
#print axioms integral_is_interval_integral
end Gimle.Asgard.Examples.IntegralStates
