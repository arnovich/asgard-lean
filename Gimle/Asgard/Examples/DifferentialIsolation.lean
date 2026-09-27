import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax

/-! An implicit first-order equation, isolated with its residual and its
initial condition, and solved.

The source is `3*D_t(x) + x = y` with `y' = 0`, `x(0) = 5` and `y(0) = 2`.
Isolation yields `D_t(x) = (y - x)/3` exactly: the pinned Python compiler
yields `diff(x,t) = (0.3333333333333333 * (y - x))` for the same source, a
binary64 approximation of the scale that is not used here as an oracle.

The declared initial values stay in the unchanged `Evolution`. The compiled
field is homogeneous linear, so the source equation has exactly one solution
on `t ≥ 0`, which is `x(t) = 2 + 3 exp(-t/3)` and `y(t) = 2`. -/
namespace Gimle.Asgard.Examples.DifferentialIsolation
open Polynomial Model

/-- Scale 3 is a parameter of the declaration, so a changed model can be checked. -/
def body (scale : ℚ) : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"state-y", "y", .state⟩]
  assignments := assignments% { dy := 0; }
  differentials := [⟨⟨"dx", "dx", .output⟩,
    .add (.mul (.constant scale) (term% diff(x, t))) (term% x), term% y⟩]
  observations := [⟨⟨"obs-gap", "gap", .output⟩, "gap"⟩]
}

/-- The written source for scale 3 is exactly `3 * diff(x, t) + x = y`. -/
example : (body 3).differentials = differentials% { dx : 3 * diff(x, t) + x = y; } := rfl

/-- The observation `gap = y - x` is added as an explicit assignment. -/
def observed (scale : ℚ) : SourceBody :=
  { body scale with assignments := assignments% { dy := 0; gap := y - x; } }

def evolution (x0 : ℚ) : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-y", "y0", .initial⟩]
  initialValues := [⟨"initial-x", x0⟩, ⟨"initial-y", 2⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def model : SourceContinuousModel (observed 3) (evolution 5) :=
  (compileSourceContinuous (observed 3) (evolution 5)).toOption.get (by decide +kernel)

/-- The residual `x` is retained and the scale inverted exactly:
`D_t(x) = (y - x)/3`, beside the untouched explicit assignments. -/
theorem isolated : model.lowered.assignments =
    [⟨⟨"dy", "dy", .output⟩, .constant 0⟩,
     ⟨⟨"gap", "gap", .output⟩, .add (.var "y") (.neg (.var "x"))⟩,
     ⟨⟨"dx", "dx", .output⟩, .mul (.constant (1 / 3)) (.add (.var "y") (.neg (.var "x")))⟩] := by
  decide +kernel

/-- The compiled field over state order [x, y]. -/
theorem rates_expressions : model.model.rates.expressions =
    (![.mul (.constant (1 / 3)) (.add (.var 1) (.neg (.var 0))), .constant 0] :
      Fin 2 → Expr 2) := by
  decide +kernel

/-- The same initial condition, read from the unchanged evolution. -/
theorem initial_eq : model.model.initial = (![5, 2] : Point 2) := by
  change (fun i : Fin 2 => (model.model.initials i : ℝ)) = _
  have values : model.model.initials = ![5, 2] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

noncomputable def solution : Dynamics.Signal 2 := fun t => ![2 + 3 * Real.exp (-t / 3), 2]

private theorem solution_deriv (t : ℝ) :
    HasDerivAt (fun t => 2 + 3 * Real.exp (-t / 3)) (-Real.exp (-t / 3)) t := by
  have h := ((((hasDerivAt_id' t).neg).div_const 3).exp.const_mul 3).const_add 2
  exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- The explicit trajectory solves the ORIGINAL implicit source equation with
its initial data. The proof goes through the proved correspondence; the source
relation reads `D_t(x)` as the derivative of `x` itself. -/
theorem solution_solves : (observed 3).Solves (evolution 5) solution := by
  rw [model.lowered.solves_iff, model.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [initial_eq]
    ext i
    fin_cases i <;> norm_num [solution, Evolution.time, evolution]
  · rw [rates_expressions]
    change Fin 2 at i
    fin_cases i
    · have hd : HasDerivWithinAt (fun t => solution t 0) (-Real.exp (-t / 3))
          (evolution 5).time.domain t := (solution_deriv t).hasDerivWithinAt
      refine hd.congr_deriv ?_
      simp [Expr.eval, solution]
    · have hd : HasDerivWithinAt (fun t => solution t 1) 0 (evolution 5).time.domain t :=
        hasDerivWithinAt_const t _ (2 : ℝ)
      refine hd.congr_deriv ?_
      simp [Expr.eval]

def linear : LinearView model.model := model.model.linear.get (by decide +kernel)

/-- Every solution of the source equation equals the explicit one on `t ≥ 0`. -/
theorem source_unique (state : Dynamics.Signal 2) (h : (observed 3).Solves (evolution 5) state) :
    Set.EqOn state solution (Set.Ici 0) := by
  have hx := (model.solves_iff_realizes state).mp h
  have hs := (model.solves_iff_realizes solution).mp solution_solves
  have := linear.unique_realization hx hs
  simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using this

/-- The observed gap `y - x = -3 exp(-t/3)` along the solution. -/
theorem gap_observed (t : ℝ) :
    model.model.outputs.circuit.run (solution t) = ![-3 * Real.exp (-t / 3)] := by
  rw [Selected.circuit, compileOutputs_correct]
  have terms : model.model.outputs.expressions =
      (![.add (.var 1) (.neg (.var 0))] : Fin 1 → Expr 2) := by decide +kernel
  rw [terms]
  ext i
  fin_cases i
  simp [Expr.eval, solution]

/-- A changed initial value is a valid model whose solutions differ. -/
theorem changed_initial : ¬ (observed 3).Solves (evolution 4) solution := by
  intro h
  have := h.1 (0 : Fin 2)
  simp [Evolution.initialValue, Evolution.time, evolution, solution] at this
  norm_num at this

/-- A changed scale is a valid model; the old solution does not solve it,
because at `t = 0` its derivative `-1` differs from `(2 - 5)/2`. -/
def changedModel : SourceContinuousModel (observed 2) (evolution 5) :=
  (compileSourceContinuous (observed 2) (evolution 5)).toOption.get (by decide +kernel)

theorem changed_scale : ¬ (observed 2).Solves (evolution 5) solution := by
  rw [changedModel.lowered.solves_iff, changedModel.model.solves_iff_field]
  rintro ⟨_, deriv⟩
  have rates : changedModel.model.rates.expressions =
      (![.mul (.constant (1 / 2)) (.add (.var 1) (.neg (.var 0))), .constant 0] :
        Fin 2 → Expr 2) := by decide +kernel
  have h := deriv 0 (by simp [Evolution.time, evolution, Dynamics.TimeDomain.domain]) (0 : Fin 2)
  rw [rates] at h
  have hsol := (solution_deriv 0).hasDerivWithinAt (s := Set.Ici 0)
  have unique := (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv _ hsol
    (by simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain, solution] using h)
  norm_num [Expr.eval, solution] at unique

#print axioms solution_solves
#print axioms source_unique
#print axioms changed_scale
end Gimle.Asgard.Examples.DifferentialIsolation
