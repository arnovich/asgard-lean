import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax

/-! Source integrals from the declared start, removed by two of the inverse
rewrites, and solved.

`decay` is `D_t(I_t(2*D_t(f) + f)) = 0` with `f(0) = 2`. The derivative of the
integral is the integrand, so it lowers to `D_t(f) = (0 - f)/2`, a homogeneous
linear field: the source has exactly one solution on `t ≥ 0`, `f = 2e^(-t/2)`.
The pinned Python compiler accepts the same source with the same rate.

`boundary` is `D_t(x) + I_t(D_t(x)) = 1` with `x(0) = 2`. The integral of the
derivative is `x - x(0)`, so it lowers to `D_t(x) = 1 - (x - 2)`, with the
declared initial value as its boundary term, and is solved by `x = 3 - e^(-t)`.
Dropping the boundary term would give `D_t(x) + x = 1`, whose solution
`1 + e^(-t)` from the same initial value does not solve the source
(`boundary_dropped`). Python rejects this source ("competing derivative"). -/
namespace Gimle.Asgard.Examples.SourceIntegrals
open Polynomial Model

def evolution (name : String) (x0 : ℚ) : Evolution := {
  states := [⟨"state-" ++ name, "d" ++ name, "initial-" ++ name⟩]
  initialPorts := [⟨"initial-" ++ name, name ++ "0", .initial⟩]
  initialValues := [⟨"initial-" ++ name, x0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-! ## The derivative of an integral -/

def decay : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩]
  assignments := []
  differentials := differentials% { df : diff(int(2 * diff(f, t) + f, t), t) = 0; }
}

def decayModel : SourceContinuousModel decay (evolution "f" 2) :=
  (compileSourceContinuous decay (evolution "f" 2)).toOption.get (by decide +kernel)

/-- `D_t(I_t(X))` became `X`, which was then isolated with its residual kept. -/
theorem decay_lowered : decayModel.lowered.assignments =
    [⟨⟨"df", "df", .output⟩, .mul (.constant (1 / 2)) (.add (.constant 0) (.neg (.var "f")))⟩] := by
  decide +kernel

theorem decay_rates : decayModel.model.rates.expressions =
    (![.mul (.constant (1 / 2)) (.add (.constant 0) (.neg (.var 0)))] : Fin 1 → Expr 1) := by
  decide +kernel

theorem decay_initial : decayModel.model.initial = (![2] : Point 1) := by
  change (fun i : Fin 1 => (decayModel.model.initials i : ℝ)) = _
  have values : decayModel.model.initials = ![2] := by decide +kernel
  rw [values]
  ext i
  fin_cases i
  norm_num

noncomputable def decaySolution : Dynamics.Signal 1 := fun t => ![2 * Real.exp (-t / 2)]

private theorem decay_deriv (t : ℝ) :
    HasDerivAt (fun t => 2 * Real.exp (-t / 2)) (-Real.exp (-t / 2)) t := by
  have h := (((hasDerivAt_id' t).neg).div_const 2).exp.const_mul 2
  exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- `2e^(-t/2)` solves the ORIGINAL source, whose integral is read as the
antiderivative from the start along the solution. -/
theorem decay_solves : decay.Solves (evolution "f" 2) decaySolution := by
  rw [decayModel.lowered.solves_iff, decayModel.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [decay_initial]
    ext i
    fin_cases i
    norm_num [decaySolution, Evolution.time, evolution]
  · rw [decay_rates]
    change Fin 1 at i
    fin_cases i
    refine (decay_deriv t).hasDerivWithinAt.congr_deriv ?_
    simp [Expr.eval, decaySolution]

def decayLinear : LinearView decayModel.model := decayModel.model.linear.get (by decide +kernel)

/-- Every solution of the source equals the explicit one on `t ≥ 0`. -/
theorem decay_unique (state : Dynamics.Signal 1) (h : decay.Solves (evolution "f" 2) state) :
    Set.EqOn state decaySolution (Set.Ici 0) := by
  have hx := (decayModel.solves_iff_realizes state).mp h
  have hs := (decayModel.solves_iff_realizes decaySolution).mp decay_solves
  have := decayLinear.unique_realization hx hs
  simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using this

/-! ## The integral of a derivative keeps its boundary term -/

def boundary : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩]
  assignments := []
  differentials := differentials% { dx : diff(x, t) + int(diff(x, t), t) = 1; }
}

def boundaryModel : SourceContinuousModel boundary (evolution "x" 2) :=
  (compileSourceContinuous boundary (evolution "x" 2)).toOption.get (by decide +kernel)

/-- `I_t(D_t(x))` became `x - 2`, the declared initial value kept as a residual. -/
theorem boundary_lowered : boundaryModel.lowered.assignments =
    [⟨⟨"dx", "dx", .output⟩,
      .add (.constant 1) (.neg (.add (.var "x") (.neg (.constant 2))))⟩] := by
  decide +kernel

theorem boundary_rates : boundaryModel.model.rates.expressions =
    (![.add (.constant 1) (.neg (.add (.var 0) (.neg (.constant 2))))] : Fin 1 → Expr 1) := by
  decide +kernel

theorem boundary_initial : boundaryModel.model.initial = (![2] : Point 1) := by
  change (fun i : Fin 1 => (boundaryModel.model.initials i : ℝ)) = _
  have values : boundaryModel.model.initials = ![2] := by decide +kernel
  rw [values]
  ext i
  fin_cases i
  norm_num

noncomputable def boundarySolution : Dynamics.Signal 1 := fun t => ![3 - Real.exp (-t)]

private theorem boundary_deriv (t : ℝ) :
    HasDerivAt (fun t => 3 - Real.exp (-t)) (Real.exp (-t)) t := by
  have h := ((hasDerivAt_id' t).neg.exp).const_sub 3
  exact h.congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- `3 - e^(-t)` solves the ORIGINAL source. -/
theorem boundary_solves : boundary.Solves (evolution "x" 2) boundarySolution := by
  rw [boundaryModel.lowered.solves_iff, boundaryModel.model.solves_iff_field]
  refine ⟨?_, fun t _ i => ?_⟩
  · rw [boundary_initial]
    ext i
    fin_cases i
    norm_num [boundarySolution, Evolution.time, evolution]
  · rw [boundary_rates]
    change Fin 1 at i
    fin_cases i
    refine (boundary_deriv t).hasDerivWithinAt.congr_deriv ?_
    simp [Expr.eval, boundarySolution]
    ring

/-- Along the solution, the source's integral reads `x(t) - 2`, not `x(t)`. -/
theorem boundary_integral (t : ℝ) (ht : 0 ≤ t) :
    boundary.atoms (evolution "x" 2) boundarySolution t (term% int(diff(x, t), t)) =
      some (1 - Real.exp (-t)) := by
  obtain ⟨i, -, reads⟩ := boundary_solves.integral_derivative (x := "x") (q := 2)
    (by decide +kernel) (by decide +kernel)
  have entry : ∀ j : Fin 1, boundarySolution t j = 3 - Real.exp (-t) := fun j => by
    fin_cases j; rfl
  rw [show (term% int(diff(x, t), t)) = .integral (evolution "x" 2).axis.name
    (.derivative (evolution "x" 2).axis.name (.var "x")) from rfl,
    reads t (by simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain] using ht),
    entry i]
  norm_num
  ring

/-- The solution of the boundary-dropped equation `D_t(x) + x = 1` from the
same initial value. -/
noncomputable def droppedSolution : Dynamics.Signal 1 := fun t => ![1 + Real.exp (-t)]

/-- Dropping the boundary term changes the solutions: `1 + e^(-t)` does not
solve the source, because at `t = 0` its derivative `-1` differs from
`1 - (2 - 2)`. -/
theorem boundary_dropped : ¬ boundary.Solves (evolution "x" 2) droppedSolution := by
  rw [boundaryModel.lowered.solves_iff, boundaryModel.model.solves_iff_field]
  rintro ⟨_, deriv⟩
  have h := deriv 0 (by simp [Evolution.time, evolution, Dynamics.TimeDomain.domain]) (0 : Fin 1)
  rw [boundary_rates] at h
  have hd : HasDerivAt (fun t => 1 + Real.exp (-t)) (-Real.exp (-0)) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).neg.exp).const_add 1
    exact this.congr_deriv (by simp)
  have unique := (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv _
    (hd.hasDerivWithinAt (s := Set.Ici 0))
    (by simpa [Evolution.time, evolution, Dynamics.TimeDomain.domain, droppedSolution] using h)
  norm_num [Expr.eval, droppedSolution] at unique

#print axioms decay_solves
#print axioms decay_unique
#print axioms boundary_solves
#print axioms boundary_integral
#print axioms boundary_dropped
end Gimle.Asgard.Examples.SourceIntegrals
