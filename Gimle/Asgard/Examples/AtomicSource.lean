import Gimle.Asgard.Model.AtomicSource
import Gimle.Asgard.Model.SourceSyntax
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source declarations with real atomics and division by expressions.

magnitude:  r := sqrt(x*x + y*y),  m := r / (1 + r),  observe m
zeroLog:    z := 0 * log(x),                          observe z
growth:     2 * x' = 1 / x,                           x(0) = 1
guarded:    x' = -1,  w := log(x) (unused),           x(0) = 1

The source relations are the unchanged `SourceBody.Observes` and
`SourceBody.Solves`; the atomics give them their domains. `magnitude` observes
`5/6` at `(3, 4)` and always observes a value in `[0, 1)`. `zeroLog` observes
nothing at `x = -1`, although its totalized value would be `0`. `growth` is
solved by `x = sqrt(1 + t)`, which stays where `1 / x` is defined. `guarded` has
no solution on `t ≥ 0` at all: the unused `log(x)` must be defined at every
time, and the only solution of `x' = -1` from `1` reaches `x = -1` at `t = 2`.
No existence, uniqueness or numerical claim is made beyond these. -/
namespace Gimle.Asgard.Examples.AtomicSource
open Gimle.Asgard Model RealAtomics

/-! ## A polynomial declaration -/

def magnitude : SourceBody := {
  inputs := [⟨"input-x", "x", .input⟩, ⟨"input-y", "y", .input⟩]
  assignments := assignments% { r := sqrt(x * x + y * y); m := r / (1 + r); }
  observations := [⟨⟨"obs-m", "m", .output⟩, "m"⟩]
}

def magnitudeModel : AtomicPolynomialModel magnitude :=
  (compileAtomicPolynomial magnitude).toOption.get (by decide +kernel)

/-- The runtime coordinates `[x, y]`. -/
abbrev Plane := (magnitude.withAssignments []).runtimePorts.length

def radius : Expr 0 Plane :=
  .unary .sqrt (.binary .add (.binary .mul (.input ⟨0, by decide⟩) (.input ⟨0, by decide⟩))
    (.binary .mul (.input ⟨1, by decide⟩) (.input ⟨1, by decide⟩)))

def ratio : Expr 0 Plane := .binary .division radius (.binary .add (.constant 1) radius)

theorem magnitude_outputs : magnitudeModel.outputs = ![ratio] := by decide +kernel

theorem magnitude_guards (j) :
    magnitudeModel.resolved.guards j = radius ∨ magnitudeModel.resolved.guards j = ratio := by
  revert j; decide +kernel

private theorem radius_value (x : Point Plane) :
    radius.value ![] x = Real.sqrt (x ⟨0, by decide⟩ * x ⟨0, by decide⟩ +
      x ⟨1, by decide⟩ * x ⟨1, by decide⟩) := rfl

/-- Every observation of the original source lies in `[0, 1)`. -/
theorem magnitude_range (x : Point Plane) (y : Point 1)
    (h : magnitude.Observes Context.empty magnitude.runtimeIds magnitude.observationIds x y) :
    0 ≤ y 0 ∧ y 0 < 1 := by
  rw [magnitudeModel.correct ![], AtomicPolynomialModel.circuit, guardedField_rel,
    magnitude_outputs] at h
  obtain ⟨-, rfl⟩ := h
  have hs := Real.sqrt_nonneg (x ⟨0, by decide⟩ * x ⟨0, by decide⟩ +
      x ⟨1, by decide⟩ * x ⟨1, by decide⟩)
  simp only [ratio, Expr.value, Binary.value, radius_value, Matrix.cons_val_zero]
  push_cast
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

/-- The point `(3, 4)`. -/
def threeFour : Point Plane := ![3, 4]

/-- At `(3, 4)` the original source observes `m = 5/6`. -/
theorem magnitude_at : magnitude.Observes Context.empty magnitude.runtimeIds
    magnitude.observationIds threeFour ![5 / 6] := by
  have t0 : threeFour ⟨0, by decide⟩ = 3 := rfl
  have t1 : threeFour ⟨1, by decide⟩ = 4 := rfl
  have five : radius.value ![] threeFour = 5 := by
    rw [radius_value, t0, t1, show (3 * 3 + 4 * 4 : ℝ) = 5 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hr : radius.Defined ![] threeFour := by
    refine ⟨by simp [Expr.Defined, Binary.Domain], ?_⟩
    show (0 : ℝ) ≤ threeFour ⟨0, by decide⟩ * threeFour ⟨0, by decide⟩ +
      threeFour ⟨1, by decide⟩ * threeFour ⟨1, by decide⟩
    rw [t0, t1]
    norm_num
  have hq : ratio.Defined ![] threeFour := by
    refine ⟨⟨hr, ⟨trivial, hr⟩, trivial⟩, ?_⟩
    show _ ≠ (0 : ℝ)
    rw [show Expr.value ![] threeFour (.binary .add (.constant 1) radius) =
      ((1 : ℚ) : ℝ) + radius.value ![] threeFour from rfl, five]
    norm_num
  rw [magnitudeModel.correct ![], AtomicPolynomialModel.circuit, guardedField_rel,
    magnitude_outputs]
  refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_⟩
  · fin_cases i
    exact hq
  · rcases magnitude_guards j with h | h <;> rw [h]
    · exact hr
    · exact hq
  · funext i
    fin_cases i
    change (5 / 6 : ℝ) = radius.value ![] threeFour / (((1 : ℚ) : ℝ) + radius.value ![] threeFour)
    rw [five]
    norm_num

/-! ## A domain under a zero multiplier -/

def zeroLog : SourceBody := {
  inputs := [⟨"input-x", "x", .input⟩]
  assignments := assignments% { z := 0 * log(x); }
  observations := [⟨⟨"obs-z", "z", .output⟩, "z"⟩]
}

def zeroLogModel : AtomicPolynomialModel zeroLog :=
  (compileAtomicPolynomial zeroLog).toOption.get (by decide +kernel)

def zeroLogTerm : Expr 0 (zeroLog.withAssignments []).runtimePorts.length :=
  .binary .mul (.constant 0) (.unary .log (.input ⟨0, by decide⟩))

theorem zeroLog_outputs : zeroLogModel.outputs = ![zeroLogTerm] := by decide +kernel

/-- The point `x = -1`. -/
def minusOne : Point (zeroLog.withAssignments []).runtimePorts.length := ![-1]

/-- At `x = -1` nothing is observed, although `0 * log(-1)` is `0` when totalized. -/
theorem zeroLog_undefined (y : Point 1) :
    ¬ zeroLog.Observes Context.empty zeroLog.runtimeIds zeroLog.observationIds minusOne y := by
  rw [zeroLogModel.correct ![], AtomicPolynomialModel.circuit, guardedField_rel,
    zeroLog_outputs]
  rintro ⟨⟨houts, -⟩, -⟩
  have h0 : 0 < zeroLog.observations.length := by decide
  have : zeroLogTerm.Defined ![] minusOne := houts ⟨0, h0⟩
  obtain ⟨⟨-, ⟨-, hlog⟩⟩, -⟩ := this
  have : (0 : ℝ) < -1 := hlog
  norm_num at this

/-! ## Continuous declarations -/

def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩]
  initialValues := [⟨"initial-x", 1⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- The single state coordinate `x`. -/
abbrev Line := evolution.states.length

def growth : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩]
  assignments := []
  differentials := differentials% { dx : 2 * diff(x, t) = 1 / x; }
}

def growthModel : AtomicContinuousModel growth evolution :=
  (compileAtomicContinuous growth evolution).toOption.get (by decide +kernel)

def growthRate : Expr 1 Line :=
  .binary .mul (.constant (1 / 2)) (.binary .division (.constant 1) (.input ⟨0, by decide⟩))

theorem growth_rates (i) : growthModel.rates i = growthRate := by revert i; decide +kernel
theorem growth_guards (j) : growthModel.resolved.guards j = growthRate := by
  revert j; decide +kernel
theorem growth_initial : growthModel.initial = fun _ => 1 := by
  funext i
  have : ∀ i, growthModel.initials i = 1 := by decide +kernel
  simp [AtomicContinuousModel.initial, this]

noncomputable def root : Dynamics.Signal Line := fun t _ => Real.sqrt (1 + t)

private theorem domain : evolution.time.domain = Set.Ici 0 := by
  simp [evolution, Evolution.time, Dynamics.TimeDomain.domain]

/-- `x = sqrt(1 + t)` solves the original source: `2 * x' = 1 / x` with every
`1 / x` defined along it. -/
theorem growth_solution : growth.Solves evolution root := by
  rw [growthModel.solves_iff, growth_initial]
  simp only [growth_rates, growth_guards, domain]
  refine ⟨by funext i; simp [root, evolution, Evolution.time], fun t ht => ?_⟩
  have ht : (0 : ℝ) ≤ t := ht
  have hpos : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr (by linarith)
  have hd : growthRate.Defined (timeAxis t) (root t) := by
    simp [growthRate, Expr.Defined, Expr.value, Binary.Domain, root, hpos.ne']
  refine ⟨⟨fun _ => hd, fun _ => hd⟩, fun i => ?_⟩
  simp only [growthRate, Expr.value, Binary.value, root]
  have inner : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
  have h := (Real.hasDerivAt_sqrt (by linarith : (1 + t : ℝ) ≠ 0)).comp t inner
  refine HasDerivAt.hasDerivWithinAt (HasDerivAt.congr_deriv h ?_)
  push_cast
  field_simp

def guarded : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩]
  assignments := assignments% { w := log(x); }
  differentials := differentials% { dx : diff(x, t) = -1; }
}

def guardedModel : AtomicContinuousModel guarded evolution :=
  (compileAtomicContinuous guarded evolution).toOption.get (by decide +kernel)

def logTerm : Expr 1 Line := .unary .log (.input ⟨0, by decide⟩)

theorem guarded_rates (i) : guardedModel.rates i = .unary .neg (.constant 1) := by
  revert i; decide +kernel
theorem guarded_log : ∃ j, guardedModel.resolved.guards j = logTerm := by decide +kernel
theorem guarded_initial : guardedModel.initial = fun _ => 1 := by
  funext i
  have : ∀ i, guardedModel.initials i = 1 := by decide +kernel
  simp [AtomicContinuousModel.initial, this]

/-- No signal solves `guarded`: the unused `log(x)` keeps its domain at every time
of the forward domain, which the only solution of `x' = -1`, `x(0) = 1`, leaves. -/
theorem guarded_unsolvable (state : Dynamics.Signal Line) :
    ¬ guarded.Solves evolution state := by
  rw [guardedModel.solves_iff, guarded_initial]
  simp only [guarded_rates, domain]
  rintro ⟨h0, h⟩
  have x0 : Fin Line := ⟨0, by decide⟩
  have line : Set.EqOn (fun t => state t ⟨0, by decide⟩) (fun t => 1 - t) (Set.Ici 0) := by
    refine eqOn_of_hasDerivWithinAt (f := fun _ => -1) (fun s hs => ?_) (fun s _ => ?_) ?_
    · simpa [Expr.value, Unary.value] using (h s hs).2 ⟨0, by decide⟩
    · exact ((hasDerivAt_id s).const_sub 1).hasDerivWithinAt.congr_deriv (by simp)
    · simpa [evolution, Evolution.time] using congrFun h0 ⟨0, by decide⟩
  obtain ⟨j, hj⟩ := guarded_log
  have two := (h 2 (by norm_num)).1.2 j
  rw [hj] at two
  simp only [logTerm, Expr.Defined, Unary.Domain, Expr.value, true_and] at two
  have := line (show (2 : ℝ) ∈ Set.Ici 0 by norm_num)
  simp only at this
  linarith

end Gimle.Asgard.Examples.AtomicSource
