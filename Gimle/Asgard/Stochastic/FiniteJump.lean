import Gimle.Asgard.Stochastic.Named
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! One concrete interpretation: ordinary Lebesgue time integration and finitely
many uncompensated jumps. Brownian, Stratonovich and compensated integration are
unsupported here. This is not a Poisson model or a sampled approximation. -/
namespace Gimle.Asgard.Stochastic
open scoped BigOperators

structure JumpSchedule (Ω : Type) where
  count : Nat
  times : Fin count → ℝ
  marks : Fin count → Ω → ℝ

noncomputable def JumpSchedule.path {Ω : Type} (s : JumpSchedule Ω) : ScalarProcess Ω :=
  fun t ω => ∑ k, if s.times k ≤ t then s.marks k ω else 0

/-- Integrands are already predictable/left-limit coefficient processes. Events
at the initial time are excluded, and events at the final time are included. -/
noncomputable def JumpSchedule.integral {Ω : Type} (s : JumpSchedule Ω) (start : ℝ)
    (f : ScalarProcess Ω) : ScalarProcess Ω :=
  fun t ω => ∑ k, if start < s.times k ∧ s.times k ≤ t then f (s.times k) ω * s.marks k ω else 0

/-- Integration has an explicit integrability premise. Totalized mathlib
integrals alone would silently assign a value to a nonintegrable function. -/
def ordinaryIntegral {Ω : Type} (time : Window) (f y : ScalarProcess Ω) : Prop :=
  (∀ t ∈ time.domain, ∀ ω, IntervalIntegrable (fun r => f r ω) MeasureTheory.volume time.start t) ∧
  ∀ t ∈ time.domain, ∀ ω, y t ω = ∫ r in time.start..t, f r ω

def JumpSchedule.semantics {Ω : Type} (s : JumpSchedule Ω) : IntegralSemantics Ω where
  time := ordinaryIntegral
  ito := fun _ _ _ _ => False
  stratonovich := fun _ _ _ _ => False
  uncompensated := fun time driver f y => driver = s.path ∧
    ∀ t ∈ time.domain, ∀ ω, y t ω = s.integral time.start f t ω
  compensated := fun _ _ _ _ => False

/-- The driving process is fixed by the schedule; replacing it cannot reuse an
uncompensated integral proof for the old process. -/
theorem JumpSchedule.driver_bound {Ω : Type} (s : JumpSchedule Ω) (time : Window)
    (driver f y : ScalarProcess Ω)
    (h : s.semantics.uncompensated time driver f y) : driver = s.path := h.1

theorem ordinaryIntegral_zero {Ω : Type} (time : Window) :
    ordinaryIntegral (Ω := Ω) time (fun _ _ => 0) (fun _ _ => 0) := by
  constructor
  · intro t _ ω
    exact intervalIntegrable_const
  · simp

/-- Every finite schedule gives a genuine nonempty zero-integrand interpretation. -/
theorem JumpSchedule.integral_zero {Ω : Type} (s : JumpSchedule Ω) (start : ℝ) :
    s.integral start (fun _ _ => 0) = fun _ _ => 0 := by
  funext t ω
  simp [integral]

#print axioms JumpSchedule.driver_bound
#print axioms ordinaryIntegral_zero
#print axioms JumpSchedule.integral_zero
end Gimle.Asgard.Stochastic
