import Gimle.Asgard.Streams.ExpPoly

/-! Exact exponential-polynomial arithmetic and all Duhamel resonance branches. -/
namespace Gimle.Asgard.Tests.ExpPoly

open Gimle.Asgard.Streams
open Polynomial

example (ν t : ℝ) (P Q : ExpPoly) :
    ExpPoly.eval ν t (P * Q) = ExpPoly.eval ν t P * ExpPoly.eval ν t Q :=
  map_mul (ExpPoly.eval ν t) P Q

example (ν : ℚ) (μ : ℕ) (P : ExpPoly) :
    ExpPoly.deriv ν (ExpPoly.duhamel ν μ P) + (ν * μ) • ExpPoly.duhamel ν μ P = P :=
  ExpPoly.deriv_duhamel ν μ P

example (ν : ℚ) (μ : ℕ) (P : ExpPoly) :
    ExpPoly.eval ν 0 (ExpPoly.duhamel ν μ P) = 0 :=
  ExpPoly.eval_duhamel_zero ν μ P

/-- Zero viscosity is resonant even when the two exponential indices differ. -/
example (μ rate : ℕ) (p : ℚ[X]) :
    ExpPoly.duhamel 0 μ (AddMonoidAlgebra.single rate p) =
      AddMonoidAlgebra.single rate (ExpPoly.integrate p) := by
  simp [ExpPoly.duhamel_single, ExpPoly.duhamelTerm]

/-- Equal indices are resonant at every viscosity. -/
example (ν : ℚ) (rate : ℕ) (p : ℚ[X]) :
    ExpPoly.duhamel ν rate (AddMonoidAlgebra.single rate p) =
      AddMonoidAlgebra.single rate (ExpPoly.integrate p) := by
  simp [ExpPoly.duhamel_single, ExpPoly.duhamelTerm]

/-- Subtraction of rates takes place in ℚ, so this is nonresonant with c = -1. -/
example : ExpPoly.duhamel 1 1 (AddMonoidAlgebra.single 2 (1 : ℚ[X])) =
    AddMonoidAlgebra.single 2 (-1 : ℚ[X]) - AddMonoidAlgebra.single 1 (-1 : ℚ[X]) := by
  norm_num [ExpPoly.duhamelTerm, ExpPoly.inverse, ExpPoly.inverseAux]

example (ν : ℚ) (μ : ℕ) (P : ExpPoly) (t : ℝ) :
    ExpPoly.eval ν t (ExpPoly.duhamel ν μ P) =
      ∫ s in (0 : ℝ)..t, Real.exp (-((ν : ℝ) * μ * (t - s))) * ExpPoly.eval ν s P :=
  ExpPoly.eval_duhamel ν μ P t

#print axioms ExpPoly.deriv_duhamel
#print axioms ExpPoly.eval_duhamel
#print axioms ExpPoly.hasDerivAt

end Gimle.Asgard.Tests.ExpPoly
