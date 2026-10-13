import Gimle.Asgard.Dynamics.Linear

namespace Gimle.Asgard.Tests.Linear
open Gimle.Asgard.Dynamics Gimle.Asgard.Dynamics.Linear

-- Noninteger coefficients and asymmetric rows make transposition/order bugs visible.
def asymmetric : Matrix 3 := ![![0, 1/3, 2], ![-3, 0, 1], ![4, -5, 6]]
example : asymmetric.field.run ![2, 3, 5] = ![11, -1, 23] := by
  rw [Matrix.field_correct]
  ext i
  fin_cases i <;> norm_num [asymmetric, Matrix.eval, Fin.sum_univ_succ]

noncomputable def shifted : Problem 3 where
  names := !["z", "x", "y"]
  matrix := asymmetric
  initial := ![2, 3, 5]
  time := ⟨"elapsed", 7⟩

example (state : Signal 3) : shifted.Solves state ↔ shifted.Realizes state :=
  shifted.solves_iff_realizes state

example (state : Signal 3) (h : shifted.Realizes state) : state 7 = ![2, 3, 5] :=
  ((shifted.solves_iff_realizes state).mpr h).1

-- Empty systems remain well typed and have a trajectory.
noncomputable def empty : Problem 0 where
  names := Fin.elim0
  matrix := Fin.elim0
  initial := Fin.elim0
  time := ⟨"t", 2⟩

example : empty.Realizes (fun _ => Fin.elim0) := by
  apply (empty.solves_iff_realizes _).mp
  exact ⟨rfl, fun _ _ i => Fin.elim0 i⟩
-- Existence and uniqueness apply to every rational matrix, including this
-- nonzero start and deliberately reordered three-state context.
example : ∃ state, shifted.Realizes state := shifted.exists_realization
example {x y : Signal 3} (hx : shifted.Realizes x) (hy : shifted.Realizes y) :
    Set.EqOn x y (Set.Ici 7) := shifted.unique_realization hx hy

noncomputable def stationary : Problem 1 where
  names := !["temperature"]
  matrix := ![![0]]
  initial := ![3]
  time := ⟨"elapsed", 5⟩

example : stationary.Realizes (fun _ => ![3]) := by
  apply (stationary.solves_iff_realizes _).mp
  refine ⟨rfl, ?_⟩
  intro t _ i
  fin_cases i
  simpa [stationary, Matrix.eval] using
    (hasDerivAt_const t (3 : ℝ)).hasDerivWithinAt (s := stationary.time.domain)

-- Wrong initial values are rejected by the complete target relation.
example : ¬ stationary.Realizes (fun _ => ![4]) := by
  intro h
  have initial := ((stationary.solves_iff_realizes _).mpr h).1
  have := congrFun initial 0
  norm_num [stationary] at this

-- A changed damping sign is still linear and has global solutions; it does not
-- inherit the original oscillator's energy-decay conclusion.
def wrongDamping : Matrix 2 := ![![0, 1], ![-1, 2]]
example : ∑ i : Fin 2, 4 * (![0, 1] : Point 2) i *
    wrongDamping.eval ![0, 1] i > 0 := by
  norm_num [wrongDamping, Matrix.eval, Fin.sum_univ_succ]

-- x' = x² is compilable as a polynomial RHS, but rejected by the linear
-- existence API. With x(0)=1 its familiar finite-time pole is at t=1.
example : (Polynomial.Expr.compile (Polynomial.Expr.mul (n := 1) (.var 0) (.var 0))).run ![2] = ![4] := by
  ext i
  fin_cases i
  norm_num [Polynomial.Expr.eval]
example : LinearSyntax.coefficients
    (Polynomial.Expr.mul (n := 1) (.var 0) (.var 0)) = none := rfl

end Gimle.Asgard.Tests.Linear
