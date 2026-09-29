import Gimle.Asgard.Examples.DeclaredAlgebraic

/-! Regression tests for declared affine algebraic loops (task 044).

Python comparison, gimle-asgard `27e5223`, with
`compile_equation_to_circuit(Equation.from_string(s))`. There is no Python
algebraic elimination to agree with, so every case differs:

- `z = z/2 + u`: Python accepts it as an unguarded `trace` circuit. Its stream
  runtime does not compute the algebraic fixed point `2u`
  (`runtime/stream/scan_evaluator.py` documents `1.0u` for `x = u + 0.5x`). Lean
  declares it (`halfDeclaration`) and eliminates it to `2u`: differs.
- `z = z + 1`: Python accepts it as a `trace` circuit. Lean refuses it with
  `invalidInverse` for every supplied inverse: differs.
- `z = z/2 + 1` with `z ∈ [-1, 1]`: Python accepts it as a `trace` circuit and
  has no loop domain. Lean cannot complete the declaration: differs.

Python's multi-equation algebraic layering (`compile/cross_wiring.py`) refuses a
cycle among algebraic equations outright, so it offers no elimination either. -/
namespace Gimle.Asgard.Tests.AlgebraicDeclarations
open Polynomial Matrix Algebraic

/-- The first diagnostic, if any. -/
def diagnostic {α : Type} : Except Model.Diagnostic α → Option Model.Diagnostic
  | .error e => some e
  | .ok _ => none

def ports : (Fin 1 → Port) × (Fin 1 → Port) :=
  (![⟨"z", "z", .state⟩], ![⟨"y", "y", .output⟩])

/-! ## Singular: `z = z + 1` -/

/-- `z = z + 1`, `y = z`, with no external input. -/
def unitLoop : Problem 1 0 1 where
  matrix := !![1]
  offset := ⟨0, ![1]⟩
  output := ⟨!![1], ![0]⟩

/-- Any supplied inverse completes the declaration; none is accepted. -/
def unitDeclaration (inverse : RationalMatrix 1 1) : Declaration 1 0 1 where
  loop := ports.1
  external := Fin.elim0
  outputs := ports.2
  problem := unitLoop
  inverse := inverse
  domain := fun _ => True
  admitted := fun _ => True
  membership := fun _ _ => trivial

#guard diagnostic (unitDeclaration !![1]).compile == some ⟨.invalidInverse, "inverse", "left"⟩
#guard diagnostic (unitDeclaration !![0]).compile == some ⟨.invalidInverse, "inverse", "left"⟩

/-- No declaration of the singular loop is accepted, whatever it supplies. -/
theorem unit_rejected {d o : Nat} (a : Declaration 1 d o) (singular : a.problem.matrix = !![1]) :
    IsEmpty (AlgebraicModel a) := by
  have none : ∀ v : RationalMatrix 1 1, v * (1 - !![1]) ≠ 1 := by
    intro v h
    have h := congrFun (congrFun h 0) 0
    norm_num [Matrix.mul_apply] at h
  refine AlgebraicModel.singular a ?_
  rintro ⟨inv⟩
  exact none inv.value (by rw [← singular]; exact inv.left)

/-- The relation still holds for every input, and is empty: `z = z + 1` has no
solution. -/
theorem unit_no_solution (u : Point 0) (y : Point 1) : ¬ (unitDeclaration 1).Solves u y := by
  rw [Declaration.solves_iff_rel]
  rintro ⟨z, _, loop, _⟩
  have h := congrFun loop 0
  simp only [Declaration.loopCircuit, Problem.loop_correct] at h
  simp [unitDeclaration, unitLoop, Affine.eval, realMatrix, Matrix.mulVec, dotProduct] at h

/-! ## Membership: `z = z/2 + 1` with `z ∈ [-1, 1]` -/

/-- `z = z/2 + 1`, `y = z`, with no external input; its solution is `z = 2`. -/
def offLoop : Problem 1 0 1 where
  matrix := !![1/2]
  offset := ⟨0, ![1]⟩
  output := ⟨!![1], ![0]⟩

def offDomain (z : Point 1) : Prop := -1 ≤ z 0 ∧ z 0 ≤ 1

/-- With the true inverse `2`, the membership obligation is false, so no
declaration with this inverse can be written down. -/
theorem off_obligation_false :
    ¬ ∀ u : Point 0, True → offDomain ((offLoop.solutionCircuit !![2]).run u) := by
  intro membership
  have h := (membership Fin.elim0 trivial).2
  simp [Problem.solution_correct, offLoop, Affine.eval, realMatrix, Matrix.mulVec,
    dotProduct] at h

/-- A wrong inverse makes the obligation provable, and is then refused. -/
def offWrong : Declaration 1 0 1 where
  loop := ports.1
  external := Fin.elim0
  outputs := ports.2
  problem := offLoop
  inverse := 0
  domain := offDomain
  admitted := fun _ => True
  membership := fun u _ => by
    simp [offDomain, Problem.solution_correct, realMatrix, Matrix.mulVec, dotProduct]

#guard diagnostic offWrong.compile == some ⟨.invalidInverse, "inverse", "left"⟩

/-- **The declaration cannot be completed.** No declaration of `z = z/2 + 1` on
`[-1, 1]` that admits an input is accepted, whatever inverse it supplies. -/
theorem off_rejected (a : Declaration 1 0 1) (problem : a.problem = offLoop)
    (domain : a.domain = offDomain) (u : Point 0) (hu : a.admitted u) :
    IsEmpty (AlgebraicModel a) := by
  refine ⟨fun m => ?_⟩
  obtain ⟨z, ⟨inside, loop⟩, _⟩ := (m.eliminate_correct u hu).1
  rw [domain] at inside
  have h := congrFun loop 0
  simp only [Declaration.loopCircuit, Problem.loop_correct, problem] at h
  simp [offLoop, Affine.eval, realMatrix, Matrix.mulVec, dotProduct] at h
  obtain ⟨_, upper⟩ := inside
  linarith

/-- Its relation is empty on the domain. -/
theorem off_no_solution (u : Point 0) (y : Point 1) : ¬ offWrong.Solves u y := by
  rw [Declaration.solves_iff_rel]
  rintro ⟨z, ⟨_, upper⟩, loop, _⟩
  have h := congrFun loop 0
  simp only [Declaration.loopCircuit, Problem.loop_correct] at h
  simp [offWrong, offLoop, Affine.eval, realMatrix, Matrix.mulVec, dotProduct] at h
  linarith

/-! ## Ports -/

def renamed (loop : Fin 1 → Port) (external : Fin 1 → Port) (outputs : Fin 1 → Port) :
    Declaration 1 1 1 :=
  { Examples.halfDeclaration with loop, external, outputs }

#guard diagnostic (renamed ![⟨"z", "z", .input⟩] ![⟨"u", "u", .input⟩]
  ![⟨"y", "y", .output⟩]).validate == some ⟨.unsupportedRole, "z", "z"⟩
#guard diagnostic (renamed ![⟨"z", "z", .state⟩] ![⟨"u", "u", .output⟩]
  ![⟨"y", "y", .output⟩]).validate == some ⟨.unsupportedRole, "u", "u"⟩
#guard diagnostic (renamed ![⟨"z", "z", .state⟩] ![⟨"z", "u", .input⟩]
  ![⟨"y", "y", .output⟩]).validate == some ⟨.duplicateId, "ports", "z"⟩
#guard diagnostic (renamed ![⟨"z", "z", .state⟩] ![⟨"u", "u", .input⟩]
  ![⟨"", "y", .output⟩]).validate == some ⟨.emptyId, "ports", "y"⟩

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Algebraic.Declaration.solves_iff_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Declaration.solves_iff_rel
/--
info: 'Gimle.Asgard.Algebraic.AlgebraicModel.eliminate_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AlgebraicModel.eliminate_correct
/--
info: 'Gimle.Asgard.Algebraic.AlgebraicModel.solves_iff_eliminated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AlgebraicModel.solves_iff_eliminated
/--
info: 'Gimle.Asgard.Algebraic.Declaration.coordinates_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Declaration.coordinates_loop
/--
info: 'Gimle.Asgard.Algebraic.Declaration.coordinates_external' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Declaration.coordinates_external
/--
info: 'Gimle.Asgard.Algebraic.Examples.half_declared' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.half_declared
/--
info: 'Gimle.Asgard.Algebraic.Examples.halfModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.halfModel
/--
info: 'Gimle.Asgard.Tests.AlgebraicDeclarations.unit_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unit_rejected
/--
info: 'Gimle.Asgard.Tests.AlgebraicDeclarations.off_obligation_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms off_obligation_false
/--
info: 'Gimle.Asgard.Tests.AlgebraicDeclarations.off_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms off_rejected

end Gimle.Asgard.Tests.AlgebraicDeclarations
