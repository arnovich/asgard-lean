import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax
import Gimle.Asgard.Examples.DifferentialIsolation

/-! Acceptance fixtures for scoped beta normalization and first-order
differential isolation.

Each fixture restates a case from the pinned Python Asgard tests
`tests/unit/test_affine_differential_isolation.py` and
`tests/unit/test_differential_side_context.py` (gimle-asgard `abb428ad`).
Python's accept/reject outcome is recorded beside each one; it is a
regression reference, not an oracle. Lean's expected values are exact, and
the cases where the fragments deliberately differ are marked "differs". -/
namespace Gimle.Asgard.Tests.DifferentialIsolation
open Polynomial Model

/-! ## Isolation of one equation

`f` and `g` are states whose derivative ports are `df` and `dg`; `a` is not a
state. Equations are solved for `df`. -/

def context : Context :=
  ⟨"t", fun s => if s = "f" then some "df" else if s = "g" then some "dg" else none,
    fun _ => none, none⟩

def solve (lhs rhs : Term) : Option NamedExpr :=
  ((isolate context "df" lhs rhs).map Isolated.expr).toOption

def reject (lhs rhs : Term) : Option ErrorCode :=
  match isolate context "df" lhs rhs with
  | .error code => some code
  | .ok _ => none

-- The task fixture: `3*D_t(x) + x = y` gives `D_t(x) = (y - x)/3`, residual kept.
example : solve (term% 3 * diff(f, t) + f) (term% g) =
    some (.mul (.constant (1 / 3)) (.add (.var "g") (.neg (.var "f")))) := by decide +kernel
-- The same equation written the other way round.
example : solve (term% g) (term% 3 * diff(f, t) + f) =
    some (.mul (.constant (1 / 3)) (.add (.var "g") (.neg (.var "f")))) := by decide +kernel

-- Python accepts; rate r in f' = r*f. Lean: the same rate, exactly.
example : solve (term% 2 * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 2)) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) + f) (term% 0) =
    some (.add (.constant 0) (.neg (.var "f"))) := by decide +kernel
example : solve (term% f) (term% 2 * diff(f, t)) =
    some (.mul (.constant (1 / 2)) (.var "f")) := by decide +kernel
example : solve (term% f - 2 * diff(f, t)) (term% 0) =
    some (.mul (.constant (-1 / 2)) (.add (.constant 0) (.neg (.var "f")))) := by decide +kernel
example : solve (term% -diff(f, t)) (term% f) =
    some (.mul (.constant (-1)) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) / 2) (term% f) =
    some (.mul (.constant 2) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) * -2) (term% f) =
    some (.mul (.constant (-1 / 2)) (.var "f")) := by decide +kernel
example : solve (term% 2 * diff(f, t) / 4) (term% f) =
    some (.mul (.constant 2) (.var "f")) := by decide +kernel
example : solve (term% 2 * (3 * diff(f, t))) (term% f) =
    some (.mul (.constant (1 / 6)) (.var "f")) := by decide +kernel
example : solve (term% (2 * 3) * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 6)) (.var "f")) := by decide +kernel
example : solve (term% 2 * 3 * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 6)) (.var "f")) := by decide +kernel
example : solve (term% +diff(f, t)) (term% f) = some (.var "f") := by decide +kernel
example : solve (term% (-2 * -3) * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 6)) (.var "f")) := by decide +kernel
example : solve (term% (2 / 4) * diff(f, t)) (term% f) =
    some (.mul (.constant 2) (.var "f")) := by decide +kernel
example : solve (term% (diff(f, t))) (term% g) = some (.var "g") := by decide +kernel
example : solve (term% g) (term% (diff(f, t))) = some (.var "g") := by decide +kernel
example : solve (term% diff(f, t)) (term% f + g) = some (.add (.var "f") (.var "g")) := by decide +kernel
example : solve (term% diff(f, t)) (term% rat(1, 2) * f) =
    some (.mul (.constant (1 / 2)) (.var "f")) := by decide +kernel

-- Python's "decay" forcing case, solved for the differentiated state.
example : solve (term% g) (term% diff(f, t) + f) =
    some (.add (.var "g") (.neg (.var "f"))) := by decide +kernel
-- Nested literal factors and a residual after them.
example : solve (term% (2 * diff(f, t)) * 3 + f) (term% g) =
    some (.mul (.constant (1 / 6)) (.add (.var "g") (.neg (.var "f")))) := by decide +kernel
-- Negation distributes over a residual sum; only a literal factor around one is refused.
example : solve (term% -(diff(f, t) + f)) (term% g) =
    some (.mul (.constant (-1)) (.add (.var "g") (.neg (.neg (.var "f"))))) := by decide +kernel

-- Python accepts grouped residuals; every residual term is retained, in order.
example : solve (term% f + (2) * (diff(f, t)) - 3) (term% 0) =
    some (.mul (.constant (1 / 2))
      (.add (.constant 0) (.neg (.add (.var "f") (.neg (.constant 3)))))) := by decide +kernel
example : solve (term% 3 - (2 * diff(f, t) + f)) (term% 0) =
    some (.mul (.constant (-1 / 2))
      (.add (.constant 0) (.neg (.add (.constant 3) (.neg (.var "f")))))) := by decide +kernel
example : solve (term% 0) (term% 3 - (2 * diff(f, t) + f)) =
    some (.mul (.constant (-1 / 2))
      (.add (.constant 0) (.neg (.add (.constant 3) (.neg (.var "f")))))) := by decide +kernel
example : solve (term% diff(f, t) - (f - 3)) (term% 0) =
    some (.add (.constant 0) (.neg (.neg (.add (.var "f") (.neg (.constant 3)))))) := by decide +kernel
example : solve (term% 3 - (diff(f, t) + f)) (term% 0) =
    some (.mul (.constant (-1))
      (.add (.constant 0) (.neg (.add (.constant 3) (.neg (.var "f")))))) := by decide +kernel

-- Applied lambdas are normalized on the derivative-free sides.
example : solve (term% 2 * diff(f, t) + (λ w => w * w)(f)) (term% (λ w => w + 1)(g)) =
    some (.mul (.constant (1 / 2))
      (.add (.add (.var "g") (.constant 1)) (.neg (.mul (.var "f") (.var "f"))))) := by decide +kernel

-- Python rejects; Lean rejects, naming the reason.
example : reject (term% 0 * diff(f, t)) (term% f) = some .zeroScale := by decide +kernel
example : reject (term% (0 * 5) * diff(f, t)) (term% f) = some .zeroScale := by decide +kernel
example : reject (term% a * diff(f, t)) (term% f) = some .nonlinearDerivative := by decide +kernel
example : reject (term% f * diff(f, t)) (term% 1) = some .nonlinearDerivative := by decide +kernel
example : reject (term% (2 + 3) * diff(f, t)) (term% f) = some .nonlinearDerivative := by decide +kernel
example : reject (term% diff(f, t) * diff(f, t)) (term% f) = some .repeatedDerivative := by decide +kernel
example : reject (term% diff(f, t) + diff(f, t)) (term% f) = some .repeatedDerivative := by decide +kernel
example : reject (term% diff(f, t) - diff(f, t)) (term% f) = some .repeatedDerivative := by decide +kernel
example : reject (term% diff(f, t) + diff(g, t)) (term% 0) = some .repeatedDerivative := by decide +kernel
example : reject (term% 2 * diff(f, t)) (term% diff(f, t) + f) =
    some .competingDerivative := by decide +kernel
example : reject (term% diff(f + g, t)) (term% a) = some .unsupportedDerivative := by decide +kernel
example : reject (term% 2 * diff(diff(f, t), t)) (term% f) =
    some .higherOrderDerivative := by decide +kernel
example : reject (term% 2 * diff(diff(f, x), t)) (term% f) = some .mixedDerivative := by decide +kernel
example : reject (term% 2 * (diff(f, t) + f)) (term% 1) = some .unsupportedDerivative := by decide +kernel
example : reject (term% (λ z => diff(z, t))(f)) (term% f) = some .unsupportedDerivative := by decide +kernel
example : reject (term% (λ z => z)(diff(f, t))) (term% f) = some .unsupportedDerivative := by decide +kernel
-- An evolution derivative on another axis ("no derivative over that dimension").
example : reject (term% diff(f, y)) (term% f) = some .mixedDerivative := by decide +kernel
-- Python accepts a bare higher-order chain and a heat equation. This context
-- declares no velocity, so the chain is rejected (declared velocities are
-- tested in `HigherOrderIsolation.lean`); heat is multi-axis (task 029).
example : reject (term% diff(diff(f, t), t)) (term% g) = some .higherOrderDerivative := by decide +kernel
example : reject (term% 2 * diff(f, t)) (term% diff(diff(f, x), x)) =
    some .mixedDerivative := by decide +kernel

-- A lambda that reduces to a literal is not a scale; Python rejects it too.
example : reject (term% (λ w => 2)(1) * diff(f, t)) (term% f) =
    some .nonlinearDerivative := by decide +kernel

-- Python accepts, and these are not yet in Lean notation (asgard-lean 030):
-- `diff(f,t) / (2 * 3)`, `diff(f,t) / (-(2 * 3))` and `(-2 / -4) * diff(f,t)`.
-- The equal scales `rat(1,6)`, `-rat(1,6)` and `rat(1,2)` are written as literals:
example : solve (term% diff(f, t) * rat(1, 6)) (term% f) =
    some (.mul (.constant 6) (.var "f")) := by decide +kernel
-- Python keeps `diff(a,t) = diff($z,t)` with `$z` an external forcing
-- parameter; a time-varying driver is outside the autonomous adapter (031).
example : reject (term% diff(f, t)) (term% diff(a, t)) = some .unsupportedDerivative := by
  decide +kernel

-- Beyond the Python table.
example : reject (term% f) (term% 1) = some .missingDerivative := by decide +kernel
-- A derivative of a non-state name.
example : reject (term% diff(a, t)) (term% 1) = some .unsupportedDerivative := by decide +kernel
-- The atom must be the derivative this equation defines.
example : reject (term% diff(g, t)) (term% 1) = some .missingDerivative := by decide +kernel

-- Differs: `^` is repeated multiplication in Lean notation, so a literal power
-- is a literal product and `D^1 = 1*D`. Python rejects both forms.
example : solve (term% (2 ^ 3) * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 8)) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) ^ 1) (term% f) = some (.var "f") := by decide +kernel
example : reject (term% diff(f, t) ^ 2) (term% f) = some .repeatedDerivative := by decide +kernel

-- Division is by a positive numeral only; a zero denominator is a notation error.
/-- error: Division is by a positive numeral -/
#guard_msgs in
#check term% diff(f, t) / 0

-- `^ 0` would erase the written atom, so the notation refuses it; Python rejects too.
/-- error: Exponent must be a positive numeral -/
#guard_msgs in
#check term% diff(f, t) ^ 0 + diff(f, t)

-- A derivative under a binder of the same name is not the outer state's rate.
example : (term% (λ f => diff(f, t))(g)).eval (fun _ => none)
    (fun _ s => if s = "f" then some 7 else none) (fun _ => some 1) = none := by
  simp [Term.eval, Term.chain]

/-! ## Scoped beta normalization -/

-- `(λx. (λy. x + y)(1))(y)`: the free `y` is not captured by the inner binder.
example : (term% (λ x => (λ y => x + y)(1))(y)).beta =
    some (.add (.var "y") (.constant 1)) := by decide +kernel

-- An inner binder shadows an outer one: `(λx. (λx. x)(7))(3) = 7`.
example : (term% (λ x => (λ x => x)(7))(3)).beta = some (.constant 7) := by decide +kernel

-- An argument is passed by name: an unused undefined argument is not evaluated.
example : (term% (λ w => 5)(missing)).eval (fun _ => none) (fun _ _ => none) (fun _ => none) =
    some 5 := by
  simp [Term.eval]

-- Beta normalization is not total over derivatives.
example : (term% (λ w => w)(diff(f, t))).beta = none := by decide +kernel

/-! ## Declarations -/

/-- `z = (λw. w*w + a)(x + 1)`, with the exact parameter `a = 1/2`. -/
def polynomial : SourceBody := {
  inputs := [⟨"input-x", "x", .input⟩, ⟨"param-a", "a", .parameter⟩]
  assignments := assignments% { z := (λ w => w * w + a)(x + 1); }
  parameters := [⟨"param-a", 1 / 2⟩]
  observations := [⟨⟨"obs-z", "z", .output⟩, "z"⟩]
}

def polynomialModel : SourcePolynomialModel polynomial :=
  (compileSourcePolynomial polynomial).toOption.get (by decide +kernel)

example : polynomialModel.lowered.assignments = [⟨⟨"z", "z", .output⟩,
    .add (.mul (.add (.var "x") (.constant 1)) (.add (.var "x") (.constant 1))) (.var "a")⟩] := by
  decide +kernel

/-- The ORIGINAL lambda source observes `z = 19/2` at `x = 2`. -/
example : polynomial.Observes Context.empty polynomialModel.lowered.body.runtimeIds
    polynomial.observationIds (![2] : Point 1) ![19 / 2] := by
  rw [polynomialModel.correct, Selected.circuit, compileOutputs_correct]
  have terms : polynomialModel.model.outputs.expressions = (![.add (.mul (.add (.var 0)
      (.constant 1)) (.add (.var 0) (.constant 1))) (.constant (1 / 2))] : Fin 1 → Expr 1) := by
    decide +kernel
  rw [terms]
  ext i
  fin_cases i
  norm_num [Expr.eval]

private def code {α : Type} : Except Diagnostic α → Option Diagnostic
  | .error d => some d
  | .ok _ => none

-- A reference in a dropped argument or out of its binder's scope is still checked.
example : code (compileSourcePolynomial { polynomial with
    assignments := assignments% { z := (λ w => 5)(missing); } }) =
    some ⟨.unknownReference, "z", "missing"⟩ := by decide +kernel
example : code (compileSourcePolynomial { polynomial with
    assignments := assignments% { z := (λ w => w)(w); } }) =
    some ⟨.unknownReference, "z", "w"⟩ := by decide +kernel
-- A polynomial declaration has no evolution axis.
example : code (compileSourcePolynomial { polynomial with
    differentials := differentials% { dx : diff(x, t) = 1; } }) =
    some ⟨.unsupportedDerivative, "dx", "differential equation without an evolution axis"⟩ := by
  decide +kernel

/-! ## Continuous declarations -/

/-- `f = 2*D_t(g)` solved for `g` with the parameter `f = 3`, as in the Python
external-forcing fixture, and a second equation written with a lambda. -/
def forced : SourceBody := {
  inputs := [⟨"param-f", "f", .parameter⟩, ⟨"state-g", "g", .state⟩,
    ⟨"state-h", "h", .state⟩]
  assignments := []
  differentials := differentials% {
    dg : f = 2 * diff(g, t);
    dh : diff(h, t) + (λ u => u * rat(1, 2))(h) = g;
  }
  parameters := [⟨"param-f", 3⟩]
}

def forcedEvolution : Evolution := {
  states := [⟨"state-h", "dh", "initial-h"⟩, ⟨"state-g", "dg", "initial-g"⟩]
  initialPorts := [⟨"initial-g", "g0", .initial⟩, ⟨"initial-h", "h0", .initial⟩]
  initialValues := [⟨"initial-g", 2⟩, ⟨"initial-h", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 1
}

def forcedModel : SourceContinuousModel forced forcedEvolution :=
  (compileSourceContinuous forced forcedEvolution).toOption.get (by decide +kernel)

/-- State order [h, g]: `h' = g - h/2` and `g' = 3/2`. -/
example : forcedModel.model.rates.expressions =
    (![.add (.var 1) (.neg (.mul (.var 0) (.constant (1 / 2)))),
      .mul (.constant (1 / 2)) (.constant 3)] : Fin 2 → Expr 2) := by decide +kernel
example : forcedModel.model.initials = ![0, 2] := by decide +kernel

-- The linear recognizer rejects the constant forcing; the compiled
-- correspondence stands without any existence claim.
example : forcedModel.model.linear.isNone = true := by decide +kernel

private def continuous (sb : SourceBody) : Option Diagnostic :=
  code (compileSourceContinuous sb forcedEvolution)

-- Malformed: a derivative in an explicit assignment.
example : continuous { forced with assignments := assignments% { r := diff(g, t); } } =
    some ⟨.unsupportedDerivative, "r", "derivative in an explicit assignment"⟩ := by
  decide +kernel
-- Malformed: an equation for `dg` whose atom is `h`'s derivative.
example : continuous { forced with differentials := differentials% {
    dg : diff(h, t) = 1; dh : diff(h, t) = g; } } =
    some ⟨.missingDerivative, "dg", "dg"⟩ := by decide +kernel
-- Malformed: the differential port collides with an explicit assignment.
example : continuous { forced with assignments := assignments% { dg := 1; } } =
    some ⟨.duplicateId, "source", "dg"⟩ := by decide +kernel
-- Malformed: the evolution names another axis.
example : code (compileSourceContinuous forced
    { forcedEvolution with axis := ⟨"time", "s"⟩ }) =
    some ⟨.mixedDerivative, "dg", "dg"⟩ := by decide +kernel
-- Malformed: a zero scale.
example : continuous { forced with differentials := differentials% {
    dg : f = 0 * diff(g, t); dh : diff(h, t) = g; } } =
    some ⟨.zeroScale, "dg", "dg"⟩ := by decide +kernel
-- Malformed: two equations for the same state (Python: failed binding).
example : continuous { forced with differentials := differentials% {
    dg : f = 2 * diff(g, t); dg : f = 2 * diff(g, t); dh : diff(h, t) = g; } } =
    some ⟨.duplicateId, "source", "dg"⟩ := by decide +kernel
-- Malformed: a declared parameter differentiated.
example : continuous { forced with differentials := differentials% {
    dg : f = 2 * diff(g, t); dh : diff(h, t) = diff(f, t); } } =
    some ⟨.unsupportedDerivative, "dh", "dh"⟩ := by decide +kernel
-- Malformed: the derivative port named inside its own equation, where it would
-- stand for the atom a second time.
example : continuous { forced with differentials := differentials% {
    dg : f = 2 * diff(g, t); dh : 3 * diff(h, t) + dh = g; } } =
    some ⟨.repeatedDerivative, "dh", "derivative port named in its own equation"⟩ := by
  decide +kernel
-- Malformed interfaces are reported before any term is read: two states named `g`.
example : continuous { forced with inputs := forced.inputs ++ [⟨"state-g2", "g", .state⟩] } =
    some ⟨.duplicateName, "source", "g"⟩ := by decide +kernel
-- Malformed: a state without its derivative equation.
example : continuous { forced with differentials := differentials% {
    dg : f = 2 * diff(g, t); } } =
    some ⟨.unknownReference, "state-h", "dh"⟩ := by decide +kernel

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Model.Term.beta_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.beta_correct
/--
info: 'Gimle.Asgard.Polynomial.NamedExpr.subst_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms NamedExpr.subst_eval
/--
info: 'Gimle.Asgard.Model.Term.literal_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.literal_correct
/--
info: 'Gimle.Asgard.Model.Term.affine_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.affine_correct
/--
info: 'Gimle.Asgard.Model.Isolated.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Isolated.correct
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.derivative_denotes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.derivative_denotes
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.derivative_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.derivative_at
/--
info: 'Gimle.Asgard.Model.Lowered.solves_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Lowered.solves_iff
/--
info: 'Gimle.Asgard.Model.SourcePolynomialModel.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourcePolynomialModel.correct
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.solves_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.solves_iff_realizes
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.constrained_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.constrained_iff
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.observations_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.observations_correct
/--
info: 'Gimle.Asgard.Examples.DifferentialIsolation.solution_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.DifferentialIsolation.solution_solves
/--
info: 'Gimle.Asgard.Examples.DifferentialIsolation.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.DifferentialIsolation.source_unique
/--
info: 'Gimle.Asgard.Examples.DifferentialIsolation.changed_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.DifferentialIsolation.changed_scale

end Gimle.Asgard.Tests.DifferentialIsolation
