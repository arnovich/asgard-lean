import Gimle.Asgard.Model.AtomicSource
import Gimle.Asgard.Model.SourceSyntax
import Gimle.Asgard.Examples.AtomicSource

/-! Acceptance fixtures for literal-quotient scales, decimal literals, real
atomics and division by expressions (asgard-lean 030).

Each fixture restates a case from the pinned Python Asgard tests
`tests/unit/test_affine_differential_isolation.py` and
`tests/unit/test_differential_side_context.py` (gimle-asgard `fba931e`).
Python's accept/reject outcome is recorded beside each one as **same** or
**differs**; it is a regression reference, not an oracle. Lean's values are
exact. -/
namespace Gimle.Asgard.Tests.AtomicSource
open Polynomial Model

/-! ## Literals -/

-- Decimal and scientific literals are the exact rationals they write.
example : term% 1e-309 = .constant (1 / 10 ^ 309) := by decide +kernel
example : term% 1e309 = .constant (10 ^ 309) := by decide +kernel
example : term% 2.5 = .constant (5 / 2) := by decide +kernel
example : term% 0.125 * x = .mul (.constant (1 / 8)) (.var "x") := by decide +kernel
-- A quotient of literal products with a nonzero denominator is a literal.
example : (term% -2 / -4).literal = some (1 / 2) := by decide +kernel
example : (term% 1 / (2 * 3)).literal = some (1 / 6) := by decide +kernel
example : (term% 1 / (2 * 0)).literal = none := by decide +kernel
-- A numeral denominator keeps its old notation: a product with its inverse.
example : term% x / 2 = .mul (.var "x") (.constant (1 / 2)) := by decide +kernel

/-! ## Isolation of one equation

As in `Tests.DifferentialIsolation`: `f` and `g` are states with derivative ports
`df` and `dg`; equations are solved for `df`. -/

def context : Context :=
  ⟨"t", fun s => if s = "f" then some "df" else if s = "g" then some "dg" else none,
    fun _ => none, none⟩

def solve (lhs rhs : Term) : Option NamedExpr :=
  ((isolate context "df" lhs rhs).map Isolated.expr).toOption

def reject (lhs rhs : Term) : Option ErrorCode :=
  match isolate context "df" lhs rhs with
  | .error code => some code
  | .ok _ => none

def solvePartial (lhs rhs : Term) : Option PartialExpr :=
  ((isolatePartial context "df" lhs rhs).map PartialIsolated.expr).toOption

def rejectPartial (lhs rhs : Term) : Option ErrorCode :=
  match isolatePartial context "df" lhs rhs with
  | .error code => some code
  | .ok _ => none

-- Python accepts, rates 6, -6 and 2. Same: the exact rates.
example : solve (term% diff(f, t) / (2 * 3)) (term% f) =
    some (.mul (.constant 6) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) / (-(2 * 3))) (term% f) =
    some (.mul (.constant (-6)) (.var "f")) := by decide +kernel
example : solve (term% (-2 / -4) * diff(f, t)) (term% f) =
    some (.mul (.constant 2) (.var "f")) := by decide +kernel
-- The same scales with partial residuals.
example : solvePartial (term% diff(f, t) / (2 * 3)) (term% f) =
    some (.binary .mul (.constant 6) (.var "f")) := by decide +kernel
example : solvePartial (term% (-2 / -4) * diff(f, t)) (term% f) =
    some (.binary .mul (.constant 2) (.var "f")) := by decide +kernel

-- Python rejects; same: a zero literal denominator names no scale.
example : reject (term% diff(f, t) / (2 * 0)) (term% f) = some .zeroScale := by decide +kernel
-- Python rejects `(2 / 0) * diff(f,t)`; same: `2 / 0` is no literal, so no scale.
example : reject (term% (2 / (0)) * diff(f, t)) (term% f) =
    some .nonlinearDerivative := by decide +kernel
-- Python rejects `diff(f,t) / 0` and `diff(f,t) ^ ...`; the numeral `0` stays a
-- notation error (`Tests.DifferentialIsolation`).
-- Python rejects; same: the atom divided by a state is not a literal scale.
example : reject (term% diff(f, t) / f) (term% 1) = some .nonlinearDerivative := by
  decide +kernel
example : rejectPartial (term% diff(f, t) / f) (term% 1) = some .nonlinearDerivative := by
  decide +kernel
-- Python rejects; same: a derivative under an atomic or in a denominator.
example : reject (term% sin(diff(f, t))) (term% f) = some .atomicDerivative := by
  decide +kernel
example : rejectPartial (term% sin(diff(f, t))) (term% f) = some .atomicDerivative := by
  decide +kernel
example : rejectPartial (term% 1 / diff(f, t)) (term% f) = some .atomicDerivative := by
  decide +kernel
example : rejectPartial (term% diff(f, t)) (term% f / diff(g, t)) =
    some .atomicDerivative := by decide +kernel
example : rejectPartial (term% diff(f, t) ^ f) (term% 1) = some .atomicDerivative := by
  decide +kernel

-- Python rejects these extreme scales, which binary64 cannot represent or would
-- lose; differs: Lean isolates them exactly.
example : solve (term% 1e-309 * diff(f, t)) (term% f) =
    some (.mul (.constant (10 ^ 309)) (.var "f")) := by decide +kernel
example : solve (term% 1e309 * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 10 ^ 309)) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) / 1e-309) (term% f) =
    some (.mul (.constant (1 / 10 ^ 309)) (.var "f")) := by decide +kernel
example : solve (term% diff(f, t) / 1e309) (term% f) =
    some (.mul (.constant (10 ^ 309)) (.var "f")) := by decide +kernel
example : solve (term% 1e200 * (1e200 * diff(f, t))) (term% f) =
    some (.mul (.constant (1 / 10 ^ 400)) (.var "f")) := by decide +kernel
example : solve (term% 1e-200 * (1e-200 * diff(f, t))) (term% f) =
    some (.mul (.constant (10 ^ 400)) (.var "f")) := by decide +kernel
example : solve (term% (1e200 * 1e200) * diff(f, t)) (term% f) =
    some (.mul (.constant (1 / 10 ^ 400)) (.var "f")) := by decide +kernel
example : solve (term% (1e-200 * 1e-200) * diff(f, t)) (term% f) =
    some (.mul (.constant (10 ^ 400)) (.var "f")) := by decide +kernel

-- Atomic residuals are kept, whole and in order.
example : solvePartial (term% 2 * diff(f, t) + sin(f)) (term% g / f) =
    some (.binary .mul (.constant (1 / 2))
      (.binary .add (.binary .division (.var "g") (.var "f")) (.unary .neg (.unary .sin (.var "f")))))
    := by decide +kernel
-- The polynomial isolation does not normalize an atomic residual.
example : reject (term% diff(f, t)) (term% sin(f)) = some .unsupportedDerivative := by
  decide +kernel

/-! ## Declarations -/

private def code {α : Type} : Except Diagnostic α → Option Diagnostic
  | .error d => some d
  | .ok _ => none

def evolution : Evolution := Examples.AtomicSource.evolution

def exponential (differentials : List DifferentialEquation) : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩]
  assignments := []
  differentials := differentials
}

-- The literal-quotient scale also compiles through the polynomial pipeline.
example : ((compileSourceContinuous (exponential (differentials% {
    dx : diff(x, t) / (2 * 3) = x; })) evolution).toOption.map
      (·.model.rates.expressions ⟨0, by decide⟩)) =
    some (.mul (.constant 6) (.var ⟨0, by decide⟩)) := by decide +kernel

-- The polynomial compilers name a real atomic as unsupported, not as a derivative.
example : code (compileSourceContinuous (exponential (differentials% {
    dx : diff(x, t) = log(x); })) evolution) =
    some ⟨.unsupportedAtomic, "dx", "real atomic"⟩ := by decide +kernel
example : code (compileSourcePolynomial { Examples.AtomicSource.magnitude with
    assignments := assignments% { r := 1; m := x / y; } }) =
    some ⟨.unsupportedAtomic, "m", "real atomic"⟩ := by decide +kernel

private def atomic (differentials : List DifferentialEquation) : Option Diagnostic :=
  code (compileAtomicContinuous (exponential differentials) evolution)

-- Accepted by the atomic compiler.
example : atomic (differentials% { dx : diff(x, t) = exp(x) / (1 + x * x); }) = none := by
  decide +kernel
-- Python rejects `sin(diff(f,t)) = f`; same.
example : atomic (differentials% { dx : sin(diff(x, t)) = x; }) =
    some ⟨.atomicDerivative, "dx", "dx"⟩ := by decide +kernel
-- Python rejects `diff(f,t) / f = 1`; same.
example : atomic (differentials% { dx : diff(x, t) / x = 1; }) =
    some ⟨.nonlinearDerivative, "dx", "dx"⟩ := by decide +kernel
-- A derivative in an explicit assignment under an atomic, and integrals.
example : code (compileAtomicContinuous { exponential (differentials% {
    dx : diff(x, t) = x; }) with assignments := assignments% { w := exp(diff(x, t)); } }
    evolution) = some ⟨.atomicDerivative, "w", "derivative in an explicit assignment"⟩ := by
  decide +kernel
example : atomic (differentials% { dx : diff(x, t) = log(int(x, t)); }) =
    some ⟨.unsupportedIntegral, "dx", "integral in an atomic declaration"⟩ := by decide +kernel
-- An unknown function name is a notation error.
/-- error: Unknown real atomic `foo` -/
#guard_msgs in
#check term% foo(x)

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Model.Term.betaPartial_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.betaPartial_correct
/--
info: 'Gimle.Asgard.Model.PartialIsolated.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms PartialIsolated.correct
/--
info: 'Gimle.Asgard.Model.AtomicResolved.source_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AtomicResolved.source_iff
/--
info: 'Gimle.Asgard.Model.AtomicPolynomialModel.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AtomicPolynomialModel.correct
/--
info: 'Gimle.Asgard.Model.AtomicContinuousModel.solves_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AtomicContinuousModel.solves_iff
/--
info: 'Gimle.Asgard.Model.AtomicContinuousModel.solves_iff_closes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AtomicContinuousModel.solves_iff_closes
/--
info: 'Gimle.Asgard.Model.Term.affine_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.affine_correct
/--
info: 'Gimle.Asgard.Examples.AtomicSource.magnitude_range' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.AtomicSource.magnitude_range
/--
info: 'Gimle.Asgard.Examples.AtomicSource.magnitude_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.AtomicSource.magnitude_at
/--
info: 'Gimle.Asgard.Examples.AtomicSource.zeroLog_undefined' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.AtomicSource.zeroLog_undefined
/--
info: 'Gimle.Asgard.Examples.AtomicSource.growth_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.AtomicSource.growth_solution
/--
info: 'Gimle.Asgard.Examples.AtomicSource.guarded_unsolvable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.AtomicSource.guarded_unsolvable

end Gimle.Asgard.Tests.AtomicSource
