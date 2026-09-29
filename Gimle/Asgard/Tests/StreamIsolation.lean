import Gimle.Asgard.Examples.HeatIsolation

/-! Coverage for isolating a scaled derivative in stream equations.

Pinned here: the declared heat equation is obtained from its source form, and
the Python heat fixture's four forms isolate as recorded in
`Examples/HeatIsolation.lean`; exact literal scales in every written form; and
each rejected form with its diagnostic, including the Python fixtures that
stay rejected: a mixed derivative on the isolated side, the unknown's own
derivative on the right-hand side, and a scaled second time derivative. A
stream declaration that states the unknown's derivative on its right-hand side
is refused by `Declaration.validate` as well. -/

namespace Gimle.Asgard.Tests.StreamIsolation

open Gimle.Asgard.Streams
open Gimle.Asgard.Examples.HeatIsolation

/-- The diagnostic isolation reports, if any. -/
def reject (se : SourceEquation) : Option Model.Diagnostic :=
  match se.isolate with
  | .ok _ => none
  | .error error => some error

/-- The isolated right-hand side, if any. -/
def isolated (se : SourceEquation) : Option NamedExpr :=
  match se.isolate with
  | .ok i => some i.equation.rhs
  | .error _ => none

/-! ### Accepted forms -/

/-- `D_t u` alone: the other side unchanged. -/
example : isolated (sourceEquation% (u, t, u0) diff(u, t) = diff(diff(u, x), x)) = some uxx := by
  decide +kernel

/-- `diff(u,t) / 2`, `-2 * diff(u,t)` and `diff(u,t) * -2`: exact scales. -/
example : isolated (sourceEquation% (u, t, u0) diff(u, t) / 2 = diff(diff(u, x), x)) =
    some (.binary .product (.constant 2) uxx) := by decide +kernel
example : isolated (sourceEquation% (u, t, u0) -2 * diff(u, t) = diff(diff(u, x), x)) =
    some (.binary .product (.constant (-1 / 2)) uxx) := by decide +kernel
example : isolated (sourceEquation% (u, t, u0) diff(u, t) * -2 = diff(diff(u, x), x)) =
    some (.binary .product (.constant (-1 / 2)) uxx) := by decide +kernel

/-- A remainder is kept in source order and subtracted: `D_t u + u = D_x² u`
gives `D_t u = D_x² u + -1 · u`. -/
example : isolated (sourceEquation% (u, t, u0) diff(u, t) + u = diff(diff(u, x), x)) =
    some (.binary .add uxx (.binary .product (.constant (-1)) (.input "u"))) := by
  decide +kernel

/-- The unknown itself, other inputs and their derivatives on any axis may stay
on the isolated side: `D_t u = u · D_x v + D_t v`. -/
example : (reject (sourceEquation% (u, t, u0)
    diff(u, t) = u * diff(v, x) + diff(v, t))).isNone := by decide +kernel

/-! ### Rejected forms -/

/-- Python `2 * diff(diff(f,x),t) = f`: `D_t(D_x u)` is mixed. -/
example : reject (sourceEquation% (u, t, u0) 2 * diff(diff(u, x), t) = u) =
    some ⟨.mixedDerivative, "u", "t"⟩ := by decide +kernel
/-- `D_x(D_t u)` is mixed too, on either side. -/
example : reject (sourceEquation% (u, t, u0) diff(diff(u, t), x) = u) =
    some ⟨.mixedDerivative, "u", "t"⟩ := by decide +kernel
example : reject (sourceEquation% (u, t, u0) 2 * diff(u, t) = diff(diff(u, t), x)) =
    some ⟨.mixedDerivative, "u", "t"⟩ := by decide +kernel
example : reject (sourceEquation% (u, t, u0) diff(u, t) + diff(diff(u, t), x) = u) =
    some ⟨.mixedDerivative, "u", "t"⟩ := by decide +kernel
/-- A second time derivative on the other side is reported as such. -/
example : reject (sourceEquation% (u, t, u0) diff(u, t) = diff(diff(u, t), t)) =
    some ⟨.higherOrderDerivative, "u", "t"⟩ := by decide +kernel

/-- Python `2 * diff(f,t) = diff(f,t) + f`: the unknown's derivative on both sides. -/
example : reject (sourceEquation% (u, t, u0) 2 * diff(u, t) = diff(u, t) + u) =
    some ⟨.competingDerivative, "u", "t"⟩ := by decide +kernel
/-- Python `diff(f,t) + diff(f,t) = f`. -/
example : reject (sourceEquation% (u, t, u0) diff(u, t) + diff(u, t) = u) =
    some ⟨.repeatedDerivative, "u", "t"⟩ := by decide +kernel
/-- Python `2 * diff(diff(u,t),t) = diff(diff(u,x),x)`: a second time derivative. -/
example : reject (sourceEquation% (u, t, u0) 2 * diff(diff(u, t), t) = diff(diff(u, x), x)) =
    some ⟨.higherOrderDerivative, "u", "t"⟩ := by decide +kernel
/-- No time derivative of the unknown at all. -/
example : reject (sourceEquation% (u, t, u0) diff(u, x) = diff(diff(u, x), x)) =
    some ⟨.missingDerivative, "u", "t"⟩ := by decide +kernel
/-- Python `0 * diff(f,t) = f`. -/
example : reject (sourceEquation% (u, t, u0) 0 * diff(u, t) = u) =
    some ⟨.zeroScale, "u", "t"⟩ := by decide +kernel
/-- Python `f * diff(f,t) = 1` and `diff(f,t) * diff(f,t) = f`. -/
example : reject (sourceEquation% (u, t, u0) u * diff(u, t) = 1) =
    some ⟨.nonlinearDerivative, "u", "t"⟩ := by decide +kernel
example : reject (sourceEquation% (u, t, u0) diff(u, t) * diff(u, t) = u) =
    some ⟨.nonlinearDerivative, "u", "t"⟩ := by decide +kernel
/-- Python `2 * (diff(f,t) + f) = 1`: a scale around a sum. -/
example : reject (sourceEquation% (u, t, u0) 2 * (diff(u, t) + u) = 1) =
    some ⟨.unsupportedDerivative, "u", "t"⟩ := by decide +kernel
/-- The time derivative of another operand that reads the unknown. -/
example : reject (sourceEquation% (u, t, u0) diff(u * u, t) = u) =
    some ⟨.unsupportedDerivative, "u", "t"⟩ := by decide +kernel
/-- Integrals and lambda applications have no stream reading; the side is named. -/
example : reject (sourceEquation% (u, t, u0) diff(u, t) = int(u, x)) =
    some ⟨.unsupportedIntegral, "u", "rhs"⟩ := by decide +kernel
example : reject (sourceEquation% (u, t, u0) (λ w => diff(w, t))(u) = u) =
    some ⟨.unsupportedApplication, "u", "lhs"⟩ := by decide +kernel
/-- Real atomics have no formal-stream reading either. -/
example : reject (sourceEquation% (u, t, u0) diff(u, t) = sqrt(u)) =
    some ⟨.unsupportedAtomic, "u", "rhs"⟩ := by decide +kernel

/-! ### Declarations -/

/-- Isolation succeeds, and validation of the isolated declaration then names
the undeclared input. -/
def undeclared : SourceDeclaration :=
  fixture (sourceEquation% (u, t, u0) 2 * diff(u, t) = diff(diff(v, x), x))

example : (match undeclared.compile with
    | .ok _ => none
    | .error error => some error) = some ⟨.unknownReference, "u", "v"⟩ := by decide +kernel

/-- The declared fixture compiles. -/
example : (match (fixture plain).compile with
    | .ok _ => true
    | .error _ => false) = true := by decide +kernel

/-- A declared stream equation with the unknown's own derivative on its
right-hand side is refused, as its isolated form would be. -/
def selfReferent (rhs : NamedExpr) : Declaration := isolatedFixture ⟨"u", "t", "u0", rhs⟩

example : (selfReferent (.binary .add (.unary (.derivative "t") (.input "u"))
    (.constant 1))).validate = .error ⟨.competingDerivative, "u", "t"⟩ := by decide
example : (selfReferent (.unary (.derivative "x") (.unary (.derivative "t") (.input "u")))).validate =
    .error ⟨.mixedDerivative, "u", "t"⟩ := by decide
example : (selfReferent (.unary (.derivative "t") (.unary (.derivative "t") (.input "u")))).validate =
    .error ⟨.higherOrderDerivative, "u", "t"⟩ := by decide
/-- The boundary's own time derivative is data, not the unknown's. -/
example : (selfReferent (.unary (.derivative "t") (.input "u0"))).validate = .ok () := by decide

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Asgard.Streams.NamedExpr.affine_means'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms NamedExpr.affine_means
/--
info: 'Gimle.Asgard.Streams.SourceEquation.Isolated.solves_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceEquation.Isolated.solves_iff
/--
info: 'Gimle.Asgard.Streams.SourceEquation.Isolated.explicit_rhs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceEquation.Isolated.explicit_rhs
/--
info: 'Gimle.Asgard.Streams.SourceDeclaration.solves_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceDeclaration.solves_iff
/--
info: 'Gimle.Asgard.Examples.HeatIsolation.isolates'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms isolates
/--
info: 'Gimle.Asgard.Examples.HeatIsolation.solutions'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms solutions
/--
info: 'Gimle.Asgard.Examples.HeatIsolation.fixture_solutions'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms fixture_solutions

end Gimle.Asgard.Tests.StreamIsolation
