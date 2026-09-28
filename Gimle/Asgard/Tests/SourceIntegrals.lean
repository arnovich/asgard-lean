import Gimle.Asgard.Examples.SourceIntegrals

/-! Regression tests for source integrals and their inverse rewrites (task 028).

Python cases restate the integral fixtures of
`tests/unit/test_affine_differential_isolation.py`,
`tests/unit/test_differential_side_context.py` and
`tests/unit/test_inverse_rewrite_boundaries.py` (gimle-asgard `fba931e`), probed
with `compile_equation_to_circuit(..., evolve_along="t")`. Each case records the
Python outcome and whether Lean agrees ("same") or deliberately differs.

Every body has states `f` and `g`, with `g' = 0`, and the parameter `p = 3`, on
the axis `t` from `0`, with `f(0) = 2`. The nonzero initial value makes every
boundary term visible: `int(diff(f,t),t)` lowers to `f - 2`, never to `f`. -/
namespace Gimle.Asgard.Tests.SourceIntegrals
open Polynomial Model

def body (equations : List DifferentialEquation)
    (extra : List SourceAssignment := []) : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-g", "g", .state⟩, ⟨"param-p", "p", .parameter⟩]
  assignments := assignments% { dg := 0; } ++ extra
  differentials := equations
  parameters := [⟨"param-p", 3⟩]
}

def evolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-g", "dg", "initial-g"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-g", "g0", .initial⟩]
  initialValues := [⟨"initial-f", 2⟩, ⟨"initial-g", 1⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- The lowered right-hand side of `df`, when the source compiles. -/
def lowered (sb : SourceBody) : Option NamedExpr :=
  (compileSourceContinuous sb evolution).toOption.bind fun m =>
    (m.lowered.assignments.find? (·.output.id == "df")).map (·.rhs)

/-- The lowered explicit assignment `h`, when the source compiles. -/
def assigned (sb : SourceBody) : Option NamedExpr :=
  (compileSourceContinuous sb evolution).toOption.bind fun m =>
    (m.lowered.assignments.find? (·.output.id == "h")).map (·.rhs)

def rejected (sb : SourceBody) : Option Diagnostic :=
  match compileSourceContinuous sb evolution with
  | .error d => some d
  | .ok _ => none

/-! ## The listed Python fixtures -/

-- `2 * diff(diff(int(f,t),t),t) = f`. Python: accepted, `f' = 0.5 f`. Same:
-- `D_t(D_t(I_t(f)))` becomes `D_t(f)`.
example : lowered (body (differentials% { df : 2 * diff(diff(int(f, t), t), t) = f; })) =
    some (.mul (.constant (1 / 2)) (.var "f")) := by decide +kernel
-- `diff(diff(int(f,t),t),t) = f`. Python: accepted, `f' = f`. Same.
example : lowered (body (differentials% { df : diff(diff(int(f, t), t), t) = f; })) =
    some (.var "f") := by decide +kernel
-- `diff(f,t) = diff(int(f + g,t),t)`. Python: accepted, `f' = f + g`. Same.
example : lowered (body (differentials% { df : diff(f, t) = diff(int(f + g, t), t); })) =
    some (.add (.var "f") (.var "g")) := by decide +kernel
-- The `2 * f` variant, and a bound parameter in the integrand.
example : lowered (body (differentials% { df : diff(f, t) = diff(int(2 * f, t), t); })) =
    some (.mul (.constant 2) (.var "f")) := by decide +kernel
example : lowered (body (differentials% { df : diff(f, t) = diff(int(f + p, t), t); })) =
    some (.add (.var "f") (.var "p")) := by decide +kernel
-- `diff(int(2 * diff(f,t) + f,t),t) = 0`. Python: accepted, `f' = -0.5 f`. Same:
-- the integrand keeps its derivative atom and is isolated after the rewrite.
example : lowered (body (differentials% { df : diff(int(2 * diff(f, t) + f, t), t) = 0; })) =
    some (.mul (.constant (1 / 2)) (.add (.constant 0) (.neg (.var "f")))) := by decide +kernel
-- `2 * diff(f,t) = int(diff(f,t),t)`. Python: rejected ("competing derivative").
-- DIFFERS: `I_t(D_t(f))` is `f - f(0)`, a derivative-free residual, so Lean
-- accepts `f' = (f - 2)/2` with the declared initial value as boundary term.
example : lowered (body (differentials% { df : 2 * diff(f, t) = int(diff(f, t), t); })) =
    some (.mul (.constant (1 / 2)) (.add (.var "f") (.neg (.constant 2)))) := by decide +kernel
-- `diff(f,t) = diff(f,t) + int(f,t)`. Python: rejected ("both sides"). Same
-- outcome: `I_t(f)` is not an inverse pair, so it is rejected first.
example : rejected (body (differentials% { df : diff(f, t) = diff(f, t) + int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = int(diff(f,t),t)`. Python: rejected ("competing derivative").
-- DIFFERS, as above: Lean accepts `f' = f - 2`.
example : lowered (body (differentials% { df : diff(f, t) = int(diff(f, t), t); })) =
    some (.add (.var "f") (.neg (.constant 2))) := by decide +kernel

/-! ## The boundary term is kept

`I_t(D_t(f))` lowers to `f - 2`, not `f`. With the boundary term dropped, the
source would have other solutions (`Examples.SourceIntegrals.boundary_dropped`),
and `integral_derivative_ne` gives a trajectory on which `I_t(D_t(x))` and `x`
differ. -/

example : lowered (body (differentials% { df : diff(f, t) = int(diff(f, t), t); })) ≠
    lowered (body (differentials% { df : diff(f, t) = f; })) := by decide +kernel
example : lowered (body (differentials% { df : diff(f, t) = int(diff(f, t), t); })) ≠
    lowered (body (differentials% { df : diff(f, t) = f - 0; })) := by decide +kernel
-- The semantic evidence: the boundary-dropped solution does not solve the source.
example : ¬ Examples.SourceIntegrals.boundary.Solves (Examples.SourceIntegrals.evolution "x" 2)
    Examples.SourceIntegrals.droppedSolution := Examples.SourceIntegrals.boundary_dropped

/-! ## Other Python integral cases -/

-- `diff(f,t) = int(f,t)`. Python: accepted as Form-A `f = int(int(f,t),t) + f0`,
-- whose hidden integral state starts silently at zero. DIFFERS: an integral that
-- no inverse rewrite removes is rejected unless a state is declared for it, with
-- initial value `0` (`Tests.IntegralStates`).
example : rejected (body (differentials% { df : diff(f, t) = int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = int(int(diff(f,t),t),t)`. Python: rejected. Same.
example : rejected (body (differentials% { df : diff(f, t) = int(int(diff(f, t), t), t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `0 * diff(f,t) + int(f,t) = g`. Python: rejected. Same.
example : rejected (body (differentials% { df : 0 * diff(f, t) + int(f, t) = g; })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `int(diff(diff(f,t),t),t) + 0 * int(int(f,t),t) = g`. Python: rejected. Same.
example : rejected (body (differentials% {
    df : int(diff(diff(f, t), t), t) + 0 * int(int(f, t), t) = g; })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = diff(diff(int(f,t),t),t)`. Python: rejected. Same: after the
-- rewrite both sides hold `D_t(f)`.
example : rejected (body (differentials% { df : diff(f, t) = diff(diff(int(f, t), t), t); })) =
    some ⟨.competingDerivative, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = diff(int(diff(f,t),t),t)`. Python: rejected. Same.
example : rejected (body (differentials% { df : diff(f, t) = diff(int(diff(f, t), t), t); })) =
    some ⟨.competingDerivative, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = diff(int(f * f,t),t)`. Python: accepted. Same.
example : lowered (body (differentials% { df : diff(f, t) = diff(int(f * f, t), t); })) =
    some (.mul (.var "f") (.var "f")) := by decide +kernel
-- `diff(f,t) = diff(int(diff(f,t) * f,t),t)`. Python: rejected. Same: a product
-- with a derivative is not a tame integrand.
example : rejected (body (differentials% { df : diff(f, t) = diff(int(diff(f, t) * f, t), t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- Python's `g = int(diff(f,t),t)`, here the assignment `h`. Python: `f - f(0)`. Same.
example : assigned (body (differentials% { df : diff(f, t) = 0; })
    (assignments% { h := int(diff(f, t), t); })) =
    some (.add (.var "f") (.neg (.constant 2))) := by decide +kernel
-- Python's `g = diff(int(f,t),t)`, here the assignment `h`. Python: `f`. Same.
example : assigned (body (differentials% { df : diff(f, t) = 0; })
    (assignments% { h := diff(int(f, t), t); })) = some (.var "f") := by decide +kernel
-- `diff(int(f,x),y) = g`. Python: rejected. Same.
example : rejected (body (differentials% { df : diff(int(f, x), y) = g; })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = diff(int(f,x),x)`. Python: accepted, `f' = f`, cancelling the pair on
-- `x`. DIFFERS: only evolution-axis integrals have a value, so Lean rejects it.
example : rejected (body (differentials% { df : diff(f, t) = diff(int(f, x), x); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `int(diff(diff(f,t),t),t) = g`. Python: rejected. Same.
example : rejected (body (differentials% { df : int(diff(diff(f, t), t), t) = g; })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = diff(int(diff(int(f,t),t),t),t)`. Python: accepted, `f' = f`.
-- DIFFERS: rewrites apply once at atom positions, never inside an integrand (task 035).
example : rejected (body (differentials% {
    df : diff(f, t) = diff(int(diff(int(f, t), t), t), t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- `diff(f,t) = diff(int(p * diff(g,t),t),t)`. Python: accepted. DIFFERS: a
-- parameter factor on a derivative is not tame (task 035).
example : rejected (body (differentials% { df : diff(f, t) = diff(int(p * diff(g, t), t), t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- A tame integrand may hold another state's derivative; it then competes.
example : rejected (body (differentials% { df : diff(f, t) = diff(int(diff(g, t), t), t); })) =
    some ⟨.competingDerivative, "df", "df"⟩ := by decide +kernel

/-! ## Lean rejections -/

-- An integral under a lambda is never rewritten.
example : rejected (body (differentials% { df : diff(f, t) = (λ w => int(diff(w, t), t))(f); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- An integrand naming an auxiliary is not tame: its reading along the trajectory
-- is not an input's.
example : rejected (body (differentials% { df : diff(f, t) = diff(int(z, t), t); })
    (assignments% { z := f; })) = some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- A parameter has no declared initial value and no derivative port.
example : rejected (body (differentials% { df : diff(f, t) = int(diff(p, t), t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- A higher-order chain under an integral is not rewritten (task 035).
example : rejected (body (differentials% { df : diff(f, t) = int(diff(diff(f, t), t), t); })) =
    some ⟨.unsupportedIntegral, "df", "df"⟩ := by decide +kernel
-- An integral left in an explicit assignment.
example : rejected (body (differentials% { df : diff(f, t) = 0; })
    (assignments% { h := int(f, t); })) =
    some ⟨.unsupportedIntegral, "h", "integral in an explicit assignment"⟩ := by decide +kernel

/-- A polynomial declaration has no start to integrate from. -/
def polynomial : SourceBody where
  inputs := [⟨"input-x", "x", .input⟩]
  assignments := assignments% { h := diff(int(x, t), t); }

example : (match compileSourcePolynomial polynomial with
    | .error d => some d | .ok _ => none) =
    some ⟨.unsupportedIntegral, "h", "integral without an evolution axis"⟩ := by decide +kernel

/-! ## The reading of integrals -/

-- Evaluation reads integrals and derivatives of non-chains from `atoms` only; a
-- chain is still read through `rates`.
example : (term% int(f, t) + diff(f + g, t) + diff(f, t)).eval (fun _ => none)
    (fun _ _ => some 5) (fun u => if u = term% int(f, t) then some 1 else some 2) = some 8 := by
  simp [Term.eval, Term.chain]
  norm_num
-- Under a binder, an atom that mentions the binder has no value.
example : (term% (λ f => int(f, t))(g)).eval (fun _ => some 0) (fun _ _ => none)
    (fun _ => some 1) = none := by
  simp [Term.eval, Term.mentions]

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Model.primitiveFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms primitiveFrom_eq
/--
info: 'Gimle.Asgard.Model.primitiveFrom_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms primitiveFrom_eq_integral
/--
info: 'Gimle.Asgard.Model.derivFrom_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms derivFrom_eq
/--
info: 'Gimle.Asgard.Model.Term.along_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.along_integral
/--
info: 'Gimle.Asgard.Model.Term.along_derivative_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.along_derivative_integral
/--
info: 'Gimle.Asgard.Model.Term.along_integral_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.along_integral_derivative
/--
info: 'Gimle.Asgard.Model.integral_derivative_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms integral_derivative_ne
/--
info: 'Gimle.Asgard.Model.Term.cancel_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.cancel_eval
/--
info: 'Gimle.Asgard.Model.Context.cancels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Context.cancels
/--
info: 'Gimle.Asgard.Model.SourceBody.cancels_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.cancels_at
/--
info: 'Gimle.Asgard.Model.Lowered.solves_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Lowered.solves_iff
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.solves_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.solves_iff_realizes
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.classical_iff_realizes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.classical_iff_realizes
/--
info: 'Gimle.Asgard.Model.SourceBody.solves_iff_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.solves_iff_classical
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.observations_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.observations_correct
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.integral_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.integral_derivative
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.derivative_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.derivative_integral
/--
info: 'Gimle.Asgard.Examples.SourceIntegrals.decay_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.SourceIntegrals.decay_solves
/--
info: 'Gimle.Asgard.Examples.SourceIntegrals.decay_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.SourceIntegrals.decay_unique
/--
info: 'Gimle.Asgard.Examples.SourceIntegrals.boundary_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.SourceIntegrals.boundary_solves
/--
info: 'Gimle.Asgard.Examples.SourceIntegrals.boundary_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.SourceIntegrals.boundary_integral
/--
info: 'Gimle.Asgard.Examples.SourceIntegrals.boundary_dropped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.SourceIntegrals.boundary_dropped
end Gimle.Asgard.Tests.SourceIntegrals
