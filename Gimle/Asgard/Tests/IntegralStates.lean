import Gimle.Asgard.Examples.IntegralStates
import Gimle.Asgard.Examples.NestedIntegralStates

/-! Regression tests for declared integral states (tasks 034 and 036).

All Python cases were probed (none is a pinned Python test fixture) at
gimle-asgard `fba931e` with `compile_equation_to_circuit(Equation.from_string(
source), normalize=n, evolve_along="t")`, for `n` false and true. Python keeps an
integral that no inverse rewrite removes as a hidden `register(t)` state whose
initial value is silently zero. Lean keeps it only through an explicit
declaration `dF : F = int(X, t)` of a state `F` whose declared initial value is
`0`, so each Python acceptance below DIFFERS in that Lean requires the
declaration Python infers; with it, Lean lowers to the rates noted.

Every body has states `f`, `g` and `F`, with `g' = 0`, and the parameter `p = 3`,
on the axis `t` from `0`, with `f(0) = 2`, `g(0) = 1` and, unless stated,
`F(0) = 0`. The nested section uses its own states `f`, `F` and `G`. -/
namespace Gimle.Asgard.Tests.IntegralStates
open Polynomial Model

def body (equations : List DifferentialEquation) (integrals : List IntegralDeclaration)
    (extra : List SourceAssignment := []) : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-g", "g", .state⟩, ⟨"state-F", "F", .state⟩,
    ⟨"param-p", "p", .parameter⟩]
  assignments := assignments% { dg := 0; } ++ extra
  differentials := equations
  integrals := integrals
  parameters := [⟨"param-p", 3⟩]
}

def evolution (F0 : ℚ := 0) : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-g", "dg", "initial-g"⟩,
    ⟨"state-F", "dF", "initial-F"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-g", "g0", .initial⟩,
    ⟨"initial-F", "F0", .initial⟩]
  initialValues := [⟨"initial-f", 2⟩, ⟨"initial-g", 1⟩, ⟨"initial-F", F0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- The lowered right-hand side of a port, when the source compiles. -/
def lowered (sb : SourceBody) (port : String := "df") : Option NamedExpr :=
  (compileSourceContinuous sb (evolution 0)).toOption.bind fun m =>
    (m.lowered.assignments.find? (·.output.id == port)).map (·.rhs)

def rejected (sb : SourceBody) (e : Evolution := evolution 0) : Option Diagnostic :=
  match compileSourceContinuous sb e with
  | .error d => some d
  | .ok _ => none

/-! ## The task fixture: `diff(f,t) = int(f,t)` -/

-- Python: accepted as Form-A `f = int(int(f,t),t) + f0`, the inner integral a
-- hidden state starting at zero. DIFFERS: without a declaration Lean rejects it
-- (`Tests.SourceIntegrals`); declared, `I_t(f)` is `F` and the declaration
-- becomes `dF := f`, with `F(0) = 0` written in the evolution.
example : lowered (body (differentials% { df : diff(f, t) = int(f, t); })
    (integrals% { dF : F = int(f, t); })) = some (.var "F") := by decide +kernel
example : lowered (body (differentials% { df : diff(f, t) = int(f, t); })
    (integrals% { dF : F = int(f, t); })) "dF" = some (.var "f") := by decide +kernel
example : (evolution 0).initialValue "initial-F" = some 0 := by decide +kernel
-- Without the declaration, with `F` an ordinary state: rejected.
example : rejected (body (differentials% { df : diff(f, t) = int(f, t); dF : diff(F, t) = f; })
    []) = some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by decide +kernel

/-! ## Other Python integral fixtures -/

-- `diff(f,t) + int(f,t) = 0`. Python: accepted. DIFFERS as above; declared,
-- `f' = 0 - F`.
example : lowered (body (differentials% { df : diff(f, t) + int(f, t) = 0; })
    (integrals% { dF : F = int(f, t); })) = some (.add (.constant 0) (.neg (.var "F"))) := by
  decide +kernel
-- `diff(f,t) = 2 * int(f,t) + f`. Python: accepted. Declared: `f' = 2F + f`.
example : lowered (body (differentials% { df : diff(f, t) = 2 * int(f, t) + f; })
    (integrals% { dF : F = int(f, t); })) =
    some (.add (.mul (.constant 2) (.var "F")) (.var "f")) := by decide +kernel
-- `diff(f,t) = int(f,t) + int(f,t)`. Python: accepted, one hidden state per
-- occurrence. Declared once, both occurrences read `F`: `f' = F + F`.
example : lowered (body (differentials% { df : diff(f, t) = int(f, t) + int(f, t); })
    (integrals% { dF : F = int(f, t); })) = some (.add (.var "F") (.var "F")) := by decide +kernel
-- `diff(f,t) = int(2 * f,t)`. Python: accepted. Declared: `f' = F`, `F' = 2f`.
example : lowered (body (differentials% { df : diff(f, t) = int(2 * f, t); })
    (integrals% { dF : F = int(2 * f, t); })) "dF" =
    some (.mul (.constant 2) (.var "f")) := by decide +kernel
-- `diff(f,t) = int(f,t) * f`. Python: accepted. Declared: `f' = F * f`.
example : lowered (body (differentials% { df : diff(f, t) = int(f, t) * f; })
    (integrals% { dF : F = int(f, t); })) = some (.mul (.var "F") (.var "f")) := by decide +kernel
-- `diff(f,t) = int(f + 1,t)`. Python: accepted without normalization, rejected
-- with it (feedback fan-out). Declared: `f' = F`, `F' = f + 1`.
example : lowered (body (differentials% { df : diff(f, t) = int(f + 1, t); })
    (integrals% { dF : F = int(f + 1, t); })) "dF" =
    some (.add (.var "f") (.constant 1)) := by decide +kernel
-- `diff(f,t) = int(int(f,t),t)`. Python: accepted, two hidden states. DIFFERS:
-- Lean needs both integrals declared (see "Nested and non-polynomial integrands"
-- below). With only the inner one declared, the outer integral stays and is
-- rejected...
example : rejected (body (differentials% { df : diff(f, t) = int(int(f, t), t); })
    (integrals% { dF : F = int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by
  decide +kernel
-- ...and with only the outer one declared, its integrand `int(f,t)` is an
-- integral no declaration reads, so it is rejected there.
example : rejected (body (differentials% { df : diff(f, t) = int(int(f, t), t); })
    (integrals% { dF : F = int(int(f, t), t); })) =
    some ⟨.unsupportedIntegral, "dF", "integrand"⟩ := by decide +kernel

-- `diff(f,t) = diff(int(int(f,t),t),t)`. Python: accepted, `f' = int(f,t)` with
-- hidden states. DIFFERS only in the declaration: the inverse pair's integrand
-- `int(f,t)` is rewritten first, to the declared `F`, which is tame, so the pair
-- lowers to `f' = F` (task 035). Without the declaration it stays rejected.
example : lowered (body (differentials% { df : diff(f, t) = diff(int(int(f, t), t), t); })
    (integrals% { dF : F = int(f, t); })) = some (.var "F") := by decide +kernel
example : rejected (body (differentials% {
    df : diff(f, t) = diff(int(int(f, t), t), t); dF : diff(F, t) = f; })
    []) = some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by decide +kernel

/-! ## Where a declared integral is read -/

-- In an explicit assignment.
example : lowered (body (differentials% { df : diff(f, t) = int(f, t); })
    (integrals% { dF : F = int(f, t); }) (assignments% { h := int(f, t) + 1; })) "h" =
    some (.add (.var "F") (.constant 1)) := by decide +kernel
-- An inverse rewrite still applies first: `D_t(I_t(f))` is `f`, not `D_t(F)`.
example : lowered (body (differentials% { df : diff(f, t) = diff(int(f, t), t); })
    (integrals% { dF : F = int(f, t); })) = some (.var "f") := by decide +kernel
-- Beside a declared velocity: `f'' = I_t(f)` lowers to `v' = F`, `f' = v`, `F' = f`.
def withVelocity : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-v", "v", .state⟩, ⟨"state-F", "F", .state⟩]
  assignments := []
  differentials := differentials% { dv : diff(diff(f, t), t) = int(f, t); }
  velocities := velocities% { df : diff(f, t) = v; }
  integrals := integrals% { dF : F = int(f, t); }
}

def velocityEvolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-v", "dv", "initial-v"⟩,
    ⟨"state-F", "dF", "initial-F"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-v", "v0", .initial⟩,
    ⟨"initial-F", "F0", .initial⟩]
  initialValues := [⟨"initial-f", 1⟩, ⟨"initial-v", 0⟩, ⟨"initial-F", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

example : ((compileSourceContinuous withVelocity velocityEvolution).toOption.map
    (·.lowered.assignments.map (·.rhs))) = some [.var "F", .var "v", .var "f"] := by
  decide +kernel

-- An integrand naming its own state: `F' = F`, `F(0) = 0`, so `F = 0 = I_t(F)`.
example : lowered (body (differentials% { df : diff(f, t) = int(F, t); })
    (integrals% { dF : F = int(F, t); })) "dF" = some (.var "F") := by decide +kernel
-- The inverse rewrite `I_t(D_t(F))` on an integral state keeps its boundary term `0`.
example : lowered (body (differentials% { df : diff(f, t) = int(diff(F, t), t); })
    (integrals% { dF : F = int(f, t); })) =
    some (.add (.var "F") (.neg (.constant 0))) := by decide +kernel
-- An integral state as another state's declared velocity.
def asVelocity : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-g", "g", .state⟩, ⟨"state-F", "F", .state⟩]
  assignments := assignments% { dg := 0; }
  velocities := velocities% { df : diff(f, t) = F; }
  integrals := integrals% { dF : F = int(g, t); }
}
example : ((compileSourceContinuous asVelocity (evolution 0)).toOption.map
    (·.lowered.assignments.map (·.rhs))) = some [.constant 0, .var "F", .var "g"] := by
  decide +kernel

/-! ## Rejections -/

-- A declared initial value other than `0`.
example : rejected (body (differentials% { df : diff(f, t) = int(f, t); })
    (integrals% { dF : F = int(f, t); })) (evolution 2) =
    some ⟨.nonzeroInitial, "dF", "F"⟩ := by decide +kernel
-- A missing initial value: `F` without a `StateBinding`, so without an initial
-- port or value, fails interface validation before any term is read.
def unbound : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-g", "dg", "initial-g"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-g", "g0", .initial⟩]
  initialValues := [⟨"initial-f", 2⟩, ⟨"initial-g", 1⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}
example : rejected (body (differentials% { df : diff(f, t) = int(f, t); })
    (integrals% { dF : F = int(f, t); })) unbound =
    some ⟨.missingBinding, "states", "state-F"⟩ := by decide +kernel
-- A binding whose initial port has no value.
def valueless : Evolution := { evolution 0 with
  initialValues := [⟨"initial-f", 2⟩, ⟨"initial-g", 1⟩] }
example : rejected (body (differentials% { df : diff(f, t) = int(f, t); })
    (integrals% { dF : F = int(f, t); })) valueless =
    some ⟨.missingBinding, "initialValues", "initial-F"⟩ := by decide +kernel
-- An undeclared integral beside a declared one.
example : rejected (body (differentials% { df : diff(f, t) = int(g, t); })
    (integrals% { dF : F = int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by
  decide +kernel
-- Matching is syntactic: `int(1 * f, t)` is not the declared `int(f, t)`. Python:
-- accepted (probed). Kept rejected: a semantic match needs a proof that the two
-- integrands read the same at every time, which nothing here decides.
example : rejected (body (differentials% { df : diff(f, t) = int(1 * f, t); })
    (integrals% { dF : F = int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by
  decide +kernel
-- An integral under a lambda is never read.
example : rejected (body (differentials% { df : diff(f, t) = (λ w => int(w, t))(f); })
    (integrals% { dF : F = int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by
  decide +kernel
-- An integral in a lambda argument, in a differential or an explicit assignment.
example : rejected (body (differentials% { df : diff(f, t) = (λ w => w)(int(f, t)); })
    (integrals% { dF : F = int(f, t); })) =
    some ⟨.unsupportedIntegral, "df", "no inverse rewrite"⟩ := by
  decide +kernel
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(f, t); }) (assignments% { h := (λ w => int(w, t))(f); })) =
    some ⟨.unsupportedIntegral, "h", "no inverse rewrite"⟩ := by decide +kernel
-- One state declared twice, or with both an integral declaration and a
-- differential: its derivative port is defined twice.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(f, t); dF : F = int(g, t); })) =
    some ⟨.duplicateId, "source", "dF"⟩ := by decide +kernel
example : rejected (body (differentials% { df : diff(f, t) = F; dF : diff(F, t) = g; })
    (integrals% { dF : F = int(f, t); })) = some ⟨.duplicateId, "source", "dF"⟩ := by
  decide +kernel
-- A declaration on another axis.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(f, x); })) = some ⟨.unsupportedIntegral, "dF", "axis"⟩ := by
  decide +kernel
-- An integrand naming an auxiliary: the trajectory reading of `Solves` names only
-- states and bound parameters, so the integral would have no value in the source
-- while the lowered state would.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(z, t); }) (assignments% { z := f; })) =
    some ⟨.unsupportedIntegral, "dF", "integrand"⟩ := by decide +kernel
-- The derivative port named in its own declaration.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(dF, t); })) =
    some ⟨.repeatedDerivative, "dF", "derivative port named in its own equation"⟩ := by
  decide +kernel
-- A declared integral state that is a parameter, or not a source name.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : p = int(f, t); })) = some ⟨.unsupportedRole, "dF", "p"⟩ := by
  decide +kernel
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : z = int(f, t); }) (assignments% { z := f; })) =
    some ⟨.unsupportedRole, "dF", "z"⟩ := by decide +kernel
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : H = int(f, t); })) = some ⟨.unknownReference, "dF", "H"⟩ := by
  decide +kernel
-- A port that is not the state's derivative port: `dg` belongs to `g`.
def wrongPort : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-g", "g", .state⟩, ⟨"state-F", "F", .state⟩]
  assignments := []
  differentials := differentials% { df : diff(f, t) = 0; dF : diff(F, t) = 0; }
  integrals := integrals% { dg : F = int(f, t); }
}
example : rejected wrongPort = some ⟨.missingDerivative, "dg", "dg"⟩ := by decide +kernel
-- Two declarations of one integral: the second is never read.
def duplicate : SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-F", "F", .state⟩, ⟨"state-G", "G", .state⟩]
  assignments := []
  differentials := differentials% { df : diff(f, t) = int(f, t); }
  integrals := integrals% { dF : F = int(f, t); dG : G = int(f, t); }
}
def duplicateEvolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-F", "dF", "initial-F"⟩,
    ⟨"state-G", "dG", "initial-G"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-F", "F0", .initial⟩,
    ⟨"initial-G", "G0", .initial⟩]
  initialValues := [⟨"initial-f", 2⟩, ⟨"initial-F", 0⟩, ⟨"initial-G", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}
example : rejected duplicate duplicateEvolution = some ⟨.duplicateId, "dG", "G"⟩ := by
  decide +kernel
-- A polynomial declaration has no start to integrate from.
def polynomial : SourceBody where
  inputs := [⟨"input-x", "x", .input⟩]
  assignments := assignments% { h := x; }
  integrals := integrals% { dF : F = int(x, t); }

example : (match compileSourcePolynomial polynomial with
    | .error d => some d | .ok _ => none) =
    some ⟨.unsupportedIntegral, "dF", "integral without an evolution axis"⟩ := by decide +kernel

/-! ## Nested and non-polynomial integrands (task 036)

A declared integrand need not be a polynomial. It must be pointwise
(`Term.pointwise`): its reading at one time, with atoms read along the signal,
is its reading along the signal. Nested integrals are read through their own
declarations, so `dG : G = int(int(f,t),t)` with `dF : F = int(f,t)` lowers to
`dG := F`; first-order atoms are read as derivative ports, `D_t(g)` as `dg`. -/

/-- States `f`, `F` and `G`, with `f(0) = 2` and `F(0) = G(0) = 0`. -/
def nested (equations : List DifferentialEquation) (integrals : List IntegralDeclaration) :
    SourceBody := {
  inputs := [⟨"state-f", "f", .state⟩, ⟨"state-F", "F", .state⟩, ⟨"state-G", "G", .state⟩]
  assignments := []
  differentials := equations
  integrals := integrals
}

def nestedEvolution : Evolution := {
  states := [⟨"state-f", "df", "initial-f"⟩, ⟨"state-F", "dF", "initial-F"⟩,
    ⟨"state-G", "dG", "initial-G"⟩]
  initialPorts := [⟨"initial-f", "f0", .initial⟩, ⟨"initial-F", "F0", .initial⟩,
    ⟨"initial-G", "G0", .initial⟩]
  initialValues := [⟨"initial-f", 2⟩, ⟨"initial-F", 0⟩, ⟨"initial-G", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def nestedLowered (sb : SourceBody) : Option (List NamedExpr) :=
  (compileSourceContinuous sb nestedEvolution).toOption.map
    (·.lowered.assignments.map (·.rhs))

-- The task fixture. Python: accepted with two hidden zero-start states (probed).
-- DIFFERS only in that Lean requires both declarations;
-- with them it lowers to `df := G`, `dF := f`, `dG := F`, in either order.
example : nestedLowered (nested (differentials% { df : diff(f, t) = int(int(f, t), t); })
    (integrals% { dF : F = int(f, t); dG : G = int(int(f, t), t); })) =
    some [.var "G", .var "f", .var "F"] := by decide +kernel
example : nestedLowered (nested (differentials% { df : diff(f, t) = int(int(f, t), t); })
    (integrals% { dG : G = int(int(f, t), t); dF : F = int(f, t); })) =
    some [.var "G", .var "F", .var "f"] := by decide +kernel
-- The compiled field over state order [f, F, G]: `f' = G`, `F' = f`, `G' = F`.
example : ((compileSourceContinuous
    (nested (differentials% { df : diff(f, t) = int(int(f, t), t); })
    (integrals% { dF : F = int(f, t); dG : G = int(int(f, t), t); })) nestedEvolution).map
    (·.model.rates.expressions)).toOption =
    some (![.var 2, .var 0, .var 1] : Fin 3 → Expr 3) := by decide +kernel
-- A nested integral in an explicit assignment, read through the outer declaration.
example : nestedLowered { nested (differentials% { df : diff(f, t) = G; })
    (integrals% { dF : F = int(f, t); dG : G = int(int(f, t), t); }) with
    assignments := assignments% { h := int(int(f, t), t) + int(f, t); } } =
    some [.add (.var "G") (.var "F"), .var "G", .var "f", .var "F"] := by decide +kernel

-- A first-order atom in a declared integrand, read as its derivative port.
-- Python: `diff(f,t) = int(diff(g,t) + f, t)` accepted (probed). DIFFERS only in
-- the declaration.
example : lowered (body (differentials% { df : diff(f, t) = int(diff(g, t) + f, t); })
    (integrals% { dF : F = int(diff(g, t) + f, t); })) = some (.var "F") := by decide +kernel
example : lowered (body (differentials% { df : diff(f, t) = int(diff(g, t) + f, t); })
    (integrals% { dF : F = int(diff(g, t) + f, t); })) "dF" =
    some (.add (.var "dg") (.var "f")) := by decide +kernel
-- A declared `int(diff(g,t),t)` is `dF := dg`; written in an equation, the inverse
-- rewrite `g - g0` applies first. Python: `diff(f,t) = int(diff(g,t), t)` accepted
-- (probed).
example : lowered (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(g, t), t); })) "dF" = some (.var "dg") := by decide +kernel
-- An applied lambda that beta-normalizes to a polynomial in inputs. Python:
-- `diff(f,t) = int(apply(λw.w * w, f), t)` accepted (probed).
example : lowered (body (differentials% { df : diff(f, t) = int((λ w => w * w)(f), t); })
    (integrals% { dF : F = int((λ w => w * w)(f), t); })) = some (.var "F") := by decide +kernel
example : lowered (body (differentials% { df : diff(f, t) = int((λ w => w * w)(f), t); })
    (integrals% { dF : F = int((λ w => w * w)(f), t); })) "dF" =
    some (.mul (.var "f") (.var "f")) := by decide +kernel
example : lowered (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int((λ w => w)(f), t); })) "dF" = some (.var "f") := by decide +kernel
-- An inverse pair inside a declared integrand is rewritten: `D_t(I_t(f))` is `f`.
example : lowered (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(int(f, t), t) + p, t); })) "dF" =
    some (.add (.var "f") (.var "p")) := by decide +kernel

-- Still rejected. Only the outer integral declared: its integrand holds an
-- integral no declaration reads, even with `F' = f` written as a differential.
example : rejected (nested (differentials% {
    df : diff(f, t) = int(int(f, t), t); dF : diff(F, t) = f; })
    (integrals% { dG : G = int(int(f, t), t); })) nestedEvolution =
    some ⟨.unsupportedIntegral, "dG", "integrand"⟩ := by decide +kernel
-- A lambda with an atom inside is not pointwise. Python: rejected (probed).
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int((λ w => diff(w, t))(f), t); })) =
    some ⟨.unsupportedIntegral, "dF", "integrand"⟩ := by decide +kernel
-- A higher-order chain is read through velocities that only a solution ties to
-- the iterated derivative, so it is not pointwise. Python rejects
-- `diff(f,t) = int(diff(diff(f,t),t),t)` as competing derivatives, but accepts
-- `diff(f,t) = int(diff(diff(g,t),t),t)` (probed): DIFFERS.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(diff(f, t), t), t); })) =
    some ⟨.unsupportedIntegral, "dF", "integrand"⟩ := by decide +kernel
-- A derivative of a non-chain is pointwise, but no rewrite removes it. Python
-- rejects `diff(f,t) = int(diff(f + g,t),t)` as competing derivatives, but accepts
-- `diff(f,t) = int(diff(g + h,t),t)` (probed): DIFFERS.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(f + g, t), t); })) =
    some ⟨.unsupportedDerivative, "dF", "integrand"⟩ := by decide +kernel
-- A derivative of a parameter is not a first-order state atom. Python rejects
-- `int(diff(p,t),t)` as well (`Tests.SourceIntegrals`).
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(p, t), t); })) =
    some ⟨.unsupportedIntegral, "dF", "integrand"⟩ := by decide +kernel
-- The state's own atom in its integrand reads its own port.
example : rejected (body (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(F, t) + f, t); })) =
    some ⟨.repeatedDerivative, "dF", "derivative port named in its own equation"⟩ := by
  decide +kernel

-- Three levels, in either order: `df := H`, `dF := f`, `dG := F`, `dH := G`.
def threeLevels (integrals : List IntegralDeclaration) : SourceBody :=
  { nested (differentials% { df : diff(f, t) = int(int(int(f, t), t), t); }) integrals with
    inputs := [⟨"state-f", "f", .state⟩, ⟨"state-F", "F", .state⟩, ⟨"state-G", "G", .state⟩,
      ⟨"state-H", "H", .state⟩] }
def threeEvolution : Evolution := { nestedEvolution with
  states := nestedEvolution.states ++ [⟨"state-H", "dH", "initial-H"⟩]
  initialPorts := nestedEvolution.initialPorts ++ [⟨"initial-H", "H0", .initial⟩]
  initialValues := nestedEvolution.initialValues ++ [⟨"initial-H", 0⟩] }
example : ((compileSourceContinuous (threeLevels (integrals% { dF : F = int(f, t);
    dG : G = int(int(f, t), t); dH : H = int(int(int(f, t), t), t); })) threeEvolution).map
    (·.lowered.assignments.map (·.rhs))).toOption =
    some [.var "H", .var "f", .var "F", .var "G"] := by decide +kernel
example : ((compileSourceContinuous (threeLevels (integrals% {
    dH : H = int(int(int(f, t), t), t); dG : G = int(int(f, t), t); dF : F = int(f, t); }))
    threeEvolution).map (·.lowered.assignments.map (·.rhs))).toOption =
    some [.var "H", .var "G", .var "F", .var "f"] := by decide +kernel
-- A nested integral beside a declared velocity: `f'' = I_t(I_t(f))` with `f' = F`
-- lowers to `dF := H`, `df := F`, `dG := f`, `dH := G`.
example : ((compileSourceContinuous { threeLevels (integrals% { dG : G = int(f, t);
    dH : H = int(int(f, t), t); }) with
    differentials := differentials% { dF : diff(diff(f, t), t) = int(int(f, t), t); }
    velocities := velocities% { df : diff(f, t) = F; } } threeEvolution).map
    (·.lowered.assignments.map (·.rhs))).toOption =
    some [.var "H", .var "F", .var "f", .var "G"] := by decide +kernel
-- Declarations that read each other: `F = I_t(I_t(F))` through `G = I_t(F)`. Both
-- start at `0`, so `F = G = 0` is the solution the lowered `F' = G`, `G' = F` has.
example : nestedLowered (nested (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(int(F, t), t); dG : G = int(F, t); })) =
    some [.var "F", .var "G", .var "F"] := by decide +kernel
-- Ports that read each other form an auxiliary cycle, which the compiler rejects.
example : rejected (nested (differentials% { df : diff(f, t) = F; })
    (integrals% { dF : F = int(diff(G, t), t); dG : G = int(diff(F, t), t); }))
    nestedEvolution = some ⟨.cyclicDependency, "dF", "dF"⟩ := by decide +kernel
-- A declaration's own checks come first, whatever the order: `F(0) = 1` is
-- reported at `F`, not at `G`, whose integrand reads it.
example : rejected (nested (differentials% { df : diff(f, t) = int(int(f, t), t); })
    (integrals% { dG : G = int(int(f, t), t); dF : F = int(f, t); }))
    { nestedEvolution with initialValues := [⟨"initial-f", 2⟩, ⟨"initial-F", 1⟩,
      ⟨"initial-G", 0⟩] } = some ⟨.nonzeroInitial, "dF", "F"⟩ := by decide +kernel

/-! ## The reading of a declared integral state

`primitiveFrom_iff`: a function is the integral from the start at every time
exactly when it vanishes at the start and is an antiderivative. So the
declaration's equation `D_t(F) = X`, with `F(0) = 0`, is `F = I_t(X)`. -/

example : (∀ t ∈ Set.Ici (0 : ℝ), primitiveFrom 0 (fun s => some (2 * s)) t = some (t ^ 2)) := by
  refine primitiveFrom_iff.mpr ⟨by norm_num, fun s _ => ⟨2 * s, rfl, ?_⟩⟩
  exact ((hasDerivAt_pow 2 s).hasDerivWithinAt).congr_deriv (by ring)
-- A nonzero start is not the integral: `1 + t²` is not `I_t(2t)` at `t = 0`.
example : ¬ (∀ t ∈ Set.Ici (0 : ℝ),
    primitiveFrom 0 (fun s => some (2 * s)) t = some (1 + t ^ 2)) := by
  intro h
  have := (primitiveFrom_iff.mp h).1
  norm_num at this

-- The worked example's integral reads its state in every solution.
example (state : Dynamics.Signal 2)
    (h : Examples.IntegralStates.body.Solves (Examples.IntegralStates.evolution 1 0) state)
    (t : ℝ) (ht : 0 ≤ t) :
    Examples.IntegralStates.body.atoms (Examples.IntegralStates.evolution 1 0) state t
      (term% int(f, t)) = some (state t 1) :=
  Examples.IntegralStates.integral_reads_state state h t ht

-- The nested worked example: both integrals read their states in every solution.
example (state : Dynamics.Signal 3)
    (h : Examples.NestedIntegralStates.body.Solves Examples.NestedIntegralStates.evolution state)
    (t : ℝ) (ht : 0 ≤ t) :
    Examples.NestedIntegralStates.body.atoms Examples.NestedIntegralStates.evolution state t
      (term% int(int(f, t), t)) = some (state t 2) :=
  (Examples.NestedIntegralStates.integrals_read_states state h t ht).2

/-! ## Axiom audits -/

/--
info: 'Gimle.Asgard.Model.primitiveFrom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms primitiveFrom_iff
/--
info: 'Gimle.Asgard.Model.Context.cancels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Context.cancels
/--
info: 'Gimle.Asgard.Model.SourceBody.regular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.regular
/--
info: 'Gimle.Asgard.Model.SourceBody.cancels_at' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.cancels_at
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.integralsAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.integralsAlong
/--
info: 'Gimle.Asgard.Model.Lowered.integralsAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Lowered.integralsAlong
/--
info: 'Gimle.Asgard.Model.SourceBody.Solves.integral_state' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.Solves.integral_state
/--
info: 'Gimle.Asgard.Model.SourceContinuousModel.integral_states' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceContinuousModel.integral_states
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
info: 'Gimle.Asgard.Examples.IntegralStates.solution_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.IntegralStates.solution_solves
/--
info: 'Gimle.Asgard.Examples.IntegralStates.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.IntegralStates.source_unique
/--
info: 'Gimle.Asgard.Examples.IntegralStates.integral_reads_state' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.IntegralStates.integral_reads_state
/--
info: 'Gimle.Asgard.Examples.IntegralStates.integral_is_interval_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.IntegralStates.integral_is_interval_integral
/--
info: 'Gimle.Asgard.Model.Term.pointwise_agrees' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.pointwise_agrees
/--
info: 'Gimle.Asgard.Model.Term.beta_along' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.beta_along
/--
info: 'Gimle.Asgard.Model.Term.cancel_eval_upTo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.cancel_eval_upTo
/--
info: 'Gimle.Asgard.Model.Context.cancelsUpTo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Context.cancelsUpTo
/--
info: 'Gimle.Asgard.Model.Term.cancelAtom_below' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.cancelAtom_below
/--
info: 'Gimle.Asgard.Model.Term.readPorts_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Term.readPorts_eval
/--
info: 'Gimle.Asgard.Model.SourceBody.regular_below' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms SourceBody.regular_below
/--
info: 'Gimle.Asgard.Examples.NestedIntegralStates.solution_solves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.NestedIntegralStates.solution_solves
/--
info: 'Gimle.Asgard.Examples.NestedIntegralStates.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.NestedIntegralStates.source_unique
/--
info: 'Gimle.Asgard.Examples.NestedIntegralStates.integrals_read_states' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.NestedIntegralStates.integrals_read_states
/--
info: 'Gimle.Asgard.Examples.NestedIntegralStates.nested_integral_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.NestedIntegralStates.nested_integral_value
end Gimle.Asgard.Tests.IntegralStates
