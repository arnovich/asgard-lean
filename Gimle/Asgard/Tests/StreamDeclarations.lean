import Gimle.Asgard.Streams.Lowering
import Gimle.Asgard.Examples.DeclaredHeat

/-! Coverage for stream declarations.

Pinned here: the basis is part of a declaration's identity; the declared heat
equation compiles, resolves and lowers as the hand-built circuit does; a series
substitution is accepted only where its constant coefficient is established,
and refused with a diagnostic even when its value is discarded; repeated axis
IDs are refused by validation and at resolution; and the diagnostics for
references, roles and bindings. -/

namespace Gimle.Asgard.Tests.StreamDeclarations

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Lowering
open Gimle.Asgard.Examples.DeclaredHeat

/-- The diagnostic `compile` refuses a declaration with, if any. -/
def refusal (s : Declaration) : Option Model.Diagnostic :=
  match s.compile with
  | .ok _ => none
  | .error error => some error

/-- The declared heat equation with a different right-hand side. -/
def withRhs (rhs : NamedExpr) : Declaration :=
  { declaration with equations := [⟨"u", "time", "boundary", rhs⟩] }

/-! ### The declared heat equation -/

example : refusal declaration = none := by decide

/-- The basis is part of the identity: the EGF declaration is another value,
and it resolves to an EGF expression. -/
example : declaration ≠ { declaration with basis := .egf } := by decide
example : ({ declaration with basis := .egf } : Declaration).resolve.map (·.map (·.rhs)) =
    some [(.unary (.derivative 1) (.unary (.derivative 1) (.input 0)) : Expr .egf 2 3)] := by
  decide

/-- Resolution follows the declared order: `time` is axis `0` in `declaration`
and axis `1` in `swapped`. -/
example : declaration.resolve.map (·.map (·.along.val)) = some [0] := by decide
example : swapped.resolve.map (·.map (·.along.val)) = some [1] := by decide

/-- Observe `u_xx` at `(0,0)` and the reconstructed `u` at `(1,0)` and `(0,2)`,
as `StreamLowering.heat_lowers` does. -/
def heatObservation : Manifest .ogf 2 2 where
  axes := ![ "t", "x" ]
  ports := ![ "u_xx", "u" ]
  slots := [⟨0, ![0, 0]⟩, ⟨1, ![1, 0]⟩, ⟨1, ![0, 2]⟩]

/-- The circuit resolved from the declaration lowers. -/
theorem declared_heat_lowers :
    declaration.resolve.map (·.map fun r =>
      (lower r.circuit ![ "u", "boundary", "unused" ] heatObservation).isOk) = some [true] := by
  decide +kernel

/-- The lowered observation of the declared circuit is exact for every input. -/
example (lowered : Lowered .ogf 3 2 2 heatObservation)
    (ok : lower equation.circuit ![ "u", "boundary", "unused" ] heatObservation = .ok lowered)
    (x : StreamPoint 2 3) :
    lowered.circuit.run (dependencyPoint lowered.inputs.slots x) =
      fun o => (equation.circuit.value x
        heatObservation.slots[o].port heatObservation.slots[o].degrees.toIndex : ℝ) :=
  lower_correct equation.circuit _ heatObservation _ lowered ok _

/-! ### Series substitution -/

/-- `u(t ↦ x)`: the inner argument is an axis variable, so it is established. -/
def substituted : Declaration :=
  withRhs (.binary (.seriesCompose "time") (.input "u") (.axisVariable "space"))

example : refusal substituted = none := by decide

/-- The accepted substitution is defined on every input. -/
example (m : StreamModel substituted) : ∀ r ∈ m.equations, ∀ x, r.rhs.Defined x :=
  m.rhs_defined

/-- `0 · u(t ↦ 1)`: the substitution of `1` for `t` is discarded by multiplying
by zero, and is still refused, naming its axis. -/
def discarded : Declaration :=
  withRhs (.binary .product (.constant 0)
    (.binary (.seriesCompose "time") (.input "u") (.constant 1)))

example : discarded.validate = .error ⟨.unestablishedCompose, "u", "time"⟩ := by decide
example : refusal discarded = some ⟨.unestablishedCompose, "u", "time"⟩ := by decide

/-- Its names resolve, but the resolved circuit has no lowering either. -/
example : discarded.resolve.map (·.map fun r => supported r.circuit) = some [false] := by
  decide +kernel

/-- An input is never evidence of a zero constant coefficient. -/
example : (withRhs (.binary (.seriesCompose "space") (.input "u") (.input "u"))).validate =
    .error ⟨.unestablishedCompose, "u", "space"⟩ := by decide

/-- A sum with a nonzero constant is not evidence either; `t + 0·x` is. -/
example : (withRhs (.binary (.seriesCompose "space") (.input "u")
    (.binary .add (.axisVariable "time") (.constant 1)))).validate =
    .error ⟨.unestablishedCompose, "u", "space"⟩ := by decide
example : refusal (withRhs (.binary (.seriesCompose "space") (.input "u")
    (.binary .add (.axisVariable "time")
      (.binary .product (.constant 0) (.axisVariable "space"))))) = none := by decide

/-! ### Axes -/

/-- Repeated axis IDs are refused by validation… -/
def repeated : Declaration :=
  { declaration with axes := [⟨"time", "t"⟩, ⟨"time", "x"⟩] }

example : repeated.validate = .error ⟨.duplicateId, "axes", "time"⟩ := by decide
example : refusal repeated = some ⟨.duplicateId, "axes", "time"⟩ := by decide
/-- …and at resolution. -/
example : repeated.resolve = none := by decide

example : ({ declaration with axes := [⟨"time", "t"⟩, ⟨"space", "t"⟩] } : Declaration).validate =
    .error ⟨.duplicateName, "axes", "t"⟩ := by decide
example : ({ declaration with axes := [⟨"", "t"⟩, ⟨"space", "x"⟩] } : Declaration).validate =
    .error ⟨.emptyId, "axes", "t"⟩ := by decide

/-! ### References, roles and bindings -/

example : ({ declaration with
    equations := [⟨"u", "depth", "boundary", Examples.FormalHeat.namedRhs⟩] } :
    Declaration).validate = .error ⟨.unknownReference, "u", "depth"⟩ := by decide
example : (withRhs (.unary (.derivative "depth") (.input "u"))).validate =
    .error ⟨.unknownReference, "u", "depth"⟩ := by decide
example : (withRhs (.input "v")).validate = .error ⟨.unknownReference, "u", "v"⟩ := by decide

/-- The boundary must be a `.boundary` input, and the unknown a `.state` one. -/
example : ({ declaration with
    equations := [⟨"u", "time", "unused", Examples.FormalHeat.namedRhs⟩] } :
    Declaration).validate = .error ⟨.unsupportedRole, "u", "unused"⟩ := by decide
example : ({ declaration with equations := [⟨"boundary", "time", "boundary",
    Examples.FormalHeat.namedRhs⟩] } : Declaration).validate =
    .error ⟨.unsupportedRole, "equations", "boundary"⟩ := by decide

/-- Every unknown has exactly one equation. -/
example : ({ declaration with equations := [] } : Declaration).validate =
    .error ⟨.missingBinding, "equations", "u"⟩ := by decide
example : ({ declaration with equations := declaration.equations ++ declaration.equations } :
    Declaration).validate = .error ⟨.duplicateBinding, "equations", "u"⟩ := by decide

/-- Only state, boundary and parameter inputs. -/
example : ({ declaration with inputs := declaration.inputs ++ [⟨"f", "f", .driver⟩] } :
    Declaration).validate = .error ⟨.unsupportedRole, "f", "f"⟩ := by decide

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Asgard.Streams.derivative_iff_integral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms derivative_iff_integral
/--
info: 'Gimle.Asgard.Streams.Equation.solves_iff_integral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Equation.solves_iff_integral
/--
info: 'Gimle.Asgard.Streams.Equation.solves_iff_rebuilt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Equation.solves_iff_rebuilt
/--
info: 'Gimle.Asgard.Streams.StreamModel.solves_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamModel.solves_iff
/--
info: 'Gimle.Asgard.Streams.StreamModel.solves_iff_integral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamModel.solves_iff_integral
/--
info: 'Gimle.Asgard.Streams.StreamModel.rhs_defined'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamModel.rhs_defined
/--
info: 'Gimle.Asgard.Streams.NamedExpr.established_defined'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms NamedExpr.established_defined
/--
info: 'Gimle.Asgard.Examples.DeclaredHeat.solutions'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms solutions
/--
info: 'Gimle.Asgard.Examples.DeclaredHeat.swapped_solutions'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms swapped_solutions
/--
info: 'Gimle.Asgard.Tests.StreamDeclarations.declared_heat_lowers'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms declared_heat_lowers

end Gimle.Asgard.Tests.StreamDeclarations
