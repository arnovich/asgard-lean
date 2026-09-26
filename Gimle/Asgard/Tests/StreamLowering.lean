import Gimle.Asgard.Streams.Lowering
import Gimle.Asgard.Examples.FormalHeat

/-! Coverage for lowering stream observations.

Pinned here: the derivative halo and its OGF/EGF factors; two streams equal on
a window whose observed derivatives differ; mixed-axis products; a boundary
read along the other axis; asymmetric wiring and permuted axes; both outputs of
the formal heat circuit on an input with a coefficient outside the naive
window; refusal of series substitution even when discarded; and resource
limits reported apart from unsupported structure.
-/

namespace Gimle.Asgard.Tests.StreamLowering

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Lowering

/-- `D_x² u` on axes `[t, x]`, one input. -/
def secondSpace (basis : Basis) : Expr basis 2 1 :=
  .unary (.derivative 1) (.unary (.derivative 1) (.input 0))

/-! ### The derivative halo -/

/-- Coefficient `(0,0)` of `D_x² u` reads only `u` at `(0,2)`… -/
example : (lowerRaw (secondSpace .ogf).compile 0 ![0, 0]).slots = [⟨0, ![0, 2]⟩] := by
  decide +kernel
/-- …and factor `1·1` in EGF. -/
example : lowerRaw (secondSpace .egf).compile 0 ![0, 0] =
    .mul (.const 1) (.mul (.const 1) (.slot ⟨0, ![0, 2]⟩)) := by decide +kernel

-- …with factor `1·2` in OGF: `secondSpace_term`, below.

/-- `x²` in OGF coefficients: `1` at `(0,2)`. -/
noncomputable def xSquared : Stream 2 := fun index => if index 0 = 0 ∧ index 1 = 2 then 1 else 0

/-- `x²` and `0` agree on the window `degree ≤ (1,1)`… -/
example (index : Index 2) (inside : index 0 ≤ 1 ∧ index 1 ≤ 1) :
    xSquared index = (0 : Stream 2) index := by
  simp only [xSquared]
  rw [if_neg (by omega)]
  rfl

/-- …but their observed `D_x²` at `(0,0)` differs, because it reads `(0,2)`. -/
theorem secondSpace_term : lowerRaw (secondSpace .ogf).compile 0 ![0, 0] =
    .mul (.const 1) (.mul (.const 2) (.slot ⟨0, ![0, 2]⟩)) := by decide +kernel

example : (secondSpace .ogf).compile.value ![xSquared] 0 (Degrees.toIndex ![0, 0]) = 2 ∧
    (secondSpace .ogf).compile.value ![0] 0 (Degrees.toIndex ![0, 0]) = 0 := by
  rw [lowerRaw_correct _ (by decide +kernel), lowerRaw_correct _ (by decide +kernel),
    secondSpace_term]
  simp [Term.eval, xSquared]
  rfl

/-! ### Products, boundaries and wiring -/

/-- The product of the two inputs, on axes `[t, x]`. -/
def product : Expr .ogf 2 2 := .binary .product (.input 0) (.input 1)

/-- Coefficient `(1,1)` of a product reads every split along both axes. -/
example : (lowerRaw product.compile 0 ![1, 1]).slots.length = 8 := by decide +kernel
example : ⟨0, ![1, 0]⟩ ∈ (lowerRaw product.compile 0 ![1, 1]).slots ∧
    ⟨1, ![0, 1]⟩ ∈ (lowerRaw product.compile 0 ![1, 1]).slots := by decide +kernel

/-- Integrate the first input along `t`, with the second as boundary. -/
def integrateTime : Expr .ogf 2 2 := .binary (.integral 0) (.input 0) (.input 1)

/-- At `t`-degree zero the integral reads the boundary at the same `x`-degree. -/
example : (lowerRaw integrateTime.compile 0 ![0, 3]).slots = [⟨1, ![0, 3]⟩] := by decide +kernel
/-- Above it, the integrand one `t`-degree down, divided by the degree. -/
example : lowerRaw integrateTime.compile 0 ![2, 3] =
    .mul (.const (1 / 2)) (.slot ⟨0, ![1, 3]⟩) := by decide +kernel

/-- Asymmetric wiring: a route that swaps two ports reads the other port. -/
example : lowerRaw (Streams.Circuit.route (basis := .ogf) (d := 2) (n := 2) ![1, 0]) 0 ![4, 5] =
    .slot ⟨1, ![4, 5]⟩ := by decide +kernel

/-- Permuting the axes moves the halo: differentiating along `t` instead of `x`
reads `(2,0)` rather than `(0,2)`. -/
def secondTime : Expr .ogf 2 1 :=
  .unary (.derivative 0) (.unary (.derivative 0) (.input 0))

example : (lowerRaw secondTime.compile 0 ![0, 0]).slots = [⟨0, ![2, 0]⟩] := by decide +kernel

/-! ### The formal heat circuit -/

open Gimle.Asgard.Examples.FormalHeat

/-- Observe `u_xx` at `(0,0)` and the reconstructed `u` at `(1,0)` and `(0,2)`. -/
def heatObservation : Manifest .ogf 2 2 where
  axes := ![ "t", "x" ]
  ports := ![ "u_xx", "u" ]
  slots := [⟨0, ![0, 0]⟩, ⟨1, ![1, 0]⟩, ⟨1, ![0, 2]⟩]

theorem heat_lowers :
    (lower circuit ![ "u", "boundary", "unused" ] heatObservation).isOk := by
  decide +kernel

/-- `u = x² + 2t` plus `5x³`: a coefficient outside the observed window that
the observation `u_xx` at `(0,1)` actually reads. -/
noncomputable def heatWithTail : Stream 2 := fun index =>
  heat index + if index 0 = 0 ∧ index 1 = 3 then 5 else 0

/-- `u_xx` at `(0,1)` reads `u` at `(0,3)` with factor `2·3`. -/
theorem uxx_term : (lowerRaw circuit 0 ![0, 1]).slots = [⟨0, ![0, 3]⟩] := by decide +kernel

/-- The lowered observation gives the tail's contribution, `u_xx(0,1) = 30`,
through `lowerRaw_correct` — not through any zero-tail assumption. -/
example (boundaryPort unused : Stream 2) :
    circuit.value ![heatWithTail, boundaryPort, unused] 0 (Degrees.toIndex ![0, 1]) = 30 := by
  rw [lowerRaw_correct _ (by decide +kernel)]
  rw [Term.eval_congr (y := ![fun index => if index 0 = 0 ∧ index 1 = 3 then 5 else 0,
      boundaryPort, unused]) _ (fun s member => by
    rw [uxx_term] at member
    simp at member
    subst member
    simp [heatWithTail, heat])]
  have := lowerRaw_correct circuit (by decide +kernel)
    ![fun index => if index 0 = 0 ∧ index 1 = 3 then 5 else 0, boundaryPort, unused] 0 ![0, 1]
  rw [← this]
  simp [circuit, rhs, rebuilt, Expr.value, Unary.value, derivative]
  norm_num

/-- Both outputs of the heat circuit, through the lowered feedforward circuit,
for the tailed input. -/
example (lowered : Lowered .ogf 3 2 2 heatObservation)
    (ok : lower circuit ![ "u", "boundary", "unused" ] heatObservation = .ok lowered)
    (unused : Stream 2) :
    lowered.circuit.run
        (dependencyPoint lowered.inputs.slots ![heatWithTail, boundary, unused]) =
      fun o => (circuit.value ![heatWithTail, boundary, unused]
        heatObservation.slots[o].port heatObservation.slots[o].degrees.toIndex : ℝ) :=
  lower_correct circuit _ heatObservation _ lowered ok _

/-! ### Named axes, permuted -/

/-- The heat context with its axes in the other order: `[x, t]`. -/
def swappedContext : Context where
  axes := [⟨"space", "x"⟩, ⟨"time", "t"⟩]
  inputs := context.inputs

/-- The same named `u_xx`, resolved under `[t, x]` and under `[x, t]`, reads
`(0,2)` and `(2,0)`: the dependency degrees follow the axis order. -/
example : ((context.resolve .ogf namedRhs).map fun e =>
    (lowerRaw e.compile 0 ![0, 0]).slots) = some [⟨⟨0, by decide⟩, ![0, 2]⟩] := by
  decide +kernel
example : ((swappedContext.resolve .ogf namedRhs).map fun e =>
    (lowerRaw e.compile 0 ![0, 0]).slots) = some [⟨⟨0, by decide⟩, ![2, 0]⟩] := by
  decide +kernel

/-- The input manifest carries the output's axis IDs. -/
example (lowered : Lowered .ogf 3 2 2 heatObservation)
    (ok : lower circuit ![ "u", "boundary", "unused" ] heatObservation = .ok lowered) :
    lowered.inputs.axes = ![ "t", "x" ] :=
  (lower_names circuit _ heatObservation _ lowered ok).2.1

/-! ### Refusals and limits -/

/-- Substituting `1` for `t` and discarding the result is still refused. -/
def discarded : Streams.Circuit .ogf 1 1 0 :=
  .compose (Expr.seriesCompose 0 (.input 0) (.constant 1)).compile (.route Fin.elim0)

example : supported discarded = false := by decide +kernel
example : (lower discarded ![ "u" ]
    (⟨![ "t" ], Fin.elim0, []⟩ : Manifest .ogf 0 1)).toBool = false := by
  decide +kernel

/-- A tiny limit is a resource failure, not an unsupported one. -/
example : (match lower product.compile ![ "a", "b" ]
    (Manifest.rectangle ![ "t", "x" ] ![ "ab" ] 0 ![3, 3]) 10 with
    | .error (.resourceLimit _) => true
    | _ => false) = true := by decide +kernel

/-- Repeated or empty axis IDs are refused. -/
example : (match lower product.compile ![ "a", "b" ]
    (⟨![ "t", "t" ], ![ "ab" ], [⟨0, ![0, 0]⟩]⟩ : Manifest .ogf 1 2) with
    | .error .invalidNames => true
    | _ => false) = true := by decide +kernel
example : (match lower product.compile ![ "a", "" ]
    (⟨![ "t", "x" ], ![ "ab" ], [⟨0, ![0, 0]⟩]⟩ : Manifest .ogf 1 2) with
    | .error .invalidNames => true
    | _ => false) = true := by decide +kernel

/-- Squaring `levels` times: linear in size, exponential in term size. -/
def squaring : (levels : Nat) → Streams.Circuit .ogf 1 1 1
  | 0 => .route id
  | levels + 1 => .compose (squaring levels)
      (.compose (.route ![0, 0]) (.binary .product))

/-- Forty levels would expand to about 2⁴⁰ nodes; the bounded lowering stops at
the limit instead of expanding first. -/
example : (match lower (squaring 40) ![ "u" ]
    (⟨![ "t" ], ![ "u40" ], [⟨0, ![0]⟩]⟩ : Manifest .ogf 1 1) 50 with
    | .error (.resourceLimit _) => true
    | _ => false) = true := by decide +kernel

/-- A repeated output slot is refused. -/
example : (match lower product.compile ![ "a", "b" ]
    ⟨![ "t", "x" ], ![ "ab" ], [⟨0, ![0, 0]⟩, ⟨0, ![0, 0]⟩]⟩ with
    | .error .duplicateSlot => true
    | _ => false) = true := by decide +kernel

/-- A window of size zero along an axis observes nothing. -/
example : (Manifest.rectangle (basis := .ogf) ![ "t", "x" ] ![ "u" ] 0 ![0, 4]).slots = [] := by
  decide +kernel

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Asgard.Streams.Lowering.lowerRaw_correct'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lowerRaw_correct
/--
info: 'Gimle.Asgard.Streams.Lowering.lower_correct'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lower_correct
/--
info: 'Gimle.Asgard.Streams.Lowering.product_coefficient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms product_coefficient

end Gimle.Asgard.Tests.StreamLowering
