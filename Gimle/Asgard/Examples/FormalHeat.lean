import Gimle.Asgard.Streams.Named
import Gimle.Asgard.Streams.Reindex

/-! Formal two-axis heat equation, in ordinary generating-function coefficients.

u(t,x) = x² + 2t
∂u/∂t = ∂²u/∂x² = 2
u(0,x) = x²

The compiled circuit returns the spatial second derivative and the reconstructed
stream obtained by integrating it along t with the complete boundary profile.
These are exact formal coefficient identities, not an analytic PDE existence
or numerical simulation claim. Axes are ordered [t,x]; inputs [u,boundary,unused]. -/
namespace Gimle.Asgard.Examples.FormalHeat
open Gimle.Asgard.Streams

def heat : Stream 2 := fun n =>
  if n 0 = 0 ∧ n 1 = 2 then 1 else if n 0 = 1 ∧ n 1 = 0 then 2 else 0

def boundary : Stream 2 := fun n => if n 0 = 0 ∧ n 1 = 2 then 1 else 0

def two : Stream 2 := fun n => if n 0 = 0 ∧ n 1 = 0 then 2 else 0

theorem heat_time : derivative .ogf 0 heat = two := by
  funext n
  simp only [derivative, heat, two, Finsupp.coe_update, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  by_cases ht : n 0 = 0 <;> by_cases hx : n 1 = 0 <;> simp_all

theorem heat_space : derivative .ogf 1 (derivative .ogf 1 heat) = two := by
  funext n
  simp only [derivative, heat, two, Finsupp.coe_update, Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  by_cases ht : n 0 = 0 <;> by_cases hx : n 1 = 0 <;> simp_all
  all_goals norm_num

theorem heat_boundary (n : Index 2) (zero : n 0 = 0) : heat n = boundary n := by
  simp [heat, boundary, zero]

theorem reconstructed : integral .ogf 0 two boundary = heat := by
  rw [← heat_time]
  calc
    integral .ogf 0 (derivative .ogf 0 heat) boundary =
        integral .ogf 0 (derivative .ogf 0 heat) heat := by
      funext n
      by_cases zero : n 0 = 0
      · simp [integral, zero, heat_boundary n zero]
      · simp [integral, zero]
    _ = heat := integral_derivative .ogf 0 heat

def context : Context where
  axes := [⟨"time", "t"⟩, ⟨"space", "x"⟩]
  inputs := [⟨"u", "u", .state⟩, ⟨"boundary", "u_at_t0", .boundary⟩,
    ⟨"unused", "unused", .parameter⟩]

def namedRhs : NamedExpr := .unary (.derivative "space") (.unary (.derivative "space") (.input "u"))

def rhs : Expr .ogf 2 3 := .unary (.derivative 1) (.unary (.derivative 1) (.input 0))

theorem resolves_rhs : context.resolve .ogf namedRhs = some rhs := by decide

def rebuilt : Expr .ogf 2 3 := .binary (.integral 0) rhs (.input 1)

def circuit : Gimle.Asgard.Streams.Circuit .ogf 2 3 2 := rhs.compile.pair rebuilt.compile

/-- The original arbitrary third input is retained as an unused input, while
both branches share the same u and boundary streams. -/
theorem circuit_behavior (unused : Stream 2) :
    circuit.Rel ![heat,boundary,unused] ![two,heat] := by
  rw [Gimle.Asgard.Streams.Circuit.rel_iff]
  constructor
  · simp [circuit, Gimle.Asgard.Streams.Circuit.pair_defined, Expr.compile_defined,
      rhs, rebuilt, Expr.Defined, Binary.Domain]
  · simp [circuit, Gimle.Asgard.Streams.Circuit.pair_value, Expr.compile_value,
      rhs, rebuilt, Expr.value, Unary.value, Binary.value, heat_space, reconstructed]

#print axioms heat_time
#print axioms heat_space
#print axioms reconstructed
#print axioms resolves_rhs
#print axioms circuit_behavior
end Gimle.Asgard.Examples.FormalHeat
