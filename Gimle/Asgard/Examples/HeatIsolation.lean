import Gimle.Asgard.Streams.Isolation
import Gimle.Asgard.Examples.DeclaredHeat

/-! Heat, written as source equations and isolated along `time`.

`diff(u, time) = diff(diff(u, space), space)` isolates to exactly the declared
heat equation of `DeclaredHeat` (`isolates`, `isolated_eq`), in either axis
order, so its solution set with boundary `x²` is `u = x² + 2t` (`solutions`).

The pinned Python fixture `test_affine_heat_preserves_half_diffusivity`
(gimle-asgard `tests/unit/test_affine_differential_isolation.py`) states
`2 * diff(u,t) = diff(diff(u,x),x)`, with the sides reversed, with the spatial
term moved to a residual `2 * diff(u,t) - diff(diff(u,x),x) = 0`, and both, and
checks the field `x² + t` from `u(0,x) = x²` in EGF coefficients. Here each of
the four isolates to a declared equation `D_t u = (…)/2`; the plain and reversed
ones to exactly `D_t u = 1/2 · D_x(D_x(u))`. With the EGF boundary `x²` each has
the single solution `x² + t` (`fixture_solutions`). Outcome: **same**. These
are formal coefficient statements; the Python test samples a simulated field. -/
namespace Gimle.Asgard.Examples.HeatIsolation
open Gimle.Asgard.Streams

/-! ## Declared heat from its source form -/

/-- `diff(u, time) = diff(diff(u, space), space)` with the context of `DeclaredHeat`. -/
def source : SourceDeclaration where
  basis := .ogf
  axes := DeclaredHeat.declaration.axes
  inputs := DeclaredHeat.declaration.inputs
  equations :=
    [sourceEquation% (u, time, boundary) diff(u, time) = diff(diff(u, space), space)]

/-- Isolation returns the declared heat equation unchanged. -/
theorem isolates : source.isolate = .ok DeclaredHeat.declaration.equations := by decide +kernel

theorem isolated_eq : source.isolated DeclaredHeat.declaration.equations =
    DeclaredHeat.declaration := rfl

/-- The source form's solution set is the declared one: `u = x² + 2t`. -/
theorem solutions (u unused : Stream 2) :
    source.Solves (![u, FormalHeat.boundary, unused] : StreamPoint 2 3) ↔ u = FormalHeat.heat := by
  rw [source.solves_iff _ isolates]
  exact DeclaredHeat.solutions u unused

/-- With the axes declared as `[space, time]`, the same source isolates to the
same equation, and the isolated declaration is `DeclaredHeat.swapped`. -/
def swappedSource : SourceDeclaration := { source with axes := DeclaredHeat.swapped.axes }

theorem swapped_isolates :
    swappedSource.isolate = .ok DeclaredHeat.swapped.equations := by decide +kernel

theorem swapped_isolated_eq :
    swappedSource.isolated DeclaredHeat.swapped.equations = DeclaredHeat.swapped := rfl

/-! ## The Python heat fixture -/

/-- The context of the fixture: axes `[t, x]`, unknown, boundary, unused input. -/
def fixture (equation : SourceEquation) : SourceDeclaration where
  basis := .egf
  axes := [⟨"t", "t"⟩, ⟨"x", "x"⟩]
  inputs := [⟨"u", "u", .state⟩, ⟨"u0", "u0", .boundary⟩, ⟨"unused", "unused", .parameter⟩]
  equations := [equation]

/-- `2 * diff(u,t) = diff(diff(u,x),x)`. -/
def plain : SourceEquation := sourceEquation% (u, t, u0) 2 * diff(u, t) = diff(diff(u, x), x)
/-- The sides reversed. -/
def reversed : SourceEquation := sourceEquation% (u, t, u0) diff(diff(u, x), x) = 2 * diff(u, t)
/-- The spatial term as a residual. -/
def residual : SourceEquation :=
  sourceEquation% (u, t, u0) 2 * diff(u, t) - diff(diff(u, x), x) = 0
/-- The residual with the sides reversed. -/
def reversedResidual : SourceEquation :=
  sourceEquation% (u, t, u0) 0 = 2 * diff(u, t) - diff(diff(u, x), x)

/-- `D_x(D_x(u))`. -/
def uxx : NamedExpr := .unary (.derivative "x") (.unary (.derivative "x") (.input "u"))

/-- The isolated equation `D_t u = 1/2 · D_x(D_x(u))`, with boundary `u0`. -/
def half : Equation := ⟨"u", "t", "u0", .binary .product (.constant (1 / 2)) uxx⟩

theorem plain_isolates : (fixture plain).isolate = .ok [half] := by decide +kernel
theorem reversed_isolates : (fixture reversed).isolate = .ok [half] := by decide +kernel

/-- The residual keeps every term: `D_t u = 1/2 · (0 + -1 · (-1 · D_x(D_x(u))))`. -/
def residualHalf : Equation :=
  ⟨"u", "t", "u0", .binary .product (.constant (1 / 2))
    (.binary .add (.constant 0) (.binary .product (.constant (-1))
      (.binary .product (.constant (-1)) uxx)))⟩

theorem residual_isolates : (fixture residual).isolate = .ok [residualHalf] := by decide +kernel
theorem reversedResidual_isolates :
    (fixture reversedResidual).isolate = .ok [residualHalf] := by decide +kernel

/-- `x² + t` in raw EGF coefficients: `2` at `(0,2)` and `1` at `(1,0)`. -/
def solution : Stream 2 := fun n =>
  if n 0 = 0 ∧ n 1 = 2 then 2 else if n 0 = 1 ∧ n 1 = 0 then 1 else 0

/-- The initial profile `x²`, as in the Python fixture's `[0, 0, 2, 0]`. -/
def profile : Stream 2 := fun n => if n 0 = 0 ∧ n 1 = 2 then 2 else 0

/-- Two formal streams with the same `t = 0` slice that both satisfy
`D_t u = c · D_x² u` are equal: the `t`-degree `k+1` coefficients are
determined by those at `t`-degree `k`, as in `Heat.formal_unique`. -/
theorem scaled_unique (basis : Basis) (c : ℚ) (a b : Stream 2)
    (ha : derivative basis 0 a = scaled c (derivative basis 1 (derivative basis 1 a)))
    (hb : derivative basis 0 b = scaled c (derivative basis 1 (derivative basis 1 b)))
    (slice : ∀ n : Index 2, n 0 = 0 → a n = b n) : a = b := by
  suffices ∀ k (n : Index 2), n 0 = k → a n = b n from funext fun n => this _ n rfl
  intro k
  induction k with
  | zero => exact slice
  | succ k ih =>
    intro n hn
    have same : ∀ m : Index 2, m 0 = k →
        scaled c (derivative basis 1 (derivative basis 1 a)) m =
          scaled c (derivative basis 1 (derivative basis 1 b)) m := by
      intro m hm
      have keep : ∀ (m : Index 2) (j : ℕ), (m.update 1 j) 0 = m 0 := by
        intro m j; simp [Finsupp.update_apply]
      cases basis <;> simp only [scaled, derivative] <;> rw [ih _ (by rw [keep, keep, hm])]
    have ea := congrFun (integral_derivative basis 0 a) n
    have eb := congrFun (integral_derivative basis 0 b) n
    rw [ha] at ea
    rw [hb] at eb
    have pos : n 0 ≠ 0 := by omega
    have prev : (n.update 0 (n 0 - 1)) 0 = k := by simp; omega
    rw [← ea, ← eb]
    cases basis <;> simp only [integral, pos, if_false] <;> rw [same _ prev]

theorem solution_time : derivative .egf 0 solution =
    scaled (1 / 2) (derivative .egf 1 (derivative .egf 1 solution)) := by
  funext n
  simp only [derivative, scaled, solution, Finsupp.coe_update, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  by_cases ht : n 0 = 0 <;> by_cases hx : n 1 = 0 <;> simp_all

/-- Reconstruction from `x²` along `t` with half the spatial second derivative
has the single solution `x² + t`. -/
theorem reconstructs_iff (u : Stream 2) :
    u = integral .egf 0 (scaled (1 / 2) (derivative .egf 1 (derivative .egf 1 u))) profile ↔
      u = solution := by
  have slice : ∀ n : Index 2, n 0 = 0 → solution n = profile n := by
    intro n zero; simp [solution, profile, zero]
  constructor
  · intro h
    obtain ⟨pde, boundary⟩ := (derivative_iff_integral .egf 0 u _ profile).mpr h
    exact scaled_unique .egf (1 / 2) u solution pde solution_time
      (fun n zero => (boundary n zero).trans (slice n zero).symm)
  · rintro rfl
    exact (derivative_iff_integral .egf 0 _ _ profile).mp ⟨solution_time, slice⟩

/-- The isolated fixture declaration with the given equation. -/
def isolatedFixture (equation : Equation) : Declaration where
  basis := .egf
  axes := [⟨"t", "t"⟩, ⟨"x", "x"⟩]
  inputs := [⟨"u", "u", .state⟩, ⟨"u0", "u0", .boundary⟩, ⟨"unused", "unused", .parameter⟩]
  equations := [equation]

/-- `D_x(D_x(u))`, resolved. -/
def resolvedUxx : Expr .egf 2 3 := .unary (.derivative 1) (.unary (.derivative 1) (.input 0))

def halfResolved : ResolvedEquation .egf 2 3 :=
  ⟨0, 0, 1, .binary .product (.constant (1 / 2)) resolvedUxx⟩

def residualResolved : ResolvedEquation .egf 2 3 :=
  ⟨0, 0, 1, .binary .product (.constant (1 / 2)) (.binary .add (.constant 0)
    (.binary .product (.constant (-1)) (.binary .product (.constant (-1)) resolvedUxx)))⟩

def halfModel : StreamModel (isolatedFixture half) :=
  ⟨by decide, [halfResolved], by decide +kernel, by decide⟩

def residualModel : StreamModel (isolatedFixture residualHalf) :=
  ⟨by decide, [residualResolved], by decide +kernel, by decide⟩

theorem half_solutions (u unused : Stream 2) :
    (isolatedFixture half).Solves (![u, profile, unused] : StreamPoint 2 3) ↔ u = solution := by
  rw [halfModel.solves_iff_integral]
  simp only [halfModel, List.mem_singleton, forall_eq]
  change u = integral .egf 0 (product .egf (constant .egf (1 / 2))
    (derivative .egf 1 (derivative .egf 1 u))) profile ↔ _
  rw [product_constant]
  exact reconstructs_iff u

theorem residual_solutions (u unused : Stream 2) :
    (isolatedFixture residualHalf).Solves (![u, profile, unused] : StreamPoint 2 3) ↔
      u = solution := by
  rw [residualModel.solves_iff_integral]
  simp only [residualModel, List.mem_singleton, forall_eq]
  change u = integral .egf 0 (product .egf (constant .egf (1 / 2))
    ((constant .egf 0 : Stream 2) + product .egf (constant .egf (-1))
      (product .egf (constant .egf (-1)) (derivative .egf 1 (derivative .egf 1 u))))) profile ↔ _
  have same : product .egf (constant .egf (1 / 2))
      ((constant .egf 0 : Stream 2) + product .egf (constant .egf (-1)) (product .egf (constant .egf (-1))
        (derivative .egf 1 (derivative .egf 1 u)))) =
      scaled (1 / 2) (derivative .egf 1 (derivative .egf 1 u)) := by
    simp only [product_constant]
    funext n
    change (1 / 2 : ℚ) * (constant .egf 0 n + -1 * (-1 * _)) = (1 / 2 : ℚ) * _
    rw [constant_apply]
    split <;> ring
  rw [same]
  exact reconstructs_iff u

/-- **The fixture's solution sets.** Each of the four source forms, with the EGF
boundary `x²`, has the single solution `x² + t`: the Python field. -/
theorem fixture_solutions (equation : SourceEquation)
    (variant : equation = plain ∨ equation = reversed ∨ equation = residual ∨
      equation = reversedResidual) (u unused : Stream 2) :
    (fixture equation).Solves (![u, profile, unused] : StreamPoint 2 3) ↔ u = solution := by
  rcases variant with rfl | rfl | rfl | rfl
  · rw [(fixture plain).solves_iff _ plain_isolates]; exact half_solutions u unused
  · rw [(fixture reversed).solves_iff _ reversed_isolates]; exact half_solutions u unused
  · rw [(fixture residual).solves_iff _ residual_isolates]; exact residual_solutions u unused
  · rw [(fixture reversedResidual).solves_iff _ reversedResidual_isolates]
    exact residual_solutions u unused

#print axioms isolates
#print axioms solutions
#print axioms swapped_isolates
#print axioms plain_isolates
#print axioms residual_isolates
#print axioms scaled_unique
#print axioms reconstructs_iff
#print axioms fixture_solutions
end Gimle.Asgard.Examples.HeatIsolation
