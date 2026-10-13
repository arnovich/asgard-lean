import Gimle.Asgard.Streams.Declaration
import Gimle.Asgard.Streams.Heat
import Gimle.Asgard.Examples.FormalHeat

/-! Formal heat, declared rather than hand-built.

The declaration names the OGF basis, the axes `[time, space]` by stable ID, the
unknown `u`, its boundary profile `u_at_t0` on the `time` axis, and the one
equation `D_t u = D_x² u`. It resolves to exactly the hand-built right-hand side
and circuit of `FormalHeat`, and its solution set with boundary `x²` is exactly
`u = x² + 2t` (`solutions`). With the axes declared in the other order the
solution set is the permuted stream (`swapped_solutions`). These are formal
coefficient statements, not an analytic PDE existence or numerical claim. -/
namespace Gimle.Asgard.Examples.DeclaredHeat
open Gimle.Asgard.Streams
open Gimle.Asgard.Examples.FormalHeat (heat boundary heat_time heat_space heat_boundary)

/-- `D_t u = D_x² u` along `time`, with `u = u_at_t0` on the `t = 0` slice. -/
def declaration : Declaration where
  basis := .ogf
  axes := [⟨"time", "t"⟩, ⟨"space", "x"⟩]
  inputs := [⟨"u", "u", .state⟩, ⟨"boundary", "u_at_t0", .boundary⟩,
    ⟨"unused", "unused", .parameter⟩]
  equations := [⟨"u", "time", "boundary", FormalHeat.namedRhs⟩]

theorem valid : declaration.validate = .ok () := by decide

/-- The resolved equation: unknown `0`, axis `0`, boundary `1`. -/
def equation : ResolvedEquation .ogf 2 3 := ⟨0, 0, 1, FormalHeat.rhs⟩

theorem resolves : declaration.resolve = some [equation] := by decide

def model : StreamModel declaration := ⟨valid, [equation], resolves, by decide⟩

/-- The declared reconstruction and observed circuit are the hand-built ones. -/
theorem rebuilt_eq : equation.rebuilt = FormalHeat.rebuilt := rfl
theorem circuit_eq : equation.circuit = FormalHeat.circuit := rfl

/-- Reconstruction from `x²` along `t` has the single solution `x² + 2t`. -/
theorem reconstructs_iff (u : Stream 2) :
    u = integral .ogf 0 (derivative .ogf 1 (derivative .ogf 1 u)) boundary ↔ u = heat := by
  rw [eq_comm, Heat.reconstructs_iff]
  constructor
  · rintro ⟨pde, slice⟩
    exact Heat.formal_unique .ogf u heat pde (by rw [heat_time, heat_space])
      (fun n zero => (slice n zero).trans (heat_boundary n zero).symm)
  · rintro rfl
    exact ⟨by rw [heat_time, heat_space], heat_boundary⟩

/-- **The declared solution set.** With boundary `x²` and any unused input, `u`
solves the declaration exactly when `u = x² + 2t`. -/
theorem solutions (u unused : Stream 2) :
    declaration.Solves (![u, boundary, unused] : StreamPoint 2 3) ↔ u = heat := by
  rw [model.solves_iff_integral]
  simp only [model, List.mem_singleton, forall_eq]
  exact reconstructs_iff u

/-- The declared heat stream solves it, through the declared circuit. -/
theorem heat_solves (unused : Stream 2) :
    equation.circuit.Rel ![heat, boundary, unused]
      ![derivative .ogf 1 (derivative .ogf 1 heat), heat] := by
  rw [circuit_eq, Gimle.Asgard.Streams.Circuit.rel_iff]
  have := FormalHeat.circuit_behavior unused
  rw [Gimle.Asgard.Streams.Circuit.rel_iff] at this
  refine ⟨this.1, ?_⟩
  rw [heat_space]
  exact this.2

/-! ## The axes declared in the other order -/

/-- The same equation with axes `[space, time]`. -/
def swapped : Declaration := { declaration with axes := [⟨"space", "x"⟩, ⟨"time", "t"⟩] }

theorem swapped_valid : swapped.validate = .ok () := by decide

/-- The IDs keep their meaning; the indices follow the declared order. -/
def swappedEquation : ResolvedEquation .ogf 2 3 :=
  ⟨0, 1, 1, .unary (.derivative 0) (.unary (.derivative 0) (.input 0))⟩

theorem swapped_resolves : swapped.resolve = some [swappedEquation] := by decide

def swappedModel : StreamModel swapped :=
  ⟨swapped_valid, [swappedEquation], swapped_resolves, by decide⟩

/-- The axis permutation `[t, x] ↦ [x, t]`. -/
def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

private theorem reindex_injective {a b : Stream 2} (same : reindex swap a = reindex swap b) :
    a = b := by
  rw [← reindex_inverse swap a, same, reindex_inverse]

/-- **Axis order under permutation.** With the boundary permuted too, the
swapped declaration's solution set is exactly the permuted heat stream. -/
theorem swapped_solutions (u unused : Stream 2) :
    swapped.Solves (![u, reindex swap boundary, unused] : StreamPoint 2 3) ↔
      u = reindex swap heat := by
  rw [swappedModel.solves_iff_integral]
  simp only [swappedModel, List.mem_singleton, forall_eq]
  change u = integral .ogf 1 (derivative .ogf 0 (derivative .ogf 0 u)) (reindex swap boundary) ↔ _
  obtain ⟨v, rfl⟩ : ∃ v, u = reindex swap v :=
    ⟨reindex swap.symm u, by simpa using (reindex_inverse swap.symm u).symm⟩
  have axes : swap 0 = 1 ∧ swap 1 = 0 := by decide
  have permuted : integral .ogf 1 (derivative .ogf 0 (derivative .ogf 0 (reindex swap v)))
      (reindex swap boundary) =
      reindex swap (integral .ogf 0 (derivative .ogf 1 (derivative .ogf 1 v)) boundary) := by
    simp only [reindex_integral, reindex_derivative, axes.1, axes.2]
  rw [permuted]
  constructor
  · intro h
    rw [(reconstructs_iff v).mp (reindex_injective h)]
  · intro h
    rw [reindex_injective h, ← (reconstructs_iff heat).mpr rfl]

#print axioms valid
#print axioms resolves
#print axioms solutions
#print axioms heat_solves
#print axioms swapped_resolves
#print axioms swapped_solutions
end Gimle.Asgard.Examples.DeclaredHeat
