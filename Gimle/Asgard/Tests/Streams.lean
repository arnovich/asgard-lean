import Gimle.Asgard.Streams.Named
import Gimle.Asgard.Streams.Reindex
import Gimle.Asgard.Examples.FormalHeat

namespace Gimle.Asgard.Tests.Streams
open Gimle.Asgard.Streams

example (basis : Basis) (a boundary : Stream 2) :
    derivative basis 0 (integral basis 0 a boundary) = a :=
  derivative_integral basis 0 a boundary

example (basis : Basis) (a : Stream 2) :
    integral basis 1 (derivative basis 1 a) a = a := integral_derivative basis 1 a

example (basis : Basis) (a b : Stream 2) (n : Index 2) (h : n 0 = 0) :
    integral basis 0 a b n = b n := integral_boundary basis 0 a b n h

/-- A nonconstant spatial boundary survives time integration. -/
example : integral .ogf 0 (0 : Stream 2) (MvPowerSeries.X 1) (Finsupp.single 1 1) = 1 := by
  simp [integral, ← MvPowerSeries.coeff_apply, MvPowerSeries.coeff_X]

example : integral .ogf 0 (0 : Stream 2) (MvPowerSeries.X 0) = 0 := by
  funext n
  by_cases h : n 0 = 0
  · simp [integral, h, ← MvPowerSeries.coeff_apply, MvPowerSeries.coeff_X]
    intro eq
    subst n
    simp at h
  · simp only [integral, h, if_false]
    change (0 : ℚ) / (n 0 : ℚ) = 0
    exact zero_div _

example : integral .ogf 0 (0 : Stream 2) (MvPowerSeries.X 1) ≠
    integral .ogf 0 0 0 := by
  intro h
  have coefficient := congrFun h (Finsupp.single 1 1)
  norm_num [integral, ← MvPowerSeries.coeff_apply, MvPowerSeries.coeff_X] at coefficient

/-- x² has ordinary coefficient 1 and exponential coefficient 2. -/
example : product .ogf (axisVariable .ogf (0 : Fin 2)) (axisVariable .ogf 0)
    (Finsupp.single 0 2) = 1 := by
  simp only [product, axisVariable, decode_encode]
  change MvPowerSeries.coeff (Finsupp.single 0 2) ((MvPowerSeries.X (0 : Fin 2) : Stream 2) * MvPowerSeries.X 0) = 1
  rw [← pow_two]
  simp [MvPowerSeries.coeff_X_pow]

example : product .egf (axisVariable .egf (0 : Fin 2)) (axisVariable .egf 0)
    (Finsupp.single 0 2) = 2 := by
  simp only [product, axisVariable, decode_encode]
  change factorial (Finsupp.single (0 : Fin 2) 2) *
    MvPowerSeries.coeff (Finsupp.single 0 2) ((MvPowerSeries.X (0 : Fin 2) : Stream 2) * MvPowerSeries.X 0) = 2
  rw [← pow_two]
  norm_num [MvPowerSeries.coeff_X_pow, factorial, Fin.prod_univ_two, Finsupp.single_apply]

/-- Actual EGF source-to-circuit admission and independently expected raw
coefficient detect an accidental OGF dispatch shared by source and target. -/
example : ∃ y : StreamPoint 2 1,
    (Expr.binary .product (.input 0) (.input 0) : Expr .egf 2 1).compile.Rel
      ![axisVariable .egf 0] y ∧ y 0 (Finsupp.single 0 2) = 2 := by
  refine ⟨![encode .egf ((MvPowerSeries.X (0 : Fin 2) : Stream 2)^2)], ?_, ?_⟩
  · rw [Expr.compile_rel]
    constructor
    · simp [Expr.Defined, Binary.Domain]
    · simp [Expr.value, Binary.value, product, axisVariable, pow_two]
  · change factorial (Finsupp.single (0 : Fin 2) 2) *
      MvPowerSeries.coeff (Finsupp.single 0 2) ((MvPowerSeries.X (0 : Fin 2) : Stream 2)^2) = 2
    norm_num [MvPowerSeries.coeff_X_pow, factorial, Fin.prod_univ_two, Finsupp.single_apply]

/-- Both axes contribute factorials: 2!*3!=12, not 2 or 6. -/
example : encode .egf (MvPowerSeries.monomial
    (Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 3) 1)
    (Finsupp.single 0 2 + Finsupp.single 1 3) = 12 := by
  change factorial _ * MvPowerSeries.coeff _ (MvPowerSeries.monomial _ (1 : ℚ)) = 12
  norm_num [factorial, Fin.prod_univ_two, Finsupp.single_apply]

private theorem update_single_same {d : Nat} (axis : Fin d) (m n : Nat) :
    (Finsupp.single axis m).update axis n = Finsupp.single axis n := by
  change ((0 : Index d).update axis m).update axis n = (0 : Index d).update axis n
  exact Finsupp.update_idem _ _ _ _

/-- Formal OGF differentiation scales degree; the EGF shift does not. -/
example (a : Stream 1) : derivative .ogf 0 a (Finsupp.single 0 2) =
    3 * a (Finsupp.single 0 3) := by norm_num [derivative, update_single_same]

example (a : Stream 1) : derivative .egf 0 a (Finsupp.single 0 2) =
    a (Finsupp.single 0 3) := by norm_num [derivative, update_single_same]

/-- The selected-axis boundary may be nonzero while the global constant is zero. -/
example : CanCompose .ogf (MvPowerSeries.X (1 : Fin 2)) := by
  simp [CanCompose, decode]

example : seriesCompose .ogf 0 (axisVariable .ogf (0 : Fin 2)) (MvPowerSeries.X 1) =
    MvPowerSeries.X 1 := by
  apply compose_variable
  simp [CanCompose, decode]

example : seriesCompose .ogf 0 (axisVariable .ogf (1 : Fin 2)) (MvPowerSeries.X 1) =
    axisVariable .ogf 1 := by
  apply compose_other_variable
  · simp [CanCompose, decode]
  · decide

/-- Substitute x↦t+x into x². Other variables are retained exactly. -/
example : seriesCompose .ogf 1
    (product .ogf (axisVariable .ogf (1 : Fin 2)) (axisVariable .ogf 1))
    (MvPowerSeries.X 0 + MvPowerSeries.X 1) =
    ((MvPowerSeries.X 0)^2 + 2*MvPowerSeries.X 0*MvPowerSeries.X 1 +
      (MvPowerSeries.X 1)^2 : Stream 2) := by
  have valid : CanCompose .ogf (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) := by
    simp [CanCompose, decode]
  rw [compose_product .ogf 1 _ _ _ valid, compose_variable .ogf 1 _ valid]
  simp only [product, decode, encode]
  ring

/-- Carried outer coordinates also participate in historical convolution:
substitute t↦t+x into t*x², retaining the outer x² factor. -/
example : seriesCompose .ogf 0
    (product .ogf (axisVariable .ogf (0 : Fin 2))
      (product .ogf (axisVariable .ogf 1) (axisVariable .ogf 1)))
    (MvPowerSeries.X 0 + MvPowerSeries.X 1) =
    ((MvPowerSeries.X 0 + MvPowerSeries.X 1) * (MvPowerSeries.X 1)^2 : Stream 2) := by
  have valid : CanCompose .ogf (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) := by
    simp [CanCompose, decode]
  rw [compose_product .ogf 0 _ _ _ valid, compose_variable .ogf 0 _ valid,
    compose_product .ogf 0 _ _ _ valid, compose_other_variable .ogf 0 1 _ valid (by decide)]
  simp only [product, axisVariable, decode, encode]
  ring

example : (Expr.binary (.convolution 0) (.axisVariable 0) (.axisVariable 1) :
    Expr .ogf 2 0).compile.Rel ![] ![axisVariable .ogf 1] := by
  rw [Expr.compile_rel]
  constructor
  · simp [Expr.Defined, Expr.value, Binary.convolution, Binary.Domain, CanCompose,
      axisVariable, decode, encode]
  · simp only [Expr.value, Binary.convolution, Binary.value]
    rw [compose_variable]
    simp [CanCompose, axisVariable, decode, encode]

/-- All names may resolve while a mathematical substitution domain still fails. -/
def invalid : Expr .ogf 2 1 := .seriesCompose 0 (.input 0) (.constant 1)

example (y : StreamPoint 2 1) : ¬ invalid.compile.Rel ![MvPowerSeries.X 0] y := by
  simp [Expr.compile_rel, invalid, Expr.seriesCompose, Expr.Defined, Expr.value,
    Binary.Domain, CanCompose, constant, decode, encode]

example (y : StreamPoint 2 1) : ¬ (Expr.binary .product (.constant 0) invalid).compile.Rel
    ![MvPowerSeries.X 0] y := by
  simp [Expr.compile_rel, invalid, Expr.seriesCompose, Expr.Defined, Expr.value,
    Binary.Domain, CanCompose, constant, decode, encode]

example (y : StreamPoint 2 0) : ¬
    (Gimle.Asgard.Streams.Circuit.compose invalid.compile (.route Fin.elim0)).Rel
      ![MvPowerSeries.X 0] y := by
  simp [Gimle.Asgard.Streams.Circuit.rel_iff, Gimle.Asgard.Streams.Circuit.Defined,
    Expr.compile_defined, invalid, Expr.seriesCompose, Expr.Defined, Expr.value,
    Binary.Domain, CanCompose, constant, decode, encode]

/-- IDs are resolved in their declared order, with distinct axis/input scopes. -/
def context : Context where
  axes := [⟨"u", "u"⟩, ⟨"space", "x"⟩]
  inputs := [⟨"u", "u", .input⟩, ⟨"v", "v", .input⟩, ⟨"unused", "unused", .parameter⟩]

example : context.valid = true := by decide
example : context.axis "space" = some ⟨1, by decide⟩ := by decide
example : context.axis "missing" = none := by decide
example : context.input "missing" = none := by decide

example : ({ context with axes := [⟨"u", "u"⟩, ⟨"u", "v"⟩] } : Context).axis "u" = none := by decide
example : ({ context with axes := [⟨"a", "x"⟩, ⟨"b", "x"⟩] } : Context).axis "a" = none := by decide
example : ({ context with inputs := [⟨"u", "u", .input⟩, ⟨"u", "v", .input⟩] } : Context).input "u" = none := by decide

example : context.resolve .ogf (.unary (.derivative "missing") (.input "u")) = none := by decide

def shared : NamedExpr := .binary .add (.input "u") (.binary .add (.input "v") (.input "u"))
def sharedResolved : Expr .ogf 2 3 := .binary .add (.input 0) (.binary .add (.input 1) (.input 0))

example : context.resolve .ogf shared = some sharedResolved := by decide

example (a b unused : Stream 2) : sharedResolved.compile.Rel ![a,b,unused] ![a+(b+a)] := by
  simp [Expr.compile_rel, sharedResolved, Expr.Defined, Expr.value, Binary.Domain, Binary.value]

/-- Concrete asymmetric routing must not swap the repeated and single inputs. -/
example : sharedResolved.compile.value ![constant .ogf 2,constant .ogf 7,0] 0 0 = 11 := by
  norm_num [Expr.compile_value, sharedResolved, Expr.value, Binary.value, constant, encode,
    ← MvPowerSeries.coeff_apply]

example : sharedResolved.compile.value ![constant .ogf 7,constant .ogf 2,0] 0 0 ≠ 11 := by
  norm_num [Expr.compile_value, sharedResolved, Expr.value, Binary.value, constant, encode,
    ← MvPowerSeries.coeff_apply]

/-- A three-cycle distinguishes a permutation from its inverse. -/
def cycle : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
noncomputable def degrees : Index 3 := Finsupp.equivFunOnFinite.symm ![1,2,3]
def asymmetric : Stream 3 := fun n => (n 0 : ℚ) + 10*n 1 + 100*n 2

example : reindex cycle asymmetric degrees = 213 := by
  have h0 : cycle 0 = 2 := by decide
  have h1 : cycle 1 = 0 := by decide
  have h2 : cycle 2 = 1 := by decide
  norm_num [reindex, pullIndex, asymmetric, degrees, h0, h1, h2, Matrix.cons_val]
  norm_num [show (![1,2,3] : Fin 3 → ℕ) 2 = 3 from rfl]

example : reindex cycle.symm asymmetric degrees ≠ 213 := by
  have h0 : cycle.symm 0 = 1 := by decide
  have h1 : cycle.symm 1 = 2 := by decide
  have h2 : cycle.symm 2 = 0 := by decide
  norm_num [reindex, pullIndex, asymmetric, degrees, h0, h1, h2, Matrix.cons_val]
  norm_num [show (![1,2,3] : Fin 3 → ℕ) 2 = 3 from rfl]

example (basis : Basis) (a boundary : Stream 3) :
    reindex cycle (integral basis 0 a boundary) =
      integral basis (cycle 0) (reindex cycle a) (reindex cycle boundary) :=
  reindex_integral cycle basis 0 a boundary

example (basis : Basis) (a : Stream 3) :
    reindex cycle (derivative basis 0 a) = derivative basis (cycle 0) (reindex cycle a) :=
  reindex_derivative cycle basis 0 a

/-- Zero-axis constants are valid formal scalar streams. -/
example : (Expr.constant (1/3) : Expr .ogf 0 0).compile.Rel ![] ![constant .ogf (1/3)] := by
  simp [Expr.compile_rel, Expr.Defined, Expr.value]

/-- Truncating away degree three destroys the retained degree-two derivative. -/
def cubic : Stream 1 := fun n => if n 0 = 3 then 1 else 0

example : derivative .ogf 0 cubic (Finsupp.single 0 2) = 3 := by
  norm_num [derivative, cubic]

example : derivative .ogf 0 (truncate (fun _ => 3) cubic) (Finsupp.single 0 2) = 0 := by
  norm_num [derivative, truncate, cubic]

example (unused : Stream 2) : Examples.FormalHeat.circuit.Rel
    ![Examples.FormalHeat.heat,Examples.FormalHeat.boundary,unused]
    ![Examples.FormalHeat.two,Examples.FormalHeat.heat] := Examples.FormalHeat.circuit_behavior unused

#print axioms Expr.compile_rel
#print axioms Context.compiled_iff
#print axioms Examples.FormalHeat.circuit_behavior
end Gimle.Asgard.Tests.Streams
