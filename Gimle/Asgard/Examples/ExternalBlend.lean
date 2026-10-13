import Gimle.Asgard.External.Partition

/-! A pointwise two-model blend, with explicit mathematical providers.

For inputs (x,y,unused), A(x,y)=(x,y), B(x,y)=(y,x), and weights x,1-x:
  blend(x,y) = (x²+(1-x)y, xy+(1-x)x).

On 0≤x≤1 and 0≤y≤1 both outputs stay in [0,1]. The theorem proves the
actual compiled circuit's contract under the declared environment. It does not
claim a Python callback or learned model implements these providers. -/
namespace Gimle.Asgard.Examples.ExternalBlend
open Gimle.Asgard.External

def first : Symbol 2 2 := ⟨"model_a", "pointwise/v1"⟩
def second : Symbol 2 2 := ⟨"model_b", "pointwise/v1"⟩

noncomputable def environment : Environment
  | 2, 2, s =>
    if s = first then some ⟨fun _ => True, fun x => ![x 0,x 1]⟩
    else if s = second then some ⟨fun _ => True, fun x => ![x 1,x 0]⟩
    else none
  | _, _, _ => none

def arguments : Source 3 2 := .polynomial ![.var 0,.var 1]
def branches : Fin 2 → Source 3 2 :=
  ![arguments.compose (.external first), arguments.compose (.external second)]
def gates : Fin 2 → Source 3 1 :=
  ![.polynomial ![.var 0], .polynomial ![.add (.constant 1) (.neg (.var 0))]]
def source : Source 3 2 := Source.partition gates branches
def circuit : Gimle.Asgard.External.Circuit 3 2 := source.compile

def region (x : Point 3) : Prop := 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ 1

/-- The applicability region is inhabited, independently of the contract. -/
theorem region_nonempty : region ![1/4,3/4,7] := by norm_num [region]

theorem partition_valid : PartitionOn environment region gates branches where
  defined x _ i := by
    fin_cases i <;>
      simp [gates, branches, arguments, Source.Defined, admitted, resolve, Symbol.valid,
        environment, first, second]
  nonnegative x hx i := by
    rcases hx with ⟨h0,h1,h2,h3⟩
    fin_cases i <;> simp [gates, Source.value, Polynomial.Expr.eval] <;> linarith
  unitSum x _ := by
    simp [gates, Source.value, Polynomial.Expr.eval, Fin.sum_univ_two]

/-- Every admitted input in the square produces two values in the unit interval. -/
theorem circuit_contract : circuit.Satisfies environment
    ⟨region, fun _ y => ∀ j, 0 ≤ y j ∧ y j ≤ 1⟩ := by
  apply Source.partition_contract environment region gates branches partition_valid
    (0 : Point 2) (1 : Point 2)
  intro x hx i _ j
  rcases hx with ⟨h0,h1,h2,h3⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [branches, arguments, Source.value, externalValue, resolve, Symbol.valid,
      environment, first, second, Polynomial.Expr.eval]

/-- Asymmetric inputs distinguish both outputs and the association of gates. -/
theorem concrete_output : circuit.Rel environment ![1/4,3/4,7] ![5/8,3/8] := by
  unfold circuit
  rw [Source.compile_rel]
  constructor
  · exact (Source.partition_defined _ _ _ _).mpr (partition_valid.defined _ region_nonempty)
  · funext j
    fin_cases j <;>
      simp [source, Source.partition_value, blendValue_apply, Fin.sum_univ_two,
        gates, branches, arguments, Source.value, Polynomial.Expr.eval,
        externalValue, resolve, Symbol.valid, environment, first, second]
    all_goals norm_num

#print axioms partition_valid
#print axioms circuit_contract
#print axioms concrete_output
end Gimle.Asgard.Examples.ExternalBlend
