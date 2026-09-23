import Gimle.Asgard.Examples.ExternalBlend

namespace Gimle.Asgard.Tests.External
open Gimle.Asgard.External

def missing : Environment := fun _ => none
def sensor : Symbol 0 2 := ⟨"sensor", "sensor.real/v1"⟩
def sensorV2 : Symbol 0 2 := ⟨"sensor", "sensor.real/v2"⟩
def transformer : Symbol 1 1 := ⟨"sensor", "sensor.real/v1"⟩
def invalidUnit : Symbol 0 1 := ⟨"invalid", "v1"⟩

noncomputable def providers : Environment
  | 0, 2, s => if s = sensor then some ⟨fun _ => True, fun _ => ![2,5]⟩
      else if s = sensorV2 then some ⟨fun _ => True, fun _ => ![3,7]⟩ else none
  | 1, 1, s => if s = transformer then some ⟨fun x => 0 ≤ x 0, fun x => ![x 0+1]⟩ else none
  | 0, 1, s => if s = invalidUnit then some ⟨fun _ => False, fun _ => ![1]⟩ else none
  | _, _, _ => none

example : (Source.external sensor).compile.Rel providers ![] ![2,5] := by
  simp [Source.compile_rel, Source.Defined, Source.value, admitted, externalValue,
    resolve, Symbol.valid, providers, sensor]

example : (Source.external sensorV2).compile.Rel providers ![] ![3,7] := by
  simp [Source.compile_rel, Source.Defined, Source.value, admitted, externalValue,
    resolve, Symbol.valid, providers, sensor, sensorV2]

/-- The same ID/version at another arity is a distinct typed key. -/
example : (Source.external transformer).compile.Rel providers ![4] ![5] := by
  simp [Source.compile_rel, Source.Defined, Source.value, admitted, externalValue,
    resolve, Symbol.valid, providers, transformer]
  all_goals norm_num

example (y : Point 1) : ¬ (Source.external transformer).compile.Rel providers ![-1] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, Symbol.valid, providers, transformer]

/-- Check the transformed intermediate input, not the original positive input. -/
example (y : Point 1) : ¬ ((Source.polynomial ![.neg (.var 0)] : Source 1 1).compose
    (.external transformer)).compile.Rel providers ![1] y := by
  simp [Source.compile_rel, Source.Defined, Source.value, Polynomial.Expr.eval,
    admitted, resolve, Symbol.valid, providers, transformer]

/-- A missing environment does not inherit another environment's denotation. -/
example (y : Point 2) : ¬ (Source.external sensor).compile.Rel missing ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, Symbol.valid, missing]

example (y : Point 2) :
    ¬ (Source.external (⟨"sensor","unknown/v3"⟩ : Symbol 0 2)).compile.Rel providers ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, Symbol.valid, providers, sensor, sensorV2]

/-- Malformed keys are rejected even if the raw provider would return a value. -/
noncomputable def permissive : Environment := fun _ => some ⟨fun _ => True, fun _ => 0⟩
/-- Same resolved key, different fixed environment, different actual value. -/
example : (Source.external sensor).compile.Rel permissive ![] (0 : Point 2) := by
  simp [Source.compile_rel, Source.Defined, Source.value, admitted, externalValue,
    resolve, Symbol.valid, permissive, sensor]

example (y : Point 1) :
    ¬ (Source.external (⟨"","v1"⟩ : Symbol 0 1)).compile.Rel permissive ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, Symbol.valid]
example (y : Point 1) :
    ¬ (Source.external (⟨"x",""⟩ : Symbol 0 1)).compile.Rel permissive ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, Symbol.valid]

/-- Contract satisfaction cannot be established vacuously by a missing provider. -/
example : ¬ (Source.external sensor).compile.Satisfies missing (⟨fun _ => True, fun _ _ => True⟩ : Contract 0 2) := by
  intro h
  have hd := (h ![] trivial).1
  simp [Source.compile_defined, Source.Defined, admitted, resolve, missing] at hd

/-- Zero weight and downstream discard retain undefined branch requirements. -/
example (y : Point 2) :
    ¬ (Source.weighted (Source.constant 0) (.external sensor)).compile.Rel missing ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, missing]

example (y : Point 0) : ¬ ((Source.external sensor).compose
    (.polynomial Fin.elim0)).compile.Rel missing ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, missing]

/-- A gate with auxiliary value one but empty domain cannot be erased. -/
example : externalValue providers invalidUnit ![] 0 = 1 := by
  simp [externalValue, resolve, Symbol.valid, providers, invalidUnit]
example (y : Point 1) : ¬ (Source.weighted (.external invalidUnit)
    (Source.constant 3)).compile.Rel providers ![] y := by
  simp [Source.compile_rel, Source.Defined, admitted, resolve, Symbol.valid, providers, invalidUnit]

/-- Two components with the same bound need not be interchangeable. -/
def bound : Contract 0 1 := ⟨fun _ => True, fun _ y => 0 ≤ y 0 ∧ y 0 ≤ 1⟩
example : (Source.constant 0 : Source 0 1).compile.Satisfies missing bound := by
  intro x _
  norm_num [Source.compile_defined, Source.compile_value, bound]
example : (Source.constant 1 : Source 0 1).compile.Satisfies missing bound := by
  intro x _
  norm_num [Source.compile_defined, Source.compile_value, bound]
example : ¬ (Source.constant 0 : Source 0 1).compile.Equivalent missing (Source.constant 1).compile := by
  intro h
  have := h ![] ![0]
  norm_num [Source.compile_rel] at this

/-- Inactive defined branches can violate the local guarantee without affecting it. -/
def activeGates : Fin 2 → Source 0 1 := ![Source.constant 1,Source.constant 0]
def localBranches : Fin 2 → Source 0 1 := ![Source.constant 3,Source.constant 100]

example : (Source.partition activeGates localBranches).compile.Rel missing ![] ![3] := by
  rw [Source.compile_rel]
  constructor
  · simp [Source.partition_defined, activeGates, localBranches, Fin.forall_fin_succ]
  · funext j; fin_cases j
    norm_num [Source.partition_value, blendValue_apply, activeGates, localBranches, Fin.sum_univ_two]

example : blendValue (![1,0] : Fin 2 → ℝ) ![![3],![100]] = (![3] : Point 1) := by
  apply blendValue_agrees
  · norm_num [Fin.sum_univ_two]
  · intro i h; fin_cases i <;> simp_all

/-- Concrete interval failures detect missing nonnegative/unit-sum hypotheses. -/
example : blendValue (![2,-1] : Fin 2 → ℝ) ![![0],![1]] 0 < 0 := by
  norm_num [blendValue_apply, Fin.sum_univ_two]
example : 1 < blendValue (![1,1] : Fin 2 → ℝ) ![![1],![1]] 0 := by
  norm_num [blendValue_apply, Fin.sum_univ_two]

example : ¬ PartitionOn missing (fun _ : Point 0 => True)
    (Fin.elim0 : Fin 0 → Source 0 1) (Fin.elim0 : Fin 0 → Source 0 1) := by
  intro h
  have := h.unitSum ![] trivial
  norm_num at this

/-- Squaring after blending is different from blending squares. -/
example : (blendValue (![1/2,1/2] : Fin 2 → ℝ) ![![0],![2]] 0)^2 = 1 ∧
    blendValue (![1/2,1/2] : Fin 2 → ℝ) ![![0^2],![2^2]] 0 = 2 := by
  norm_num [blendValue_apply, Fin.sum_univ_two]

example : Gimle.Asgard.Examples.ExternalBlend.circuit.Rel
    Gimle.Asgard.Examples.ExternalBlend.environment ![1/4,3/4,7] ![5/8,3/8] :=
  Gimle.Asgard.Examples.ExternalBlend.concrete_output

#print axioms Source.compile_rel
#print axioms Source.partition_contract
#print axioms Source.partition_postcompose
end Gimle.Asgard.Tests.External
