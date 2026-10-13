import Gimle.Asgard.Examples.Approximation

namespace Gimle.Asgard.Tests.Approximation
open Gimle.Asgard.Approximation
open Gimle.Asgard.Examples.Approximation

example : Budget.ofRat (-1) = none := by decide
example : (Budget.ofRat (1/4)).map Budget.value = some (1/4) := by norm_num [Budget.ofRat]
example (b : Budget) : b.value ≠ -1 := by
  intro h
  have hn := b.nonnegative
  rw [h] at hn
  norm_num at hn

/-- Legacy coordinatewise facts may be vacuous; claims still require Budget. -/
example : QuantitativeCircuitEquivalence Circuit.terminal Circuit.terminal (fun _ => True) (-1) := by
  intro _ _ i; exact Fin.elim0 i
example : QuantitativeCircuitEquivalence Circuit.id Circuit.id (fun _ => False) (-1) := by
  intro _ h; exact h.elim

example : Context.parse "asgard.feedforward.real.v1" "linf" = .ok {} := by decide
example : Context.parse "asgard.feedforward.real.v1" "l2" =
    .error "Unsupported approximation interpretation or metric" := by decide
example : Context.parse "asgard.formal-product-stream.ogf/v1" "linf" =
    .error "Unsupported approximation interpretation or metric" := by decide

example : ¬ QuantitativeCircuitEquivalence square Circuit.id unitRegion (1/8) := by
  intro h
  have hd := h ![1/2] (by norm_num [unitRegion]) 0
  rw [interior_error] at hd
  norm_num at hd
example : ¬ QuantitativeCircuitEquivalence square Circuit.id unitRegion 0 := by
  intro h
  have hd := h ![1/2] (by norm_num [unitRegion]) 0
  rw [interior_error] at hd
  norm_num at hd

/-- Omitting downstream amplification would claim 1/4+1/10=7/20. -/
example : ¬ QuantitativeCircuitEquivalence amplifiedClaim.source amplifiedClaim.target unitRegion (7/20) := by
  intro h
  have hd := h ![1/2] (by norm_num [unitRegion]) 0
  rw [sharp_error] at hd
  norm_num at hd

example : ¬ ({amplifiedClaim with error := ⟨4/5, by norm_num⟩} : Claim 1 1).Holds := by
  intro h
  have hd := h ![1/2] (by norm_num [amplifiedClaim, Claim.compose, secantClaim, unitRegion]) 0
  change |amplifiedClaim.source.run ![1/2] 0-amplifiedClaim.target.run ![1/2] 0| ≤ ((4/5 : ℚ) : ℝ) at hd
  rw [sharp_error] at hd
  norm_num at hd

def zeroCircuit : Circuit 1 1 := .compose .terminal (.const 0)

theorem singleton_equal : QuantitativeCircuitEquivalence Circuit.id zeroCircuit (fun x => x 0 = 0) 0 := by
  intro x hx i
  fin_cases i
  simp [zeroCircuit, hx]

example : ¬ GlobalCircuitEquivalence Circuit.id zeroCircuit := by
  intro h
  have hd := congrFun (h ![1]) 0
  norm_num [zeroCircuit] at hd

example : QuantitativeCircuitEquivalence (.compose (.scalar 0) .id)
    (.compose (.scalar 0) zeroCircuit) (fun _ => True) 0 := by
  apply precompose (.scalar 0) singleton_equal
  intro x _; simp

/-- Producing an input outside the certified singleton region invalidates reuse. -/
example : ¬ QuantitativeCircuitEquivalence (.compose (.scalar 1) .id)
    (.compose (.scalar 1) zeroCircuit) (fun _ => True) 0 := by
  intro h
  have hd := h ![1] trivial 0
  norm_num [zeroCircuit] at hd

example : ¬ QuantitativeCircuitEquivalence (.compose (.scalar 3) square)
    (.compose (.scalar 3) .id) unitRegion (1/4) := by
  intro h
  have hd := h ![1] (by norm_num [unitRegion]) 0
  norm_num [square] at hd

/-- Two unequal nonzero component errors use max, not addition or l2. -/
def pairedSource : Circuit 0 2 := .parallel (.const 0) (.const 0)
def pairedTarget : Circuit 0 2 := .parallel (.const (3/5)) (.const (4/5))
theorem paired_bound : QuantitativeCircuitEquivalence pairedSource pairedTarget (fun _ => True) (4/5) := by
  have a : QuantitativeCircuitEquivalence (.const 0) (.const (3/5)) (fun _ => True) (3/5) := by
    intro x _ i; fin_cases i; norm_num
  have b : QuantitativeCircuitEquivalence (.const 0) (.const (4/5)) (fun _ => True) (4/5) := by
    intro x _ i; fin_cases i; norm_num
  simpa only [max_eq_right (by norm_num : (3/5 : ℝ) ≤ 4/5), and_self,
    pairedSource, pairedTarget] using parallel a b

example : (∑ i : Fin 2, (pairedSource.run ![] i - pairedTarget.run ![] i)^2) = 1 := by
  norm_num [Fin.sum_univ_two, pairedSource, pairedTarget]
example : (4/5 : ℝ)^2 < 1 := by norm_num

example : endpointObservations.measuredMaximum = 0 := rfl
example : square.run ![0] = Circuit.id.run ![0] ∧ square.run ![1] = Circuit.id.run ![1] := endpoint_values

#print axioms amplified_bound
#print axioms paired_bound
#print axioms singleton_equal
end Gimle.Asgard.Tests.Approximation
