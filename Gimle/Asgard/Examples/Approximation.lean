import Gimle.Asgard.Approximation
import Gimle.Asgard.Compile.Polynomial

/-! The secant x approximates x² on [0,1] with sharp error 1/4.
Composing the source with 3z and the target with 3z+1/10 amplifies the
upstream error: 3*(1/4)+1/10 = 17/20, attained at x=1/2.
These are universal circuit facts; the endpoint sample record is only data. -/
namespace Gimle.Asgard.Examples.Approximation
open Gimle.Asgard.Approximation

def square : Circuit 1 1 := .compose .split .multiplication
def unitRegion (x : Point 1) : Prop := 0 ≤ x 0 ∧ x 0 ≤ 1

def secantClaim : Claim 1 1 where
  source := square
  target := .id
  region := unitRegion
  error := ⟨1/4, by norm_num⟩

theorem secant_bound : secantClaim.Holds := by
  intro x hx i
  fin_cases i
  norm_num [secantClaim, square]
  rcases hx with ⟨h0,h1⟩
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x 0 - 1/2), mul_nonneg h0 (sub_nonneg.mpr h1)]

def postSource : Circuit 1 1 := .scalar 3
def postTarget : Circuit 1 1 := Polynomial.compileOutputs
  ![.add (.mul (.constant 3) (.var 0)) (.constant (1/10))]
def postClaim : Claim 1 1 where
  source := postSource
  target := postTarget
  region := unitRegion
  error := ⟨1/10, by norm_num⟩
def gain : Budget := ⟨3, by norm_num⟩

theorem post_bound : postClaim.Holds := by
  intro x _ i
  fin_cases i
  norm_num [postClaim, postSource, postTarget, Polynomial.Expr.eval]

theorem post_lipschitz : LipschitzOn postSource unitRegion gain := by
  intro a b _ _ delta _ h i
  fin_cases i
  change |(3 : ℝ)*a 0 - 3*b 0| ≤ 3*delta
  rw [show (3 : ℝ)*a 0-3*b 0 = 3*(a 0-b 0) by ring, abs_mul]
  norm_num
  exact h 0

theorem intermediate_coverage (x : Point 1) (hx : unitRegion x) :
    unitRegion (square.run x) ∧ unitRegion (Circuit.id.run x) := by
  rcases hx with ⟨h0,h1⟩
  simp [unitRegion, square]
  constructor
  · constructor <;> nlinarith [sq_nonneg (x 0), mul_nonneg h0 (sub_nonneg.mpr h1)]
  · exact ⟨h0,h1⟩

def amplifiedClaim : Claim 1 1 := secantClaim.compose postClaim gain

theorem amplified_bound : amplifiedClaim.Holds :=
  Claim.compose_holds secantClaim postClaim gain secant_bound post_bound post_lipschitz intermediate_coverage

theorem amplified_allowance : amplifiedClaim.error.value = 17/20 := by
  norm_num [amplifiedClaim, Claim.compose, secantClaim, postClaim, gain, Budget.add, Budget.mul]

theorem sharp_error : |amplifiedClaim.source.run ![1/2] 0 - amplifiedClaim.target.run ![1/2] 0| = 17/20 := by
  norm_num [amplifiedClaim, Claim.compose, secantClaim, postClaim, postSource, postTarget,
    square, Polynomial.Expr.eval]

/-- These samples fit exactly, but no universal certificate is stored here. -/
def endpointObservations : Observation square Circuit.id where
  datasetId := "unit-interval-endpoints/v1"
  regionDescription := "0 <= x <= 1; samples only x=0 and x=1"
  interpretation := interpretationName
  metric := metricName
  samples := #[⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, ⟨fun _ => 1, fun _ => 1, fun _ => 1⟩]
  measuredMaximum := 0
  fittingLoss := 0
  statisticalConfidence := none
  provenance := "Two declared endpoint observations; no universal authority"

theorem endpoint_values : square.run ![0] = Circuit.id.run ![0] ∧
    square.run ![1] = Circuit.id.run ![1] := by
  constructor <;> funext i <;> fin_cases i <;> norm_num [square]

theorem interior_error : |square.run ![1/2] 0 - Circuit.id.run ![1/2] 0| = 1/4 := by
  norm_num [square]

#print axioms secant_bound
#print axioms post_lipschitz
#print axioms amplified_bound
#print axioms sharp_error
end Gimle.Asgard.Examples.Approximation
