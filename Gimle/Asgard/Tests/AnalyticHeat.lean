import Gimle.Asgard.Examples.ExpHeat

/-! Coverage for heat streams of analytic profiles (task 026).

Pinned here: the profile round-trips through either basis; a polynomial profile
reproduces 024's `Heat.stream`; the circuit reconstructs only the constructed
stream; a profile violating its claimed bound has no profile bound, and a
profile with a finite radius of convergence has a divergent heat series inside
every would-be box, so no certificate of any majorant covers that point; boxes
on or beyond the radii `[ρ², ρ]` are rejected; and a transitive standard-axiom
audit of every public theorem. -/

namespace Gimle.Asgard.Tests.AnalyticHeat

open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.AnalyticHeat

/-! ### Representation -/

/-- The profile is recovered from its stream in either basis. -/
example (basis : Basis) (g : ℕ → ℚ) : coeffs basis (profile basis g) = g := coeffs_profile basis g

/-- `e^x` as a one-axis EGF stream is all ones; as an OGF stream it is `1/j!`. -/
example (α : Index 1) : profile .egf Examples.ExpHeat.g α = 1 := profile_egf_apply _ α

example (α : Index 1) :
    profile .ogf Examples.ExpHeat.g α = 1 / ((α 0).factorial : ℚ) := profile_ogf_apply _ α

/-- The OGF heat coefficient at `(n, k) = (1, 2)` of `e^x` is `1/(1!·2!)`. -/
example : stream .ogf Examples.ExpHeat.g (Finsupp.single 0 1 + Finsupp.single 1 2) = 1 / 2 := by
  rw [stream_ogf_apply]
  simp [Examples.ExpHeat.g]

/-- The boundary carries the profile on `t = 0` and nothing at positive `t`-degree. -/
example (g : ℕ → ℚ) : boundary .egf g (Finsupp.single 0 1) = 0 := by
  rw [boundary_egf_apply]
  simp

/-! ### Agreement with polynomial profiles -/

/-- `x²` has raw EGF coefficients `(0, 0, 2, 0, …)` and heat stream `x² + 2t`,
exactly 024's. -/
example (basis : Basis) :
    stream basis (ofPolynomial (_root_.Polynomial.X ^ 2)) =
      Heat.stream basis (_root_.Polynomial.X ^ 2) :=
  stream_ofPolynomial basis _

example : ofPolynomial (_root_.Polynomial.X ^ 2 : Heat.Profile) 2 = 2 := by
  simp [ofPolynomial, _root_.Polynomial.coeff_X_pow]

/-! ### The circuit reconstructs only the constructed stream -/

/-- A stream reconstructed from the `e^x` boundary is the `e^(x+t)` stream. -/
example (basis : Basis) (a unused v : Stream 2)
    (rel : (Heat.circuit basis).Rel ![a, boundary basis Examples.ExpHeat.g, unused] ![v, a]) :
    a = stream basis Examples.ExpHeat.g :=
  candidate_stream basis _ a unused v rel

/-- Changing the boundary changes the reconstructed stream: the `e^x` heat
stream is not reconstructed from the zero profile. -/
example (basis : Basis) (unused v : Stream 2) :
    ¬ (Heat.circuit basis).Rel ![stream basis Examples.ExpHeat.g, boundary basis (fun _ => 0),
      unused] ![v, stream basis Examples.ExpHeat.g] := by
  intro rel
  have h := congrFun (congrArg (decode basis) (candidate_stream basis _ _ unused v rel)) 0
  simp [series, Examples.ExpHeat.g, factorial] at h

/-! ### A violated bound gives no certificate -/

/-- `g_j = 2^j` claims `M = ρ = 1` and fails at `j = 1`. -/
example : ¬ ProfileBound (fun j => 2 ^ j) 1 1 := by
  intro h
  have := h 1
  norm_num at this

/-- `g_j = j!·4^j`: the profile `1/(1 − 4x)`, radius of convergence `1/4`. -/
def hostile : ℕ → ℚ := fun j => (j.factorial : ℚ) * 4 ^ j

private theorem single_one_apply_zero (k : ℕ) : (Finsupp.single (1 : Fin 2) k) 0 = 0 := by
  simp

/-- At `(t, x) = (0, 1/2)` its heat series diverges: the terms along `t`-degree
`0` are `4^k · (1/2)^k = 2^k`. -/
theorem hostile_diverges (basis : Basis) :
    ¬ Summable (seriesTerm basis (stream basis hostile) ![0, 1 / 2]) := by
  intro summable
  have along :=
    (summable.comp_injective (Finsupp.single_injective (1 : Fin 2))).tendsto_atTop_zero
  have big : ∀ k, (seriesTerm basis (stream basis hostile) ![0, 1 / 2] ∘
      Finsupp.single (1 : Fin 2)) k = 2 ^ k := by
    intro k
    simp only [Function.comp_apply, seriesTerm, decode_stream, series, hostile, factorial,
      Fin.prod_univ_two, single_one_apply_zero, Finsupp.single_eq_same, Matrix.cons_val_zero,
      Matrix.cons_val_one, pow_zero, mul_zero, add_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    have : ((k.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    rw [mul_div_cancel_left₀ _ this]
    push_cast
    rw [← mul_pow]
    norm_num
  rw [funext big] at along
  have := along.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨k, hk⟩ := this.exists
  linarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := k) (by norm_num)]

/-- No certificate of any majorant covers `(0, 1/2)`. -/
theorem hostile_uncertifiable (basis : Basis) (c : TailCertificate basis (stream basis hostile)) :
    ¬ c.box.Mem ![0, 1 / 2] :=
  fun mem => hostile_diverges basis (c.summable_norm mem).of_norm

/-- Hence no profile bound with `ρ = 1` holds for it, whatever `M` is claimed. -/
theorem hostile_not_bounded (M : ℚ) (hM : 0 ≤ M) : ¬ ProfileBound hostile M 1 := by
  intro bound
  refine hostile_uncertifiable .ogf
    (certificate .ogf hM (by norm_num) bound Examples.ExpHeat.box ?_) ?_
  · exact Examples.ExpHeat.inside
  · intro i
    fin_cases i <;> norm_num [certificate, Examples.ExpHeat.box]

/-! ### Boxes on or beyond the radii are rejected -/

/-- `r_x = ρ`: on the spatial radius. -/
def onRadius : Box 2 := ⟨![1 / 2, 1], fun i => by fin_cases i <;> norm_num⟩

/-- `r_t = 2 > ρ² = 1`: beyond the time radius. -/
def beyond : Box 2 := ⟨![2, 1 / 2], fun i => by fin_cases i <;> norm_num⟩

example : ¬ ∀ i, onRadius.radius i < Examples.ExpHeat.majorant.radius i := by
  decide +kernel

example : ¬ ∀ i, beyond.radius i < Examples.ExpHeat.majorant.radius i := by
  decide +kernel

/-- The time radius is `ρ²`, not `ρ`: with `ρ = 1/2`, `r_t = 1/3` is rejected
even though `1/3 < ρ`. -/
example : ¬ (∀ i, (⟨![1 / 3, 1 / 4], fun i => by fin_cases i <;> norm_num⟩ : Box 2).radius i <
    (heatMajorant 1 (1 / 2) (by norm_num) (by norm_num)).radius i) := by
  rw [inside_iff]
  norm_num

/-! ### Transitive axiom audit -/

/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.coeffs_profile'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.coeffs_profile
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.profile_coeffs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.profile_coeffs
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.stream_egf_apply'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.stream_egf_apply
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.stream_ogf_apply'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.stream_ogf_apply
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.boundary_egf_apply'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.AnalyticHeat.boundary_egf_apply
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.decode_boundary_apply'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.AnalyticHeat.decode_boundary_apply
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.stream_pde'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.stream_pde
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.stream_slice'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.stream_slice
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.circuit_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.circuit_stream
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.candidate_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.candidate_stream
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.boundary_ofPolynomial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.AnalyticHeat.boundary_ofPolynomial
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.stream_ofPolynomial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.AnalyticHeat.stream_ofPolynomial
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.inside_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.inside_iff
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.majorizes_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.majorizes_stream
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.certificate_error'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.certificate_error
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.truncationBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.truncationBound
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.analyticField_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.AnalyticHeat.analyticField_stream
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.windowField_stream'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Streams.AnalyticHeat.windowField_stream
/--
info: 'Gimle.Asgard.Examples.ExpHeat.stream_egf'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.stream_egf
/--
info: 'Gimle.Asgard.Examples.ExpHeat.profileBound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.profileBound
/--
info: 'Gimle.Asgard.Examples.ExpHeat.inside'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.inside
/--
info: 'Gimle.Asgard.Examples.ExpHeat.error_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.error_eq
/--
info: 'Gimle.Asgard.Examples.ExpHeat.bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.bound
/--
info: 'Gimle.Asgard.Examples.ExpHeat.hasSum_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.hasSum_field
/--
info: 'Gimle.Asgard.Examples.ExpHeat.analyticField_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.analyticField_eq
/--
info: 'Gimle.Asgard.Examples.ExpHeat.exp_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Examples.ExpHeat.exp_bound
/--
info: 'Gimle.Asgard.Tests.AnalyticHeat.hostile_uncertifiable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Asgard.Tests.AnalyticHeat.hostile_uncertifiable
/--
info: 'Gimle.Asgard.Tests.AnalyticHeat.hostile_not_bounded'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Tests.AnalyticHeat.hostile_not_bounded


/-! ### Exponential sums and root claims -/

/-- `e^x` as an exponential sum is the example's profile. -/
example : expSum [(1, 1)] = Examples.ExpHeat.g := by
  funext j; simp [expSum, Examples.ExpHeat.g]

/-- `cosh x = (e^x + e^(−x))/2`: raw coefficients alternate `1, 0, 1, 0, …`. -/
example : expSum [(1 / 2, 1), (1 / 2, -1)] 3 = 0 ∧ expSum [(1 / 2, 1), (1 / 2, -1)] 4 = 1 := by
  decide +kernel

/-- The fit check refuses a rate too large for the radius: `e^(2x)` at `ρ = 1`. -/
example : expSumFits [(1, 2)] 1 = false := by decide +kernel

/-- The root claim for `e^x`, every side condition decided by the kernel: every
reconstruction from the `e^x` boundary is within `1/1000` of its window on the
example box. -/
example (basis : Basis) :
    ∀ a unused v : Stream 2,
      (Heat.circuit basis).Rel ![a, boundary basis (expSum [(1, 1)]), unused] ![v, a] →
        TruncationBound basis a Examples.ExpHeat.box Examples.ExpHeat.window (1 / 1000) :=
  expSum_truncation basis [(1, 1)] (ρ := 1) (by decide +kernel) (by decide +kernel)
    Examples.ExpHeat.box (by decide +kernel) Examples.ExpHeat.window (by decide +kernel)

/-- `cosh x` on `|t| ≤ 1/4`, `|x| ≤ 1/2` at window `[8, 16]`: the weight is
`1/2 + 1/2 = 1`, so the certified bound equals the `e^x` one. -/
example (basis : Basis) :
    ∀ a unused v : Stream 2,
      (Heat.circuit basis).Rel
          ![a, boundary basis (expSum [(1 / 2, 1), (1 / 2, -1)]), unused] ![v, a] →
        TruncationBound basis a Examples.ExpHeat.box Examples.ExpHeat.window (1 / 12288) :=
  expSum_truncation basis _ (ρ := 1) (by decide +kernel) (by decide +kernel)
    Examples.ExpHeat.box (by decide +kernel) Examples.ExpHeat.window (by decide +kernel)

/-- An `ε` below the certified bound has no proof by this route: the side
condition is false. -/
example : ¬ tailBound (heatMajorant (expSumWeight [(1, 1)]) 1 (expSumWeight_nonneg _)
    (by decide +kernel)) Examples.ExpHeat.box Examples.ExpHeat.window ≤ 1 / 20000 := by
  decide +kernel

/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.profileBound_expSum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.profileBound_expSum
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.circuit_truncation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.circuit_truncation
/--
info: 'Gimle.Asgard.Streams.AnalyticHeat.expSum_truncation'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Asgard.Streams.AnalyticHeat.expSum_truncation
end Gimle.Asgard.Tests.AnalyticHeat
