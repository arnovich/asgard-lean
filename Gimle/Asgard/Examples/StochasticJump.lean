import Gimle.Asgard.Stochastic.FiniteJump
import Mathlib.Tactic

/-! A genuine finite-jump equation, with no sampling or assumed solution theorem:

    dX(t) = X(t-) dJ(t),   X(0) = 2,
    J(t) = 0 for t < 1, and 3 for t ≥ 1, on 0 ≤ t ≤ 2.

The pre-jump state is 2, hence ΔX(1) = 2·3 = 6 and X(1) = 8.
We prove the named source equation and the compiled initialized circuit admit
this trajectory. Brownian integration and probability bounds are not used. -/
namespace Gimle.Asgard.Examples.StochasticJump
open Stochastic Polynomial
open scoped BigOperators Topology

abbrev system : NamedSystem 1 0 0 1 := {
  inputs := ![⟨"state-x", "x", .state⟩]
  noiseIds := Fin.elim0
  jumpIds := !["jump-J"]
  axis := "physical-time"
  calculus := .ito
  jumpConvention := .uncompensated
  drift := fun _ => .constant 0
  diffusion := Fin.elim0
  jump := fun _ _ => .var "x"
}

def prepared : Prepared system := system.prepare.get (by decide)

abbrev schedule : JumpSchedule Unit := ⟨1, ![1], fun _ _ => 3⟩
def time : Window := ⟨"physical-time", 0, 2, by norm_num⟩
noncomputable def context : Context Unit 0 1 := {
  time := time
  integrals := schedule.semantics
  noise := Fin.elim0
  jumps := fun _ => schedule.path
  admissible := True
}

noncomputable def trajectory : Process Unit 1 := fun t _ _ => if t < 1 then 2 else 8
noncomputable def input : Process Unit (1 + 0) := append trajectory (fun _ _ => Fin.elim0)

lemma trajectory_monotone : Monotone (fun t : ℝ => if t < 1 then (2 : ℝ) else 8) := by
  intro a b h
  dsimp only
  split_ifs <;> linarith

lemma input_left_limits : HasLeftLimits time input := by
  intro t _ ω i
  refine ⟨Function.leftLim (fun r => if r < 1 then (2 : ℝ) else 8) t, ?_⟩
  simpa [input, append, trajectory, pointAppend] using trajectory_monotone.tendsto_leftLim t

lemma before_jump (ω : Unit) : before input 1 ω 0 = 2 := by
  change Function.leftLim (fun r => if r < 1 then (2 : ℝ) else 8) 1 = 2
  apply leftLim_eq_of_tendsto
  apply Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (2 : ℝ)) _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Set.mem_Iio] at hr
  simp [hr]

@[simp] lemma kind_time : system.kind 0 = .time := rfl
@[simp] lemma kind_jump : system.kind 1 = .jump .uncompensated 0 := rfl

lemma fields (k : Channels 0 1) (x : Point 1) :
    (prepared.field k).run x = fun _ => if k = 0 then 0 else x 0 := by
  have he : prepared.expressions = (fun k : Fin 2 => fun _ : Fin 1 =>
      if k = 0 then Expr.constant (n := 1) 0 else .var 0) := by decide
  simp only [Prepared.field, compileOutputs_correct, he]
  funext i
  split_ifs <;> simp [Expr.eval]

noncomputable def integrals : Channels 0 1 → Process Unit 1 :=
  fun k t _ _ => if k = 0 then 0 else if 1 ≤ t then 6 else 0

lemma integral_at_jump (t : ℝ) (ω : Unit) :
    schedule.integral time.start (fun r ω => before input r ω 0) t ω =
      if 1 ≤ t then 6 else 0 := by
  change (∑ k : Fin 1, if (0 : ℝ) < schedule.times k ∧ schedule.times k ≤ t then
    before input (schedule.times k) ω 0 * schedule.marks k ω else 0) = _
  rw [Fin.sum_univ_one]
  change (if (0 : ℝ) < 1 ∧ 1 ≤ t then before input 1 ω 0 * 3 else 0) = _
  rw [before_jump]
  norm_num

lemma source_increments : system.Increments context input
    (fun t ω i => ∑ k, integrals k t ω i) := by
  apply prepared.increments_of_integrals context input integrals trivial rfl
  · intro k _
    exact input_left_limits
  · intro k i
    fin_cases k
    · simpa [kind_time, Context.integral, context, JumpSchedule.semantics,
        fields, sample, IntegralKind.predictable, integrals] using
        ordinaryIntegral_zero (Ω := Unit) time
    · change schedule.semantics.uncompensated time schedule.path
        (fun t ω => (prepared.field 1).run (sample (system.kind 1) input t ω) i)
        (fun t ω => integrals 1 t ω i)
      refine ⟨rfl, ?_⟩
      intro t _ ω
      have hf : (fun t ω => (prepared.field 1).run (sample (system.kind 1) input t ω) i) =
          (fun t ω => before input t ω 0) := by
        funext t ω
        rw [fields]
        rfl
      rw [hf]
      exact (integral_at_jump t ω).symm

/-- Exact solution of the independent named integral equations. -/
theorem source_solution : system.Solves context (fun _ _ => Fin.elim0)
    (fun _ => ![2]) trajectory := by
  refine ⟨_, source_increments, ?_, ?_⟩
  · intro ω
    ext i
    simp [trajectory, context, time]
  · intro t _ ω i
    fin_cases i
    change trajectory t ω 0 = 2 + ∑ k : Fin 2, integrals k t ω 0
    rw [Fin.sum_univ_two]
    by_cases h : t < 1
    · norm_num [trajectory, integrals, h, not_le.mpr h]
    · norm_num [trajectory, integrals, h, le_of_not_gt h]

/-- The actual compiled circuit, including physical-time initialization and
feedback, has the same solution. -/
theorem circuit_solution : prepared.compile.close.Rel context
    (append (fun _ _ => Fin.elim0) (fun _ _ => ![2])) trajectory :=
  (prepared.solves_iff_circuit context _ _ trajectory).mp source_solution

-- Reading the post-jump value would predict 8·3 = 24 instead of ΔX = 6.
example : trajectory 1 () 0 = 8 := by norm_num [trajectory]
example : trajectory 1 () 0 - 2 ≠ trajectory 1 () 0 * 3 := by norm_num [trajectory]
example : before input 1 () 0 * 3 = trajectory 1 () 0 - 2 := by rw [before_jump]; norm_num [trajectory]

#print axioms before_jump
#print axioms source_solution
#print axioms circuit_solution
end Gimle.Asgard.Examples.StochasticJump
