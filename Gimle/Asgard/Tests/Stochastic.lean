import Gimle.Asgard.Examples.StochasticJump

import Gimle.Asgard.Stochastic.Named
import Gimle.Asgard.Stochastic.FiniteJump

namespace Gimle.Asgard.Tests.Stochastic
open Gimle.Asgard.Stochastic Polynomial

-- The compiler must preserve the complete increment and initialized solution
-- relations for every admitted integral interpretation and shared driver family.
example {n d w j : Nat} (s : NamedSystem n d w j) (p : Prepared s)
    {Ω : Type} (ctx : Context Ω w j) (u : Process Ω d)
    (initial : Ω → Point n) (x : Process Ω n) :
    s.Solves ctx u initial x ↔ (p.compile.close).Rel ctx
      (append u (fun _ => initial)) x := p.solves_iff_circuit ctx u initial x

end Gimle.Asgard.Tests.Stochastic

namespace Gimle.Asgard.Tests.Stochastic
open Gimle.Asgard.Stochastic Polynomial
open scoped BigOperators Topology

-- Asymmetric state order [y,x], an ordinary driver named u0, one unused
-- external, repeated state references, and two noise columns shared by states.
abbrev coupled : NamedSystem 2 2 2 0 := {
  inputs := ![⟨"sy", "y", .state⟩, ⟨"sx", "x", .state⟩,
    ⟨"driver", "u0", .driver⟩, ⟨"unused", "unused", .parameter⟩]
  noiseIds := !["shared-W", "second-W"]
  jumpIds := Fin.elim0
  axis := "physical-time"
  calculus := .ito
  jumpConvention := .uncompensated
  drift := ![.add (.add (.add (.var "y") (.var "y")) (.var "x")) (.var "u0"),
    .add (.var "x") (.neg (.var "y"))]
  diffusion := ![![.add (.var "y") (.var "x"), .mul (.constant 2) (.var "y")],
    ![.mul (.constant 3) (.var "x"), .constant 1]]
  jump := Fin.elim0
}

def coupledPrepared : Prepared coupled := coupled.prepare.get (by decide)

-- These are actual compiled circuit outputs, not metadata comparisons.
lemma coupled_fields (x : Point 4) (k : Channels 2 0) :
    (coupledPrepared.field k).run x =
      (![![x 0 + x 0 + x 1 + x 2, x 1 - x 0],
          ![x 0 + x 1, 2*x 0], ![3*x 1, 1]] : Fin 3 → Point 2) k := by
  have es : coupledPrepared.expressions =
      (![![Expr.add (.add (.add (.var 0) (.var 0)) (.var 1)) (.var 2),
          .add (.var 1) (.neg (.var 0))],
        ![.add (.var 0) (.var 1), .mul (.constant 2) (.var 0)],
        ![.mul (.constant 3) (.var 1), .constant 1]] : Fin 3 → Fin 2 → Expr 4) := by decide
  simp only [Prepared.field, compileOutputs_correct, es]
  funext i
  fin_cases k <;> fin_cases i <;> simp [Expr.eval, sub_eq_add_neg]

example : (coupledPrepared.field 0).run ![2,5,7,11] = ![16,3] := by
  rw [coupled_fields]
  simp only [Matrix.cons_val]
  norm_num
example : (coupledPrepared.field 1).run ![2,5,7,11] = ![7,4] := by
  rw [coupled_fields]
  simp only [Matrix.cons_val]
  norm_num
example : (coupledPrepared.field 2).run ![2,5,7,11] = ![15,1] := by
  rw [coupled_fields]
  simp only [Matrix.cons_val]
  norm_num
example : (coupledPrepared.field 0).run ![2,5,7,11] ≠
    (coupledPrepared.field 0).run ![5,2,7,11] := by
  rw [coupled_fields, coupled_fields]
  intro h
  have := congrFun h 1
  norm_num at this
example (unused : ℝ) (k : Channels 2 0) :
    (coupledPrepared.field k).run ![2,5,7,unused] =
      (coupledPrepared.field k).run ![2,5,7,11] := by simp only [coupled_fields]; rfl

#guard ({ coupled with inputs := ![⟨"sy","y",.state⟩,⟨"sx","y",.state⟩,
  ⟨"driver","u0",.driver⟩,⟨"unused","unused",.parameter⟩] } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with inputs := ![⟨"sy","y",.state⟩,⟨"sy","x",.state⟩,
  ⟨"driver","u0",.driver⟩,⟨"unused","unused",.parameter⟩] } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with noiseIds := !["W","W"] } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with noiseIds := !["W",""] } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with axis := "" } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with drift := fun _ => .var "missing" } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with diffusion := fun _ _ => .var "missing" } : NamedSystem 2 2 2 0).prepare.isNone
#guard ({ coupled with inputs := ![⟨"sy","y",.state⟩,⟨"sx","x",.state⟩,
  ⟨"driver","u0",.initial⟩,⟨"unused","unused",.parameter⟩] } : NamedSystem 2 2 2 0).prepare.isNone

-- Deliberately synthetic relations test dispatch/wiring only. They are NOT an
-- Itô/Stratonovich realization or stochastic calculus correction theorem.
def dispatch : IntegralSemantics Unit where
  time := fun _ f y => y = f
  ito := fun _ driver f y => y = fun t ω => f t ω * driver t ω
  stratonovich := fun _ driver f y => y = fun t ω => f t ω * driver t ω + 1
  uncompensated := fun _ driver f y => y = fun t ω => f t ω * driver t ω + 2
  compensated := fun _ driver f y => y = fun t ω => f t ω * driver t ω + 3

def dispatchContext : Context Unit 2 0 := {
  time := ⟨"physical-time",0,1,by norm_num⟩
  integrals := dispatch
  noise := fun k _ _ => if k = 0 then 2 else 3
  jumps := Fin.elim0
  admissible := True
}

example : (Gimle.Asgard.Stochastic.Circuit.integrate (.noise .ito 0) 1).Rel dispatchContext
    (fun _ _ => ![5]) (fun _ _ => ![10]) := by
  intro i
  norm_num [Context.integral, dispatchContext, dispatch]
example : ¬ (Gimle.Asgard.Stochastic.Circuit.integrate (.noise .stratonovich 0) 1).Rel dispatchContext
    (fun _ _ => ![5]) (fun _ _ => ![10]) := by
  intro h
  have bad := congrFun (congrFun (h 0) 0) ()
  norm_num [Context.integral, dispatchContext, dispatch] at bad
example : ¬ (Gimle.Asgard.Stochastic.Circuit.integrate (.noise .ito 1) 1).Rel dispatchContext
    (fun _ _ => ![5]) (fun _ _ => ![10]) := by
  intro h
  have bad := congrFun (congrFun (h 0) 0) ()
  norm_num [Context.integral, dispatchContext, dispatch] at bad

-- A stochastic context is not admitted merely because coefficients compile.
example (x : Process Unit 4) (y : Process Unit 2) :
    ¬ coupledPrepared.compile.Rel { dispatchContext with admissible := False } x y := by
  simp [Prepared.compile, Gimle.Asgard.Stochastic.Circuit.Rel]
example (x : Process Unit 4) (y : Process Unit 2) :
    ¬ coupledPrepared.compile.Rel
      { dispatchContext with time := ⟨"wrong-axis",0,1,by norm_num⟩ } x y := by
  simp [Prepared.compile, Gimle.Asgard.Stochastic.Circuit.Rel]

-- Empty state/external/noise/jump contexts remain dimensionally well formed.
def empty : NamedSystem 0 0 0 0 := {
  inputs := Fin.elim0, noiseIds := Fin.elim0, jumpIds := Fin.elim0,
  axis := "t", calculus := .ito, jumpConvention := .uncompensated,
  drift := Fin.elim0, diffusion := Fin.elim0, jump := Fin.elim0
}
#guard empty.prepare.isSome

end Gimle.Asgard.Tests.Stochastic

namespace Gimle.Asgard.Tests.Stochastic
open Gimle.Asgard.Stochastic Polynomial
open Examples.StochasticJump

-- Reusing the valid trajectory with a different initial value fails on the
-- closed target circuit, rather than merely changing a descriptor.
example : ¬ prepared.compile.close.Rel context
    (append (fun _ _ => Fin.elim0) (fun _ _ => ![3])) trajectory := by
  rw [Gimle.Asgard.Stochastic.Circuit.close_correct]
  rintro ⟨_, _, hi, _⟩
  have bad := congrFun (hi ()) 0
  norm_num [trajectory, context, time] at bad

example : ¬ schedule.semantics.uncompensated time (fun _ _ => 0)
    (fun _ _ => 2) (fun _ _ => 0) := by
  intro h
  have bad := congrFun (congrFun (schedule.driver_bound time _ _ _ h) 1) ()
  norm_num [JumpSchedule.path, schedule] at bad

-- The actual finite-jump interpretation has no Brownian/compensated fallback.
example (driver f y : ScalarProcess Unit) : ¬ schedule.semantics.ito time driver f y := by
  simp [JumpSchedule.semantics]
example (driver f y : ScalarProcess Unit) : ¬ schedule.semantics.compensated time driver f y := by
  simp [JumpSchedule.semantics]

-- Exact event/horizon endpoints: a jump at the end counts, one at the start does not.
example : schedule.integral 0 (fun _ _ => 2) 1 () = 6 := by
  change (∑ k : Fin 1, if (0 : ℝ) < schedule.times k ∧ schedule.times k ≤ 1 then
    2 * schedule.marks k () else 0) = 6
  rw [Fin.sum_univ_one]
  simp only [Matrix.cons_val]
  norm_num
example : schedule.integral 0 (fun _ _ => 2) (1/2) () = 0 := by
  change (∑ k : Fin 1, if (0 : ℝ) < schedule.times k ∧ schedule.times k ≤ 1/2 then
    2 * schedule.marks k () else 0) = 0
  rw [Fin.sum_univ_one]
  simp only [Matrix.cons_val]
  norm_num
example : schedule.integral 1 (fun _ _ => 2) 1 () = 0 := by
  change (∑ k : Fin 1, if (1 : ℝ) < schedule.times k ∧ schedule.times k ≤ 1 then
    2 * schedule.marks k () else 0) = 0
  rw [Fin.sum_univ_one]
  simp only [Matrix.cons_val]
  norm_num

abbrev compensatedSystem : NamedSystem 1 0 0 1 := { system with jumpConvention := .compensated }
example (u : Process Unit 0) (initial : Unit → Point 1) (x : Process Unit 1) :
    ¬ compensatedSystem.Solves context u initial x := by
  rintro ⟨_, ⟨_, _, _, _, _, _, hi, _⟩, _⟩
  exact hi 1 0

end Gimle.Asgard.Tests.Stochastic

namespace Gimle.Asgard.Tests.Stochastic
open Gimle.Asgard.Stochastic Polynomial
open scoped BigOperators Topology

lemma constant_limits {Ω : Type} {n : Nat} (time : Window) (x : Point n) :
    HasLeftLimits (Ω := Ω) time (fun _ _ => x) := by
  intro t _ ω i
  exact ⟨x i, tendsto_const_nhds⟩

lemma before_constant {Ω : Type} {n : Nat} (x : Point n) :
    before (Ω := Ω) (fun _ _ => x) = fun _ _ => x := by
  funext t ω i
  exact leftLim_eq_of_tendsto tendsto_const_nhds

/-- Changing calculus preserves the already checked coefficient resolution. -/
def preparedFor (c : Calculus) : Prepared ({ coupled with calculus := c } : NamedSystem 2 2 2 0) := {
  valid := coupledPrepared.valid
  expressions := coupledPrepared.expressions
  resolved := coupledPrepared.resolved
}

def dispatchBonus : Calculus → ℝ
  | .ito => 0
  | .stratonovich => 1

-- Functional characterization of the complete coupled branch under explicitly
-- synthetic dispatch. This checks the channel-to-driver map as well as atomics.
lemma branch_dispatch (c : Calculus) (k : Channels 2 0) (noise : Fin 2 → ℝ) (y : Process Unit 2) :
    ((preparedFor c).branch k).Rel
      { dispatchContext with noise := fun k _ _ => noise k }
      (fun _ _ => ![2,5,7,11]) y ↔
    y = fun _ _ => (![![16,3], ![7 * noise 0 + dispatchBonus c,4 * noise 0 + dispatchBonus c],
      ![15 * noise 1 + dispatchBonus c,noise 1 + dispatchBonus c]] : Fin 3 → Point 2) k := by
  rw [(preparedFor c).branch_correct]
  simp only [(preparedFor c).evaluates_iff, sampleAdmissible, constant_limits,
    implies_true, true_and, sample, before_constant, ite_self, exists_eq_left]
  have kinds : ({ coupled with calculus := c } : NamedSystem 2 2 2 0).kind =
      (![.time, .noise c 0, .noise c 1] : Fin 3 → IntegralKind 2 0) := by
    funext i
    fin_cases i <;> rfl
  rw [kinds]
  have fields : (preparedFor c).field = coupledPrepared.field := rfl
  rw [fields]
  simp only [coupled_fields]
  cases c <;> fin_cases k <;>
    simp only [Matrix.cons_val,
      Context.integral, dispatchContext, dispatch, dispatchBonus] <;>
    constructor
  all_goals
    intro h
    first
    | (funext t ω i
       have hi := congrFun (congrFun (h i) t) ω
       fin_cases i <;> norm_num at hi ⊢ <;> exact hi)
    | (subst y
       intro i
       funext t ω
       fin_cases i <;> norm_num)

lemma coupled_dispatch (c : Calculus) (noise : Fin 2 → ℝ) (y : Process Unit 2) :
    (preparedFor c).compile.Rel { dispatchContext with noise := fun k _ _ => noise k }
      (fun _ _ => ![2,5,7,11]) y ↔
    y = fun _ _ => ![16 + 7*noise 0 + 15*noise 1 + 2*dispatchBonus c,
      3 + 4*noise 0 + noise 1 + 2*dispatchBonus c] := by
  simp only [Prepared.compile, Gimle.Asgard.Stochastic.Circuit.Rel]
  constructor
  · rintro ⟨_, _, values, hv, hy⟩
    have hv' := fun k => (branch_dispatch c k noise (values k)).mp (hv k)
    subst y
    funext t ω i
    change (∑ k : Fin 3, values k t ω i) = _
    rw [Fin.sum_univ_three, hv' 0, hv' 1, hv' 2]
    fin_cases i
    · change 16 + (7*noise 0 + dispatchBonus c) + (15*noise 1 + dispatchBonus c) =
        16 + 7*noise 0 + 15*noise 1 + 2*dispatchBonus c
      ring
    · change 3 + (4*noise 0 + dispatchBonus c) + (noise 1 + dispatchBonus c) =
        3 + 4*noise 0 + noise 1 + 2*dispatchBonus c
      ring
  · intro hy
    subst y
    refine ⟨trivial, rfl,
      (fun k _ _ => (![![16,3], ![7 * noise 0 + dispatchBonus c,4 * noise 0 + dispatchBonus c],
        ![15 * noise 1 + dispatchBonus c,noise 1 + dispatchBonus c]] : Fin 3 → Point 2) k),
      (fun k => (branch_dispatch c k noise _).mpr rfl), ?_⟩
    funext t ω i
    change _ = ∑ k : Fin 3, _
    rw [Fin.sum_univ_three]
    fin_cases i
    · change 16 + 7*noise 0 + 15*noise 1 + 2*dispatchBonus c =
        16 + (7*noise 0 + dispatchBonus c) + (15*noise 1 + dispatchBonus c)
      ring
    · change 3 + 4*noise 0 + noise 1 + 2*dispatchBonus c =
        3 + (4*noise 0 + dispatchBonus c) + (noise 1 + dispatchBonus c)
      ring

example : (preparedFor .ito).compile.Rel
    { dispatchContext with noise := fun k _ _ => (![2,3] : Fin 2 → ℝ) k }
    (fun _ _ => ![2,5,7,11]) (fun _ _ => ![75,14]) := by
  rw [coupled_dispatch]
  funext t ω i
  fin_cases i <;> norm_num [dispatchBonus]

example : ¬ (preparedFor .ito).compile.Rel
    { dispatchContext with noise := fun k _ _ => (![3,2] : Fin 2 → ℝ) k }
    (fun _ _ => ![2,5,7,11]) (fun _ _ => ![75,14]) := by
  rw [coupled_dispatch]
  intro h
  have bad := congrFun (congrFun (congrFun h 0) ()) 0
  norm_num [dispatchBonus] at bad

example : ¬ (preparedFor .stratonovich).compile.Rel
    { dispatchContext with noise := fun k _ _ => (![2,3] : Fin 2 → ℝ) k }
    (fun _ _ => ![2,5,7,11]) (fun _ _ => ![75,14]) := by
  rw [coupled_dispatch]
  intro h
  have bad := congrFun (congrFun (congrFun h 0) ()) 0
  norm_num [dispatchBonus] at bad

#print axioms coupled_dispatch

-- A missing left limit rejects the whole compiled body, including for an
-- unused external whose regularity is conservatively required by this fragment.
example (x : Process Unit 4) (y : Process Unit 2)
    (bad : ¬ HasLeftLimits dispatchContext.time x) :
    ¬ coupledPrepared.compile.Rel dispatchContext x y := by
  rintro ⟨_, _, values, hv, _⟩
  obtain ⟨a, ha, _⟩ := (coupledPrepared.branch_correct 1 dispatchContext x (values 1)).mp (hv 1)
  exact bad (ha.1 rfl)

end Gimle.Asgard.Tests.Stochastic
