import Gimle.Asgard.Dynamics.Trace
import Gimle.Asgard.Dynamics.Named
import Gimle.Asgard.Compile.Syntax
import Gimle.Asgard.Examples.Feedback

namespace Gimle.Asgard.Tests.Feedback
open Polynomial Dynamics

-- The general theorem concerns actual integrators and trace, including zero states.
example {d n : Nat} (axis : String) (field : Gimle.Asgard.Circuit (d + n) n)
    (time : TimeDomain) (drivers : Signal d) (initial : Point n) (state : Signal n) :
    (close axis field).Rel time (signalAppend drivers (fun _ => initial)) state ↔
      axis = time.axis ∧ state time.start = initial ∧
      ∀ t ∈ time.domain, ∀ i,
        HasDerivWithinAt (fun t => state t i)
          (field.run (pointAppend (drivers t) (state t)) i) time.domain t :=
  close_correct axis field time drivers initial state

example (time : TimeDomain) (u : Signal 3) :
    (close time.axis (Wiring.discard 3)).Rel time
      (signalAppend u (fun _ => fun i : Fin 0 => Fin.elim0 i)) (fun _ i => Fin.elim0 i) := by
  rw [close_correct]
  exact ⟨rfl, rfl, fun _ _ i => Fin.elim0 i⟩

-- Interleaved source order, repeated self/cross references, retained algebraic
-- assignments and three coupled states. The state named t does not denote the axis.
abbrev coupled : System := {
  program := {
    inputs := [⟨"driver", "u0", .driver⟩, ⟨"sz", "z", .state⟩,
      ⟨"parameter", "p", .parameter⟩, ⟨"sx", "t", .state⟩, ⟨"sy", "y", .state⟩]
    assignments := equations% {
      shared := t + y;
      dx := shared + y + u0;
      dz := t + z + p;
      dy := z + y + y;
    }
  }
  states := [⟨"sy", "dy", "iy"⟩, ⟨"sz", "dz", "iz"⟩, ⟨"sx", "dx", "ix"⟩]
  externalIds := ["driver", "parameter"]
  initialPorts := [⟨"ix", "x0", .initial⟩, ⟨"iz", "z0", .initial⟩, ⟨"iy", "y0", .initial⟩]
  axis := ⟨"time-axis", "t"⟩
  evolveAlong := "time-axis"
}

def coupledPrepared : Prepared coupled := coupled.prepare.get (by decide)

example : coupledPrepared.inputRoute = (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) := by decide +kernel
example : coupledPrepared.outputRoute = ![3, 2, 1] := by decide +kernel
example : coupledPrepared.initialRoute = ![2, 1, 0] := by decide +kernel

example : coupledPrepared.field.run ![7, 11, 2, 3, 5] = ![7, 19, 16] := by
  have es : coupledPrepared.expressions =
      ([Expr.add (.var 3) (.var 4),
       .add (.add (.add (.var 3) (.var 4)) (.var 4)) (.var 0),
       .add (.add (.var 3) (.var 1)) (.var 2),
       .add (.add (.var 1) (.var 4)) (.var 4)] : List (Expr 5)) := by decide
  have hi : coupledPrepared.inputRoute = (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) := by decide +kernel
  have ho : coupledPrepared.outputRoute = ![3, 2, 1] := by decide +kernel
  simp only [Prepared.field, Gimle.Asgard.Circuit.run, Polynomial.route_correct,
    compileList, compileOutputs_correct, hi, ho]
  funext i
  fin_cases i <;> simp only [es]
  · change (3 + 2 + 2 : ℝ) = 7
    norm_num
  · change (5 + 3 + 11 : ℝ) = 19
    norm_num
  · change (5 + 2 + 2 + 7 : ℝ) = 16
    norm_num

-- No silent name, role, axis, output or initial-value fallback.
#guard ({ coupled with evolveAlong := "other-axis" } : System).prepare.isNone
#guard ({ coupled with axis := ⟨"", "t"⟩ } : System).prepare.isNone
#guard ({ coupled with states := coupled.states ++ [⟨"sy", "dy", "iy"⟩] } : System).prepare.isNone
#guard ({ coupled with states := coupled.states.tail } : System).prepare.isNone
#guard ({ coupled with externalIds := ["driver", "missing"] } : System).prepare.isNone
#guard ({ coupled with externalIds := ["driver", "driver"] } : System).prepare.isNone
#guard ({ coupled with states := [⟨"sy", "absent", "iy"⟩, ⟨"sz", "dz", "iz"⟩,
  ⟨"sx", "dx", "ix"⟩] } : System).prepare.isNone
#guard ({ coupled with states := [⟨"sy", "dy", "absent"⟩, ⟨"sz", "dz", "iz"⟩,
  ⟨"sx", "dx", "ix"⟩] } : System).prepare.isNone
#guard ({ coupled with states := [⟨"sy", "dy", "ix"⟩, ⟨"sz", "dz", "iz"⟩,
  ⟨"sx", "dx", "ix"⟩] } : System).prepare.isNone
#guard ({ coupled with initialPorts := [⟨"ix", "x0", .driver⟩,
  ⟨"iz", "z0", .initial⟩, ⟨"iy", "y0", .initial⟩] } : System).prepare.isNone
#guard ({ coupled with program := { coupled.program with
  assignments := equations% { dx := dy; dy := dx; dz := z; } } } : System).prepare.isNone

-- Nested trace fusion includes nontrivial external/hidden block sizes and
-- asymmetric routing; both input and output coordinate reassociations matter.
def nestedBody : Dynamics.Circuit ((1 + 2) + 1) ((1 + 2) + 1) :=
  .lift (Polynomial.route (fun i : Fin 4 => ![2, 0, 3, 1] i))
example : Equivalent (.trace 2 (.trace 1 nestedBody)) (fuse nestedBody) :=
  nested_trace_fusion nestedBody
example : (unassociate 1 2 1).run (pointAppend ![2] (pointAppend ![5, 7] ![11])) =
    pointAppend (pointAppend ![2] ![5, 7]) ![11] := unassociate_run _ _ _

-- One state and two independent asymmetric equations admit concrete trajectories.
example (ic : ℝ) : (close "t" (Polynomial.compileOutputs
    (fun _ : Fin 1 => Expr.constant (n := 0 + 1) 2))).Rel ⟨"t", 0⟩
      (signalAppend (fun _ => fun i : Fin 0 => Fin.elim0 i) (fun _ => ![ic]))
      (fun t => ![ic + 2*t]) := by
  rw [close_correct]
  refine ⟨rfl, ?_, ?_⟩
  · ext i; fin_cases i; simp
  · intro t _ i
    fin_cases i
    simpa [Expr.eval, TimeDomain.domain] using
      (((hasDerivAt_id t).const_mul 2).const_add ic).hasDerivWithinAt (s := Set.Ici 0)

example (initial : Point 2) :
    (close "t" (Polynomial.compileOutputs (fun i : Fin 2 =>
      if i = 0 then Expr.constant (n := 0 + 2) 2 else .constant 3))).Rel ⟨"t", 0⟩
      (signalAppend (fun _ => fun i : Fin 0 => Fin.elim0 i) (fun _ => initial))
      (fun t => ![initial 0 + 2*t, initial 1 + 3*t]) := by
  rw [close_correct]
  refine ⟨rfl, ?_, ?_⟩
  · ext i; fin_cases i <;> simp
  · intro t _ i
    fin_cases i
    · simpa [Expr.eval, TimeDomain.domain] using
        (((hasDerivAt_id t).const_mul 2).const_add (initial 0)).hasDerivWithinAt (s := Set.Ici 0)
    · simpa [Expr.eval, TimeDomain.domain] using
        (((hasDerivAt_id t).const_mul 3).const_add (initial 1)).hasDerivWithinAt (s := Set.Ici 0)

open Examples.Feedback in
-- Swapped initial values cannot certify the original oscillator trajectory.
example : ¬ circuit.Rel ⟨"physical-time", 0⟩ (fun _ => ![5, 2])
    (fun t => ![Oscillator.position 2 5 t, Oscillator.velocity 2 5 t]) := by
  rw [circuit_equations]
  intro h
  have wrong := congrFun h.2.1 0
  norm_num [Oscillator.position] at wrong

open Examples.Feedback in
example (initial : Point 2) (state : Signal 2) :
    ¬ circuit.Rel ⟨"wrong-axis", 0⟩ (fun _ => initial) state := by
  rw [circuit_equations]
  simp

-- A feedback pairing mistake changes the observable field at a concrete state.
open Examples.Feedback in
example : prepared.field.run ![2, 5] ≠ prepared.field.run ![5, 2] := by
  intro h
  have bad := congrFun h 0
  simp [field_equations] at bad

open Examples.Feedback in
example : prepared.field.run ![0, 1] 1 ≠ (2 : ℝ) := by
  rw [field_equations]
  norm_num

-- The derivative-to-state connection is swapped in an actual closed target.
-- The legitimate trajectory (2t,3t) cannot satisfy that miswired circuit.
def wrongPairing : Dynamics.Circuit 2 2 :=
  close "t" (.compose (Polynomial.compileOutputs (fun i : Fin 2 =>
    if i = 0 then Expr.constant (n := 0 + 2) 2 else .constant 3)) .swap)

example : ¬ wrongPairing.Rel ⟨"t", 0⟩
    (signalAppend Examples.Feedback.noDrivers (fun _ => ![0, 0]))
    (fun t => ![2*t, 3*t]) := by
  rw [wrongPairing, close_correct]
  intro h
  have bad := h.2.2 1 (by norm_num [TimeDomain.domain]) 0
  have badWithin : HasDerivWithinAt (fun t : ℝ => 2*t) 3 (Set.Ici 0) 1 := by
    simpa [Expr.eval, TimeDomain.domain] using bad
  have badAt := badWithin.hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have goodAt := (hasDerivAt_id (1 : ℝ)).const_mul 2
  have impossible := goodAt.unique badAt
  norm_num at impossible

end Gimle.Asgard.Tests.Feedback
