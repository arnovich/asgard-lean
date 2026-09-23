import Gimle.Asgard.Examples.ThreeStateExecution

/-! The installed-worker handoff for the shared three-state research model.

Everything printed here is numerical evidence from an installed Python worker.
The theorems live in `Gimle/Asgard/Examples/ThreeState.lean` and do not depend
on this executable or on any worker being present. -/
open Gimle.Asgard Gimle.Asgard.Simulation Gimle.Asgard.Examples.ThreeState Lean

def main (args : List String) : IO UInt32 := do
  let [python] := args | throw (IO.userError "Usage: three_state_demo PYTHON")
  let cancel ← IO.mkRef false
  -- The decoder already enforces the row count and the initial row against the
  -- exact declared initialization, so this checks what it does not: the field
  -- routing and the step, by mirroring the compiled AST's own evaluation order.
  let euler ← Rational.run eulerRequest {python := python} cancel
  -- The returned time grid is the claim "33 rows from t=2 to t=6", checked
  -- against the worker rather than only asserted in Lean.
  let some times := euler.times | throw (IO.userError "missing Euler time grid")
  unless times.size == 33 && times[0]! == 2.0 && times[32]! == 6.0 do
    throw (IO.userError "Euler time grid is not 33 rows from 2 to 6")
  let dx := ((-(1.0 / 3)) * 1.0 + 2.0) + 1.0
  let dy := ((-1.0) + -(0.5 * 2.0)) + -1.0
  let dz := (1.0 + -2.0) + -(2.0 * -1.0)
  let expected := #[1.0 + 0.125 * dx, 2.0 + 0.125 * dy, -1.0 + 0.125 * dz]
  unless euler.trajectory[1]! == expected do
    throw (IO.userError "Euler state routing or step changed")
  -- The exact oracle is (4/3, 13/8, -7/8). 13/8 and -7/8 are dyadic and must
  -- agree bit for bit; 4/3 is not, so it is checked through the chain above.
  unless expected[1]! == 13.0 / 8 && expected[2]! == -(7.0 / 8) do
    throw (IO.userError "dyadic Euler components disagree with the exact oracle")
  -- Every returned row goes back through the same compiled observation circuit,
  -- so V is evaluated by the model rather than retyped here.
  let request ← IO.ofExcept ((observationRequest euler.trajectory).mapError IO.userError)
  let observed ← Rational.run request {python := python} cancel
  -- Observations are [z,x,y,V] over state order [x,y,z]; V(2) = 1+4+1 = 6.
  unless observed.trajectory[0]! == #[-1, 1, 2, 6] do
    throw (IO.userError "observation order or initial energy changed")
  -- Explicit Euler is not unconditionally energy-decreasing: that needs
  -- (I+hA)ᵀ(I+hA) ⪯ I, which holds at h=1/8 but fails for larger steps. This is
  -- a regression guard on the retained numerical setting, not a theorem.
  let energies := observed.trajectory.map (fun row => row[3]!)
  unless (List.range (energies.size - 1)).all (fun k => energies[k + 1]! <= energies[k]!) do
    throw (IO.userError "observed energy is not monotone at the retained step")
  IO.println (Json.mkObj [("euler", encodeRows euler.trajectory),
    ("times", toJson (times.map encodeFloat)),
    ("observations", encodeRows observed.trajectory),
    ("request", ← IO.ofExcept (eulerRequest.toJson.mapError IO.userError)),
    ("observationRequest", ← IO.ofExcept (request.toJson.mapError IO.userError)),
    ("provenance", euler.provenance), ("diagnostics", euler.diagnostics)]).compress
  return 0
