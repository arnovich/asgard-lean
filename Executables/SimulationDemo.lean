import Gimle.Asgard.Simulation.Client
import Gimle.Asgard.Compile.Syntax

open Gimle.Asgard Gimle.Asgard.Simulation Gimle.Asgard.Polynomial Lean

/-- E(x,y)=2x²+2y², evaluated at three supplied points. -/
def energyRequest : Request 2 1 where
  circuit := compileOutputs ![.mul (.constant 2)
    (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))]
  inputs := [⟨"x", "x", .input⟩, ⟨"y", "y", .input⟩]
  outputs := [⟨"energy", "energy", .output⟩]
  requestId := "energy-points"
  artifactId := "original-energy-circuit"
  settings := .points #[#[0, 0], #[1, 0], #[1, 1]]

/-- Numerical Euler steps for x'=y, y'=-x. Coordinate updates are simultaneous.
This demonstration claims no numerical accuracy or preservation of energy. -/
def oscillatorRequest : Request 2 2 where
  circuit := .compose .swap (.parallel .id (.scalar (-1)))
  inputs := [⟨"x", "x", .state⟩, ⟨"y", "y", .state⟩]
  outputs := [⟨"dx", "dx", .output⟩, ⟨"dy", "dy", .output⟩]
  requestId := "oscillator-euler"
  artifactId := "original-oscillator-rhs"
  settings := .euler #[1, 0] 0 0.5 2

/-- Bit-sensitive samples exercise the lossless wire format independently of dynamics. -/
def precisionRequest : Request 1 1 where
  circuit := .id
  inputs := [⟨"x", "x", .input⟩]
  outputs := [⟨"y", "y", .output⟩]
  requestId := "binary64-roundtrip"
  artifactId := "original-identity"
  settings := .points #[#[1], #[1e-10], #[1.2345678901234567], #[1e100],
    #[Float.ofBits 1], #[Float.ofBits 9223372036854775808]]

def main (args : List String) : IO UInt32 := do
  let [python] := args | throw (IO.userError "Usage: simulation_demo /absolute/venv/bin/python")
  let cancel ← IO.mkRef false
  let energy ← run energyRequest {python := python} cancel
  let oscillator ← run oscillatorRequest {python := python} cancel
  unless energy.trajectory == #[#[0], #[2], #[4]] do throw (IO.userError "unexpected energy samples")
  unless oscillator.trajectory == #[#[1, 0], #[1, -0.5], #[0.75, -1]] do
    throw (IO.userError "unexpected simultaneous Euler trajectory")
  let precision ← run precisionRequest {python := python} cancel
  let .points samples := precisionRequest.settings | throw (IO.userError "invalid precision fixture")
  unless precision.trajectory.map (·.map Float.toBits) == samples.map (·.map Float.toBits) do
    throw (IO.userError "binary64 round trip lost bits")
  IO.println (Json.mkObj [("energy", toJson energy.trajectory),
    ("oscillator", toJson oscillator.trajectory), ("times", toJson oscillator.times),
    ("provenance", oscillator.provenance), ("diagnostics", oscillator.diagnostics)]).compress
  return 0
