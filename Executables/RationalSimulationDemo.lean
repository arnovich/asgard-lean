import Gimle.Asgard.Examples.RationalExecution

open Gimle.Asgard Gimle.Asgard.Simulation Gimle.Asgard.Examples.RationalExecution Lean

def main (args : List String) : IO UInt32 := do
  let [python] := args | throw (IO.userError "Usage: rational_simulation_demo PYTHON")
  let cancel ← IO.mkRef false
  let points ← Rational.run pointRequest {python := python} cancel
  unless points.trajectory == #[#[-2, 0.5]] do throw (IO.userError "observation order changed")
  let rhsRequest := {eulerRequest with initialization := none, settings := .points #[#[0.5, -2]]}
  let rhs ← Rational.run rhsRequest {python := python} cancel
  unless rhs.trajectory == #[#[(1.0/3)*(-2), -(2.0/7)*0.5]] do
    throw (IO.userError "rational RHS values changed")
  let euler ← Rational.run eulerRequest {python := python} cancel
  let expectedFirst := #[0.5 + 0.5*((1.0/3)*(-2)), -2 + 0.5*(-(2.0/7)*0.5)]
  unless euler.trajectory[1]! == expectedFirst do throw (IO.userError "Euler routing changed")
  -- Large integer sticky-bit cases must agree with Python's full-integer rounding.
  let big : ℚ := (2^64 + 2^11 + 1 : Int)
  let precisionRequest := {eulerRequest with initialization := some ⟨#[big, -big], 2/3, "time"⟩}
  let _ ← Rational.run precisionRequest {python := python} cancel
  let cases : Array ℚ := #[big, -big, (2^53 + 3 : Int), -(2^53 + 3 : Int),
    1 / big, -1 / big, (2^53 + 1 : Int), (2^54 - 1 : Int), 1/3, 1/(10^308 : ℚ)]
  let conversions ← cases.mapM fun q => do
    let value ← IO.ofExcept ((Rational.numericalValue q).mapError IO.userError)
    return Json.mkObj [("rational", Rational.rationalJson q), ("value", .str (encodeFloat value))]
  let request ← IO.ofExcept (eulerRequest.toJson.mapError IO.userError)
  IO.println (Json.mkObj [("points", encodeRows points.trajectory),
    ("rhs", encodeRows rhs.trajectory), ("euler", encodeRows euler.trajectory),
    ("request", request), ("conversions", .arr conversions), ("provenance", euler.provenance),
    ("diagnostics", euler.diagnostics)]).compress
  return 0
