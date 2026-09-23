import Gimle.Asgard.Examples.PolynomialCompiler

/-! Generate integration fixtures through the actual Lean compiler/exporter.
Run explicitly; importing the formal library does not execute this program. -/
open Gimle.Asgard Gimle.Asgard.Polynomial Gimle.Asgard.Interchange

private def port (name : String) (role : PortRole) : Port := ⟨name, name, role⟩

private def fixture {n m : Nat} (name : String) (c : Circuit n m)
    (inputs outputs : List Port) (points expected : List (List String)) : Except String Lean.Json := do
  let envelope ← exportPython c inputs outputs
  return Lean.Json.mkObj [
    ("name", .str name), ("envelope", envelope),
    ("points", Lean.toJson points), ("expected", Lean.toJson expected)]

def fixtures : Except String Lean.Json := do
  let energy := Gimle.Asgard.Examples.PolynomialCompiler.energyProgram
  let oscillator := Gimle.Asgard.Examples.PolynomialCompiler.oscillatorProgram
  let cases ← [
    fixture "constant" (Circuit.const 7) [] [port "out" .output] [[]] [["7"]],
    fixture "empty" Wiring.empty [] [] [[]] [[]],
    fixture "discard" (Wiring.discard 3)
      [port "x" .input, port "y" .input, port "u0" .driver] [] [["2", "5", "11"]] [[]],
    fixture "asymmetric" (compileOutputs (n := 3) ![
      Expr.add (.var 2) (.neg (.var 0)), Expr.add (.var 0) (.var 0)])
      [port "x" .input, port "unused" .parameter, port "u0" .driver]
      [port "difference" .output, port "double" .output]
      [["2", "5", "11"], ["1/3", "8", "-2/5"]] [["9", "4"], ["-11/15", "2/3"]],
    fixture "permutation" (route (n := 3) ![2, 0, 1])
      [port "x" .input, port "y" .input, port "z" .input]
      [port "a" .output, port "b" .output, port "c" .output]
      [["2", "5", "11"]] [["11", "2", "5"]],
    fixture "energy" Gimle.Asgard.Examples.PolynomialCompiler.energyCircuit
      energy.inputs (energy.assignments.map Assignment.output)
      [["2", "5"], ["1/3", "-2/5"]] [["7", "-3", "58"], ["-1/15", "11/15", "122/225"]],
    fixture "oscillator" Gimle.Asgard.Examples.PolynomialCompiler.oscillatorCircuit
      oscillator.inputs (oscillator.assignments.map Assignment.output)
      [["2", "5"], ["1/3", "-2/5"]] [["5", "-12"], ["-2/5", "7/15"]],
    fixture "large_integer" (Circuit.const (-123456789012345678901234567890))
      [] [port "out" .output] [[]] [["-123456789012345678901234567890"]]
    ].mapM id
  return .arr cases.toArray

def main : IO Unit := do
  match fixtures with
  | .error message => throw (IO.userError message)
  | .ok value => IO.println value.compress
