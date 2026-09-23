import Gimle.Asgard.Visualization.Model
import Gimle.Asgard.Examples.EnergyOptimization
import Gimle.Asgard.Examples.EquationModels
import Gimle.Asgard.Examples.RationalExecution

open Gimle.Asgard Visualization

def main (args : List String) : IO UInt32 := do
  let [name, destination] := args | do
    IO.eprintln "Usage: lake exe diagram_demo energy|energy-optimized|energy-compiled|oscillator|rational|rational-raw OUTPUT.svg"
    return 1
  let result := match name with
    | "energy" => (ofCircuit EnergyDemo.energy).map Diagram.scene
    | "energy-optimized" => (ofCircuit EnergyOptimization.optimized).map Diagram.scene
    | "energy-compiled" => (ofCircuit Examples.EquationModels.energy).map Diagram.scene
    | "oscillator" => (ofDynamics Examples.EquationModels.feedback).map Diagram.scene
    | "rational" => (overview Examples.RationalExecution.model).map ModelOverview.scene
    | "rational-raw" => (ofDynamics Examples.RationalExecution.model.feedback).map Diagram.scene
    | _ => .error s!"Unknown diagram: {name}"
  match result with
  | .error message => IO.eprintln message; return 1
  | .ok scene =>
    if ← System.FilePath.pathExists destination then
      IO.eprintln s!"Refusing to overwrite {destination}"
      return 1
    let output ← IO.FS.Handle.mk destination .writeNew
    output.putStr (scene.xml ++ "\n")
    IO.println s!"Saved {destination}"
    return 0
