import Gimle.Asgard.Visualization.Model
import Gimle.Asgard.Compile.Syntax

namespace Gimle.Asgard.Tests.Visualization
open Gimle.Asgard Visualization

-- Composition is left first; parallel ports concatenate without interleaving.
private def asymmetric : Circuit 2 2 := .compose .swap
  (.parallel (.compose (.scalar 3) (.compose .split .add)) (.scalar 3))
#eval IO.ofExcept do
  let g ← ofCircuit asymmetric
  unless g.inputs.length == 2 && g.outputs.length == 2 do
    throw "incorrect external interface"
  unless g.edges.length == 5 do throw "composition lost a wire"

-- Trace feeds the LAST k output ports back into the LAST k input ports.
private def feedback : Dynamics.Circuit 1 2 := .trace 1
  (.lift (.parallel .split .id))
#eval IO.ofExcept do
  let g ← ofDynamics feedback
  unless g.inputs.length == 1 && g.outputs.length == 2 do
    throw "trace exposed feedback ports"
  unless g.edges.any (fun e => e.feedback && e.source.port == 0 && e.target.port == 0) do
    throw "trace lost feedback edge"
end Gimle.Asgard.Tests.Visualization

namespace Gimle.Asgard.Tests.Visualization
open Gimle.Asgard Visualization

/-- Independent arithmetic oracle over the emitted graph edges, not Circuit.run. -/
private def evaluate (g : Diagram) (inputs : List ℚ) : Except String (List ℚ) := do
  let mut values : List (List ℚ) := []
  for (node,id) in g.nodes.zipIdx do
    let arguments ← (List.range node.inputs).mapM fun port => do
      let endpoint : Endpoint := ⟨id,port⟩
      if let some (_,index) := g.inputs.zipIdx.find? (fun (e,_) => e == endpoint) then
        return inputs[index]!
      let some edge := g.edges.find? (·.target == endpoint) | throw "unbound node input"
      if edge.feedback then throw "feedback is relational; no feedforward evaluation"
      let some prior := values[edge.source.node]? | throw "edge is not topologically ordered"
      let some value := prior[edge.source.port]? | throw "source output is missing"
      return value
    let outputs ← match node.operation, arguments with
      | .identity, [a] => pure [a]
      | .constant q, [] => pure [q]
      | .scalar q, [a] => pure [q*a]
      | .add, [a,b] => pure [a+b]
      | .multiply, [a,b] => pure [a*b]
      | .split, [a] => pure [a,a]
      | .swap, [a,b] => pure [b,a]
      | .terminal, [_] => pure []
      | _, _ => throw "wrong atomic interface"
    values := values ++ [outputs]
  g.outputs.mapM fun e => do
    let some node := values[e.node]? | throw "external output node missing"
    let some value := node[e.port]? | throw "external output port missing"
    return value

private def check {n m : Nat} (c : Circuit n m) (input expected : List ℚ) : Except String Unit := do
  let g ← ofCircuit c
  unless (← evaluate g input) == expected do throw "rendered wiring changes the result"

#eval IO.ofExcept <| check asymmetric [5,11] [66,15]
#eval IO.ofExcept <| check (.compose .split .multiplication) [3/7] [9/49]
#eval IO.ofExcept <| check (.parallel (.const (-2/3)) .terminal) [9] [-2/3]
#eval IO.ofExcept <| check (.compose (.parallel .terminal .id) (.scalar (1/2))) [5,11] [11/2]
#eval IO.ofExcept <| check (.compose (.const 5) .terminal) [] []
#eval IO.ofExcept <| check (.parallel (.parallel .id .id) (.const 7)) [5,11] [5,11,7]

-- Two trace lanes: unequal exposed input/output counts remain separate.
#eval IO.ofExcept do
  let body : Dynamics.Circuit 3 4 := .lift (.parallel .split (.parallel .id .id))
  let g ← ofDynamics (@Dynamics.Circuit.trace 1 2 2 body)
  let loops := g.edges.filter (·.feedback)
  unless loops.map (fun e => (e.source.node,e.target.node)) == [(1,1),(2,2)] do
    throw "trace did not bind the final ports in order"
  unless g.inputs == [⟨0,0⟩] && g.outputs == [⟨0,0⟩,⟨0,1⟩] do
    throw "trace changed exposed ports"
  let integrator ← ofDynamics (.integrate "time" 2)
  unless integrator.inputs == [⟨0,0⟩,⟨0,1⟩,⟨0,2⟩,⟨0,3⟩] do
    throw "integrator input grouping changed"
  unless (ofDynamics (.integrate "time" 33)).toOption.isNone do throw "port limit ignored"
  unless (ofDynamics (.integrate (String.singleton (Char.ofNat 0)) 1)).toOption.isNone do
    throw "invalid XML character accepted"
  let xml := (← ofDynamics (.integrate "t<&\"" 1)).scene.xml
  unless (xml.splitOn "t&lt;&amp;&quot;").length > 1 do throw "label was not XML-escaped"

end Gimle.Asgard.Tests.Visualization

namespace Gimle.Asgard.Tests.Visualization
open Gimle.Asgard Visualization Polynomial Model

private def body : Body := {
  program := ⟨[⟨"z", "z", .state⟩, ⟨"x", "x", .state⟩, ⟨"y", "y", .state⟩],
    equations% { dx := rat(1,3)*y; dy := -rat(2,7)*z; dz := 5*x; }⟩
  observations := [⟨⟨"oz", "z", .output⟩, "z"⟩, ⟨⟨"ox", "x", .output⟩, "x"⟩]
}
private def evolution : Evolution := {
  states := [⟨"y","dy","iy"⟩,⟨"z","dz","iz"⟩,⟨"x","dx","ix"⟩]
  initialPorts := [⟨"ix","x0",.initial⟩,⟨"iy","y0",.initial⟩,⟨"iz","z0",.initial⟩]
  initialValues := [⟨"iz",-3/4⟩,⟨"ix",1/2⟩,⟨"iy",2/3⟩]
  axis := ⟨"time","t"⟩
  evolveAlong := "time"
  start := 7/5
}
private def compiled : ContinuousModel body evolution :=
  (compileContinuous body evolution).toOption.get (by decide +kernel)
#eval IO.ofExcept do
  let view ← overview compiled
  unless view.states.map (·.id) == ["y","z","x"] do throw "wrong state order"
  unless view.states.map (·.initial) == ["2/3","-3/4","1/2"] do throw "wrong IC binding"
  unless view.states.map (·.equation) ==
      ["dy/dt = ((-2/7) × z)","dz/dt = (5 × x)","dx/dt = (1/3 × y)"] do
    throw s!"wrong equations: {repr (view.states.map (·.equation))}"
  unless view.start == "7/5" && view.observations == [("z","z"),("x","x")] do
    throw "start or observation ordering changed"
  let g ← ofCircuit compiled.rates.circuit
  unless (← evaluate g [2,3,5]) == [-6/7,25,2/3] do
    throw "compiled equation graph disagrees with displayed equations"
  unless (expression (fun _ : Fin 1 => "x") 0 (.var 0)).toOption.isNone do
    throw "expression depth limit ignored"
end Gimle.Asgard.Tests.Visualization

namespace Gimle.Asgard.Tests.Visualization
open Gimle.Asgard Visualization Polynomial Model

private def chain : Nat → Circuit 1 1
  | 0 => .id
  | n+1 => .compose (chain n) .id
#eval IO.ofExcept do
  unless (ofCircuit (chain 256)).toOption.isNone do throw "nesting limit ignored"
  let g ← ofDynamics (.integrate "a_very_long_time_axis_name_used_in_a_model" 1)
  unless g.width > 160 do throw "long exact labels must grow their boxes"
  let loops ← ofDynamics (@Dynamics.Circuit.trace 0 0 2 (.lift (@Circuit.parallel 1 1 1 1 .id .id)))
  unless loops.edges.map (·.leftRail) == [44,32] &&
      loops.edges.map (·.rightRail) == [244,256] do
    throw "distinct feedback signals share return rails"

private def renamed : NamedExpr → NamedExpr
  | .var name => .var (if name == "x" then "1" else if name == "y" then "t" else name)
  | .constant q => .constant q
  | .add a b => .add (renamed a) (renamed b)
  | .mul a b => .mul (renamed a) (renamed b)
  | .neg a => .neg (renamed a)
private def ambiguousBody : Body := { body with
  program := {
    inputs := body.program.inputs.map fun p =>
      { p with name := if p.id == "x" then "1" else if p.id == "y" then "t" else p.name }
    assignments := body.program.assignments.map fun a => { a with rhs := renamed a.rhs } } }
-- Rename source expressions with their input names; stable interface IDs stay fixed.
private def ambiguousModel : ContinuousModel ambiguousBody evolution :=
  (compileContinuous ambiguousBody evolution).toOption.get (by decide +kernel)
#eval IO.ofExcept do
  let view ← overview ambiguousModel
  unless view.states.map (·.name) == ["t[state:y]","z","‘1’"] do
    throw "ambiguous display names are not distinguished from literals or the axis"
end Gimle.Asgard.Tests.Visualization

namespace Gimle.Asgard.Tests.Visualization
open Gimle.Asgard Visualization
#eval IO.ofExcept do
  let g ← ofCircuit (.compose (.parallel .id .id) (@Circuit.parallel 0 1 2 1 (.const 0) .add))
  unless (← evaluate g [5,11]) == [0,16] do throw "asymmetric constant branch miswired"
  -- Curves avoid coincident horizontal runs when an output and another input share y.
  unless (g.scene.xml.splitOn "data-role=\"wire\"").length == 3 do
    throw "forward links lost independent curved paths"
  let wide ← ofDynamics (.integrate (String.ofList (List.replicate 80 'W')) 1)
  unless (wide.scene.xml.splitOn "lengthAdjust").length > 1 do
    throw "wide glyph labels lack a bounded text extent"
end Gimle.Asgard.Tests.Visualization
