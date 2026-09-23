import Gimle.Asgard.Visualization.Diagram
import Gimle.Asgard.Model.Continuous

namespace Gimle.Asgard.Visualization
open Polynomial Model

/-- Fully parenthesized expressions preserve precedence and exact rationals.
Limits are checked during recursion, before a potentially exponential display. -/
def expression {n : Nat} (names : Fin n → String) : Nat → Expr n → Except String String
  | 0, _ => .error "Equation display nesting limit exceeded (32)."
  | fuel+1, e => do
    let text ← match e with
      | .var i => pure (names i)
      | .constant q => pure (rational q)
      | .neg a => return s!"(-{← expression names fuel a})"
      | .add a b => return s!"({← expression names fuel a} + {← expression names fuel b})"
      | .mul a b => return s!"({← expression names fuel a} × {← expression names fuel b})"
    if text.length > 2048 then throw "Equation display length limit exceeded (2048)."
    return text

structure StateRow where
  id : String
  derivativeId : String
  initialId : String
  name : String
  equation : String
  initial : String
  deriving Repr, BEq

structure ModelOverview where
  axis : String
  axisId : String
  start : String
  states : List StateRow
  observations : List (String × String)
  deriving Repr, BEq

private def displayName (name : String) : String :=
  if name.toList.all (fun c => c.isAlphanum || c == '_') &&
      (name.toList.head?.any (fun c => c.isAlpha || c == '_')) then name
  else s!"‘{name}’"

/-- Bind names and ICs by stable IDs, following the compiled state order. -/
def overview {b : Body} {e : Evolution} (p : ContinuousModel b e) : Except String ModelOverview := do
  if e.states.length > 32 || b.observations.length > 64 then
    throw "Model overview limit exceeded (32 states, 64 observations)."
  let names := fun i : Fin e.states.length =>
    let name := ((b.program.inputs.find? (·.id == e.states[i].stateId)).map (·.name)).getD
      e.states[i].stateId
    if name == e.axis.name then s!"{displayName name}[state:{e.states[i].stateId}]"
    else displayName name
  let labels := [e.axis.name,e.axis.id] ++ b.program.inputs.flatMap (fun p => [p.name,p.id]) ++
    e.states.flatMap (fun s => [s.stateId,s.derivativeId,s.initialId]) ++
    b.observations.flatMap (fun o => [o.port.name,o.port.id,o.sourceId])
  if labels.any (fun s => !validText s) then throw "Model label contains an XML-invalid control character."
  if labels.any (fun s => s.length > 100) then throw "Model label limit exceeded (100 characters)."
  let rows ← (List.finRange e.states.length).mapM fun i => do
    let rhs ← expression names 32 (p.rates.expressions i)
    let initial := rational (p.initials i)
    if initial.length > 100 then throw "Initial value display limit exceeded."
    return StateRow.mk e.states[i].stateId e.states[i].derivativeId e.states[i].initialId
      (names i) s!"d{names i}/d{displayName e.axis.name} = {rhs}" initial
  let start := rational e.start
  if start.length > 100 then throw "Start value display limit exceeded."
  return ⟨displayName e.axis.name, e.axis.id, start, rows,
    b.observations.map (fun o => (displayName o.port.name, o.sourceId))⟩

/-- An explicitly labelled overview of the compiled vector field and integrator.
The separate raw view retains every structural atomic and all trace wires. -/
def ModelOverview.scene (model : ModelOverview) : Element := Id.run do
  let fieldWidth := max 390 (model.states.foldl (fun w s => max w (s.equation.length*9+40)) 0)
  let initialWidth := model.states.foldl (fun w s =>
    max w ((s.name.length+model.start.length+s.initial.length+10)*9+40)) 240
  let integratorWidth := max initialWidth ((model.axis.length+20)*9+40)
  let outputWidth := model.states.foldl (fun w s => max w (s.name.length*9+75))
    (max 180 (model.states.length*12+60))
  let fieldLeft := max 100 (40+model.states.length*12)
  let integratorX := fieldLeft + fieldWidth + 110
  let totalWidth := max (integratorX + integratorWidth + outputWidth)
    ((model.axis.length+model.axisId.length+model.start.length+40)*9)
  let fieldHeight := max 130 (model.states.length*90+60)
  let mut items := [label 35 35 "Continuous circuit · compiled model overview" 20,
    label 35 62 s!"Axis {model.axis} [{model.axisId}] • start {model.start} • exact coefficients" 14,
    box fieldLeft 100 fieldWidth fieldHeight,
    label (fieldLeft+20) 125 "Compiled vector field" 15,
    box integratorX 100 integratorWidth fieldHeight,
    label (integratorX+20) 125 s!"Integrate along {model.axis}" 15]
  for (row,i) in model.states.zipIdx do
    let y := 165 + i*90
    items := items ++ [.tag "g" [] [
      .tag "title" [] [.text s!"state: {row.id}; derivative: {row.derivativeId}; initial: {row.initialId}"],
      label (fieldLeft+20) y row.equation,
      line [(fieldWidth+fieldLeft,y),(integratorX,y)], arrow integratorX y,
      label (integratorX+20) y s!"∫  →  {row.name}",
      label (integratorX+20) (y+24) s!"{row.name}({model.start}) = {row.initial}" 13,
      line [(integratorX+integratorWidth,y),(totalWidth-30,y)], arrow (totalWidth-30) y,
      label (integratorX+integratorWidth+15) (y-10) s!"{i}: {row.name}" 12]]
  for (row,i) in model.states.zipIdx do
    let y := 165+i*90
    let bottom := fieldHeight+140+i*28
    let right := totalWidth-50-i*12
    let left := 20+i*12
    items := items ++ [.tag "circle" [("cx",toString right),("cy",toString y),
        ("r","3"),("fill","#a65328")] [], line [(right,y),(right,bottom),(left,bottom),(left,y),(fieldLeft,y)]
        "#a65328", arrow fieldLeft y "#a65328",
      label (fieldLeft+20) (bottom-7) s!"Feedback {i}: {row.name}" 12]
  let bottom := fieldHeight+140+model.states.length*28
  items := items ++ [label 35 (bottom+20) "Observations (declared order):" 13]
  for ((name,id),i) in model.observations.zipIdx do
    items := items ++ [label 35 (bottom+45+i*22) s!"{i}: {name} ← {id}" 13]
  let footer := bottom+45+model.observations.length*22
  items := items ++ [
    label 35 footer "Crossings are not junctions. IC inputs are read at the start time." 12,
    label 35 (footer+25) "Diagram only. Existence, uniqueness and bounds require separate proofs." 12]
  let observationWidth := model.observations.foldl
    (fun w (name,id) => max w ((name.length+id.length+15)*9+70)) totalWidth
  return svg observationWidth (footer+50) items

end Gimle.Asgard.Visualization
