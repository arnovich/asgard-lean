import Gimle.Asgard.Visualization.Model
import ProofWidgets.Component.HtmlDisplay

/-! Optional Infoview adapter. The same element tree is used by SVG export. -/
namespace Gimle.Asgard.Visualization
open Lean ProofWidgets

meta def Element.html : Element → Html
  | .text value => .text value
  | .tag name attributes children => .element name
      (attributes.map (fun (key,value) =>
        (if key == "font-size" then "fontSize" else if key == "font-family" then "fontFamily"
        else if key == "stroke-width" then "strokeWidth" else key, Json.str value))).toArray
      (children.map Element.html).toArray

meta def display (result : Except String Element) : Html := match result with
  | .error message => .element "p" #[] #[.text s!"Cannot display circuit: {message}"]
  | .ok scene => .element "div" #[("style", json% {overflow: "auto", maxHeight: "650px"})]
      #[scene.html]

meta def circuit {n m : Nat} (c : Gimle.Asgard.Circuit n m) : Html :=
  display ((ofCircuit c).map Diagram.scene)

meta def dynamics {n m : Nat} (c : Dynamics.Circuit n m) : Html :=
  display ((ofDynamics c).map Diagram.scene)

meta def model {b : Model.Body} {e : Model.Evolution} (p : Model.ContinuousModel b e) : Html :=
  .element "div" #[] #[display ((overview p).map ModelOverview.scene),
    .element "details" #[] #[.element "summary" #[] #[.text "Full circuit with trace and IC ports"],
      dynamics p.feedback],
    .element "details" #[] #[.element "summary" #[] #[.text "Observation circuit"],
      circuit p.outputs.circuit]]
end Gimle.Asgard.Visualization
