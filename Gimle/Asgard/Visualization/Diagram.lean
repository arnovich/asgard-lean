import Gimle.Asgard.Dynamics.Circuit

/-! Optional, computable circuit pictures. Edges retain ordered typed ports;
layout and SVG carry no proof authority. No UI imports enter the circuit library. -/
namespace Gimle.Asgard.Visualization

structure Endpoint where
  node : Nat
  port : Nat
  deriving Repr, BEq, Inhabited

inductive Operation where
  | identity | constant (q : ℚ) | scalar (q : ℚ) | add | multiply | split | swap | terminal
  | integrate (axis : String) (dimension : Nat)
  deriving Repr, BEq, Inhabited

structure Node where
  operation : Operation
  inputs : Nat
  outputs : Nat
  x : Nat := 0
  y : Nat := 0
  deriving Repr, Inhabited

structure Edge where
  source : Endpoint
  target : Endpoint
  feedback : Bool := false
  -- Return lanes are explicit, so nested traces never pass through their body.
  lane : Nat := 0
  leftRail : Nat := 0
  rightRail : Nat := 0
  feedbackLabel : String := ""
  deriving Repr, BEq, Inhabited

structure Diagram where
  nodes : List Node
  edges : List Edge
  inputs : List Endpoint
  outputs : List Endpoint
  width : Nat
  height : Nat
  deriving Repr, Inhabited

/-- Exact fractions, never rounded display values. -/
def rational (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

def Operation.label : Operation → String
  | .identity => "id" | .constant q => rational q | .scalar q => s!"× ({rational q})"
  | .add => "+" | .multiply => "×" | .split => "split" | .swap => "swap"
  | .terminal => "discard" | .integrate axis n => s!"∫ d{axis} [{n}]"

def Node.width (n : Node) : Nat := max 160 (n.operation.label.length * 9 + 75)

private def checked (g : Diagram) : Except String Diagram :=
  if g.nodes.length > 2048 || g.width > 60000 || g.height > 30000 then
    .error "Diagram exceeds display limits (2048 nodes, 60000×30000). Select a smaller circuit."
  else .ok g

/-- XML 1.0 permits tab/newline/CR and non-control Unicode scalar values. -/
def validText (s : String) : Bool := s.toList.all fun c =>
  c == '\t' || c == '\n' || c == '\r' ||
    (c.toNat >= 32 && c.toNat != 65534 && c.toNat != 65535)

private def atomic (op : Operation) (n m : Nat) : Except String Diagram := do
  if !validText op.label then throw "Label contains an XML-invalid control character."
  if max n m > 64 || op.label.length > 100 then
    throw "Diagram port or label limit exceeded (64 ports, 100 characters)."
  return ⟨[⟨op, n, m, 0, 0⟩], [],
    (List.range n).map (⟨0, ·⟩), (List.range m).map (⟨0, ·⟩),
    max 160 (op.label.length * 9 + 75), 40 * (max 1 (max n m) + 1)⟩

private def offset (e : Endpoint) (n : Nat) : Endpoint := ⟨e.node + n, e.port⟩
private def shifted (g : Diagram) (dx dy dn : Nat) : Diagram :=
  { g with
    nodes := g.nodes.map (fun n => { n with x := n.x + dx, y := n.y + dy })
    edges := g.edges.map (fun e =>
      { e with
        source := offset e.source dn
        target := offset e.target dn
        lane := e.lane + (if e.feedback then dy else dx)
        leftRail := e.leftRail + dx
        rightRail := e.rightRail + dx })
    inputs := g.inputs.map (offset · dn)
    outputs := g.outputs.map (offset · dn) }

private def join (serial : Bool) (a b : Diagram) : Except String Diagram := do
  let gap := 60 + a.outputs.length * 12
  let c := shifted b (if serial then a.width + gap else 0)
    (if serial then 0 else a.height + 40) a.nodes.length
  let links := if serial then ((a.outputs.zip c.inputs).zipIdx).map
    (fun ((s,t),i) => { source := s, target := t, lane := a.width + 25 + i*12 : Edge }) else []
  checked ⟨a.nodes ++ c.nodes, a.edges ++ c.edges ++ links,
    if serial then a.inputs else a.inputs ++ c.inputs,
    if serial then c.outputs else a.outputs ++ c.outputs,
    if serial then a.width + gap + b.width else max a.width b.width,
    if serial then max a.height b.height else a.height + 40 + b.height⟩

private def polynomial : Nat → {n m : Nat} → Gimle.Asgard.Circuit n m → Except String Diagram
  | 0, _, _, _ => .error "Diagram nesting limit exceeded (256). Select a smaller circuit."
  | fuel+1, _, _, circuit => match circuit with
    | .id => atomic .identity 1 1
    | .const q => atomic (.constant q) 0 1
    | .scalar q => atomic (.scalar q) 1 1
    | .add => atomic .add 2 1
    | .multiplication => atomic .multiply 2 1
    | .split => atomic .split 1 2
    | .swap => atomic .swap 2 2
    | .terminal => atomic .terminal 1 0
    | .compose a b => do join true (← polynomial fuel a) (← polynomial fuel b)
    | .parallel a b => do join false (← polynomial fuel a) (← polynomial fuel b)

private def continuous : Nat → {n m : Nat} → Dynamics.Circuit n m → Except String Diagram
  | 0, _, _, _ => .error "Diagram nesting limit exceeded (256). Select a smaller circuit."
  | fuel+1, _, _, circuit => match circuit with
    | .lift c => polynomial fuel c
    | .integrate axis n => atomic (.integrate axis n) (n+n) n
    | .compose a b => do join true (← continuous fuel a) (← continuous fuel b)
    | .parallel a b => do join false (← continuous fuel a) (← continuous fuel b)
    | @Dynamics.Circuit.trace n m k body => do
      if k > 64 then throw "Feedback port limit exceeded (64)."
      let g ← continuous fuel body
      let padding := 40 + k*12
      let bodyWidth := g.width
      let g := shifted g padding (40 * k + 40) 0
      let loops := ((g.outputs.drop m).zip (g.inputs.drop n)).zipIdx |>.map
        fun ((s,t),i) => {
          source := s
          target := t
          feedback := true
          lane := 20+i*40
          leftRail := padding-20-i*12
          rightRail := padding+bodyWidth+20+i*12
          feedbackLabel := s!"feedback: out {m+i} → in {n+i}" : Edge }
      checked { g with
        inputs := g.inputs.take n
        outputs := g.outputs.take m
        edges := g.edges ++ loops
        width := g.width + 2*padding
        height := g.height + 40*k + 40 }

def ofCircuit {n m : Nat} (c : Gimle.Asgard.Circuit n m) : Except String Diagram :=
  polynomial 256 c

def ofDynamics {n m : Nat} (c : Dynamics.Circuit n m) : Except String Diagram :=
  continuous 256 c

/-- A small renderer-owned XML tree, shared by standalone SVG and the widget. -/
inductive Element where
  | text (value : String)
  | tag (name : String) (attributes : List (String × String)) (children : List Element)
  deriving Inhabited

private def escape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;" |>.replace "'" "&apos;"

def Element.xml : Element → String
  | .text s => escape s
  | .tag name attrs children =>
    "<" ++ name ++ String.join (attrs.map fun (k,v) => s!" {k}=\"{escape v}\"") ++ ">" ++
      String.join (children.map Element.xml) ++ "</" ++ name ++ ">"

def label (x y : Nat) (value : String) (size : Nat := 14) : Element :=
  .tag "text" [("x",toString x),("y",toString y),("font-size",toString size),
    ("fill","#172f43"),("textLength",toString (value.length*size*3/5)),
    ("lengthAdjust","spacingAndGlyphs")] [.text value]

def line (points : List (Nat × Nat)) (color : String := "#476579") : Element :=
  .tag "polyline" [("points",String.intercalate " " (points.map fun (x,y) => s!"{x},{y}")),
    ("fill","none"),("stroke",color),("stroke-width","2")] []

/-- Arrows are polygons rather than shared marker IDs: multiple widgets are safe. -/
def arrow (x y : Nat) (color : String := "#476579") : Element :=
  .tag "polygon" [("points",s!"{x},{y} {x-7},{y-4} {x-7},{y+4}"),("fill",color)] []

def box (x y width height : Nat) : Element :=
  .tag "rect" [("x",toString x),("y",toString y),("width",toString width),
    ("height",toString height),("rx","8"),("fill","#edf5f8"),("stroke","#476579")] []

private def coordinate (g : Diagram) (output : Bool) (e : Endpoint) : Nat × Nat :=
  let n := g.nodes[e.node]!
  (80 + n.x + if output then n.width else 0, 50 + n.y + 40 * (e.port+1))

private def renderEdge (g : Diagram) (e : Edge) : List Element :=
  let (sx,sy) := coordinate g true e.source
  let (tx,ty) := coordinate g false e.target
  let points := if e.feedback then
    [(sx,sy),(80+e.rightRail,sy),(80+e.rightRail,50+e.lane),
      (80+e.leftRail,50+e.lane),(80+e.leftRail,ty),(tx,ty)]
    else [(sx,sy),(80+e.lane,sy),(80+e.lane,ty),(tx,ty)]
  let color := if e.feedback then "#a65328" else "#476579"
  let wire := if e.feedback then line points color else
    .tag "path" [("d",s!"M {sx} {sy} C {80+e.lane} {sy} {80+e.lane} {ty} {tx} {ty}"),
      ("fill","none"),("stroke",color),("stroke-width","2"),("data-role","wire")] []
  [wire, arrow tx ty color] ++ if e.feedback then
    [label (tx+8) (44+e.lane) e.feedbackLabel 12] else []

private def renderNode (n : Node) : List Element := Id.run do
  let x := n.x + 80
  let y := n.y + 50
  let height := 40 * (max 1 (max n.inputs n.outputs) + 1)
  let mut contents := [box x (y+10) n.width (height-20), label (x+35) (y+25) n.operation.label 13]
  for i in List.range n.inputs do
    let text := match n.operation with
      | .integrate _ d => if i < d then s!"d{i}" else s!"IC{i-d}"
      | _ => toString i
    contents := contents ++ [label (x+5) (y+40*(i+1)+5) text 11]
  for i in List.range n.outputs do
    contents := contents ++ [label (x+n.width-20) (y+40*(i+1)+5) (toString i) 11]
  -- Show the actual wiring of structural atomics, including uncoupled crossings.
  match n.operation with
  | .identity => contents := contents ++ [line [(x+25,y+40),(x+n.width-30,y+40)]]
  | .split => contents := contents ++ [line [(x+25,y+40),(x+75,y+40),(x+n.width-30,y+40)],
      line [(x+75,y+40),(x+75,y+80),(x+n.width-30,y+80)]]
  | .swap => contents := contents ++ [line [(x+25,y+40),(x+n.width-30,y+80)],
      .tag "path" [("d",s!"M {x+25} {y+80} L {x+130} {y+40}"),
        ("stroke","#edf5f8"),("stroke-width","7")] [],
      line [(x+25,y+80),(x+n.width-30,y+40)]]
  | _ => pure ()
  return contents

def svg (width height : Nat) (children : List Element) : Element :=
  .tag "svg" [("xmlns","http://www.w3.org/2000/svg"),("viewBox",s!"0 0 {width} {height}"),
    ("width",toString width),("height",toString height),("role","img"),
    ("font-family","system-ui, sans-serif")] (
      [.tag "title" [] [.text "Asgard circuit"],
       .tag "rect" [("width","100%"),("height","100%"),("fill","#ffffff")] []] ++ children)

def Diagram.scene (g : Diagram) : Element :=
  let ins := (g.inputs.zipIdx).flatMap fun (e,i) =>
    let (x,y) := coordinate g false e
    [line [(20,y),(x,y)], arrow x y, label 20 (y-8) s!"in {i}" 11]
  let outs := (g.outputs.zipIdx).flatMap fun (e,i) =>
    let (x,y) := coordinate g true e
    [line [(x,y),(g.width+140,y)], arrow (g.width+140) y,
      label (g.width+105) (y-8) s!"out {i}" 11]
  svg (max 640 (g.width+170)) (g.height+140)
    (g.edges.flatMap (renderEdge g) ++ ins ++ outs ++ g.nodes.flatMap renderNode ++
      [label 20 (g.height+90) "Ports start at 0. Crossings are not junctions." 12,
       label 20 (g.height+112) "Diagram of syntax; mathematical claims require separate proofs." 12])

end Gimle.Asgard.Visualization
