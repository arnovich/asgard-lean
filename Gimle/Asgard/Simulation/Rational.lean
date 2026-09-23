import Gimle.Asgard.Compile.RationalInterchange
import Gimle.Asgard.Simulation.Client

/-! V2 retains exact mathematical data. Binary64 conversion is an explicit
numerical operation and grants neither proof authority nor an accuracy bound. -/
namespace Gimle.Asgard.Simulation.Rational
open Lean Polynomial Interchange.RationalWire

def requestSchema := "asgard.simulation-request/v2"
def responseSchema := "asgard.simulation-response/v2"
def modelSchema := "gimle.asgard.polynomial-circuit/v2"

def rationalJson (q : ℚ) : Json := (literalEncode q).toJson

def admitRational (q : ℚ) : Except String Unit := do
  if (toString q.num.natAbs).length > 512 || (toString q.den).length > 512 then
    throw "rational digit limit"

/-- Round the COMPLETE integer to 53 significant bits, ties to even. Lean's
stock Float.ofNat first truncates large integers to 64 bits, which can lose the
sticky bit deciding a later tie. Only the rounded mantissa reaches Float here. -/
def integerFloat (value : Int) : Float := Id.run do
  let n := value.natAbs
  let shift := n.log2 - 52
  let high := n >>> shift
  let low := n - (high <<< shift)
  let half := 2 ^ (shift - 1)
  let increment := shift > 0 && (low > half || (low == half && high % 2 == 1))
  let mantissa := if increment then high + 1 else high
  let result := Float.ofBinaryScientific mantissa (Int.ofNat shift)
  return if value < 0 then -result else result

/-- Integer rounding followed by binary64 division, matching the worker policy.
A finite rational may be unsupported because an integer intermediate overflows. -/
def numericalValue (q : ℚ) : Except String Float := do
  let numerator := integerFloat q.num
  let denominator := integerFloat (Int.ofNat q.den)
  let result := numerator / denominator
  if !numerator.isFinite || !denominator.isFinite || !result.isFinite ||
      (q != 0 && result == 0) then throw "unsupported numerical rational conversion"
  return result

private def admitTree : Interchange.RawCircuit → Nat → Nat → Except String (Nat × Nat × Nat)
  | _, 0, _ => throw "circuit depth limit"
  | _, _, 0 => throw "circuit node limit"
  | tree, depth + 1, fuel + 1 => do
    match tree with
    | .id => return (fuel, 1, 1)
    | .add | .multiplication => return (fuel, 2, 1)
    | .split => return (fuel, 1, 2)
    | .swap => return (fuel, 2, 2)
    | .terminal => return (fuel, 1, 0)
    | .constant q => admitRational q; return (fuel, 0, 1)
    | .scalar q => admitRational q; return (fuel, 1, 1)
    | .compose a b =>
      let (rest, n, m) ← admitTree a depth fuel
      let (rest, k, o) ← admitTree b depth rest
      if m != k then throw "composition interface mismatch"
      return (rest, n, o)
    | .parallel a b =>
      let (rest, n, m) ← admitTree a depth fuel
      let (rest, k, o) ← admitTree b depth rest
      if n + k > 64 || m + o > 64 then throw "wire limit"
      return (rest, n + k, m + o)

structure Initialization where
  values : Array ℚ
  start : ℚ
  axis : String

def Initialization.toJson (i : Initialization) : Json := Json.mkObj [
  ("values", .arr (i.values.map rationalJson)), ("start", rationalJson i.start),
  ("axis", .str i.axis)]

inductive Settings where
  | points (rows : Array (Array Float))
  | euler (step : Float) (steps : Nat)

def Settings.toJson : Settings → Json
  | .points rows => Json.mkObj [("method", .str "points"), ("points", encodeRows rows)]
  | .euler step steps => Json.mkObj [("method", .str "euler"),
      ("step", .str (encodeFloat step)), ("steps", Lean.toJson steps)]

structure Request (n m : Nat) where
  circuit : Circuit n m
  inputs : List Port
  outputs : List Port
  sourceIds : List String
  outputSources : List String
  initialization : Option Initialization := none
  requestId : String
  artifactId : String
  settings : Settings

/-- This derived numerical view never replaces exact request data. -/
def Request.numericalSettings {n m : Nat} (r : Request n m) :
    Except String Simulation.Settings := do
  match r.settings, r.initialization with
  | .points rows, none => return .points rows
  | .euler step steps, some initial =>
    return .euler (← initial.values.mapM numericalValue) (← numericalValue initial.start) step steps
  | _, _ => throw "initialization/method mismatch"

private def label (value : String) : Except String Unit := do
  if value.isEmpty || value.utf8ByteSize > 128 then throw "invalid label"

/-- V2 accepts cross-direction display names while retaining distinct port IDs.
Source references are checked metadata, not authentication of an external source. -/
def Request.toJson {n m : Nat} (r : Request n m) : Except String Json := do
  if n > 64 || m > 64 || r.inputs.length != n || r.outputs.length != m ||
      r.outputSources.length != m then throw "interface length/wire limit"
  if !validPorts r.inputs || !validPorts r.outputs ||
      !(decide (((r.inputs ++ r.outputs).map Port.id).Nodup)) then throw "duplicate port identity/name"
  if !(r.inputs.all (fun p => p.role != .output)) ||
      !(r.outputs.all (fun p => p.role == .output)) then throw "invalid port role"
  if r.sourceIds.length > 1024 || !(decide r.sourceIds.Nodup) ||
      !(r.inputs.all (fun p => r.sourceIds.contains p.id)) ||
      !(r.outputSources.all r.sourceIds.contains) then throw "invalid source catalog/reference"
  for value in [r.requestId, r.artifactId] ++ r.sourceIds ++
      (r.inputs ++ r.outputs).flatMap (fun p => [p.id, p.name]) do label value
  let _ ← admitTree (Interchange.encode r.circuit) 65 1024
  if let some initial := r.initialization then
    label initial.axis
    if initial.values.size != n then throw "initial dimension mismatch"
    for value in initial.values do admitRational value
    admitRational initial.start
  let numerical ← r.numericalSettings
  validateSettings numerical n m r.inputs
  let outputs := List.zipWith (fun p source => Json.mkObj [
    ("id", .str p.id), ("name", .str p.name), ("role", .str "output"),
    ("sourceId", .str source)]) r.outputs r.outputSources
  let model := Json.mkObj [
    ("schema", .str modelSchema), ("fragment", .str fragmentVersion),
    ("pythonSemantics", .str Interchange.pythonSemantics), ("coefficients", .str "rationals"),
    ("inputs", .arr (r.inputs.map Interchange.portJson).toArray),
    ("outputs", .arr outputs.toArray), ("sourceIds", Lean.toJson r.sourceIds),
    ("exactCircuit", (encodeCircuit r.circuit).toJson),
    ("initialization", r.initialization.map Initialization.toJson |>.getD .null)]
  let result := Json.mkObj [("schema", .str requestSchema),
    ("numericEncoding", .str "binary64-bits-decimal/v1"), ("requestId", .str r.requestId),
    ("artifactId", .str r.artifactId), ("model", model), ("settings", r.settings.toJson)]
  if result.compress.utf8ByteSize > maxRequestBytes then throw "request byte limit"
  return result

structure Observation {n m : Nat} (original : Request n m) extends ResponseData

def decodeObservation {n m : Nat} (original : Request n m) (text : String) :
    Except String (Observation original) := do
  return ⟨← decodeResponse (← original.toJson) (← original.numericalSettings) m
    responseSchema "gimle.asgard.lean_worker/v2" text⟩

def run {n m : Nat} (request : Request n m) (worker : Worker)
    (cancelled : IO.Ref Bool) : IO (Observation request) := do
  let payload ← IO.ofExcept (request.toJson.mapError IO.userError)
  runPayload payload (decodeObservation request) worker cancelled

end Gimle.Asgard.Simulation.Rational
