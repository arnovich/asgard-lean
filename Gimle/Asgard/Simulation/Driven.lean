import Gimle.Asgard.Simulation.Rational

/-! Driven Euler requests: a compiled right-hand side on `[drivers, states]`,
exact initial data, and one exact rational sample of every driver coordinate per
Euler interval, on the uniform grid of the rational v2 request.

This is its own request family, `asgard.driven-simulation-request/v1`; the
rational v2 request and its decoding are unchanged. The runtime holds each
sample row on its interval `[t_i, t_{i+1})` (`holdConvention`): step `i` uses
the states at `t_i` and sample row `i`. That held sequence is the runtime's
driver, **not** the declared one. A piecewise-constant signal is generally not
continuous, and a held derivative-port sample is not the derivative of a held
driver sample, so a held sequence is never admitted by `Evolution.Admitted`,
and a run says nothing about the driven relation of `Model.Driven`. Results are
binary64 observations, as for every request here.

Binary64 enters at the same named points as in v2: the step, and
`Rational.numericalValue` for the initial values, the start and the samples.
The request carries the samples exactly; their conversion is checked when the
request is encoded, so a sample the runtime cannot represent is refused. -/
namespace Gimle.Asgard.Simulation.Driven
open Lean Polynomial Interchange.RationalWire Rational

def requestSchema := "asgard.driven-simulation-request/v1"
def responseSchema := "asgard.driven-simulation-response/v1"
def workerVersion := "gimle.asgard.lean_worker/driven-v1"
/-- Sample row `i` is applied on `[t_i, t_{i+1})`, by forward Euler from `t_i`. -/
def holdConvention := "zero-order-previous"
/-- The worker's fixed statement, required in every decoded driven response. -/
def heldMessage :=
  "Numerical observations only; drivers held as zero-order samples, not the declared signal; " ++
    "no accuracy, stability or proof claim"

/-- One driver coordinate: its `.driver` port, and, for a derivative port, the
ID of the driver whose declared derivative it is. -/
structure DriverPort where
  port : Port
  derivativeOf : Option String := none

def DriverPort.toJson (d : DriverPort) : Json := Json.mkObj [
  ("id", .str d.port.id), ("derivativeOf", d.derivativeOf.map Json.str |>.getD .null)]

/-- The field reads `k` driver coordinates, then `s` states, and returns the
`s` state derivatives. -/
structure Request (k s : Nat) where
  circuit : Circuit (k + s) s
  drivers : List DriverPort
  states : List Port
  outputs : List Port
  sourceIds : List String
  outputSources : List String
  initialization : Initialization
  requestId : String
  artifactId : String
  step : Float
  steps : Nat
  samples : Array (Array ℚ)

/-- The explicitly approximate view of the state trajectory the runtime returns:
Euler over the states, on the uniform grid. -/
def Request.numericalSettings {k s : Nat} (r : Request k s) : Except String Simulation.Settings :=
  return .euler (← r.initialization.values.mapM numericalValue)
    (← numericalValue r.initialization.start) r.step r.steps

/-- The binary64 samples the runtime applies, one row per interval. -/
def Request.numericalSamples {k s : Nat} (r : Request k s) : Except String (Array (Array Float)) :=
  r.samples.mapM (·.mapM numericalValue)

/-- A derivative port names another driver port, which is not itself a
derivative, and no driver has two derivative ports. -/
private def checkDerivatives (drivers : List DriverPort) : Except String Unit := do
  let ids := drivers.map (·.port.id)
  let targets := drivers.filterMap (·.derivativeOf)
  if !(decide targets.Nodup) then throw "driver with two derivative ports"
  for d in drivers do
    if let some target := d.derivativeOf then
      if target == d.port.id || !ids.contains target then throw "unknown derivative driver"
      if (drivers.find? (·.port.id == target)).any (·.derivativeOf.isSome) then
        throw "derivative of a derivative port"

def Request.toJson {k s : Nat} (r : Request k s) : Except String Json := do
  let inputs := r.drivers.map (·.port) ++ r.states
  if k == 0 then throw "driven request needs a driver"
  if k + s > 64 || s == 0 || r.drivers.length != k || r.states.length != s ||
      r.outputs.length != s || r.outputSources.length != s then
    throw "interface length/wire limit"
  if !validPorts inputs || !validPorts r.outputs ||
      !(decide (((inputs ++ r.outputs).map Port.id).Nodup)) then throw "duplicate port identity/name"
  if !(r.drivers.all (·.port.role == .driver)) || !(r.states.all (·.role == .state)) ||
      !(r.outputs.all (·.role == .output)) then throw "invalid port role"
  checkDerivatives r.drivers
  if r.sourceIds.length > 1024 || !(decide r.sourceIds.Nodup) ||
      !(inputs.all (fun p => r.sourceIds.contains p.id)) ||
      !(r.outputSources.all r.sourceIds.contains) then throw "invalid source catalog/reference"
  for value in [r.requestId, r.artifactId, r.initialization.axis] ++ r.sourceIds ++
      (inputs ++ r.outputs).flatMap (fun p => [p.id, p.name]) do label value
  let _ ← admitTree (Interchange.encode r.circuit) 65 1024
  if r.initialization.values.size != s then throw "initial dimension mismatch"
  for value in r.initialization.values do admitRational value
  admitRational r.initialization.start
  validateSettings (← r.numericalSettings) s s r.states
  if r.samples.size != r.steps then throw "driver sample count mismatch"
  if !(r.samples.all (·.size == k)) then throw "driver sample dimension mismatch"
  for row in r.samples do
    for value in row do admitRational value
  let _ ← r.numericalSamples
  let outputs := List.zipWith (fun p source => Json.mkObj [
    ("id", .str p.id), ("name", .str p.name), ("role", .str "output"),
    ("sourceId", .str source)]) r.outputs r.outputSources
  let model := Json.mkObj [
    ("schema", .str modelSchema), ("fragment", .str fragmentVersion),
    ("pythonSemantics", .str Interchange.pythonSemantics), ("coefficients", .str "rationals"),
    ("inputs", .arr (inputs.map Interchange.portJson).toArray),
    ("drivers", .arr (r.drivers.map DriverPort.toJson).toArray),
    ("outputs", .arr outputs.toArray), ("sourceIds", Lean.toJson r.sourceIds),
    ("exactCircuit", (encodeCircuit r.circuit).toJson),
    ("initialization", r.initialization.toJson)]
  let settings := Json.mkObj [("method", .str "euler"),
    ("step", .str (encodeFloat r.step)), ("steps", Lean.toJson r.steps),
    ("hold", .str holdConvention),
    ("samples", .arr (r.samples.map fun row => .arr (row.map rationalJson)))]
  let result := Json.mkObj [("schema", .str requestSchema),
    ("numericEncoding", .str "binary64-bits-decimal/v1"), ("requestId", .str r.requestId),
    ("artifactId", .str r.artifactId), ("model", model), ("settings", settings)]
  if result.compress.utf8ByteSize > maxRequestBytes then throw "request byte limit"
  return result

/-- A state trajectory on the uniform grid, bound to the caller's request, whose
diagnostics state `heldMessage`: the drivers were held samples, not the
declared signal. -/
structure Observation {k s : Nat} (original : Request k s) extends ResponseData

def decodeObservation {k s : Nat} (original : Request k s) (text : String) :
    Except String (Observation original) := do
  let data ← decodeResponse (← original.toJson) (← original.numericalSettings) s
    responseSchema workerVersion text
  unless (← data.diagnostics.getObjValAs? String "message") == heldMessage do
    throw "driver hold not stated"
  return ⟨data⟩

def run {k s : Nat} (request : Request k s) (worker : Worker)
    (cancelled : IO.Ref Bool) : IO (Observation request) := do
  let payload ← IO.ofExcept (request.toJson.mapError IO.userError)
  runPayload payload (decodeObservation request) worker cancelled

end Gimle.Asgard.Simulation.Driven
