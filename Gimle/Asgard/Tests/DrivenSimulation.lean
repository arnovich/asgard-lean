import Gimle.Asgard.Model.Execution
import Gimle.Asgard.Examples.DrivenForcing

/-! Regression tests for driven Euler requests (task 041), built from the
compiled `Examples.DrivenForcing` model: `D_t(x) = (du + u) - x` over `[u, du, x]`,
with `du` the declared derivative port of `u`. -/
open Gimle.Asgard Gimle.Asgard.Simulation Gimle.Asgard.Examples.DrivenForcing Lean

private def request (samples : Array (Array ℚ)) :
    Except String (Driven.Request (Model.DriverBinding.width drivers) evolution.states.length) :=
  model.model.eulerRequest "driven-regression" "driven-forcing" 0.5 2 samples

private def response (request : Json) (rows : Array (Array Float)) (times : Json)
    (schema : String := Driven.responseSchema) (worker : String := Driven.workerVersion)
    (message : String := Driven.heldMessage) : Json :=
  Json.mkObj [("schema", .str schema), ("kind", .str "observation"),
    ("request", request), ("trajectory", encodeRows rows), ("times", times),
    ("provenance", Json.mkObj [("worker", .str worker),
      ("package", .str "test"), ("python", .str "test"), ("jax", .str "test"),
      ("arithmetic", .str "cpu-binary64-materialized"), ("module", .str "test")]),
    ("diagnostics", Json.mkObj [("certifiedError", .null), ("message", .str message)])]

/-- The same interface with no driver, reading only the state. -/
private def undriven {k s : Nat} (good : Driven.Request k s) : Driven.Request 0 s where
  circuit := Polynomial.route fun i => Fin.cast (Nat.zero_add s).symm i
  drivers := []
  states := good.states
  outputs := good.outputs
  sourceIds := good.sourceIds
  outputSources := good.outputSources
  initialization := good.initialization
  requestId := good.requestId
  artifactId := good.artifactId
  step := good.step
  steps := 1
  samples := #[#[]]

private def refuses (r : Except String Json) (reason : String) : IO Unit :=
  match r with
  | .ok _ => throw (IO.userError s!"accepted a request that should fail with {reason}")
  | .error message => unless message == reason do
      throw (IO.userError s!"expected {reason}, got {message}")

#eval (show IO Unit from do
  let good ← IO.ofExcept ((request #[#[0, 1], #[1 / 2, 7 / 8]]).mapError IO.userError)
  let json ← IO.ofExcept (good.toJson.mapError IO.userError)
  -- Drivers and derivative roles come from the declaration, in coordinate order.
  let model := json.getObjValD "model"
  unless model.getObjValD "drivers" == .arr #[
      Json.mkObj [("id", .str "driver-u"), ("derivativeOf", .null)],
      Json.mkObj [("id", .str "driver-du"), ("derivativeOf", .str "driver-u")]] do
    throw (IO.userError "driver roles lost")
  let settings := json.getObjValD "settings"
  unless settings.getObjValD "hold" == .str Driven.holdConvention &&
      json.getObjValD "schema" == .str Driven.requestSchema do
    throw (IO.userError "hold convention or schema missing")
  unless settings.getObjValD "samples" == .arr #[
      .arr #[Rational.rationalJson 0, Rational.rationalJson 1],
      .arr #[Rational.rationalJson (1 / 2), Rational.rationalJson (7 / 8)]] do
    throw (IO.userError "samples not carried exactly")
  -- One sample row per interval, one value per driver coordinate.
  refuses ((← IO.ofExcept ((request #[#[0, 1]]).mapError IO.userError)).toJson)
    "driver sample count mismatch"
  refuses ((← IO.ofExcept ((request #[#[0, 1], #[0]]).mapError IO.userError)).toJson)
    "driver sample dimension mismatch"
  -- Hand-built requests must keep the declared driver interface.
  let unknown : List Driven.DriverPort := good.drivers.map fun (d : Driven.DriverPort) =>
    { d with derivativeOf := if d.derivativeOf.isSome then some "driver-x" else none }
  refuses { good with drivers := unknown }.toJson "unknown derivative driver"
  refuses { good with drivers := good.drivers.map fun (d : Driven.DriverPort) =>
    { d with derivativeOf := if d.port.id == "driver-u" then some "driver-u" else none } }.toJson
    "unknown derivative driver"
  refuses { good with drivers := good.drivers.map fun (d : Driven.DriverPort) =>
    { d with derivativeOf := some "driver-u" } }.toJson "driver with two derivative ports"
  refuses { good with drivers := good.drivers.map fun (d : Driven.DriverPort) =>
    { d with derivativeOf := some (if d.port.id == "driver-u" then "driver-du" else "driver-u") } }.toJson
    "derivative of a derivative port"
  refuses { good with drivers := good.drivers.map fun (d : Driven.DriverPort) =>
    { d with port := { d.port with role := .input } } }.toJson "invalid port role"
  refuses { good with drivers := good.drivers.take 1 }.toJson "interface length/wire limit"
  -- A sample the runtime cannot represent is refused, not approximated.
  refuses ((← IO.ofExcept ((request #[#[0, 1], #[1 / (10 ^ 400 : ℚ), 1]]).mapError IO.userError)).toJson)
    "unsupported numerical rational conversion"
  -- A driven request has a driver.
  refuses (undriven good).toJson "driven request needs a driver"
  -- The response is a state trajectory on the uniform grid, bound to the request.
  let .euler initial start step steps ← IO.ofExcept (good.numericalSettings.mapError IO.userError)
    | throw (IO.userError "wrong method")
  let times := toJson ((Array.ofFn (n := steps + 1) (fun i => start + i.val.toFloat * step)).map encodeFloat)
  let rows := Array.replicate (steps + 1) initial
  unless (Driven.decodeObservation good (response json rows times).compress).isOk do
    throw (IO.userError "rejected valid driven observation")
  for bad in [response json rows times Rational.responseSchema,
      response json rows times Driven.responseSchema "gimle.asgard.lean_worker/v2",
      (response json rows times).setObjVal! "request"
        (json.setObjVal! "settings" (settings.setObjVal! "samples" (.arr #[]))),
      response json (rows.push initial) times,
      response json rows times (message := "observations")] do
    if (Driven.decodeObservation good bad.compress).isOk then
      throw (IO.userError "accepted a mismatched driven observation")
)
