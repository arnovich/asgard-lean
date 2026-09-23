import Gimle.Asgard.Simulation.Protocol

open Gimle.Asgard.Simulation

#eval (show IO Unit from do
  let invalid := ["{\"a\":1,\"a\":2}", "{\"a\":1,\"\\u0061\":2}", "1e1000000000", "1e-1000000000",
    String.ofList (List.replicate 513 '1'),
    String.ofList (List.replicate 151 '[')]
  for s in invalid do
    if (preflight s).isOk then throw (IO.userError "accepted unbounded/ambiguous JSON")
  if !(preflight "{\"a\":[1.5,-1e-10],\"b\":{\"a\":1}}").isOk then
    throw (IO.userError "rejected valid nested JSON")

)

open Gimle.Asgard Lean

private def original : Request 1 1 where
  circuit := .id
  inputs := [⟨"x", "x", .input⟩]
  outputs := [⟨"y", "y", .output⟩]
  requestId := "response-tests"
  artifactId := "original-id"
  settings := .points #[#[1]]

private def response : Except String Json := do
  return Json.mkObj [("schema", toJson responseSchema), ("kind", toJson "observation"),
    ("request", ← original.toJson), ("trajectory", encodeRows #[#[1.0]]),
    ("times", Json.null), ("provenance", Json.mkObj [
      ("worker", toJson "gimle.asgard.lean_worker/v1"), ("package", toJson "test"),
      ("python", toJson "test"), ("jax", toJson "test"),
      ("arithmetic", toJson "cpu-binary64-materialized"), ("module", toJson "test")]),
    ("diagnostics", Json.mkObj [("certifiedError", Json.null), ("message", toJson "empirical")])]

#eval (show IO Unit from do
  let good ← IO.ofExcept (response.mapError IO.userError)
  unless (decodeObservation original good.compress).isOk do
    throw (IO.userError "valid observation rejected")
  let request ← IO.ofExcept (original.toJson.mapError IO.userError)
  let model := request.getObjValD "model"
  let settings := request.getObjValD "settings"
  let badRequests := [request.setObjVal! "artifactId" (toJson "other"),
    request.setObjVal! "requestId" (toJson "other"),
    request.setObjVal! "model" (model.setObjVal! "pythonSemantics" (toJson "other")),
    request.setObjVal! "model" (model.setObjVal! "exactCircuit" (toJson (["split"] : List String))),
    request.setObjVal! "model" (model.setObjVal! "inputs" (model.getObjValD "outputs")),
    request.setObjVal! "settings" (settings.setObjVal! "method" (toJson "euler")),
    request.setObjVal! "settings" (settings.setObjVal! "points" (encodeRows #[#[2.0]]))]
  for bad in badRequests do
    if (decodeObservation original (good.setObjVal! "request" bad).compress).isOk then
      throw (IO.userError "accepted changed original binding")
  let badResponses := [good.setObjVal! "kind" (toJson "PROVEN"),
    good.setObjVal! "trajectory" (toJson (#[] : Array Json)),
    good.setObjVal! "trajectory" (encodeRows #[#[]]),
    good.setObjVal! "trajectory" (Json.arr #[Json.arr #[Json.str "NaN"]]),
    good.setObjVal! "times" (toJson (#[0.0] : Array Float)),
    good.setObjVal! "diagnostics" ((good.getObjValD "diagnostics").setObjVal! "certifiedError" (toJson (0 : Nat)))]
  for bad in badResponses do
    if (decodeObservation original bad.compress).isOk then
      throw (IO.userError "accepted malformed/authoritative response")
  for q in [(1/2 : Rat), 1/3, 9007199254740993] do
    let bad := {original with circuit := .scalar q}
    if bad.toJson.isOk then throw (IO.userError "accepted unsupported coefficient")
  let big := {original with circuit := .scalar 9007199254740992}
  unless big.toJson.isOk do throw (IO.userError "rejected exact binary64 boundary")

)

#eval (show IO Unit from do
  let good ← IO.ofExcept (response.mapError IO.userError)
  for value in ([1, 1e-10, 1.2345678901234567, 1e100,
      Float.ofBits 1, Float.ofBits 9223372036854775808] : List Float) do
    let r := {original with settings := .points #[#[value]]}
    let request ← IO.ofExcept (r.toJson.mapError IO.userError)
    let encoded := (good.setObjVal! "request" request).setObjVal! "trajectory" (encodeRows #[#[value]])
    let decoded ← IO.ofExcept ((decodeObservation r encoded.compress).mapError IO.userError)
    unless ((decoded.trajectory[0]!)[0]!).toBits == value.toBits do
      throw (IO.userError "numeric bits changed")
  let r := {original with
    inputs := [⟨"x", "x", .state⟩]
    settings := .euler #[1] 0 0.5 2}
  let request ← IO.ofExcept (r.toJson.mapError IO.userError)
  let good := (good.setObjVal! "request" request).setObjVal! "trajectory" (encodeRows #[#[1], #[1.5], #[2.25]])
  let good := good.setObjVal! "times" (toJson ((#[0, 0.5, 1] : Array Float).map encodeFloat))
  unless (decodeObservation r good.compress).isOk do throw (IO.userError "valid Euler response rejected")
  let malformed := [good.setObjVal! "trajectory" (encodeRows #[#[2], #[1.5], #[2.25]]),
    good.setObjVal! "times" (toJson ((#[0, 0.5] : Array Float).map encodeFloat)),
    good.setObjVal! "times" (toJson ((#[0, 0.75, 1] : Array Float).map encodeFloat)),
    good.setObjVal! "times" (toJson (["f64:9218868437227405312", encodeFloat 0.5, encodeFloat 1] : List String))]
  for bad in malformed do
    if (decodeObservation r bad.compress).isOk then throw (IO.userError "accepted malformed Euler response")
  let settings := request.getObjValD "settings"
  for (field, value) in [("start", toJson (encodeFloat 1)), ("step", toJson (encodeFloat 0.25)), ("steps", toJson (3 : Nat))] do
    let bad := good.setObjVal! "request" (request.setObjVal! "settings" (settings.setObjVal! field value))
    if (decodeObservation r bad.compress).isOk then throw (IO.userError "accepted changed Euler settings")
)
