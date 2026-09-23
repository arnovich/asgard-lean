import Gimle.Asgard.Examples.RationalExecution

open Gimle.Asgard Gimle.Asgard.Simulation Gimle.Asgard.Examples.RationalExecution Lean

private def response (request : Json) (rows : Array (Array Float)) (times : Json) : Json :=
  Json.mkObj [("schema", .str Rational.responseSchema), ("kind", .str "observation"),
    ("request", request), ("trajectory", encodeRows rows), ("times", times),
    ("provenance", Json.mkObj [("worker", .str "gimle.asgard.lean_worker/v2"),
      ("package", .str "test"), ("python", .str "test"), ("jax", .str "test"),
      ("arithmetic", .str "cpu-binary64-materialized"), ("module", .str "test")]),
    ("diagnostics", Json.mkObj [("certifiedError", .null), ("message", .str "observations")])]

#eval (show IO Unit from do
  let req ← IO.ofExcept (pointRequest.toJson.mapError IO.userError)
  let good := response req #[#[-2, 0.5]] .null
  unless (Rational.decodeObservation pointRequest good.compress).isOk do
    throw (IO.userError "rejected valid rational observation")
  let model := req.getObjValD "model"
  let outputs ← IO.ofExcept ((model.getObjValD "outputs").getArr?.mapError IO.userError)
  let badModels := [model.setObjVal! "exactCircuit" (toJson (["id"] : List String)),
    model.setObjVal! "outputs" (.arr outputs.reverse),
    model.setObjVal! "sourceIds" (toJson (["other"] : List String)),
    model.setObjVal! "outputs" (.arr (outputs.set! 0 ((outputs[0]!).setObjVal! "sourceId" (.str "state-x"))))]
  for bad in badModels do
    let altered := good.setObjVal! "request" (req.setObjVal! "model" bad)
    if (Rational.decodeObservation pointRequest altered.compress).isOk then
      throw (IO.userError "accepted altered original exact model")
  let badRequests := [{pointRequest with outputs := [⟨"state-x", "y", .output⟩, ⟨"obs-x", "x", .output⟩]},
    {pointRequest with outputs := [⟨"obs-y", "x", .output⟩, ⟨"obs-x", "x", .output⟩]},
    {pointRequest with outputSources := ["missing", "state-x"]},
    {pointRequest with sourceIds := ["state-x", "state-x"]}]
  for bad in badRequests do
    if bad.toJson.isOk then throw (IO.userError "accepted invalid v2 interface")
  let req ← IO.ofExcept (eulerRequest.toJson.mapError IO.userError)
  let .euler initial start step steps ← IO.ofExcept (eulerRequest.numericalSettings.mapError IO.userError)
    | throw (IO.userError "wrong method")
  let times := toJson ((Array.ofFn (n := 3) (fun i => start + i.val.toFloat * step)).map encodeFloat)
  let good := response req (Array.replicate (steps + 1) initial) times
  unless (Rational.decodeObservation eulerRequest good.compress).isOk do
    throw (IO.userError "rejected valid bound Euler response")
  let model := req.getObjValD "model"
  let init := model.getObjValD "initialization"
  for (key, value) in [("start", Rational.rationalJson 1),
      ("values", .arr #[Rational.rationalJson 0, Rational.rationalJson 0]), ("axis", .str "other")] do
    let changed := req.setObjVal! "model" (model.setObjVal! "initialization" (init.setObjVal! key value))
    if (Rational.decodeObservation eulerRequest (good.setObjVal! "request" changed).compress).isOk then
      throw (IO.userError "accepted altered exact initialization")
  for bad in [good.setObjVal! "trajectory" (encodeRows #[#[0,0], initial, initial]),
      good.setObjVal! "times" (toJson ((#[0,1,2] : Array Float).map encodeFloat)),
      good.setObjVal! "schema" (.str Simulation.responseSchema)] do
    if (Rational.decodeObservation eulerRequest bad.compress).isOk then
      throw (IO.userError "accepted malformed rational Euler response")
  let big : Int := 2^64 + 2^11 + 1
  unless (Rational.integerFloat big).toBits == (Float.ofNat (2^64 + 4096)).toBits &&
      (Rational.integerFloat (-big)).toBits == (-(Float.ofNat (2^64 + 4096))).toBits do
    throw (IO.userError "lost large-integer rounding sticky bit")
  unless (Rational.numericalValue (1 / (10^308 : ℚ))).isOk do
    throw (IO.userError "rejected supported subnormal")
  for q in [((10^400 + 1 : ℚ)/(10^400 + 3)), (1/(10^400 : ℚ))] do
    unless (Rational.admitRational q).isOk do throw (IO.userError "rejected exact rational")
    if (Rational.numericalValue q).isOk then throw (IO.userError "accepted unsupported conversion")
)
