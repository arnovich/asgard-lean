import Gimle.Asgard.Compile.Interchange

/-! Optional numerical protocol. Requests retain typed circuits and responses
contain observations only. Neither this module nor its client grants proof authority. -/
namespace Gimle.Asgard.Simulation
open Lean

def requestSchema := "asgard.simulation-request/v1"
def responseSchema := "asgard.simulation-response/v1"
def maxRequestBytes : Nat := 1048576
def maxResponseBytes : Nat := 4194304

/-- Bound parser allocation and reject duplicate keys before the general parser.
Numbers have at most 512 characters and exponent magnitude at most 400. -/
def preflight (text : String) : Except String Unit := do
  if text.utf8ByteSize > maxResponseBytes then throw "response byte limit"
  let chars := text.toList.toArray
  let mut stack : Array (Array String) := #[]
  let mut i := 0
  let mut nodes := 0
  while i < chars.size do
    let c := chars[i]!
    if c == '{' || c == '[' then
      stack := stack.push #[]
      if stack.size > 150 then throw "JSON depth limit"
      nodes := nodes + 1
      i := i + 1
    else if c == '}' || c == ']' then
      if stack.isEmpty then throw "unbalanced JSON"
      stack := stack.pop
      i := i + 1
    else if c == '"' then
      let start := i
      i := i + 1
      let mut closed := false
      while i < chars.size && !closed do
        if chars[i]! == '\\' then i := i + 2
        else if chars[i]! == '"' then
          closed := true
          i := i + 1
        else i := i + 1
      if !closed then throw "unclosed JSON string"
      let mut next := i
      while next < chars.size && chars[next]!.isWhitespace do next := next + 1
      if next < chars.size && chars[next]! == ':' then
        if i - start > 256 || stack.isEmpty then throw "invalid JSON key"
        let key ← (← Json.parse (String.ofList (chars.extract start i).toList)).getStr?
        let keys := stack.back!
        if keys.contains key then throw "duplicate JSON key"
        if keys.size >= 32 then throw "JSON object field limit"
        stack := stack.set! (stack.size - 1) (keys.push key)
      nodes := nodes + 1
    else if c.isDigit || c == '-' then
      let start := i
      while i < chars.size && !(chars[i]!.isWhitespace || [',', ']', '}'].contains chars[i]!) do
        i := i + 1
      if i - start > 512 then throw "JSON number length limit"
      let token := String.ofList (chars.extract start i).toList
      let parts := (token.replace "E" "e").splitOn "e"
      if parts.length > 2 then throw "invalid JSON exponent"
      if let [_, exponent] := parts then
        let digits := (exponent.replace "-" "").replace "+" ""
        if digits.length > 3 then throw "JSON exponent limit"
        let some magnitude := digits.toNat? | throw "invalid JSON exponent"
        if magnitude > 400 then throw "JSON exponent limit"
      nodes := nodes + 1
    else if c == 't' || c == 'f' || c == 'n' then
      while i < chars.size && chars[i]!.isAlpha do i := i + 1
      nodes := nodes + 1
    else i := i + 1
    if nodes > 300000 then throw "JSON node limit"
  if !stack.isEmpty then throw "unbalanced JSON"

/-- Canonical binary64 bits avoid Lean's lossy default Float JSON formatter. -/
def encodeFloat (value : Float) : String := "f64:" ++ toString value.toBits.toNat

private def numeric (j : Json) : Except String Float := do
  let text ← j.getStr?
  let [tag, digits] := text.splitOn ":" | throw "invalid binary64 token"
  if tag != "f64" || digits.isEmpty || digits.length > 20 then throw "invalid binary64 token"
  let some bits := digits.toNat? | throw "invalid binary64 bits"
  if bits >= 18446744073709551616 || digits != toString bits then throw "noncanonical binary64 bits"
  let f := Float.ofBits bits.toUInt64
  if !f.isFinite then throw "nonfinite observation"
  return f

def encodeRows (rows : Array (Array Float)) : Json := Lean.toJson (rows.map (·.map encodeFloat))

inductive Settings where
  | points (rows : Array (Array Float))
  | euler (initial : Array Float) (start step : Float) (steps : Nat)

def Settings.toJson : Settings → Json
  | .points rows => Json.mkObj [("method", Lean.toJson "points"), ("points", encodeRows rows)]
  | .euler initial start step steps => Json.mkObj [("method", Lean.toJson "euler"),
      ("initial", Lean.toJson (initial.map encodeFloat)), ("start", Lean.toJson (encodeFloat start)), ("step", Lean.toJson (encodeFloat step)), ("steps", Lean.toJson steps)]

structure Request (n m : Nat) where
  circuit : Circuit n m
  inputs : List Polynomial.Port
  outputs : List Polynomial.Port
  requestId : String
  artifactId : String
  settings : Settings

private def finiteRow (row : Array Float) (n : Nat) : Bool :=
  row.size == n && row.all Float.isFinite

private def boundedTree (raw : Interchange.RawCircuit) : Nat → Nat → Except String Nat
  | 0, _ => throw "circuit depth limit"
  | _, 0 => throw "circuit node limit"
  | depth + 1, fuel + 1 => do
    match raw with
    | .constant q | .scalar q =>
      if q.den != 1 || q.num.natAbs > 9007199254740992 then throw "unsupported exact coefficient"
      return fuel
    | .compose a b | .parallel a b =>
      let remaining ← boundedTree a depth fuel
      boundedTree b depth remaining
    | _ => return fuel

/-- Shared numerical validation, separate from exact model admission. -/
def validateSettings (settings : Settings) (n m : Nat) (inputs : List Polynomial.Port) :
    Except String Unit := do
  match settings with
  | .points rows =>
    if rows.isEmpty || rows.size > 4096 || !(rows.all (fun row => finiteRow row n)) then
      throw "invalid point samples"
  | .euler initial start step steps =>
    if n == 0 || n != m || !(inputs.all (fun p => p.role == .state)) then
      throw "Euler needs square autonomous RHS and ordered state inputs"
    if !(finiteRow initial n) || !start.isFinite || !step.isFinite || step <= 0 || steps == 0 || steps >= 4096 then
      throw "invalid Euler settings"
    let mut previous := start
    for k in [1:steps + 1] do
      let t := start + k.toFloat * step
      if !t.isFinite || t <= previous then throw "nonadvancing time grid"
      previous := t

def Request.toJson {n m : Nat} (r : Request n m) : Except String Json := do
  if n > 64 || m > 64 then throw "wire limit"
  for label in [r.requestId, r.artifactId] ++ (r.inputs ++ r.outputs).flatMap (fun p => [p.id, p.name]) do
    if label.isEmpty || label.utf8ByteSize > 128 then throw "invalid label"
  let _ ← boundedTree (Interchange.encode r.circuit) 65 1024
  let model ← Interchange.exportPython r.circuit r.inputs r.outputs
  validateSettings r.settings n m r.inputs
  let result := Json.mkObj [("schema", Lean.toJson requestSchema),
    ("numericEncoding", Lean.toJson "binary64-bits-decimal/v1"), ("requestId", Lean.toJson r.requestId),
    ("artifactId", Lean.toJson r.artifactId), ("model", model), ("settings", r.settings.toJson)]
  if result.compress.utf8ByteSize > maxRequestBytes then throw "request byte limit"
  return result

/-- The original request remains the type index; worker data carries no proof field. -/
structure Observation {n m : Nat} (original : Request n m) where
  trajectory : Array (Array Float)
  times : Option (Array Float)
  provenance : Json
  diagnostics : Json

private def fields (j : Json) (expected : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size != expected.length then throw "unexpected response fields"
  for key in expected do let _ ← j.getObjVal? key

/-- Validated observation data, without any mathematical authority. -/
structure ResponseData where
  trajectory : Array (Array Float)
  times : Option (Array Float)
  provenance : Json
  diagnostics : Json

/-- Binding is checked against the caller's request, never supplied by the worker. -/
def decodeResponse (expected : Json) (settings : Settings) (outputWidth : Nat)
    (schema worker : String) (text : String) : Except String ResponseData := do
  preflight text
  let response ← Json.parse text
  fields response ["schema", "kind", "request", "trajectory", "times", "provenance", "diagnostics"]
  unless (← response.getObjValAs? String "schema") == schema &&
      (← response.getObjValAs? String "kind") == "observation" do throw "unsupported response kind"
  unless (← response.getObjVal? "request") == expected do throw "original request mismatch"
  let rows ← (← response.getObjVal? "trajectory").getArr?
  let (count, width) := match settings with
    | .points points => (points.size, outputWidth)
    | .euler initial _ _ steps => (steps + 1, initial.size)
  if rows.size != count then throw "trajectory length mismatch"
  let trajectory ← rows.mapM fun row => do
    let values ← row.getArr?
    if values.size != width then throw "trajectory dimension mismatch"
    values.mapM numeric
  let timesJson ← response.getObjVal? "times"
  let times ← match settings with
    | .points _ => do
      if timesJson != Json.null then throw "unexpected times for point evaluation"
      pure none
    | .euler initial start step steps => do
      if (trajectory[0]!).map Float.toBits != initial.map Float.toBits then throw "initial state mismatch"
      let values ← timesJson.getArr?
      if values.size != steps + 1 then throw "time count mismatch"
      let times ← values.mapM numeric
      for k in [:times.size] do
        if times[k]!.toBits != (start + k.toFloat * step).toBits then throw "time grid mismatch"
      pure (some times)
  let provenance ← response.getObjVal? "provenance"
  fields provenance ["worker", "package", "python", "jax", "arithmetic", "module"]
  for key in ["worker", "package", "python", "jax", "arithmetic", "module"] do
    let value ← provenance.getObjValAs? String key
    if value.isEmpty || value.utf8ByteSize > 4096 then throw "invalid provenance"
  unless (← provenance.getObjValAs? String "worker") == worker &&
      (← provenance.getObjValAs? String "arithmetic") == "cpu-binary64-materialized" do
    throw "unsupported numerical execution"
  let diagnostics ← response.getObjVal? "diagnostics"
  fields diagnostics ["certifiedError", "message"]
  if (← diagnostics.getObjVal? "certifiedError") != Json.null then throw "worker cannot certify error"
  let _ ← diagnostics.getObjValAs? String "message"
  return ⟨trajectory, times, provenance, diagnostics⟩

/-- Binding is checked against the caller's v1 request, never supplied by the worker. -/
def decodeObservation {n m : Nat} (original : Request n m) (text : String) :
    Except String (Observation original) := do
  let data ← decodeResponse (← original.toJson) original.settings m responseSchema
    "gimle.asgard.lean_worker/v1" text
  return ⟨data.trajectory, data.times, data.provenance, data.diagnostics⟩

end Gimle.Asgard.Simulation
