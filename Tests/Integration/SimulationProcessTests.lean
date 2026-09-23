import Gimle.Asgard.Simulation.Rational

open Gimle.Asgard Gimle.Asgard.Simulation

def sampleRequest : Request 1 1 where
  circuit := .id
  inputs := [⟨"x", "x", .input⟩]
  outputs := [⟨"y", "y", .output⟩]
  requestId := "process-regression"
  artifactId := "original-identity"
  settings := .points #[#[1]]

private def mustFail (request : Request 1 1) (python : System.FilePath)
    (reason : String) (timeout : Nat := 5000) (cancelAfter : Bool := false) : IO Unit := do
  let cancel ← IO.mkRef false
  let _ ← IO.asTask (do
    if cancelAfter then
      IO.sleep 100
      cancel.set true) .dedicated
  let start ← IO.monoMsNow
  let failure ← try
    let _ ← run request ⟨python, timeout, 4096, 4096⟩ cancel
    pure none
  catch error => pure (some error.toString)
  let some message := failure | throw (IO.userError s!"worker {python} unexpectedly succeeded")
  unless (message.splitOn reason).length > 1 do
    throw (IO.userError s!"expected {reason}, got {message}")
  if (← IO.monoMsNow) - start > timeout + 3000 then throw (IO.userError "cleanup exceeded bound")

def main (args : List String) : IO UInt32 := do
  let [directory] := args | throw (IO.userError "Usage: simulation_process_tests FIXTURE_DIRECTORY")
  let root : System.FilePath := directory
  for name in ["hang", "descendant", "ignore_term", "term_marker"] do
    mustFail sampleRequest (root / name) "timeout" 1000
  mustFail sampleRequest (root / "hang") "cancelled" 1000 true
  mustFail sampleRequest (root / "flood") "byte limit"
  mustFail sampleRequest (root / "stderr_flood") "byte limit"
  mustFail sampleRequest (root / "crash") "exited"
  mustFail sampleRequest (root / "bad_stderr") "invalid UTF-8 stderr"
  mustFail sampleRequest (root / "bad_json") "JSON"
  mustFail sampleRequest (root / "huge_exponent") "exponent limit"
  mustFail sampleRequest (root / "bad_utf8") "UTF-8"
  -- More than a pipe buffer: the worker never reads it. Deadline covers stdin.
  let large := {sampleRequest with settings := .points (Array.replicate 4096 #[123456789.125])}
  mustFail large (root / "hang") "timeout" 1000
  let rational : Rational.Request 1 1 := {
    circuit := .scalar (1/3)
    inputs := [⟨"x", "x", .input⟩]
    outputs := [⟨"out-x", "x", .output⟩]
    sourceIds := ["x"]
    outputSources := ["x"]
    requestId := "rational-process"
    artifactId := "rational-original"
    settings := .points #[#[1]]
  }
  for (name, reason) in [("crash", "exited"), ("bad_json", "JSON"), ("hang", "timeout")] do
    let cancel ← IO.mkRef false
    let failure ← try
      let _ ← Rational.run rational ⟨root / name, if name == "hang" then 1000 else 5000, 4096, 4096⟩ cancel
      pure none
    catch error => pure (some error.toString)
    let some message := failure | throw (IO.userError "rational worker unexpectedly succeeded")
    unless (message.splitOn reason).length > 1 do
      throw (IO.userError s!"expected rational failure {reason}, got {message}")
  IO.println "Process limits, cancellation and cleanup checks passed"
  return 0
