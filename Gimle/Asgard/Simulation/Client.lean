import Gimle.Asgard.Simulation.Protocol

/-! Explicit POSIX subprocess client for a selected, trusted Python installation.
Process groups provide lifecycle cleanup, not a sandbox for arbitrary code. -/
namespace Gimle.Asgard.Simulation

structure Worker where
  python : System.FilePath
  timeoutMs : Nat := 30000
  stdoutLimit : Nat := maxResponseBytes
  stderrLimit : Nat := 65536

private def readBounded (handle : IO.FS.Handle) (limit : Nat) : IO ByteArray := do
  let mut result := ByteArray.empty
  repeat
    let chunk ← handle.read (min 4096 (limit + 1 - result.size)).toUSize
    if chunk.isEmpty then return result
    result := result ++ chunk
    if result.size > limit then throw (IO.userError "worker output byte limit")

private def signalGroup (pid : UInt32) (signal : String) : IO Unit := do
  let killer ← IO.Process.spawn {
    cmd := "/bin/kill"
    args := #[signal, "--", "-" ++ toString pid]
    stdin := .null
    stdout := .null
    stderr := .null
    inheritEnv := false
  }
  let _ ← killer.wait
  pure ()

private def stop {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  -- Explicit signals avoid depending on runtime-specific Child.kill behavior.
  try signalGroup child.pid "-TERM" catch _ => pure ()
  IO.sleep 50
  signalGroup child.pid "-KILL"
  let _ ← child.wait
  pure ()

/-- Total wall time includes writing stdin and draining both output pipes.
Cancellation is requested by setting the supplied reference; the child is reaped. -/
def runPayload {α : Type} (payload : Lean.Json) (decode : String → Except String α)
    (worker : Worker) (cancelled : IO.Ref Bool) : IO α := do
  if System.Platform.isWindows then throw (IO.userError "simulation bridge requires POSIX")
  if !worker.python.isAbsolute || worker.timeoutMs == 0 || worker.timeoutMs > 120000 ||
      worker.stdoutLimit == 0 || worker.stdoutLimit > maxResponseBytes ||
      worker.stderrLimit == 0 || worker.stderrLimit > 65536 then
    throw (IO.userError "invalid worker configuration")
  if ← cancelled.get then throw (IO.userError "simulation cancelled")
  if payload.compress.utf8ByteSize > maxRequestBytes then
    throw (IO.userError "request byte limit")
  let start ← IO.monoMsNow
  let (child, writer) ← do
    let (stdin, child) ← (← IO.Process.spawn {
      -- env clears the environment after exec. Lean 4.32.1 crashes in macOS
      -- setenv when inheritEnv=false is combined with nonempty overrides.
      cmd := "/usr/bin/env"
      args := #["-i", "PATH=/usr/bin:/bin", "JAX_ENABLE_X64=true",
        "JAX_PLATFORMS=cpu", "XLA_PYTHON_CLIENT_PREALLOCATE=false",
        worker.python.toString, "-I", "-m", "gimle.asgard.lean_worker"]
      stdin := .piped, stdout := .piped, stderr := .piped, setsid := true}).takeStdin
    let writer ← IO.asTask (do stdin.putStr payload.compress; stdin.flush) .dedicated
    pure (child, writer)
  let stdout ← IO.asTask (readBounded child.stdout worker.stdoutLimit) .dedicated
  let stderr ← IO.asTask (readBounded child.stderr worker.stderrLimit) .dedicated
  let reaped ← IO.mkRef false
  try
    repeat
      if ← cancelled.get then throw (IO.userError "simulation cancelled")
      if (← IO.monoMsNow) - start >= worker.timeoutMs then throw (IO.userError "simulation timeout")
      if ← IO.hasFinished writer then let _ ← IO.ofExcept writer.get
      if ← IO.hasFinished stdout then let _ ← IO.ofExcept stdout.get
      if ← IO.hasFinished stderr then let _ ← IO.ofExcept stderr.get
      -- Keep the leader unreaped while a writer/reader can still hold a pipe.
      -- Its PID then anchors the process group throughout failure cleanup.
      if (← IO.hasFinished writer) && (← IO.hasFinished stdout) && (← IO.hasFinished stderr) then
        if let some code ← child.tryWait then
          reaped.set true
          if code != 0 then
            let diagnostic := (String.fromUTF8? (← IO.ofExcept stderr.get)).getD "[invalid UTF-8 stderr]"
            throw (IO.userError s!"simulation worker exited {code}: {diagnostic}")
          let bytes ← IO.ofExcept stdout.get
          let some text := String.fromUTF8? bytes | throw (IO.userError "worker returned invalid UTF-8")
          let observation ← IO.ofExcept ((decode text).mapError IO.userError)
          return observation
      IO.sleep 5
    throw (IO.userError "unreachable simulation loop")
  finally
    unless ← reaped.get do stop child

/-- V1 API retains its original request-bound decoder and integer-only protocol. -/
def run {n m : Nat} (request : Request n m) (worker : Worker)
    (cancelled : IO.Ref Bool) : IO (Observation request) := do
  let payload ← IO.ofExcept (request.toJson.mapError IO.userError)
  runPayload payload (decodeObservation request) worker cancelled

end Gimle.Asgard.Simulation
