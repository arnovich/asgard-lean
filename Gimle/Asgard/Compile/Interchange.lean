import Gimle.Asgard.Compile.Named
import Lean

/-! Structural interchange has a typed decoder and an exact round-trip theorem.
The Python syntax export is a deliberately narrower integer-only fragment. -/
namespace Gimle.Asgard.Interchange

def schemaVersion : String := "gimle.asgard.polynomial-circuit/v1"
def pythonSemantics : String := "asgard.feedforward.real.v1"

inductive RawCircuit where
  | id | add | multiplication | split | swap | terminal
  | constant (value : ℚ)
  | scalar (value : ℚ)
  | compose (left right : RawCircuit)
  | parallel (left right : RawCircuit)
  deriving Repr, DecidableEq

def encode {n m : Nat} : Circuit n m → RawCircuit
  | .id => .id
  | .const q => .constant q
  | .scalar q => .scalar q
  | .add => .add
  | .multiplication => .multiplication
  | .split => .split
  | .swap => .swap
  | .terminal => .terminal
  | .compose a b => .compose (encode a) (encode b)
  | .parallel a b => .parallel (encode a) (encode b)

abbrev PackedCircuit := (n : Nat) × (m : Nat) × Circuit n m

def decode : RawCircuit → Option PackedCircuit
  | .id => some ⟨1, 1, .id⟩
  | .constant q => some ⟨0, 1, .const q⟩
  | .scalar q => some ⟨1, 1, .scalar q⟩
  | .add => some ⟨2, 1, .add⟩
  | .multiplication => some ⟨2, 1, .multiplication⟩
  | .split => some ⟨1, 2, .split⟩
  | .swap => some ⟨2, 2, .swap⟩
  | .terminal => some ⟨1, 0, .terminal⟩
  | .compose a b => do
      let ⟨n, m, ca⟩ ← decode a
      let ⟨k, o, cb⟩ ← decode b
      if h : m = k then return ⟨n, o, .compose ca (h.symm ▸ cb)⟩ else none
  | .parallel a b => do
      let ⟨n, m, ca⟩ ← decode a
      let ⟨k, o, cb⟩ ← decode b
      return ⟨n + k, m + o, .parallel ca cb⟩

@[simp] theorem decode_encode {n m : Nat} (c : Circuit n m) :
    decode (encode c) = some ⟨n, m, c⟩ := by
  induction c <;> simp_all [encode, decode]

/-- A successful round trip retains the very same typed circuit and interpreter. -/
theorem decoded_semantics {n m : Nat} (c : Circuit n m) (x : Point n) :
    ∃ d : Circuit n m, decode (encode c) = some ⟨n, m, d⟩ ∧ d.run x = c.run x :=
  ⟨c, decode_encode c, rfl⟩

private def integerLiteral (q : ℚ) : Except String String :=
  if q.den = 1 then .ok (toString q.num)
  else .error "Python integer-coefficient interchange rejects non-integer rationals"

/-- Export no rounded constants. Both 1/2 and 1/3 are explicitly unsupported. -/
def RawCircuit.toPython : RawCircuit → Except String String
  | .id => .ok "id"
  | .constant q => do return "const(" ++ (← integerLiteral q) ++ ")"
  | .scalar q => do return "scalar(" ++ (← integerLiteral q) ++ ")"
  | .add => .ok "add"
  | .multiplication => .ok "multiplication"
  | .split => .ok "split"
  | .swap => .ok "swap"
  | .terminal => .ok "terminal"
  | .compose a b => do return "composition(" ++ (← a.toPython) ++ "," ++ (← b.toPython) ++ ")"
  | .parallel a b => do return "monoidal(" ++ (← a.toPython) ++ "," ++ (← b.toPython) ++ ")"

/-- Exact rational fields are decimal integer strings, including arbitrarily large values. -/
def RawCircuit.toJson : RawCircuit → Lean.Json
  | .id => Lean.toJson (["id"] : List String)
  | .constant q => Lean.toJson (["const", toString q.num, toString q.den] : List String)
  | .scalar q => Lean.toJson (["scalar", toString q.num, toString q.den] : List String)
  | .add => Lean.toJson (["add"] : List String)
  | .multiplication => Lean.toJson (["multiplication"] : List String)
  | .split => Lean.toJson (["split"] : List String)
  | .swap => Lean.toJson (["swap"] : List String)
  | .terminal => Lean.toJson (["terminal"] : List String)
  | .compose a b => .arr #[.str "compose", a.toJson, b.toJson]
  | .parallel a b => .arr #[.str "parallel", a.toJson, b.toJson]

def roleName : Polynomial.PortRole → String
  | .input => "input" | .parameter => "parameter" | .state => "state"
  | .driver => "driver" | .initial => "initial" | .boundary => "boundary" | .output => "output"

def portJson (p : Polynomial.Port) : Lean.Json :=
  Lean.Json.mkObj [("id", .str p.id), ("name", .str p.name), ("role", .str (roleName p.role))]

/-- The envelope binds both ordered interfaces and the explicit interpretation mapping.
No axes or evolution settings are part of this finite real-vector fragment. -/
def exportPython {n m : Nat} (c : Circuit n m)
    (inputs outputs : List Polynomial.Port) : Except String Lean.Json := do
  unless inputs.length = n && outputs.length = m do
    throw "Interface lengths do not match the typed circuit"
  unless Polynomial.validPorts (inputs ++ outputs) do
    throw "Interface IDs and names must be nonempty and unique"
  unless inputs.all (fun p => p.role != .output) do
    throw "Input ports cannot have output role"
  unless outputs.all (fun p => p.role == .output) do
    throw "Every result port must have output role"
  let raw := encode c
  let source ← raw.toPython
  return Lean.Json.mkObj [
    ("schema", .str schemaVersion), ("fragment", .str fragmentVersion),
    ("pythonSemantics", .str pythonSemantics), ("coefficients", .str "integers"),
    ("inputs", .arr (inputs.map portJson).toArray),
    ("outputs", .arr (outputs.map portJson).toArray),
    ("exactCircuit", raw.toJson),
    ("circuit", Lean.Json.mkObj [("type", .str "Circuit"), ("trees", .arr #[.str source])])]

#print axioms decode_encode
#print axioms decoded_semantics

end Gimle.Asgard.Interchange
