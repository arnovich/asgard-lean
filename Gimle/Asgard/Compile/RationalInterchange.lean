import Gimle.Asgard.Compile.Interchange

/-! V2 exact structural codec. Mathematical round trips are unbounded; protocol
admission applies separate byte, digit, node, depth and wire limits. -/
namespace Gimle.Asgard.Interchange.RationalWire

structure Literal where
  num : Int
  den : Nat
  deriving Repr, DecidableEq

def literalEncode (q : ℚ) : Literal := ⟨q.num, q.den⟩

def literalDecode (v : Literal) : Option ℚ :=
  if v.den = 0 ∨ v.num.natAbs.gcd v.den ≠ 1 then none else some (mkRat v.num v.den)

@[simp] theorem literal_roundtrip (q : ℚ) : literalDecode (literalEncode q) = some q := by
  simp [literalEncode, literalDecode, q.den_nz, q.reduced.gcd_eq_one, Rat.mkRat_self]

inductive Tree where
  | id | add | multiplication | split | swap | terminal
  | constant (value : Literal)
  | scalar (value : Literal)
  | compose (left right : Tree)
  | parallel (left right : Tree)
  deriving Repr, DecidableEq

def encodeRaw : RawCircuit → Tree
  | .id => .id
  | .add => .add
  | .multiplication => .multiplication
  | .split => .split
  | .swap => .swap
  | .terminal => .terminal
  | .constant q => .constant (literalEncode q)
  | .scalar q => .scalar (literalEncode q)
  | .compose a b => .compose (encodeRaw a) (encodeRaw b)
  | .parallel a b => .parallel (encodeRaw a) (encodeRaw b)

def decodeRaw : Tree → Option RawCircuit
  | .id => some .id
  | .add => some .add
  | .multiplication => some .multiplication
  | .split => some .split
  | .swap => some .swap
  | .terminal => some .terminal
  | .constant q => .constant <$> literalDecode q
  | .scalar q => .scalar <$> literalDecode q
  | .compose a b => return .compose (← decodeRaw a) (← decodeRaw b)
  | .parallel a b => return .parallel (← decodeRaw a) (← decodeRaw b)

@[simp] theorem decode_encodeRaw (c : RawCircuit) : decodeRaw (encodeRaw c) = some c := by
  induction c <;> simp_all [encodeRaw, decodeRaw]

def encodeCircuit {n m : Nat} (c : Circuit n m) : Tree := encodeRaw (encode c)
def decodeCircuit (t : Tree) : Option PackedCircuit := (decodeRaw t).bind decode

@[simp] theorem decode_encodeCircuit {n m : Nat} (c : Circuit n m) :
    decodeCircuit (encodeCircuit c) = some ⟨n,m,c⟩ := by
  simp [decodeCircuit, encodeCircuit]

def Literal.toJson (v : Literal) : Lean.Json :=
  Lean.toJson [toString v.num, toString v.den]

def Tree.toJson : Tree → Lean.Json
  | .id => Lean.toJson (["id"] : List String)
  | .add => Lean.toJson (["add"] : List String)
  | .multiplication => Lean.toJson (["multiplication"] : List String)
  | .split => Lean.toJson (["split"] : List String)
  | .swap => Lean.toJson (["swap"] : List String)
  | .terminal => Lean.toJson (["terminal"] : List String)
  | .constant q => Lean.toJson ["const", toString q.num, toString q.den]
  | .scalar q => Lean.toJson ["scalar", toString q.num, toString q.den]
  | .compose a b => .arr #[.str "compose", a.toJson, b.toJson]
  | .parallel a b => .arr #[.str "parallel", a.toJson, b.toJson]

/-- The new literal codec emits the same exact rational node payloads as the
existing structural renderer, without exporting lossy Python decimal syntax. -/
theorem json_consistent (raw : RawCircuit) : (encodeRaw raw).toJson = raw.toJson := by
  induction raw <;> simp_all [encodeRaw, Tree.toJson, RawCircuit.toJson, literalEncode]

#print axioms literal_roundtrip
#print axioms decode_encodeCircuit
#print axioms json_consistent
end Gimle.Asgard.Interchange.RationalWire
