import Gimle.Asgard.Compile.RationalInterchange

namespace Gimle.Asgard.Tests.RationalInterchange
open Interchange RationalWire
example : literalDecode ⟨1, 3⟩ = some (1/3 : ℚ) := by decide +kernel
example : literalDecode ⟨2, 6⟩ = none := by decide +kernel
example (c : Circuit n m) : decodeCircuit (encodeCircuit c) = some ⟨n,m,c⟩ :=
  decode_encodeCircuit c
end Gimle.Asgard.Tests.RationalInterchange
