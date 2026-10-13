import Gimle.Asgard

namespace Gimle.Asgard.Tests

-- Zero inputs and an exact fraction that the Python decimal grammar cannot encode.
example (input : Point 0) : (Circuit.const (1 / 3)).run input 0 = (1 / 3 : ℝ) := by
  norm_num

-- Asymmetry detects accidental reversal of sequential/parallel wire order.
example : (Circuit.compose (.parallel .id (.scalar (-1))) .add).run ![2, 5] 0 = -3 := by
  norm_num

example : Circuit.swap.run ![2, 5] = ![5, 2] := rfl

-- Arbitrary finite dimensions are supported by the structural constructors.
example (c : Circuit 7 3) (d : Circuit 3 0) (x : Point 7) :
    (Circuit.compose c d).run x = d.run (c.run x) := rfl

example : ¬ GlobalCircuitEquivalence Circuit.add Circuit.multiplication := by
  intro h
  have bad := congrFun (h ![2, 3]) 0
  norm_num at bad

end Gimle.Asgard.Tests
