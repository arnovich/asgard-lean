import Gimle.Asgard.Semantics.Real

namespace Gimle.Asgard

def LinfClose {dimension : Nat}
    (epsilon : ℝ) (left right : Point dimension) : Prop :=
  ∀ coordinate, |left coordinate - right coordinate| ≤ epsilon

def GlobalCircuitEquivalence {inputDegree outputDegree : Nat}
    (source target : Circuit inputDegree outputDegree) : Prop :=
  ∀ input, source.run input = target.run input

/-- Approximation is a circuit fact on an explicit region, independent of Hoare logic. -/
def QuantitativeCircuitEquivalence {input output : Nat}
    (source target : Circuit input output) (region : Point input → Prop) (epsilon : ℝ) : Prop :=
  ∀ input, region input → LinfClose epsilon (source.run input) (target.run input)

theorem circuitReflexivity {inputDegree outputDegree : Nat}
    (circuit : Circuit inputDegree outputDegree) :
    GlobalCircuitEquivalence circuit circuit := by
  intro input
  rfl

theorem circuitSymmetry {inputDegree outputDegree : Nat}
    {source target : Circuit inputDegree outputDegree}
    (premise : GlobalCircuitEquivalence source target) :
    GlobalCircuitEquivalence target source := by
  intro input
  exact (premise input).symm

theorem circuitTransitivity {inputDegree outputDegree : Nat}
    {first second third : Circuit inputDegree outputDegree}
    (left : GlobalCircuitEquivalence first second)
    (right : GlobalCircuitEquivalence second third) :
    GlobalCircuitEquivalence first third := by
  intro input
  exact (left input).trans (right input)

theorem compositionCongruence {n m k : Nat} {a b : Circuit n m} {c d : Circuit m k}
    (first : GlobalCircuitEquivalence a b) (second : GlobalCircuitEquivalence c d) :
    GlobalCircuitEquivalence (.compose a c) (.compose b d) := by
  intro input
  simp only [Circuit.run, first input, second (b.run input)]

theorem parallelCongruence {n m k l : Nat} {a b : Circuit n m} {c d : Circuit k l}
    (left : GlobalCircuitEquivalence a b) (right : GlobalCircuitEquivalence c d) :
    GlobalCircuitEquivalence (.parallel a c) (.parallel b d) := by
  intro input
  simp only [Circuit.run, left (pointLeft input), right (pointRight input)]

theorem compositionAssociativity {n m k l : Nat}
    (a : Circuit n m) (b : Circuit m k) (c : Circuit k l) :
    GlobalCircuitEquivalence (.compose (.compose a b) c) (.compose a (.compose b c)) := by
  intro input
  rfl

#print axioms compositionCongruence
#print axioms parallelCongruence
#print axioms compositionAssociativity

end Gimle.Asgard
