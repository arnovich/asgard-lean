import Gimle.Asgard.Examples.EnergyDemo

namespace Gimle.Asgard.EnergyOptimization

-- Square each input, add the squares, and multiply by two.
-- E(x,y) = 2*(x²+y²), with fewer arithmetic blocks than (x+y)²+(x−y)².
def optimized : Circuit 2 1 :=
  .compose (.compose EnergyDemo.squareBoth .add) (.scalar 2)

theorem optimizedIdentity (input : Point 2) :
    optimized.run input 0 = 2 * ((input 0)^2 + (input 1)^2) := by
  norm_num [optimized, EnergyDemo.squareBoth, EnergyDemo.square]
  ring

-- Global equivalence: the replacement computes the same output on every input.
theorem equivalence : GlobalCircuitEquivalence EnergyDemo.energy optimized := by
  intro input
  funext coordinate
  have zero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  rw [EnergyDemo.energyIdentity, optimizedIdentity]
  ring


def wrongMultiplier : Circuit 2 1 :=
  .compose (.compose EnergyDemo.squareBoth .add) (.scalar 3)

-- The changed circuit gives 6 where the original gives 4.
theorem counterexample :
    EnergyDemo.energy.run ![1, 1] 0 = 4 ∧ wrongMultiplier.run ![1, 1] 0 = 6 := by
  norm_num [EnergyDemo.energyIdentity, wrongMultiplier, EnergyDemo.squareBoth, EnergyDemo.square]

theorem wrongIsNotEquivalent : ¬ GlobalCircuitEquivalence EnergyDemo.energy wrongMultiplier := by
  intro claim
  have equal := congrFun (claim ![1, 1]) 0
  rw [counterexample.1, counterexample.2] at equal
  norm_num at equal

#print axioms equivalence
#print axioms wrongIsNotEquivalent

end Gimle.Asgard.EnergyOptimization
