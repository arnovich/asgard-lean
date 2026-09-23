import Gimle.Asgard

namespace Gimle.Asgard.EnergyDemo

-- Each stage states its wiring dimensions explicitly.
def duplicate : Circuit 2 4 :=
  .parallel .split .split

-- Parallel splits give [x,x,y,y]; swap the middle wires to get [x,y,x,y].
def interleave : Circuit 4 4 :=
  .parallel (leftInput := 1) (leftOutput := 1) .id
    (.parallel (leftInput := 2) (leftOutput := 2) .swap .id)

def difference : Circuit 2 1 :=
  .compose (.parallel .id (.scalar (-1))) .add

def sumAndDifference : Circuit 4 2 :=
  .parallel .add difference

def square : Circuit 1 1 :=
  .compose .split .multiplication

def squareBoth : Circuit 2 2 :=
  .parallel square square

-- The complete pipeline computes (x+y)^2 + (x-y)^2.
def energy : Circuit 2 1 :=
  .compose
    (.compose
      (.compose
        (.compose duplicate interleave)
        sumAndDifference)
      squareBoth)
    .add

-- A wiring error can preserve a loose bound. This identity checks the full formula.
theorem energyIdentity (input : Point 2) :
    energy.run input 0 = 2 * (input 0)^2 + 2 * (input 1)^2 := by
  norm_num [energy, duplicate, interleave, sumAndDifference, difference, squareBoth, square]
  ring


#print axioms energyIdentity

end Gimle.Asgard.EnergyDemo
