import Gimle.Asgard.Visualization.Widget
import Gimle.Asgard.Examples.EnergyOptimization
import Gimle.Asgard.Examples.EquationModels
import Gimle.Asgard.Examples.RationalExecution
import Gimle.Asgard.Examples.ThreeState

/-! Open this file in VS Code and put the cursor on a #html command.
Edit the circuit/model, save, and inspect the updated Lean Infoview.
Pictures are read-only views; theorems in the imported examples carry the claims. -/
open Gimle.Asgard

-- Every atomic and the asymmetric split/swap wiring are visible here.
#html Visualization.circuit (.compose .swap
  (.parallel (.compose (.scalar 3) (.compose .split .add)) (.scalar 3)))

-- Compact typed stages for E=(x+y)²+(x-y)², with a checked identity.
#html Visualization.circuit EnergyDemo.energy

-- The smaller 2(x²+y²) circuit has a checked global equivalence theorem.
#html Visualization.circuit EnergyOptimization.optimized

-- Optional detailed view: all wiring introduced by equation compilation.
#html Visualization.circuit Examples.EquationModels.energy

-- The original oscillator circuit closed with integrators and explicit trace.
#html Visualization.dynamics Examples.EquationModels.feedback

-- Exact two-state equations, t₀=2/3, reordered source declarations and ICs.
-- Expand the full circuit or observation circuit below the overview.
#html Visualization.model Examples.RationalExecution.model

-- A coupled three-state model. The overview
-- shows all three coupled feedback paths x->y->z->x closed at t=2; expand the
-- full circuit for the compiled field and the observation circuit for [z,x,y,V].
#html Visualization.model Examples.ThreeState.model

-- The same model's initialized feedback on its own, with the explicit trace.
#html Visualization.dynamics Examples.ThreeState.feedback
