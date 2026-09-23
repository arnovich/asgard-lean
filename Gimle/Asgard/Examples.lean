-- Gimle/Asgard/Examples/CircuitGallery.lean is deliberately NOT imported here.
-- It pulls in Visualization.Widget, the only ProofWidgets consumer in this
-- repository; importing it would make an Infoview UI dependency mandatory for
-- the whole examples library. It builds as its own lean_lib target instead.
import Gimle.Asgard.Examples.EnergyDemo
import Gimle.Asgard.Examples.EnergyOptimization
import Gimle.Asgard.Examples.Oscillator
import Gimle.Asgard.Examples.VerifiedTranslation
import Gimle.Asgard.Examples.PolynomialCompiler
import Gimle.Asgard.Examples.Feedback
import Gimle.Asgard.Examples.LinearOscillator
import Gimle.Asgard.Examples.LinearDiagram
import Gimle.Asgard.Examples.AlgebraicFeedback
import Gimle.Asgard.Examples.StochasticJump
import Gimle.Asgard.Examples.VariableIsolation
import Gimle.Asgard.Examples.RealAtomics
import Gimle.Asgard.Examples.FormalHeat
import Gimle.Asgard.Examples.ExternalBlend
import Gimle.Asgard.Examples.Approximation
import Gimle.Asgard.Examples.EquationModels
import Gimle.Asgard.Examples.RationalExecution
import Gimle.Asgard.Examples.ThreeState
import Gimle.Asgard.Examples.ThreeStateExecution
