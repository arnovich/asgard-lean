module

public import Gimle.Asgard.Examples.AIF
-- Gimle/Asgard/Examples/CircuitGallery.lean is deliberately NOT imported here.
-- It pulls in Visualization.Widget, the only ProofWidgets consumer in this
-- repository; importing it would make an Infoview UI dependency mandatory for
-- the whole examples library. It builds as its own lean_lib target instead.
public import Gimle.Asgard.Examples.EnergyDemo
public import Gimle.Asgard.Examples.EnergyOptimization
public import Gimle.Asgard.Examples.Oscillator
public import Gimle.Asgard.Examples.VerifiedTranslation
public import Gimle.Asgard.Examples.PolynomialCompiler
public import Gimle.Asgard.Examples.Feedback
public import Gimle.Asgard.Examples.LinearOscillator
public import Gimle.Asgard.Examples.LinearDiagram
public import Gimle.Asgard.Examples.AlgebraicFeedback
public import Gimle.Asgard.Examples.DeclaredAlgebraic
public import Gimle.Asgard.Examples.StochasticJump
public import Gimle.Asgard.Examples.VariableIsolation
public import Gimle.Asgard.Examples.DifferentialIsolation
public import Gimle.Asgard.Examples.HigherOrderIsolation
public import Gimle.Asgard.Examples.DampedOscillator
public import Gimle.Asgard.Examples.SourceIntegrals
public import Gimle.Asgard.Examples.DrivenForcing
public import Gimle.Asgard.Examples.IntegralStates
public import Gimle.Asgard.Examples.NestedIntegralStates
public import Gimle.Asgard.Examples.RealAtomics
public import Gimle.Asgard.Examples.PartialFeedback
public import Gimle.Asgard.Examples.AtomicSource
public import Gimle.Asgard.Examples.FormalHeat
public import Gimle.Asgard.Examples.DeclaredHeat
public import Gimle.Asgard.Examples.HeatIsolation
public import Gimle.Asgard.Examples.PolynomialHeat
public import Gimle.Asgard.Examples.GeometricTail
public import Gimle.Asgard.Examples.ExpHeat
public import Gimle.Asgard.Examples.ExternalBlend
public import Gimle.Asgard.Examples.Approximation
public import Gimle.Asgard.Examples.EquationModels
public import Gimle.Asgard.Examples.RationalModel
public import Gimle.Asgard.Examples.ThreeState
public import Gimle.Asgard.Examples.BurgersSquare
public import Gimle.Asgard.Examples.BurgersFront
public import Gimle.Asgard.Examples.EulerThreeMode
public import Gimle.Asgard.Examples.EulerBand
public import Gimle.Asgard.Examples.MildBand
