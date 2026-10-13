# Asgard Lean

Asgard is a circuit language for dynamical systems, written in Lean 4. Its circuits
are typed, with exact real semantics. A verified compiler takes equations as you
would write them (polynomial models, ODEs, PDEs given as formal power series)
to circuits whose meaning provably matches the original equations.

- **Circuits:** feedforward polynomial and real-atomic circuits, continuous
  feedback with initialized integrators, unit-delay iteration, and formal
  coefficient streams over named axes.
- **Compilation:** named equations with exact rational coefficients,
  implicit and higher-order ODEs, integrals, declared drivers, `sqrt`, `log` and
  division with their domains kept, and affine algebraic loops. Each path is
  proved equivalent to its source.
- **Rewrites:** normalization, substitution and equation isolation that
  preserve values and constraints.
- **Analysis:** linear existence and uniqueness, approximation error bounds,
  and formal stream solutions of heat, Burgers, and 2D Euler and Navier–Stokes,
  with certified truncation errors and classical-solution theorems.
- **Diagrams:** interactive circuit views in Lean Infoview and SVG export.

Every result is a kernel-checked theorem using only `propext`, `Classical.choice`
and `Quot.sound`. Proofs concern the stated interpretations and assumptions;
floating-point accuracy and numerical integration are not certified.

Public showcase, licensed under [MIT](LICENSE). External pull requests are not accepted.

## Build

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build
```

Lean and mathlib are pinned. The build checks the library, examples, regression
proofs, and diagram exporter.

## Explore

Open an example in VS Code with the Lean 4 extension. Each module's header
states what it proves and what it does not.

| Example | What it shows |
| --- | --- |
| [Energy](Gimle/Asgard/Examples/EnergyDemo.lean) | Typed circuits and an exact energy identity |
| [Equation compiler](Gimle/Asgard/Examples/PolynomialCompiler.lean) | Named equations compiled to primitive circuits |
| [Three-state model](Gimle/Asgard/Examples/ThreeState.lean) | Coupled ODEs, exact initial data, and energy calculations |
| [Differential isolation](Gimle/Asgard/Examples/DifferentialIsolation.lean) | `3*D_t(x) + x = y` isolated with its residual and initial data, and solved |
| [Higher-order isolation](Gimle/Asgard/Examples/HigherOrderIsolation.lean) | `4*D_t(D_t(x)) + x = 0` lowered through a declared velocity state |
| [Damped oscillator](Gimle/Asgard/Examples/DampedOscillator.lean) | `D_t(D_t(x)) + c*D_t(x) + k*x = 0` with a declared velocity, and solved |
| [Source integrals](Gimle/Asgard/Examples/SourceIntegrals.lean) | Integrals lowered with their boundary terms kept, and solved |
| [Integral states](Gimle/Asgard/Examples/IntegralStates.lean) | `D_t(f) = I_t(f)` through a declared integral state, solved by `f = cosh t`; [nested](Gimle/Asgard/Examples/NestedIntegralStates.lean) |
| [Formal heat](Gimle/Asgard/Examples/FormalHeat.lean) | Formal derivatives and boundary-preserving integration |
| [Declared heat](Gimle/Asgard/Examples/DeclaredHeat.lean) | Heat as a stream equation; from boundary `x²` the solution set is exactly `x² + 2t` |
| [Heat isolation](Gimle/Asgard/Examples/HeatIsolation.lean) | `diff(u,t) = diff(diff(u,x),x)` isolated to the declared heat equation |
| [Polynomial heat](Gimle/Asgard/Examples/PolynomialHeat.lean) | Heat evolution of any polynomial profile, as a stream and a real field |
| [Geometric tail](Gimle/Asgard/Examples/GeometricTail.lean) | A coefficient majorant certifies convergence and a uniform truncation error |
| [Exponential heat](Gimle/Asgard/Examples/ExpHeat.lean) | `e^x` evolves to `e^(x+t)`, with a kernel-computed truncation bound |
| [Burgers from `x²`](Gimle/Asgard/Examples/BurgersSquare.lean) | The formal Burgers stream from any profile, unique by Picard iteration |
| [Burgers front](Gimle/Asgard/Examples/BurgersFront.lean) | The Cole–Hopf front with a certified truncation error and a field band proved and refuted |
| [Euler from three modes](Gimle/Asgard/Examples/EulerThreeMode.lean) | The formal vorticity stream of 2D Euler and Navier–Stokes on the torus |
| [Euler feedback circuit](Gimle/Asgard/Streams/VorticityCircuit.lean) | A typed Fourier feedback circuit whose unique output is that stream |
| [Euler band](Gimle/Asgard/Examples/EulerBand.lean) | A certified radius, truncation error and band, and a classical Euler solution on `\|t\| < 1/648` |
| [Mild viscous circuit](Gimle/Asgard/Streams/MildCircuit.lean) | Heat, Duhamel integration and interaction terms as a feedback circuit; its output is the Wild expansion |
| [Mild bounds and band](Gimle/Asgard/Examples/MildBand.lean) | Two convergence bounds for the viscous series, classical realization and energy/enstrophy dissipation |
| [Circuit gallery](Gimle/Asgard/Examples/CircuitGallery.lean) | Interactive diagrams in Lean Infoview |

Check an individual example with `lake env lean Gimle/Asgard/Examples/EnergyDemo.lean`.

## What is proved

| Feature | Proved | Limits |
| --- | --- | --- |
| Polynomial compilation | Original equations ↔ compiled outputs | Exact rationals; starts at the Lean syntax tree, not text parsing |
| Continuous feedback | Initialized ODE ↔ compiled solution relation | Autonomous polynomial fields on `t ≥ start`; no existence, uniqueness or stability by itself |
| Linear analysis | Existence and uniqueness on `t ≥ start` | Homogeneous rational linear systems; no stability claim |
| [Isolation](Gimle/Asgard/Examples/VariableIsolation.lean) | Substitution and conditional isolation preserve values and constraints | Affine recognition with a proved inverse; no general solver |
| [Differential and higher-order isolation](Gimle/Asgard/Examples/DifferentialIsolation.lean) | Implicit and higher-order ODEs ↔ compiled feedback, same initial data | One top atom per equation; lower orders through declared velocity states |
| [Source integrals](Gimle/Asgard/Examples/SourceIntegrals.lean) | Integrals denote antiderivatives from the start | Only the boundary-keeping inverse rewrites and declared integral states |
| [Drivers](Gimle/Asgard/Examples/DrivenForcing.lean) | Driven source ↔ driven feedback, for each admitted driver | Continuous drivers with actual derivatives; no existence claim |
| [Real atomics](Gimle/Asgard/Examples/RealAtomics.lean) | Values **and domains** preserved, also inside [feedback](Gimle/Asgard/Examples/PartialFeedback.lean) | `sqrt` nonnegative, `log` and powers positive, denominators nonzero |
| [Algebraic loops](Gimle/Asgard/Examples/DeclaredAlgebraic.lean) | A unique loop point and the eliminated output on admitted inputs | Affine loops with a checked rational inverse |
| [External components](Gimle/Asgard/Examples/ExternalBlend.lean) | Pointwise contracts and weighted partitions | Fixed explicit environment; no certification of external code |
| [Stochastic translation](Gimle/Asgard/Examples/StochasticJump.lean) | Source ↔ process circuit | Same supplied integral; no SDE existence, Itô formula or probability bounds |
| [Approximation](Gimle/Asgard/Examples/Approximation.lean) | Uniform coordinate error bounds on a region | Feedforward real circuits; coverage and Lipschitz premises for composition |
| [Formal streams](Gimle/Asgard/Streams/Core.lean) | Exact coefficient semantics, OGF or EGF, with checked derivative/integral laws | Formal series; analytic claims only where a radius is certified |

Partial operations stay undefined even when their result is discarded or
multiplied by zero. A trace hides internal signals; it does not guarantee a solution.

## Diagrams

Open [CircuitGallery.lean](Gimle/Asgard/Examples/CircuitGallery.lean), place the
cursor on a `#html` command and open Lean Infoview. `Visualization.circuit`,
`Visualization.dynamics` and `Visualization.model` draw polynomial circuits,
continuous circuits and compiled models. To export SVG:

```sh
lake exe diagram_demo rational .lake/build/rational-circuit.svg
```

Other presets: `energy`, `energy-optimized`, `energy-compiled`, `oscillator`,
`rational-raw`. Existing files are never overwritten. Ports are zero-indexed,
composition runs left first, and feedback connects the last outputs to the last
inputs in order.
