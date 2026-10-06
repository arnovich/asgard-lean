# Asgard Lean

Lean 4 proofs for typed circuits, equation compilation, and circuit rewrites.
Examples cover polynomial models, continuous feedback, linear ODEs, formal
streams, certified stream truncation, and approximation bounds.

Public showcase, licensed under [MIT](LICENSE). External pull requests are not accepted.

## Build

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build
```

Lean and mathlib are pinned. The build checks the library, examples, regression
proofs, and diagram exporter. No Python installation is needed.

## Explore

Open an example in VS Code with the Lean 4 extension:

| Example | What it shows |
| --- | --- |
| [Energy](Gimle/Asgard/Examples/EnergyDemo.lean) | Typed circuits and an exact energy identity |
| [Equation compiler](Gimle/Asgard/Examples/PolynomialCompiler.lean) | Named equations compiled to primitive circuits |
| [Three-state model](Gimle/Asgard/Examples/ThreeState.lean) | Coupled ODEs, exact initial data, and energy calculations |
| [Differential isolation](Gimle/Asgard/Examples/DifferentialIsolation.lean) | `3*D_t(x) + x = y` isolated with its residual and initial data, and solved |
| [Higher-order isolation](Gimle/Asgard/Examples/HigherOrderIsolation.lean) | `4*D_t(D_t(x)) + x = 0` lowered through a declared velocity state and its initial value, and solved |
| [Damped oscillator](Gimle/Asgard/Examples/DampedOscillator.lean) | `D_t(D_t(x)) + c*D_t(x) + k*x = 0` with the lower-order atom read as the declared velocity, and solved |
| [Source integrals](Gimle/Asgard/Examples/SourceIntegrals.lean) | `D_t(I_t(2*D_t(f) + f)) = 0` and `D_t(x) + I_t(D_t(x)) = 1` lowered with the boundary term `x(0)` kept, and solved |
| [Integral states](Gimle/Asgard/Examples/IntegralStates.lean) | `D_t(f) = I_t(f)` lowered through a declared integral state `F` with `F(0) = 0`, solved by `f = cosh t`, and `I_t(f)` read as `F` in every solution |
| [Nested integral states](Gimle/Asgard/Examples/NestedIntegralStates.lean) | `D_t(f) = I_t(I_t(f))` lowered through two declared integral states, the outer integrand read through the inner, and solved |
| [Formal heat](Gimle/Asgard/Examples/FormalHeat.lean) | Formal derivatives and boundary-preserving integration |
| [Declared heat](Gimle/Asgard/Examples/DeclaredHeat.lean) | Heat declared as a stream equation; its solution set from boundary `x²` is exactly `x² + 2t` |
| [Heat isolation](Gimle/Asgard/Examples/HeatIsolation.lean) | `diff(u,t) = diff(diff(u,x),x)` isolated to the declared heat equation, with the same solution set |
| [Polynomial heat](Gimle/Asgard/Examples/PolynomialHeat.lean) | Heat evolution of any polynomial profile, as a stream and a real field |
| [Geometric tail](Gimle/Asgard/Examples/GeometricTail.lean) | A proved coefficient majorant certifies convergence and a uniform truncation error |
| [Exponential heat](Gimle/Asgard/Examples/ExpHeat.lean) | The analytic profile `e^x` evolves to `e^(x+t)`, with a kernel-computed certified truncation bound |
| [Burgers from `x²`](Gimle/Asgard/Examples/BurgersSquare.lean) | Formal Burgers stream `D_t u = −u·D_x u + ν·D_x² u` from any profile, unique by Picard iteration in the `t`-degree, with the first coefficients read off polynomial iterates |
| [Burgers front](Gimle/Asgard/Examples/BurgersFront.lean) | The formal Burgers stream of the Cole–Hopf front `−2ν φ_x/φ`, `φ(0, x) = 1 + e^(−x)`, with a kernel-computed certified truncation error `1/16384` on a box; its analytic field there is `1/(1 + e^(x − t/2))`, with the band `2/5 ≤ u ≤ 3/5` proved and `u ≤ 27/50` refuted at a corner, twice: from the closed form, and from a kernel-checked window table alone |
| [Euler from three modes](Gimle/Asgard/Examples/EulerThreeMode.lean) | The formal vorticity stream of 2D Euler and Navier–Stokes on the torus, `D_t ω = νΔω − u·∇ω` with trigonometric-polynomial coefficients, unique by the causal lemma over an abstract axis; from `cos x + cos(x+y) + cos(2x+y)` selected coefficients through `t³` are kernel-checked, and every coefficient is proved mean zero and even (the real-valued cosine subspace in the exponential reading) |
| [Euler feedback circuit](Gimle/Asgard/Streams/VorticityCircuit.lean) | Fourier operators and time integration wired into a typed feedback circuit: from boundary data alone, its unique formal output is the existing Euler/Navier–Stokes stream, in OGF or EGF |
| [Mild viscous circuit](Gimle/Asgard/Streams/MildCircuit.lean) | Heat, Duhamel integration and an interaction-degree shift wired into a typed feedback circuit; its unique exact output is the Wild expansion, with computable coefficient tables and evaluated agreement with Euler at zero viscosity. Both convergence bounds and certified windows are proved in `MildRadius`; `MildSolution` and `MildDissipation` prove classical realization and the infinite energy/enstrophy identities |
| [Mild bounds and band](Gimle/Asgard/Examples/MildBand.lean) | Two physical bounds on the actual mild-circuit output: viscosity-dependent Catalan majorants and the Euler scale at every nonnegative viscosity. For the three-mode start at ν = 1/10, the first gives time 1/5760, a four-term tail 21/1024 and band ±3.519; the second converges for 0 ≤ t < 1/648. No norms of redundant exponential-polynomial coefficients are used. Both intervals support the classical PDE, a right derivative at the start, and nonincreasing spectral energy/enstrophy |
| [Euler band](Gimle/Asgard/Examples/EulerBand.lean) | A certified radius for the two-dimensional Euler stream from three modes, by a Cauchy–Kowalevski induction in a scale of weighted norms: `l1 ω_n ≤ 9·648ⁿ`, the `t`-series of the stream's field converges for `|t| < 1/648`, and on `|t| ≤ 1/6480` that analytic field is within `1/100` of its finite sum through `t²` and within `1/50` of `cos x + cos(x+y) + cos(2x+y)`; on `|t| < 1/648` that field is a classical solution of the vorticity equation, `∂_t ω + u·∇ω = 0` with `u = ∇⊥Ψ`, `ΔΨ = ω`, every partial derivative that appears the sum of the termwise derivatives and continuous (`EulerSolution`); Gevrey-1 growth in `t`, and no radius, for `ν = 1/10` |
| [Circuit gallery](Gimle/Asgard/Examples/CircuitGallery.lean) | Interactive diagrams in Lean Infoview |

Check an individual example with `lake env lean Gimle/Asgard/Examples/EnergyDemo.lean`.

## Guides

- [Models and proof coverage](docs/models.md)
- [Formal streams](docs/formal-streams.md)
- [Circuit diagrams and SVG export](docs/circuit-viewer.md)
- [Optional Python simulation](docs/simulation.md)

Proofs concern the stated Lean interpretations and assumptions. Numerical
simulation is optional and does not establish a theorem.
