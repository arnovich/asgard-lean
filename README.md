# Asgard Lean

Lean 4 proofs for typed circuits, equation compilation, and circuit rewrites.
Examples cover polynomial models, continuous feedback, linear ODEs, formal
streams, and approximation bounds.

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
| [Formal heat](Gimle/Asgard/Examples/FormalHeat.lean) | Formal derivatives and boundary-preserving integration |
| [Circuit gallery](Gimle/Asgard/Examples/CircuitGallery.lean) | Interactive diagrams in Lean Infoview |

Check an individual example with `lake env lean Gimle/Asgard/Examples/EnergyDemo.lean`.

## Guides

- [Models and proof coverage](docs/models.md)
- [Formal streams](docs/formal-streams.md)
- [Circuit diagrams and SVG export](docs/circuit-viewer.md)
- [Optional Python simulation](docs/simulation.md)

Proofs concern the stated Lean interpretations and assumptions. Numerical
simulation is optional and does not establish a theorem.
