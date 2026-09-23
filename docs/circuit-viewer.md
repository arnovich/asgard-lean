# Circuit diagrams

1. Run `lake build`.
2. Open [CircuitGallery.lean](../Gimle/Asgard/Examples/CircuitGallery.lean) in VS Code with the Lean 4 extension.
3. Place the cursor on a `#html` command and open Lean Infoview.
4. Expand a model's field or observation circuit; edit and save to refresh.

| Function | Input |
| --- | --- |
| `Visualization.circuit` | Typed polynomial circuit |
| `Visualization.dynamics` | Continuous circuit |
| `Visualization.model` | Compiled continuous model |

## Export SVG

```sh
lake exe diagram_demo rational .lake/build/rational-circuit.svg
lake exe diagram_demo energy .lake/build/energy-circuit.svg
```

Other presets: `energy-optimized`, `energy-compiled`, `oscillator`, `rational-raw`.
Choose a new filename; existing files are refused. No Python renderer is needed.
Keep generated images under `.lake/`; put images used by docs in `docs/`.

Ports are zero-indexed. Composition runs left first; parallel places left ports
first. Crossings are not junctions. Feedback connects the last outputs to the
last inputs in order; it does not imply existence, uniqueness, or stability.
Large views may exceed rendering limits; use the overview or scroll at full size.
