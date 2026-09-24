# Asgard Lean development

Use a feature branch and worktree. Keep changes small and follow the existing
Lean module, example, and regression-test patterns.

Asgard owns circuit syntax, interpretations, and correctness-preserving rewrites.
Keep property-search systems, Python execution, and simulation out of core
imports. Preserve exact coefficients and explicit semantic assumptions. Never
add `sorry`, unchecked axioms, or treat simulation as mathematical authority.

Run `lake build` for the library, examples, viewer, and regression proofs.
Compile the optional executable entry points with:

```sh
lake build simulation_demo simulation_process_tests rational_simulation_demo three_state_demo
```

Inspect axiom reports; only `propext`, `Classical.choice`, and `Quot.sound` are
expected. Review substantial changes for mathematical correctness and integration.
Keep executable entry points under `Executables/` and `Tests/Integration/`,
outside the core library. Keep generated output under the ignored `.lake/`
directory; diagrams referenced by documentation belong in `docs/`.

Commit only explicitly selected files after reviewing and checking the change.
This is a public showcase; external pull requests are not being accepted.
