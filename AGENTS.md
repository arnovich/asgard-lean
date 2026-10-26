# Asgard Lean development

Use a feature branch and worktree. Keep changes small and follow the existing
Lean module, example, and regression-test patterns.

Asgard owns circuit syntax, interpretations, and correctness-preserving rewrites.
Keep property search, Python execution and simulation out of this repository.
Preserve exact coefficients and explicit semantic assumptions. Never add `sorry`, unchecked
axioms, or treat simulation as mathematical authority.

Run `lake build` for the library, examples, viewer, and regression proofs.

Every file is a Lean `module`. Imports are `public import`, and declarations sit
in an `@[expose] public section` so that importing modules can compute with,
unfold and `decide` the definitions. A helper that an exposed definition or a
public statement uses must itself be public. Commands that run code, such as
`#guard`, `#eval` and `#html`, need a `meta import` of the modules they run;
macro helpers are `meta def`.

Inspect axiom reports; only `propext`, `Classical.choice`, and `Quot.sound` are
expected. Review substantial changes for mathematical correctness and integration.
Keep executable entry points under `Executables/`, outside the core library.
Keep generated output under the ignored `.lake/` directory. There is no separate
docs folder: explain each result in its module header and keep the README to a
short index.

Commit only explicitly selected files after reviewing and checking the change.
This is a public showcase; external pull requests are not being accepted. It
must stand on its own: never mention internal repositories, research, task or PR
numbers, people, or paths outside this repository in sources, the README or
commit messages.
