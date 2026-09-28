---
title: Declare integral states for integrals no inverse rewrite removes
state: closed
priority: medium
labels: [compiler, isolation, migration]
related: ["028"]
---

## Context

Task 028 gave source terms `int(X,t)`, read as the antiderivative from the
declared start, and three inverse rewrites that remove integrals before
isolation (`Model.Integral`). Every other integral is rejected with
`unsupportedIntegral`. The pinned Python compiler (gimle-asgard `fba931e`)
accepts `diff(f,t) = int(f,t)` as Form-A `f = int(int(f,t),t) + f0`: the inner
integral becomes a hidden state whose initial value is silently zero. Lean
rejects it.

As with velocities (027), the Lean answer is an explicit declaration rather than
an inferred state: a declaration such as `integrals% { dF : F = int(X, t); }`
naming a state `F`, its derivative port, and an initial value that must be
declared as `0`, read `int(X,t)` as `F` wherever it occurs.

## Outcome

- A source can declare an integral state `F` for `int(X,t)`; lowering reads the
  integral as `F` and adds `dF := X`, and a declared initial value other than `0`
  is rejected with a diagnostic.
- `diff(f,t) = int(f,t)` with a declared integral state lowers, and a proof shows
  that the source's integral reading equals the state along every solution.
- `Lowered.solves_iff`, `SourceContinuousModel.solves_iff_realizes`,
  `classical_iff_realizes` and `solves_iff_classical` keep their statements.
- The Python fixture `diff(f,t) = int(f,t)` is restated with its outcome; full
  `lake build` is clean and axiom audits show only standard axioms.
