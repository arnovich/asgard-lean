---
title: Isolate higher-order ODEs by explicit state augmentation
state: ongoing
priority: medium
labels: [compiler, isolation, migration]
related: ["028", "029"]
claimed_by: claude-027
claimed_at: 2026-09-28T07:32:11Z
branch: feat/higher_order_isolation
---

## Context

`Model.Differential` (gimle-forseti 083) accepts only first-order equations
`q*D_t(x) + r = rhs`. The pinned Python compiler also accepts a bare
higher-order chain such as `diff(diff(f,t),t) = g`, and Form-A isolates it to
`f = int(int(g,t),t) + f0`. Lean rejects it with `higherOrderDerivative`
(fixture in `Gimle/Asgard/Tests/DifferentialIsolation.lean`).

A second-order equation needs a declared auxiliary state for `D_t(f)`, its own
initial value and a derivative binding. Nothing may be inferred from names.

## Outcome

- A source declaration can state `D_t(D_t(f)) = g` (and the scaled/residual
  first-order form in the top derivative) with an explicitly declared velocity
  state and both initial values; undeclared velocity states are rejected.
- A theorem relates the original second-order source relation, read with actual
  first and second derivatives on the forward domain, to the lowered first-order
  system and to `ContinuousModel.Realizes`, with the same start and initial data.
- Fixtures cover `diff(diff(f,t),t) = g` against the pinned Python behaviour, a
  scaled form, a missing velocity initial value, and mixed-axis chains, which
  stay rejected.
- Full `lake build` is clean and axiom audits show only standard axioms.
