---
title: Admit time-varying drivers in source declarations
state: open
priority: medium
labels: [compiler, isolation, migration]
related: ["030"]
---

## Context

The common continuous adapter is autonomous: parameters are fixed rationals and
`Model.Differential` (gimle-forseti 083) rejects a derivative of anything but a
declared state with `unsupportedDerivative`. The pinned Python compiler keeps an
external forcing parameter differentiated on the other side, as in
`test_parameter_derivative_can_remain_external_forcing`
(`diff(a,t) = diff($z,t)`), and accepts driver inputs such as `f` in
`f = 2 * diff(g,t)`. The lower-level `Dynamics` modules already accept drivers;
common source declarations cannot reach them.

## Outcome

- A source declaration can declare a driver signal on the evolution axis, use
  it in residuals, and, where the driver is declared differentiable, use its
  derivative; nothing is inferred from a name or a `$` prefix.
- A theorem relates the source relation, for a given driver signal, to the
  driven compiled feedback on the same domain and initial data.
- The Python fixture above is restated with its outcome; an undeclared driver
  or a derivative of a fixed parameter stays rejected.
- Full `lake build` is clean and axiom audits show only standard axioms.

## Conversation

### note · claude/084 · 2026-09-29T08:00:59Z

gimle-forseti 084 (`docs/model-family-contracts.md`, "Driven continuous
models") puts this task at the head of the medium-priority chain (then 041,
gimle-asgard 259, gimle-forseti 170), because it replaces the trajectory lane's
vacuous `fun _ => True` driver predicate. The contract asks that a declared
driver derivative be bound inside the relation to the driver's actual
derivative, never an unconstrained extra input, and that the stated driver
precondition include the regularity the classical relation needs (at least
continuity), as forseti-lean `DisturbedFeedback.admitted` does.
