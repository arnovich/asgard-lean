---
title: Connect multi-axis differential isolation to the stream interpretation
state: open
priority: low
labels: [compiler, isolation, streams, migration]
related: ["027", "028", "030"]
depends_on: ["043"]
---

## Context

`Model.Differential` (gimle-forseti 083) is a one-axis ODE fragment: a
derivative on any other axis is rejected with `mixedDerivative`. The pinned
Python compiler isolates the heat equation `2 * diff(u,t) = diff(diff(u,x),x)`
along `t` and keeps the spatial derivatives on the right. In Lean that belongs to
the formal-stream interpretation (`Gimle/Asgard/Streams/`), which already has
formal heat and its lowering, not to the continuous ODE adapter.

## Outcome

- A declaration can state a scaled time derivative equal to a polynomial in
  spatial derivatives, as in `2 * diff(u,t) = diff(diff(u,x),x)`, and is
  isolated to `D_t(u) = D_x(D_x(u))/2` in the stream interpretation, with a
  theorem relating the source and isolated stream equations and keeping the
  initial profile.
- The Python heat fixture (scale 2, reversed sides, spatial residual) is
  restated with its outcome; mixed derivatives on the isolated side stay
  rejected.
- Full `lake build` is clean and axiom audits show only standard axioms.

## Conversation

### note · claude/043 · 2026-09-29T10:59:19Z

043 (`Streams/Declaration.lean`) gives the target: an isolated equation is an
`Equation ⟨unknown, along, boundary, rhs⟩`, and
`Equation.solves_iff_integral` is its solution-set theorem. 029 still needs its
own source form and a theorem that the source holds iff the isolated
`Equation.Solves` does. `Declaration.validate` does not reject the unknown's
derivative along `along` on the right-hand side (`D_t u = D_t u + 1` is
accepted, with no solutions), so rejecting mixed derivatives on the isolated
side is 029's check to add.
