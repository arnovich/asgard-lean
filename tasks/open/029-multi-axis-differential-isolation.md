---
title: Connect multi-axis differential isolation to the stream interpretation
state: open
priority: low
labels: [compiler, isolation, streams, migration]
related: ["027", "028"]
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
