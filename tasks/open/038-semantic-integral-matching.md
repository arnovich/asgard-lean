---
title: Match declared integrals up to the meaning of their integrands
state: open
priority: low
labels: [compiler, isolation]
related: ["034", "036"]
---

## Context

A declared integral state `dF : F = int(X, t)` is read for a written `int(Y, t)`
only when `Y` and `X` are the same `Term` (`SourceBody.boundary`, task 034;
integrands widened to `Term.pointwise` in task 036). So `diff(f,t) = int(1 * f, t)`
against a declared `int(f, t)` is rejected with `unsupportedIntegral`. The pinned
Python compiler (gimle-asgard `fba931e`) accepts it, with a hidden state. Reading
`int(Y, t)` as `F` is exact whenever `Y` and `X` have the same trajectory reading
at every time, but nothing decides that today.

## Outcome

- A written integral whose integrand has the same normal form as a declared one
  (for example both beta-normalize to the same polynomial in states and bound
  parameters) is read as the declared state. A proof shows that the two readings
  agree along every trajectory.
- The fixture `int(1 * f, t)` against `int(f, t)` in `Tests/IntegralStates.lean`
  moves from rejected to accepted, and integrands that differ in meaning stay
  rejected.
- `Lowered.solves_iff` and the other end-to-end theorems keep their statements.
