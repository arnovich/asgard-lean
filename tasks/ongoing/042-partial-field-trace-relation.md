---
title: Close continuous models over partial real vector fields
state: ongoing
priority: low
labels: [compiler, atomics, dynamics]
blocks: ["030"]
claimed_by: claude-042
claimed_at: 2026-09-29T10:21:05Z
branch: feat/partial_field_trace
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Partial real functions": `Dynamics.close` and
`ContinuousModel.solves_iff_realizes` close only a total polynomial circuit
field. Once 030 admits `RealAtomics` in assignments, an atomic feeding a
continuous model's field has no relation that keeps its domain, so the domain
obligation would be silently dropped inside an ODE.

## Outcome

- A trace relation for continuous models whose field is a `RealAtomics`
  expression, requiring `Defined` at every time of the domain along the state.
- A close theorem relating that relation to the classical solution relation, in
  both directions, with `Defined` carried in the relation, not beside it.
- Positive: a field such as `x' = -sqrt(x)` on `x > 0`; hostile: a
  trajectory that leaves the domain has no relation output.
- Full `lake build` is clean and axiom audits show only standard axioms.
