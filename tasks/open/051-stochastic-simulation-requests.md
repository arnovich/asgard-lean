---
title: Route stochastic declarations to a physical-grid request
state: open
priority: low
labels: [simulation, execution, stochastic]
depends_on: ["046"]
related: ["gimle-asgard/262", "gimle-forseti/052"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Stochastic and jump processes", execution adapter.
`Simulation/Protocol.lean` rejects non-uniform times and no Lean request
reaches gimle-asgard's `SDESimulator`, whose physical-grid and own-state
contracts must be kept. The Lean model has no law.

## Outcome

- A v3 request and response with a physical grid, returned times, and a new
  `decodeResponse`; v2 is unchanged.
- The request names the sampled law (independent Brownian drivers, a
  deterministic jump schedule) and the method; a method whose interpretation
  does not match the declared calculus is refused.
- Jumps under Milstein or SRK1, and cross-state diffusion the own-state
  contract forbids, are refused with named diagnostics, tested.
- Full `lake build` is clean and axiom audits show only standard axioms.
