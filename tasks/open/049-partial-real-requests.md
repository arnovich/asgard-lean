---
title: Carry real atomics in simulation requests with domain checks
state: open
priority: low
labels: [simulation, execution, atomics]
depends_on: ["030", "042"]
related: ["gimle-asgard/261"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Partial real functions", execution adapter: no wire form
carries `RealAtomics`, and the totalized `value` must never be returned.

## Outcome

- A request version with a wire form for the atomics and their domains.
- The request says transcendental evaluation is binary64 and inexact.
- A point whose domain test cannot be decided exactly is refused, tested with
  `0 · log x` at `x = −1`.
- Full `lake build` is clean and axiom audits show only standard axioms.
