---
title: Name external symbol bindings in simulation requests
state: open
priority: low
labels: [simulation, execution, external]
depends_on: ["047"]
related: ["gimle-asgard/263"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "External components and partitions", execution adapter: a
run of an external component is an observation about the bound implementation,
never about the declared component.

## Outcome

- A request version naming each symbol's id and version and, where declared, a
  rational-box domain; the response records the binding and its trust status.
- A component without a decidable domain is marked unchecked in the response.
- A request naming a symbol absent from the environment is refused, tested.
- Full `lake build` is clean and axiom audits show only standard axioms.
