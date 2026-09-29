---
title: Tag polynomial simulation requests with their model family
state: open
priority: low
labels: [simulation, execution, interchange]
depends_on: ["043", "044"]
related: ["gimle-asgard/260"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084): an eliminated algebraic circuit and a lowered stream window are
ordinary polynomial circuits, but the request carries a single fragment tuple
and cannot tell families apart. The algebraic `admitted` predicate is an
arbitrary `Prop`, and a lowered window reads input slots outside the observed
window.

## Outcome

- A new request version with a family field; the old version is unchanged.
- Algebraic requests carry `admitted` as a rational box; streams carry the
  slot manifest with every input slot the window reads.
- A request missing a slot, or an algebraic request without a box, is refused
  with a named diagnostic, tested.
- The schema states results are binary64 observations, not exact values.
- Full `lake build` is clean and axiom audits show only standard axioms.
