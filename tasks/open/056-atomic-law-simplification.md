---
title: Simplify source atomics by their laws within their regions
state: open
priority: low
labels: [compiler, atomics, rewrites]
related: ["030"]
---

## Context

Task 030 compiles source atomics without applying `RealAtomics/Laws.lean`
(`log_exp`, `sqrt_square`, ...): `log(exp(x))` keeps both domains. The
model-family contract allows those laws only within their regions.

## Outcome

- A simplification pass applies a law only where its region is established,
  with a theorem that the simplified term has the same value and the same (or a
  proved-equal) domain.
- `log(exp(x))` simplifies to `x`; a law outside its region is not applied,
  tested.
- Full `lake build` is clean and axiom audits show only standard axioms.
