---
title: Prove axis permutation invariance for stream declarations
state: open
priority: low
labels: [streams]
related: ["043", "029"]
---

## Context

Task 043 proves that resolved axes sit at their declared positions
(`Equation.resolve_ids`), but the permuted solution set is proved for heat only
(`DeclaredHeat.swapped_solutions`). A general statement needs reindex lemmas for
product, constant and axis-variable values, which do not exist.

## Outcome

- A theorem: permuting a declaration's axes (and its boundary profiles) permutes
  its solution set by the same bijection, for every accepted declaration.
- `swapped_solutions` follows from it.
- Full `lake build` is clean and axiom audits show only standard axioms.
