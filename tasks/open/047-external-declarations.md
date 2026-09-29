---
title: Declare external components against named environments
state: open
priority: low
labels: [compiler, external, declaration]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "External components and partitions": `External`'s
`compile_rel` is relative to an `Environment`, which may be any Lean term.
Making the environment part of a model's identity needs it to be nameable and
hashable.

## Outcome

- A declaration case for symbols (id, version, arity) and partitions, with the
  region's definedness, nonnegativity and unit sum as obligations.
- The environment is a named Lean definition whose name and content hash enter
  the declaration; an anonymous environment is rejected.
- Every theorem stays relative to the declared environment.
- Positive: `ExternalBlend`. Hostile: missing environment, a transformer
  outside its domain, a vacuous contract.
- Full `lake build` is clean and axiom audits show only standard axioms.
