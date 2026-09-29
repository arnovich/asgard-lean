---
title: Own initialized discrete recurrences with a source compiler
state: open
priority: low
labels: [compiler, discrete, semantics]
related: ["forseti-lean/032"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Initialized discrete updates": the recurrence `run` and
`Realizes` live in forseti-lean `Discrete.lean` over a supplied update
circuit. asgard-lean has no clock or delay, there is no source form, and
`Realizes` carries no clock identity. Asgard owns circuit semantics.

## Outcome

- The recurrence semantics in asgard-lean: clock ℕ anchored at tick 0 as a
  relation clause, one-step delay, declared initial state at observation 0,
  simultaneous update, port order state/input/parameter, fixed parameters and
  input sequence, and a `RealizesThrough n` variant for finite prefixes.
- A discrete declaration case and `Source.Solves ↔ Realizes` with the clock
  clause.
- Positive: the averaging update and the simultaneous swap. Hostile
  declarations: a missing initial value and a same-tick input read, rejected
  with diagnostics; a sequential-swap test showing it differs from the
  simultaneous one.
- No correspondence to continuous traces or OGF streams is stated.
- Full `lake build` is clean and axiom audits show only standard axioms.
