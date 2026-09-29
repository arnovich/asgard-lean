---
title: Evaluate finite discrete prefixes exactly in Lean
state: open
priority: low
labels: [simulation, execution, discrete]
depends_on: ["045"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Initialized discrete updates", execution adapter: a
polynomial recurrence over ℚ can be run exactly by Lean itself, with no worker
and no binary64 step.

## Outcome

- A function evaluating `run` for `n` ticks over ℚ for a polynomial update,
  returning the states per tick with the clock anchor, with a theorem that it
  agrees with `RealizesThrough n`.
- Its result is labelled an observation of a prefix; nothing states a claim
  about later ticks.
- Tested on the averaging update and the swap.
- Full `lake build` is clean and axiom audits show only standard axioms.
