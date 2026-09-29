---
title: Declare stochastic and jump systems with explicit calculus
state: open
priority: low
labels: [compiler, stochastic, declaration]
related: ["gimle-forseti/052"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Stochastic and jump processes": `NamedSystem` and
`Prepared.solves_iff_circuit` exist, reachable only by hand. The Lean
`Context` has no law; probability stays with gimle-forseti 052.

## Outcome

- A declaration case naming noise and jump ids, the calculus and the jump
  convention; a missing calculus is rejected, never defaulted.
- A theorem tying the declaration to `Prepared.solves_iff_circuit`, keeping
  driver identity, predictable sampling (`before x`) and the initial value at
  the window start.
- A convention `JumpSchedule.semantics` does not support is rejected as
  unsupported, with a diagnostic that never reads as a refutation.
- Positive: `StochasticJump` (`X = 8` after the jump). Hostile: swapped
  noise ids, Stratonovich given Itô semantics, a wrong driver.
- Full `lake build` is clean and axiom audits show only standard axioms.
