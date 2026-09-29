---
title: Admit integrals, drivers and observations beside real atomics
state: open
priority: low
labels: [compiler, atomics]
related: ["030", "042", "053"]
---

## Context

Task 030's atomic compilers (`Model/AtomicSource.lean`) reject integrals and
integral declarations (`unsupportedIntegral`), drivers (`unsupportedRole`) and,
for continuous declarations, observations (`unsupportedRole`, site
`observations`). `docs/models.md` lists this under "Not yet in the source
grammar" without a task. 042's `Circuit.CloseRel` already takes drivers.

## Outcome

- A continuous declaration with atomics may declare drivers (as in 031's
  `DriverBinding`) and observations, and `compileAtomicContinuous` relates source
  and compiled model for them, with every assignment `Defined` at every time.
- Integrals beside atomics are either admitted through the integral rewrites with
  their domains kept, or remain rejected with the reason documented; the docs
  item cites this task.
- Full `lake build` is clean and axiom audits show only standard axioms.
