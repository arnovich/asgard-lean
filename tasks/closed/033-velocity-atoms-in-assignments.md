---
title: Read declared-velocity atoms in explicit assignments
state: closed
priority: low
labels: [compiler, isolation]
related: ["032"]
---

## Context

Task 032 (PR #10) reads an evolution-axis atom `D_t(y)` as the declared
velocity of `y` inside differential equations (`Term.readVelocities`). The
reading is exact only where the velocity equations hold, and `SourceBody.lower`
discharges that premise for the whole system.

Explicit assignments do not get this reading. `dw := diff(h, t)` with `h`'s
velocity `w` declared is still rejected with `unsupportedDerivative`
("derivative in an explicit assignment"), while the same relation written as the
differential `dw : diff(w, t) = diff(h, t)` is accepted. Atoms inside lambda
applications are also never read. That is deliberate, because a binder named
like a velocity would capture the substituted name.

## Outcome

- Either explicit assignments read declared-velocity atoms, under the same
  premise, with `Lowered.equations` still proved for every environment, or the
  asymmetry is kept and documented in `docs/models.md` as a deliberate choice
  with a reason.
- Atoms inside lambdas remain rejected unless a capture-safe reading is proved.
- The fixture in `Tests/HigherOrderIsolation.lean` pinning
  `dv := diff(h, t)` as `unsupportedDerivative` is updated to match.
