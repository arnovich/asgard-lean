---
title: Read declared-velocity atoms inside lambda applications without capture
state: open
priority: low
labels: [compiler, isolation]
related: ["032", "033"]
---

## Context

Tasks 032 and 033 read an evolution-axis atom `D_t(y)` as the declared velocity
`z` of `y` in differential equations and explicit assignments
(`Term.readVelocities`). Lambda applications are left whole: under a binder
named `z`, substituting `z` for the atom would capture it, and `Term.eval`
masks a binder's name for chains and atoms. So every atom inside a lambda
application, in its body or its argument, stays rejected with
`unsupportedDerivative`, for example `w := (λ u => diff(f, t) + u)(0)` and
`w := (λ u => u)(diff(f, t))`. The argument is outside the binder's scope, so
reading it there would already be capture-free.

## Outcome

- An atom in a lambda argument is read as its declared velocity, with a proof of
  preservation under `Context.VelocitiesHold`.
- An atom in a lambda body is either read with a proved capture-safe reading
  (renaming, or refusing only when the binder shadows the velocity or the
  state), or kept rejected with the reason stated in `docs/models.md`.
- Fixtures cover a binder named like the velocity, like the state, and an
  unrelated binder, in both differentials and explicit assignments.
