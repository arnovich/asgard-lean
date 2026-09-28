---
title: Accept lower-order derivative atoms beside a declared chain
state: ongoing
priority: low
labels: [compiler, isolation, migration]
related: ["027"]
claimed_by: claude-032
claimed_at: 2026-09-28T12:00:00Z
branch: feat/lower_order_atoms
---

## Context

Task 027 reads `D_t(D_t(x))` as `D_t(v)` through a declared velocity `v`
(`Term.collapse`), then runs the first-order isolation of gimle-forseti 083.
Only the chain is collapsed. A lower-order atom of the same state beside it,
as in the damped oscillator `D_t(D_t(x)) + c*D_t(x) + k*x = 0`, stays a second
atom and is rejected with `repeatedDerivative`. The user has to write `v` for
`D_t(x)` by hand. The pinned Python compiler rejects this form as well.

Replacing `D_t(x)` with `v` does not preserve meaning in every environment, as
`Term.collapse_eval` does. It holds only where the velocity equation
`D_t(x) = v` holds. So the per-equation correspondence that
`lowerDifferential` returns would need the velocity equations as a premise,
and `Lowered.equations` would have to discharge that premise at the level of
the whole system.

## Outcome

- `dv : D_t(D_t(x)) + c*D_t(x) + k*x = 0`, with `dx : D_t(x) = v` declared,
  lowers to `dv := -(c*v + k*x)` (exact, with the residual kept in source
  order). `SourceContinuousModel.solves_iff_realizes` and
  `classical_iff_realizes` still hold unchanged.
- A lower-order atom whose state has no declared velocity is still rejected,
  with the same diagnostic as today.
- The fixture in `Tests/HigherOrderIsolation.lean` that expects
  `repeatedDerivative` is updated, and records Python's rejection as a
  "differs".
- A full `lake build` is clean, and the axiom audits show only the standard
  axioms.
