---
title: Declare formal stream equations with a solution-set theorem
state: closed
priority: low
labels: [compiler, streams, declaration]
blocks: ["029"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Formal streams": `Context.compiled_iff` relates a resolved
stream expression to its value, not an equation to its solutions.
`FormalHeat` takes `u` as an input and checks the reconstruction. Stream
models are hand-built `NamedExpr` values and there is no declaration case.

## Outcome

- A declaration case naming the basis (OGF or EGF, part of model identity),
  ordered axes by stable id, inputs, and a boundary profile as a declared input
  on a named axis.
- A theorem: `u` solves `D_t u = F(u)` with boundary `b` iff
  `u = integral(F(u), b)` along the declared axis, with right-hand sides tied
  to `Context.compiled_iff`.
- Axis order is preserved under permutation; `seriesCompose` without an
  established `CanCompose` is refused.
- Positive: formal heat `u = x² + 2t` from `x²`, declared and lowering as
  `heat_lowers`. Hostile: the discarded `seriesCompose` and duplicate axis
  ids, rejected with diagnostics.
- Full `lake build` is clean and axiom audits show only standard axioms.
