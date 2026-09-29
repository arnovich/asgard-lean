---
title: Admit integrals in driven source declarations
state: open
priority: low
labels: [compiler, drivers, integrals]
depends_on: ["031"]
related: ["039"]
---

## Context

Task 031 added driven source declarations (`Model.DrivenSource`), but only
without integrals: the driven context has no boundary, `compileSourceDriven`
rejects every integral with "integral in a driven declaration", and
`SourceBody.SolvesDriven` reads every non-local atom as undefined. The
trajectory reading of integrals (`SourceBody.trajectory`, `Model.Integral`)
reads only states and bound parameters, so an integrand naming a driver has no
value along it, and the inverse rewrites' discharge (`SourceBody.cancels_at`)
is stated over the undriven `Solves`.

## Outcome

- A driven declaration may use the inverse rewrites and declared integral states
  of `Model.Source`, with integrands that may read drivers, and the driven
  relation reads integrals along the trajectory of states and drivers.
- `SourceDrivenModel.solves_iff_realizes` holds for such declarations; the 031
  fixtures and the undriven integral fixtures keep their outcomes.
- Full `lake build` is clean and axiom audits show only standard axioms.
