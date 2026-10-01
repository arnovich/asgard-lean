---
title: The analytic field of a product, an inverse and the Cole–Hopf front
state: closed
priority: medium
labels: [streams, lean]
depends_on: ["061"]
---

# The analytic field of a product, an inverse and the Cole–Hopf front

## Context

Phase A of gimle-forseti task 189 (umbrella 182). `Streams/Tail.lean`'s
`analyticField` is a `tsum` of decoded coefficients, and 061 certifies the
front's truncation, but nothing identifies the front's field with anything:
no theorem says the field of a product or an inverse of streams is the product
or inverse of their fields where both converge, nor what the heat stream of an
exponential-sum profile sums to. So `Examples/BurgersFront.lean` must say
"nothing here identifies the analytic field with `1/(1 + e^(x − t/2))`", and
no field bound on the front is provable.

## Outcome

- `Streams/AnalyticField.lean`: `analyticField_mul` on a box strictly inside
  both majorants (Mathlib's Cauchy product over `Finsupp.antidiagonal`, from
  absolute convergence), `analyticField_C_mul`, `analyticField_one`, and
  `analyticField_inv` as the corollary of `φ⁻¹ * φ = 1`
- `Streams/ColeHopf.lean`: `analyticField_heatSeries_expSum`: the heat stream
  of `Σ cᵢ e^(aᵢ x)` sums to `Σ cᵢ e^(ν aᵢ² t + aᵢ x)` wherever it is
  majorized, and `analyticField_front`: on a box strictly inside the front's
  radii `r/2`, the front's field is `−2ν (Σ cᵢ aᵢ e^(…)) / (Σ cᵢ e^(…))`
- `Examples/BurgersFront.lean`: `front_field_eq` on the certified box, the
  band `2/5 ≤ u ≤ 3/5` there for every stream the circuit reconstructs from
  the front's slice, and `u ≤ 27/50` refuted at the corner `(1/6, −1/8)`, all
  from `Real.add_one_le_exp`; the "nothing identifies" caveat removed
- Tests with axiom audits; docs; released as v1.10.0

## Conversation

### note · claude/17d157a0 · 2026-10-01T17:30:00Z

Closed with PR #25, released as v1.10.0 (`beb851eb`). Every new theorem is audited to the three standard axioms.
