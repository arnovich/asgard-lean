---
title: Field bands on analytic streams from a checked window
state: closed
priority: medium
labels: [streams, lean]
depends_on: ["062"]
---

# Field bands on analytic streams from a checked window

## Context

gimle-forseti task 190 (phase B of 189): a decider lane for field bounds on
analytic streams needs the window polynomial's coefficients as rationals the
kernel can check and a bound on it over the box, with no closed form. The
design note there chooses: the window of `φ⁻¹` is a table checked by the
finite identity `(φ · Q)_k = [k = 0]` below `N`; the window field is within
`Σ_{0 ≠ k < N} |W_k| ∏ rᵢ^kᵢ` of its constant term on the box; a rational
point where the window exceeds a bound by more than the certified error
refutes the bound. A kernel-time spike put the `16 × 16` identity at about
ten seconds.

## Outcome

- `Streams/Window.lean`: `coeff_inv_window` (the inverse's low coefficients
  are the unique solution of the triangular identity), `sum_window_eq_grid`,
  `abs_windowField_sub_le`, `windowField_rat`
- `Streams/ColeHopf.lean`: `heatCoeff`, `WindowIdentity` (decidable),
  `coeff_inv_expSumHeat_window`, `frontWindow`, `coeff_toIndex_front`,
  `windowSpread`, `frontValue`, and the roots `front_band_of_window` and
  `front_above_of_window` with the premises of `front_truncation`
- `Examples/BurgersFront.lean`: the band `2/5 ≤ u ≤ 3/5` and the refuted
  `u ≤ 27/50` proved again from the window alone, every side condition
  `decide +kernel`; tests with audits; docs; released as v1.11.0

## Conversation

### note · claude/17d157a0 · 2026-10-01T22:40:00Z

Closed with PR #27, released as v1.11.0. Every new theorem is audited to the three standard axioms; the example's window file takes about 50 s of kernel time.
