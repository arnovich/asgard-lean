---
title: Burgers certified truncation via Cole–Hopf and a majorant calculus
state: closed
priority: medium
labels: [streams, lean]
depends_on: ["060"]
---

# Burgers certified truncation via Cole–Hopf and a majorant calculus

## Context

Phase B of gimle-forseti task 182 (its 186). `Streams/Tail.lean`'s geometric
majorant `M ∏ Rᵢ^{−αᵢ}` has no calculus: nothing says a product, an inverse
or a derivative of majorized streams is majorized. Cole–Hopf writes the
Burgers stream of 060 as `u = −2ν · D_x φ · φ⁻¹` with `φ` the heat stream
(viscosity ν) of an exponential-sum profile, so a certified truncation of
`u` reduces to a few lemmas on `MvPowerSeries (Fin d) ℚ` and the existing
`TailCertificate`. The formal series from polynomial profiles diverges
(060), so this is the route to any convergent Burgers statement.

## Outcome

- `Streams/Majorant.lean`: `majorizes_mono`, `majorizes_smul`,
  `majorizes_product` (bounds multiply, radii halve), `majorizes_inv`
  (constant coefficient `c ≠ 0`; well-founded induction on the index with
  `MvPowerSeries.coeff_inv`; decidable side condition
  `(M/|c|)(∏(1 − rᵢ/Rᵢ)⁻¹ − 1) ≤ 1`), and a coefficient-level Leibniz rule
  `derivative (product a b) = product (D a) b + product a (D b)`
- `Streams/ColeHopf.lean`: `heatSeries ν g` (AnalyticHeat with viscosity),
  `quotient ν g := (−2ν) • D_x φ * φ⁻¹`, `quotient_pde` (solves 060's
  `rhs`), `quotient_eq_stream` by 060's `formal_unique`, `majorizes_quotient`
  for exponential-sum data, and an `expSum_truncation` root of the same
  shape as `AnalyticHeat.expSum_truncation`, every side condition decidable
- Worked front `φ₀ = 1 + e^{−x}`, ν = 1/2 (`u = 1/(1 + e^{x − t/2})`):
  `Majorizes u ⟨1/2, (1/3, 1/4)⟩`, box |t| ≤ 1/6, |x| ≤ 1/8, window (16, 16),
  certified ε = 1/16384, by `decide +kernel`
- Tests with hostile cases and axiom audits; docs and README; released
- The docs say why the bound is loose (factorials dropped twice, the inverse
  step, the product halving) and that the true error on that box is far
  smaller; nothing about the real PDE beyond the analytic field of this series

## Conversation

### note · claude/17d157a0 · 2026-10-01T01:30:00Z

Closed after PR #24, tagged v1.9.0. Names shipped differ from the outcome as
written: `majorizes_C_mul`/`majorizes_mul` (they are `C q *` and `*` on
`MvPowerSeries`), `majorizes_front` and `front_truncation` (the quotient of
an exponential-sum heat stream is `front`), plus `constantCoeff_front`,
`certificate` and `circuit_front` that the review asked for. The derivative
algebra is under `ogfD`. `Streams/Grid.lean` was split out of `Lowering`
so the majorant calculus does not import the lowering pass. Everything else
as stated; the certified error of the worked front is exactly 1/16384.
