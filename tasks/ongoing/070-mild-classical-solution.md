---
title: The mild sum is a classical solution — one-sided at the start, with the enstrophy and energy identities
state: ongoing
priority: medium
labels: [streams, lean, research]
related: ["067", "069"]
depends_on: ["069"]
claimed_by: codex/fluid_contracts
claimed_at: 2026-10-06T01:29:07Z
branch: feat/mild_classical_dissipation
---

# The mild sum is a classical solution — one-sided at the start, with the enstrophy and energy identities

## Context

After task 069 the shelf can say that the Wild series of the mild vorticity
equation converges on `[0, T]` with certified tails and bands, and nothing
about the equation: as task 067 did for Euler, this task ties the sum to the
PDE. Each term satisfies its own equation exactly in the carrier
(`deriv_wild_succ`, task 068); the `t`-derivative series
`Σ_n (νΔω_n − Σ_{m+l=n−1} B(ω_m, ω_l))` has ℓ¹ norms bounded by
`(n+1)²K² ν a_n + (n+1)K Σ a_m a_l`, geometric with a polynomial factor, and
the space derivatives cost the same `|k| ≤ (n+1)K`. The design note
(gimle-forseti `docs/mild-stream-design.md`, 2026-10-05) sizes this against
067 and records two differences: none of `IsClassicalSolution`'s fields
typechecks for the mild field, whose terms are `eval ν (ω_n k) t · cos(k·x)`
rather than `field (ω n) x · tⁿ`; and nothing is certified for `t < 0`, so at
`t = 0` only a one-sided derivative is available.

## Outcome

- `Streams/MildSolution.lean`: `mildField ν ω₀ t x`, the field lemmas of
  `EulerSolution.lean` restated with `t` as a parameter and the exponential
  polynomials' derivatives from `deriv` in the carrier; the derivative series
  summed on `(0, T)` by `hasDerivAt_tsum_of_isPreconnected` on `Ioo`, with
  continuity and the initial value at `0`
- `IsMildClassicalSolution`, a new structure after `IsClassicalSolution`
  (pointwise partials on `(0, T) × 𝕋²`, continuity of every field that
  appears, the stream-function Laplacian, the equation), and
  `mild_classical` for an even, mean-zero start on the certified interval of
  either bound of task 069
- the enstrophy identity `Z'(t) = −2ν Σ_k |k|² |ω̂_k(t)|²` on `(0, T)` and
  `Z(t) ≤ Z(0)` (the series over `k` differentiated under its own summable
  majorant on `|ω̂_k| |ω̂_k'|`; `ContinuousOn Z (Icc 0 T)` with
  `antitoneOn_of_deriv_nonpos`), and the energy identity `E' = −2νZ` by the
  other exchange (`p ↔ r`), both from the finite antisymmetry
  `Σ_k W_{−k} B(W, W)_k = 0` for every trigonometric polynomial `W`
- `Examples/MildBand.lean` extended with the restatements for the three-mode
  start; docs; nothing about uniqueness, continuation or the inviscid limit,
  said so; audited; a release

## Notes

Sized in the design note against task 067 (1479 lines over its commits, of
which 1011 `EulerSolution.lean`, 313 tests): at least 1500 lines; 067's
proofs carry over as method, not as code.


## Plan

Use the reviewed physical bounds and exact term equations to construct the
classical field on the interior of the certified forward interval, with
continuity and the initial field on the closed interval. Port the finite
Fourier derivative/Jacobian lemmas to real evaluated coefficients, establish
summable derivative majorants, and sum the exact PDE identities. Prove both
finite transport cancellations and justify the infinite energy/enstrophy
exchanges before deriving dissipation and nonincrease. Add boundary and
three-mode regressions, standard axiom audits, full/optional builds, a
three-role panel and CI. No arbitrary-classical uniqueness, continuation or
inviscid limit is asserted.

## Conversation

The owner authorized the complete three-stage fluid flow with PRs and merges.
Task069 is implemented, tested and panel-approved in dependent Asgard PR34;
task068 PR33 passed CI. This work starts from the reviewed bounds commit.
Development overlaps waiting CI, while publication remains ordered after
the replay repair, generalized Euler consumer, circuit and bounds releases.

## Implementation and validation

The classical field, one-sided initial derivative, coefficient PDE, both
finite and infinite nonlinear cancellations, modewise differentiated energy
and enstrophy sums, and closed-interval nonincrease are implemented. A
reconstruction theorem explicitly identifies the spectral coefficient sum
with the classical field. Both bounds apply to the same actual Wild output;
zero viscosity and zero geometric ratio are covered. Regression proofs pass (3436 jobs), the full build passes (7022 jobs), and all
four optional executables pass (6811 jobs). Axiom audits report only propext,
Classical.choice and Quot.sound; no placeholders or unchecked axioms remain.
All three panel roles passed. The mathematical reviewer requested an explicit
reconstruction bridge, now implemented and re-reviewed. CI, ordered merge,
and release remain pending.
