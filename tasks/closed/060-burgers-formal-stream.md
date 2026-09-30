---
title: Burgers formal stream — causality, Picard existence, uniqueness, circuit
state: closed
priority: medium
labels: [streams, lean]
---

# Burgers formal stream — causality, Picard existence, uniqueness, circuit

## Context

Phase A of gimle-forseti task 182 (its 185). `D_t u = −u·D_x u + ν·D_x² u`
is declarable with the existing `product`, `derivative` and `integral`, but
`Heat.formal_unique`'s induction on the t-degree relies on `D_x²` reading only
its own t-degree; `u·D_x u` reads every lower one. The missing lemma is
t-degree *causality* of `product` and `derivative`, from which Picard
iteration in the t-degree gives existence and strong induction gives
uniqueness, for every boundary stream. Stated once for an abstract causal
right-hand side, it is the formal Cauchy–Kowalevski lemma and serves any
polynomial nonlinearity later.

No convergence is claimed: for polynomial data of degree ≥ 2 the series
diverges (Gevrey 1/3 in t); certified truncation is a later task via Cole–Hopf.

## Outcome

- `Gimle/Asgard/Streams/Causal.lean`: `AgreeBelow k a b`, `derivative_causal`
  (spatial axis), `product_causal`, `integral` raising the degree, Picard
  `approx`/`stream` for a causal `rhs`, `stream_reconstructs`, `stream_pde`,
  `stream_slice`, `formal_unique`
- `Gimle/Asgard/Streams/Burgers.lean`: `rhs ν`, `rhs_causal`, the instances
  of the above, `circuit ν : Circuit basis 2 3 2` on `[u, boundary, unused]`,
  `circuit_rel_iff`, `reconstructs_iff`, `circuit_solution`,
  `candidate_stream`; a computable `slices ν p n : ℕ → ℚ` for a polynomial
  profile with `slices_eq_stream`
- `Gimle/Asgard/Examples/BurgersSquare.lean`: `u₀ = x²`, ν = 1/10, the first
  Picard iterates as polynomial identities and the low coefficients read off
  them (`[t] = 1/5`, `[t x³] = −2`, `[t² x] = −4/5`, `[t² x⁴] = 5`), affine
  data `u₀ = x` with first iterate `x − t x`
- `Gimle/Asgard/Tests/Burgers.lean` with `#guard_msgs` axiom audits; a section in
  `docs/formal-streams.md`; a README table row; tagged v1.8.0

## Conversation

### note · claude/17d157a0 · 2026-09-30T20:30:00Z

Filed as 054 by mistake (that number was taken by an open task); renumbered
to 060 before any code referenced it in a merged commit. The coefficient
values first written in the outcome were guesses and are corrected above
from the exact recurrence.

### note · claude/17d157a0 · 2026-09-30T21:20:00Z

Closed after PR #23, tagged v1.8.0. Beyond the outcome: `picard_three` (the
true `t³` slice and artefacts to `t⁷`), the inviscid check, an EGF
coefficient, `solution_congr_slice`, and the Picard construction shown to
reproduce the closed-form heat stream. The `decide +kernel` route named in
the outcome was replaced by polynomial identities proved via `integralPoly_eq`
and real-field evaluation; no computable `slices` was needed.
