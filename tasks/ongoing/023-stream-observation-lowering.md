---
title: Lower finite stream observations to circuits with checked dependencies
state: ongoing
claimed_by: claude-a023
claimed_at: 2026-09-26T16:30:22Z
branch: feat/stream_observation_lowering
priority: high
labels: [streams, compiler, observations, semantics]
related: ["024", "025"]
---

# Lower finite stream observations to circuits with checked dependencies

## Context

This builds on the existing formal stream implementation in `Gimle/Asgard/Streams/`.

Finite polynomial certificates can help prove stream properties only when their
variables are connected to the original stream circuit by a theorem.
`Streams.truncate_inside` currently proves
coefficient agreement inside a window; it does not prove that running an
operator on a truncated input produces the correct output window.

Asgard owns this lowering and its correctness. Downstream property systems own
predicates and theorems that use it; they must not become compiler dependencies.

## Outcome

- [x] Define a finite observation manifest whose slots identify port ID and
      natural multi-index, with separate ordered axis IDs and an explicit OGF/EGF
      basis. Read exact rational coefficients from full `StreamPoint d n` inputs.
      Bounds, duplicate slots, zero-sized windows and dimension/order consistency
      have specified behavior; no anonymous flattening establishes identity.
- [x] Given an original stream circuit and finite output observation, compute
      sufficient finite input dependencies and a typed rational-polynomial
      feedforward circuit for those output coefficients. Support routing,
      constants, axis variables, addition, stream product (coefficient
      convolution), selected-axis derivatives/integrals, sequential and parallel
      composition.
- [x] Prove that evaluating the lowered circuit on the extracted coefficients
      (cast exactly into its real interpretation) equals the extracted output
      of the original full-stream circuit. The theorem names the original
      circuit, basis and both manifests; lowering data alone grants no claim.
- [x] Dependency propagation accounts for derivative halo coefficients,
      convolution splits along every axis, and the complete required boundary
      slice of an integral. Propagate requirements backwards through composition;
      do not assume all intermediate windows have the same shape.
- [x] Reject `seriesCompose` and any future unsupported constructor explicitly
      in this first lowering, including unsupported operations whose output is
      later discarded. This must not erase Asgard's strict domain semantics.
- [x] Two-axis tests show that output coefficient `(0,0)` of `D_x² u` needs
      input coefficient `(0,2)` with OGF factor 2 and EGF factor 1. Two streams
      agreeing on a smaller window can yield different observed derivatives.
      Include mixed-axis products, boundary dependence on the other axis,
      asymmetric wiring and named-axis permutations.
- [x] Check both outputs of the existing `FormalHeat` circuit through this
      bridge and include a polynomial input with a nonzero coefficient outside
      the naive window. The observation theorem, not just the example's zero
      tail, must justify each successful finite evaluation.
- [x] Bound dependency expansion and intermediate polynomial size in the
      executable lowering; distinguish unsupported structure from exhausted
      resource limits. No numerical tolerance enters coefficient claims.
- [x] `lake build`, executable standard-axiom audit and positive/hostile
      regressions pass. Update `docs/formal-streams.md` with the precise supported
      observation fragment and the derivative counterexample.

## Plan

1. Fix manifests and exact extraction; write the missing-halo counterexample.
2. Lower each primitive with a correctness theorem and compose dependency maps.
   Reuse the existing polynomial compiler and stream encode/decode laws.
3. Verify the full heat fixture, both bases, reordered axes and refusal paths;
   review compiler correctness and input/evidence binding.

## Scope

This theorem concerns selected exact coefficients, not the full stream or its
analytic values. There is no zero-tail assumption, numerical error estimate,
general substitution lowering, feedback solver, Python compiler port or proof
of JAX execution. Analytic evaluation and tail bounds are tasks 024 and 025.

## Conversation

### note · claude/88c9ba9a · 2026-09-26T16:59:33Z

Done in `Gimle/Asgard/Streams/Lowering.lean`. `lowerRaw_correct` is the exact
coefficient theorem for every supported constructor; `lower_correct`,
`lower_names` and `lower_defined` bind a lowered observation to the original
circuit, its basis and both manifests. Degrees are `Fin d → ℕ` so the lowering
computes; `Degrees`, `Slot` and `Term` have hand-written decidable equality
because the derived instances (and `Function.update`) do not reduce in the
kernel. For forseti-lean 020: `lower` output plus `lower_correct` is the bridge
from a finite polynomial certificate over the dependency coefficients to the
observed output coefficients; `dependencyPoint_extract` connects it to
`Manifest.extract`.
