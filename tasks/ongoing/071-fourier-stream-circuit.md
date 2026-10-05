---
title: Fourier stream circuits and the Euler feedback semantics
state: ongoing
priority: medium
labels: [circuits, euler, formal-methods]
claimed_by: codex/euler_circuit
claimed_at: 2026-10-05T10:24:03Z
branch: feat/euler_circuit
---

## Context

The Euler vorticity stream currently bypasses Asgard circuit syntax. The owner requested a circuit interpretation and a proved connection to the existing analytical solution, so Forseti can state contracts over the circuit.

## Outcome

- Typed Fourier-stream circuit primitives, wiring and relational feedback have explicit semantics.
- An Euler/Navier-Stokes feedback circuit is assembled from those primitives.
- Its relation is equivalent to the formal vorticity equation with the input boundary, and to the unique existing NS.stream.
- Regression proofs cover both bases, boundary dependence, a wrong candidate and standard axiom policy.
- Full library build and panel review pass.

## Plan

Study the existing stream and continuous circuit semantics. Add regression statements first, implement the circuit/contract bridge, then check all build targets and independent panel findings. Keep the mathematical stream as the semantic reference and keep feedback relational; never assume an arbitrary loop has a solution.

## Validation

Implemented `Streams/FourierCircuit.lean` (typed operators, relational trace,
expression compiler), `Streams/VorticityCircuit.lean` (the explicit loop and
its equation/unique-solution bridges), and `Tests/FourierCircuit.lean`.
The regression statements were added first and failed on the missing module.
`lake build` passes, as do all four optional executable targets. The relation
and PDE bridge axiom guards permit only propext, Classical.choice and Quot.sound.

A three-role panel reviewed circuit architecture, mathematical proof boundaries,
and integration/claims. All passed without blocking findings. Pairing and guarded
feedback contract rules can be added in Forseti when another example needs them.
The Python application's existing release pin is not changed by this work.
