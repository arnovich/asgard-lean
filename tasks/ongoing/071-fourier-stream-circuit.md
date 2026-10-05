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
