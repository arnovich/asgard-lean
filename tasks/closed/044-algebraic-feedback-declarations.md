---
title: Declare affine algebraic loops with checked inverses
state: closed
priority: low
labels: [compiler, algebraic, declaration]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Algebraic feedback": `compile_correct` and
`Problem.eliminate_correct` exist, but the common compiler rejects every cycle
as `cyclicDependency`. Python refuses algebraic loops and is not ported; only
elimination with a supplied inverse admits one in Lean.

## Outcome

- A declaration case for simultaneous affine equations with a loop domain, an
  admitted-input predicate and a supplied inverse of `1 − M`, both products
  checked; a singular system is rejected with a diagnostic.
- Two theorems kept apart: the declaration's relation equals `Rel` for every
  input, and on admitted inputs it has exactly the eliminated solution.
- The membership obligation `∀ u, admitted u → domain (solution u)` is a
  proof obligation of the declaration; the coordinate order is [loop, external].
- Positive: `halfLoop`. Hostile: `z = z + 1` (no inverse), and
  `z = z/2 + 1` with `z ∈ [−1, 1]` (membership fails).
- Full `lake build` is clean and axiom audits show only standard axioms.
