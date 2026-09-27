---
title: Admit real atomics and non-literal division in source terms
state: open
priority: low
labels: [compiler, isolation, migration]
related: ["029", "031"]
---

## Context

The source terms of `Model.Term` (gimle-forseti 083) are polynomials with
applied lambdas: division is only by a positive numeral, and there are no real
atomics. Python also accepts scales written as `diff(f,t) / (2 * 3)`,
`diff(f,t) / (-(2 * 3))` and `(-2 / -4) * diff(f,t)`, which Lean can only
state with an equal `rat(n,d)` literal today. The pinned Python grammar also has `sin`, `exp`, `log`, powers and
division by expressions, as in `sin(diff(f,t)) = f` and `diff(f,t) / f = 1`,
and decimal or scientific literals such as `1e-309`. `RealAtomics` already
compiles partial real functions with their domains, but common source
declarations cannot reach it.

## Outcome

- Explicit assignments and derivative-free residuals may use the `RealAtomics`
  operations, with every domain condition retained in the source relation.
- Division by an expression keeps its nonzero-denominator condition; a
  derivative under an atomic or in a denominator stays rejected by isolation.
- Decimal and scientific literals elaborate to exact rationals.
- Division by a literal product or a negative numeral is accepted as a scale,
  so the three Python scale fixtures above isolate to their exact values.
- The Python fixtures named above are restated with their outcome.
- Full `lake build` is clean and axiom audits show only standard axioms.
