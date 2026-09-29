---
title: Read division by a nonzero literal as a scale in every source pass
state: open
priority: low
labels: [compiler, isolation]
related: ["030"]
---

## Context

Task 030 reads a division by a nonzero literal product as a scale only in
isolation (`Term.affine`) and beta normalization. The integral rewrites
(`Term.cancel`), the reading of declared velocities, and the `pointwise` and
`tame` checks do not look inside `.binary .division`, so
`int(diff(f,t),t) / (2*3)` or a lower-order `diff(x,t)/(2*3)` is rejected where
the same term written `* rat(1,6)` is accepted. The docs record this as a
completeness gap.

## Outcome

- Division by a nonzero literal is normalized to a product by its inverse before
  those passes (or each pass reads it), exactly, with a theorem.
- The two forms above are accepted and lower as their `* rat(1,6)` forms do.
- Full `lake build` is clean and axiom audits show only standard axioms.
