---
title: Accept series substitutions with a proved zero constant coefficient
state: open
priority: low
labels: [streams]
related: ["043"]
---

## Context

Task 043 accepts `seriesCompose` only when its inner argument is in a syntactic
class proved to have zero constant coefficient (`NamedExpr.composable`,
`composable_sound`). A substitution whose argument vanishes at the origin for
semantic reasons, such as a declared input constrained to do so, is refused as
`unestablishedCompose`.

## Outcome

- A declaration can carry evidence that a substitution's inner argument has zero
  constant coefficient (for example a declared input constraint), and such a
  substitution is accepted with `CanCompose` established from it.
- The syntactic class keeps working unchanged; an unsupported case is still
  refused as unsupported.
- Full `lake build` is clean and axiom audits show only standard axioms.
