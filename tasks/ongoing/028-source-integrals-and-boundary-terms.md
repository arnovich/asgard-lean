---
title: Add source integrals with explicit boundary terms
state: ongoing
claimed_by: claude-028
claimed_at: 2026-09-28T09:38:43Z
branch: feat/source_integrals
priority: medium
labels: [compiler, isolation, migration]
related: ["027", "029"]
---

## Context

The source terms of `Model.Term` (gimle-forseti 083) have no integral. The
pinned Python grammar has `int(X,t)`, cancels `diff(int(X,t),t)` to `X`, and
isolates `diff(f,t) = g` to Form-A `f = int(g,t) + f0`. Python fixtures such as
`2 * diff(diff(int(f,t),t),t) = f`, `diff(diff(int(f,t),t),t) = f`,
`diff(f,t) = diff(int(f + g,t),t)`, `diff(int(2 * diff(f,t) + f,t),t) = 0`,
`2 * diff(f,t) = int(diff(f,t),t)`, `diff(f,t) = diff(f,t) + int(f,t)` and
`diff(f,t) = int(diff(f,t),t)` are therefore not representable in Lean.

The inverse directions differ: `D(I(X)) = X`, but `I(D(X)) = X - X(start)`, so
an integral-after-derivative rewrite must keep the boundary term.

## Outcome

- `Term` has an integral over a named axis from the declared start, with a
  source semantics that does not use totalized integrals of non-integrable
  functions.
- `D_t(I_t(X))` reduces to `X` with a proof; `I_t(D_t(X))` reduces only to
  `X - X(start)`, and a test shows that dropping the boundary term is rejected.
- The Python fixtures listed above are restated with their outcome, including
  any deliberate difference.
- Full `lake build` is clean and axiom audits show only standard axioms.
