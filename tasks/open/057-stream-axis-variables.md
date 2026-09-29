---
title: Read axis variables in stream source terms
state: open
priority: low
labels: [streams, isolation]
related: ["029", "043"]
---

## Context

Task 029's `NamedExpr.ofTerm` reads every name in a stream source term as an
input, so a source such as `diff(u,t) = t`, where `t` is the axis variable, reads
an input named `t` instead; Python would read the axis. Axes and inputs have
separate namespaces in `Streams.Declaration`.

## Outcome

- A stream source term can name an axis variable, resolved by the declared axis
  namespace, and a name that is both an axis and an input is refused with a
  diagnostic.
- `diff(u,t) = t` isolates with the axis variable and its solution set is proved;
  a Python fixture using an axis variable is restated with its outcome.
- Full `lake build` is clean and axiom audits show only standard axioms.
