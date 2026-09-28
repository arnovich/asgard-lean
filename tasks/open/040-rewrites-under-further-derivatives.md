---
title: Rewrite inverse pairs under further derivatives and inside chain integrals
state: open
priority: low
labels: [compiler, isolation]
related: ["035", "036"]
---

## Context

Task 035 rewrites inside the integrand of an inverse pair `D_t(I_t(X))` before the
pair itself, and rewrites `D_t^m(I_t(x))` and `I_t(D_t^(k+1)(x))` for a state `x`
through declared velocities. It does not rewrite inside other shapes, so two forms
the pinned Python compiler (gimle-asgard `fba931e`) accepts stay rejected with
`unsupportedIntegral` (`no inverse rewrite`):

- `diff(f,t) = diff(diff(int(int(f,t),t),t),t)`, which Python reads as `f' = f`. The
  pair `D_t(I_t(I_t(f)))` sits under a further derivative, and `D_t^m(I_t(X))` is
  rewritten only for a state `X`. This holds even with `F = int(f,t)` declared.
- `diff(f,t) = int(diff(int(diff(g,t),t),t),t)`: the operand of `I_t(D_t(·))` holds a
  pair, and it is never rewritten inside.

Both have an exact meaning. For example, `D_t(D_t(I_t(X)))` is `D_t(X)` along the
trajectory whenever `X` is tame and not a chain.

## Outcome

- `D_t^m(I_t(X))` for a compound tame `X`, and `I_t(D_t(Y))` whose operand `Y`
  rewrites to a state, lower with a proof of preservation in the style of
  `Term.cancelAtom_along`, keeping every boundary term.
- The two Python fixtures above move from "DIFFERS" to "Same" in
  `Tests/SourceIntegrals.lean`.
- `Lowered.solves_iff` and the other end-to-end theorems keep their statements.
