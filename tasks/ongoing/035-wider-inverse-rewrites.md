---
title: Widen the inverse rewrites to declared chains and richer integrands
state: ongoing
claimed_by: claude-a035
claimed_at: 2026-09-28T15:05:10Z
branch: feat/wider_inverse_rewrites
priority: low
labels: [compiler, isolation]
related: ["028", "034"]
---

## Context

Task 028's inverse rewrites (`Term.cancelAtom` in `Model.Integral`) accept only
`D_t(I_t(X))` with a tame `X` (a polynomial in states and bound parameters plus
literal multiples of first-order state derivatives), `D_t(D_t(I_t(x)))` and
`I_t(D_t(x))` for a state `x`, and only at the atom positions of sums, products
and negations. These are rejected with `unsupportedIntegral` although their
meaning is exact:

- `int(diff(diff(f,t),t),t)`, which is `v - v0` when `v` is the declared velocity
  of `f`, and longer chains;
- `D_t^k(I_t(x))` for `k ≥ 3`, which Python accepts;
- nested pairs such as `diff(f,t) = diff(int(diff(int(f,t),t),t),t)`, which
  Python accepts as `f' = f`: `Term.cancel` rewrites once at atom positions and
  never inside an integrand;
- a bound parameter factor on a derivative in an integrand,
  `diff(int(p * diff(g,t),t),t)`, which Python accepts; `Term.tame` allows only
  literal factors;
- integrands with applied lambdas or auxiliaries, whose readings along the
  trajectory are continuous once their assignments are (the trajectory reading
  of `SourceBody.Solves` names only states and parameters today).

Diagnostics for these all read `unsupportedIntegral` with the equation's output
as reference, so a wrong axis, a non-tame integrand and an integral with no
rewrite look alike.

## Outcome

- Each form above lowers to the expected assignment with a proof of
  preservation, using the declared velocities for chains, and keeps its boundary
  term.
- Regression tests cover each new form and the forms that stay rejected, and the
  Python fixtures above move from "differs" to "same" where Lean now agrees.
- An `unsupportedIntegral` diagnostic names the reason (axis, integrand, or no
  inverse rewrite).
- The end-to-end theorems keep their statements; full `lake build` is clean and
  axiom audits show only standard axioms.
