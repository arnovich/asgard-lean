---
title: The Euler radius — a Cauchy–Kowalevski induction in a scale, certified truncation and a band for the vorticity stream
state: closed
priority: medium
labels: [streams, lean, research]
related: ["061", "062", "065"]
depends_on: ["065"]
---

# The Euler radius — a Cauchy–Kowalevski induction in a scale, certified truncation and a band for the vorticity stream

## Context

For positive viscosity nothing certifies a radius in `t` for the formal
vorticity stream of task 065 (for viscous Burgers from `sin x` it is zero by
a one-line Tonelli computation on the Cole–Hopf series; for Navier–Stokes
that is the generic expectation, with single-shell data an entire exception),
and gimle-forseti's `docs/ns-stream-design.md` plans no field band there.
For the Euler equation (`ν = 0`) a radius is provable, and it is the one new
theorem of the arc: the derivative costs a factor `|q|` on a trigonometric
polynomial whose degree grows linearly in the step, and the multiplier
`|p×q|/|p|² ≤ |q|`, so the termwise geometric induction fails by a linear
factor and the Cauchy–Kowalevski device in a scale is needed (Nirenberg 1972,
Nishida 1977; Bardos–Benachour 1977 for Euler; Levermore–Oliver 1997 and
Kukavica–Vicol 2009 for the periodic radius). The library's majorants are
geometric bounds combined by a calculus (`Streams/Tail.lean`, `Majorant.lean`),
never a majorant equation.

## Outcome

- weighted ℓ¹ norms `‖P‖_σ = Σ |P̂_k| e^{σ|k|}` on `TrigPoly` with the Nagumo
  estimate `|k| e^{σ'|k|} ≤ e^{σ|k|}/(e(σ − σ'))`
- the weighted induction `‖ω_n‖_σ ≤ M (C/(σ₀ − σ))ⁿ/(n+1)²` for every
  `σ < σ₀` (intermediate radius `σ' = σ + (σ₀ − σ)/(n+1)`, the convolution
  sum `Σ_m 1/((m+1)²(n−m+1)²) ≤ c/(n+1)²`), hence `‖ω_n‖_{σ₀/2} ≤ M (2C/σ₀)ⁿ`
  and a radius `t ≥ σ₀/(2C)` from the data's ℓ¹ norm and largest mode, both
  decidable
- the one-axis tail in `t`: `TruncationBound` on `|t| ≤ r` with the window a
  trigonometric polynomial of `t`-degree `< N`, and a band on the field from
  the window's ℓ¹ spread plus the certified error (`abs_cos_le_one`), with no
  inverse table and no closed form
- for `ν > 0`, the Gevrey-1 lemma `‖ω_n‖_{ℓ¹} ≤ M Cⁿ n!` and a docs section
  with the Tonelli computation for Burgers, the single-shell exception and
  the growth ratios as evidence, as `Examples/BurgersSquare` does
- audited; a release

## Conversation

### note · claude/17d157a0 · 2026-10-04T15:30:00Z

Closed after PR #30, tagged v1.14.0. Delivered with these differences from
the text above: Nagumo is stated as `dnorm σ Q ≤ wnorm σ' Q/(2(σ' − σ))` for
`σ < σ'` (the constant `1/2` for `1/e`, keeping every constant rational; the
outcome's `σ, σ'` are the other way round); the intermediate radius is
`σ + (σ₀ − σ)/(n+2)`, the convolution sum `≤ 8/(n+2)²`, and `C = 24M`; the
ℓ¹ bound is taken at `σ = 0` (not `σ₀/2`), `l1 ω_n ≤ M (24M/σ₀)ⁿ`, and the
rational radius is `1/(72 L K)` for modes of size at most `K` and ℓ¹ norm at
most `L`; the one-axis tail is stated directly for `TrigStream`
(`TruncationBound`, `tailBound`), not through `Tail.lean`'s `TruncationBound`,
whose carrier differs, and the "window" is the finite sum through `t`-degree
`N − 1`, not a polynomial object; the Gevrey constant is `νK² + KL` over the
ℓ¹ size (the crude `m!(n−m)! ≤ n!` closes it); the docs give the Tonelli
computation in one paragraph and point to gimle-forseti's design note as its
owner, and show no growth ratios — evidence belongs to the notebook (task
216). Every statement is about the analytic field of the formal stream; its
identification with the Euler solution is paper work, said so in docs and
docstrings. Example: `l1 ω_n ≤ 9·648ⁿ`, convergence for `|t| < 1/648`,
truncation `1/100` and band `1/50` on `|t| ≤ 1/6480`.
