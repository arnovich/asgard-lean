---
title: The analytic field of the Euler stream is a classical solution — termwise derivatives, the Jacobian identity and the equation on |t| < 1/ρ
state: ongoing
priority: medium
labels: [streams, lean, research]
related: ["065", "066"]
depends_on: ["066"]
claimed_by: claude/17d157a0
claimed_at: 2026-10-04T17:40:00Z
branch: task/067_euler_classical_solution
---

# The analytic field of the Euler stream is a classical solution — termwise derivatives, the Jacobian identity and the equation on |t| < 1/ρ

## Context

Task 066 certifies a radius for the formal vorticity stream of the Euler
equation and proves truncations and bands of the sum of its `t`-series,
`analyticField ω t x = Σ_n field (ω n) x tⁿ`. Every docstring, the lecture
notes and the `Euler.lean` notebook say the same sentence: that this sum is
a solution of the Euler equation is a Cauchy–Kowalevski identification made
on paper, not a statement of the library. That sentence is the first gap
between the shelf and any statement about a fluid equation itself, and it is
the same machinery the planned mild (viscous) stream will need.

The identification is elementary once the objects are explicit. For a
mean-zero `P` and an even `Q`, `field (transport P Q) = ∂₁ψ ∂₂q − ∂₂ψ ∂₁q`
with `ψ = field (laplacianInv P)` and `q = field Q`: expanding the products
of sines by `sin a sin b = (cos(a − b) − cos(a + b))/2` and using the
evenness of `Q` to fold the `a − b` terms turns the Jacobian into
`Σ_{p,q} (p×q)/|p|² P_p Q_q cos((p+q)·x)`, which is `transport_apply`. The
series in `t` is differentiated termwise under the geometric bound
(`hasDerivAt_tsum_of_isPreconnected`) in `t`, and in `x` because the modes
of `ω_n` have size at most `(n+1)K` (`sizeLE_stream`), so the derivative
coefficients are bounded by `(n+1)K M ρⁿ`; the Euler recursion `euler_succ`
turns `∂_t` of the series into minus the Cauchy product of the series of
`ψ` and `ω` (`tsum_mul_tsum_eq_tsum_sum_antidiagonal`, as `AnalyticField`
does for the heat stream).

## Outcome

- partial derivatives of `field`: `∂ᵢ field P x` as the finite sine sum
  `−Σ_k kᵢ P_k sin(k·x)`, `HasDerivAt` in each coordinate, second
  derivatives, and `field (laplacian P) = Δ (field P)` pointwise
- the Jacobian identity `field (transport P Q) x = ∂₁ψ ∂₂q − ∂₂ψ ∂₁q` for
  mean-zero `P` and even `Q`, `ψ = field (laplacianInv P)`, `q = field Q`
- the stream function series `Ψ(t, x) = Σ_n field (laplacianInv (ω n)) x tⁿ`
  with `ΔΨ = analyticField ω` pointwise on `|t| < 1/ρ`, and the velocity
  `u = ∇⊥Ψ = (−∂₂Ψ, ∂₁Ψ)`, divergence-free
- termwise `HasDerivAt` of `analyticField` and `Ψ` in `t` and in each `x`
  coordinate on `|t| < 1/ρ`, from `GeometricBound ω M ρ` and
  `SizeLE K (b 0)`
- **the equation**: for `ω = NS.stream .ogf 0 b` with an even, mean-zero
  start, on `|t| < 1/ρ` and at every `x`,
  `∂_t analyticField + u·∇ analyticField = 0`, i.e.
  `∂_t F + ∂₁Ψ ∂₂F − ∂₂Ψ ∂₁F = 0`, and `F(0, x) = field (b 0) x`
- the three-mode example: a classical solution on `|t| < 1/648`
  (`Examples/EulerBand`), stated so gimle-forseti's `Euler.lean` can restate
  "solves the Euler equation" for the first time
- docs and docstrings: the sentence "identification on paper" replaced
  everywhere it appears by the theorem; what remains paper work (that the
  cosine field of an even polynomial is the real exponential sum, and that
  the formal transport is the physical `u·∇ω`) stated once, in `TrigField`
- audited; a release
