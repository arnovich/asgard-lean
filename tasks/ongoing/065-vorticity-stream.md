---
title: The formal vorticity stream on the torus — trigonometric-polynomial coefficients and the causal lemma over a module
state: ongoing
priority: medium
labels: [streams, lean, research]
related: ["060"]
claimed_by: claude/17d157a0
claimed_at: 2026-10-04T07:47:49Z
branch: feat/vorticity_stream
---

# The formal vorticity stream on the torus — trigonometric-polynomial coefficients and the causal lemma over a module

## Context

gimle-forseti's `docs/ns-stream-design.md` (2026-10-03) asks what the stream
machinery can say about the two-dimensional Navier–Stokes equations
themselves. The formal half is within reach of what exists: `Streams.Causal`
is generic in the equation but monomorphic in `Stream d = MvPowerSeries (Fin
d) ℚ`, and the vorticity equation `ω_t + u·∇ω = νΔω`, `u = ∇⊥Δ⁻¹ω`, from
trigonometric-polynomial initial vorticity has, at `t`-degree `n`, the
right-hand side `−νΔω_n − Σ_{m ≤ n} B(ω_m, ω_{n−m})` with
`B(P, Q) = Σ_{p+q=k} (p×q)/|p|² P_p Q_q`, both terms coefficientwise in `n`
and so causal trivially. The carrier is `ℚ[Fin 2 → ℤ]` (Mathlib's
`AddMonoidAlgebra`, Laurent polynomials in `e^{ix}, e^{iy}`): with ℚ
coefficients in the exponential basis it is the even (cosine) subspace by
construction, which the equation preserves, as it preserves mean zero. The
exponential-basis coupling differs from forseti-lean `GalerkinNS/Family.lean`'s
cosine-basis one by exactly that change of basis.

## Outcome

- `TrigPoly` (mean-zero `ℚ[Fin 2 → ℤ]`, or `(Fin 2 → ℤ) →₀ ℚ` with the
  invariant), `laplacian`, `laplacianInv` (zero on the zero mode), the
  bilinear `transport`, with the mean-zero and even-subspace invariants proved
- `TrigStream := ℕ → TrigPoly` with `derivative`/`integral` along `t` in OGF
  and EGF, and `Streams.Causal` restated over a ℚ-module carrier
  (`AgreeBelow`, `IsCausal`, Picard `approx`/`solution`, `solution_pde`,
  `formal_unique`, `eq_solution`), the existing lemma an instance
- `NS.rhs ν ω`, `rhs_causal`, `stream`, `stream_pde`, `formal_unique`; a
  computable `picard` for finitely supported data with coefficients read off
  by `decide +kernel`; an example from a three-mode start
- the lemma that the stream's coupling agrees with `Family.lean`'s cosine
  coupling on the even subspace
- roots stated over `derivative 0 ω = rhs ω`; the circuit tie
  (`circuit_solution`/`candidate_stream`) needs multiplier operations in the
  stream circuit language and is out of scope here
- audited to the three standard axioms; docs updated
