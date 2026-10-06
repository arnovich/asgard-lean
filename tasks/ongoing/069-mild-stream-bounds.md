---
title: Two bounds for the mild vorticity stream — the Wiener-algebra contraction, the Euler scale at every viscosity, certified truncation and bands
state: ongoing
priority: medium
labels: [streams, lean, research]
related: ["066", "068"]
depends_on: ["068"]
claimed_by: codex/fluid_contracts
claimed_at: 2026-10-06T01:07:56Z
branch: feat/mild_vorticity_bounds
---

# Two bounds for the mild vorticity stream — the Wiener-algebra contraction, the Euler scale at every viscosity, certified truncation and bands

## Context

Task 068 builds the Wild expansion of the mild vorticity equation and computes
its terms; nothing there estimates. gimle-forseti's `docs/mild-stream-design.md`
(2026-10-05) derives two bounds on the terms, both with rational constants,
and sizes them against task 066.

**Bound one**, the Wiener-algebra contraction, in the norm
`‖ω‖_T = Σ_k sup_{[0,T]} |ω̂_k|`: with `p + q = k`, `coupling(p, q)² ≤ |k|²/|p|²`
by Lagrange's identity (`cross_sq_le`), so the derivative loss sits on the
output mode; the heat kernel absorbs it, `sup |D_λ e| ≤ min(T, 1/(νλ)) sup |e|`;
and `|k| · min(T, 1/(ν|k|²)) ≤ r` whenever `T ≤ ν r²`, in squares. Hence
`‖D B(a, b)‖_T ≤ r ‖a‖_T ‖b‖_T`, the terms satisfy `‖ω_n‖_T ≤ a_n` with
`a_n = L (rL)ⁿ C_n` (Catalan), `a_{n+1} ≤ θ a_n` for `θ = 4rL` from
`C_{n+1}/C_n ≤ 4`, and `Σ_{n>N} a_n ≤ a_{N+1}/(1−θ)`. For the three-mode start
(`L = 3`) at `ν = 1/10`, `θ = 1/2`: `T = ν r² = 1/5760`, tail `21/1024` after
`ω_3`, band `±3.519` from the bounds alone.

**Bound two**: the heat factor is in `(0, 1]` modewise, so `euler_wnorm_bound`'s
induction goes through for the Wild terms with `∫₀ᵗ sⁿ ds = tⁿ⁺¹/(n+1)` in
place of the OGF division, giving `l1 (ω_n(t)) ≤ 3L (72 L K)ⁿ tⁿ` at every
`ν ≥ 0`: the Euler time `1/648` for the same start, uniformly in `ν`, nine
times longer than bound one's at this viscosity. It is the same induction in a
new analytic wrapper, not a transfer: `wnorm`, `dnorm`, `wnorm_transport_le`
and `dnorm_le_wnorm_div` are stated on rational `TrigPoly`s, and the evaluated
terms have real coefficients.

The note's spike (`docs/spikes/219-mild-stream`) checks bound one's constant
and every rational above exactly; bound two's figures are arithmetic from
`euler_l1_geometric`'s constants.

## Outcome

- `Streams/MildRadius.lean`, bound one: `coupling_sq_le` (hypothesis-free,
  `coupling 0 q = 0`), the two Duhamel sup lemmas `≤ t·A` and `≤ A/a` for
  `0 < a` (the fundamental theorem of calculus with `integral_exp`, the only
  integrals in bound one), `Majorized ν T P m := ∀ k, ∀ t ∈ Icc 0 T,
  |eval ν (P k) t| ≤ m k` with `m : (ℤ × ℤ) →₀ ℚ` — no `sSup` —
  `transport_majorized` through the per-pair, square-free lemma
  `|coupling p q| · min(T, 1/(ν · lam (p+q))) ≤ r`, `duhamel_majorized`,
  `wild_catalan : l1 m_n ≤ L (rL)ⁿ C_n` and `wild_geometric` with the two
  Catalan consequences from `succ_mul_catalan_eq_centralBinom`,
  `succ_mul_centralBinom_succ`, `catalan_eq_centralBinom_div` and
  `centralBinom_le_four_pow`
- bound two: `mwnorm σ ν P t := Σ_k |eval ν (P k) t| · e^{σ|k|₁}` and its
  `dnorm`, the transport and Nagumo inequalities re-proved over `eval`, the
  modewise Duhamel integral representation with `|D f_k(t)| ≤ ∫₀ᵗ |f_k(s)| ds`,
  `wild_wnorm_bound` by the strong induction of `euler_wnorm_bound` with
  `∀ s ∈ [0, t]` inside (reusing `convolution_sum_le`, `ratio_pow_le_three`
  and the closing arithmetic), and `wild_l1_geometric` for every `ν ≥ 0`
- a generic tail lemma (`|f n| ≤ M ρⁿ` for `n ≥ N`, `ρ < 1`, gives
  `|∑' f − Σ_{n<N} f n| ≤ M ρᴺ/(1−ρ)`), `MildTruncationBound ν ω₀ T N ε` with
  the window `Finset.range N` as in `TrigField.lean`, the tail from either
  bound, and the band `L + Σ_{1≤n<N} a_n + tail` from the bounds alone — the
  carrier's coefficients are never read
- `Examples/MildBand.lean`, the three-mode start at `ν = 1/10`: `T = 1/5760`
  with the tail `21/1024` after `ω_3` and the band `±3.519` (rounded up), and
  `t < 1/648` at every `ν ≥ 0` with the tail `9 q⁴/(1−q)`, `q = 648 t`
- every statement about the series; nothing about the equation, not even its
  integral form, said so in docs and docstrings; audited; a release

## Notes

Sized in the design note against task 066 (1619 lines, of which 303 tests):
about 1800 lines, bound two about 500 of them, all bookkeeping. The two bounds
cross at `ν > 2L/(9Kθ²)`, `8/9` for this start at `θ = 1/2`; a notebook can
state both and the lane (gimle-forseti) certifies the better. Both are far
from sharp: the spike's 60-digit sups fall by about `10⁻⁴` per degree.

## Plan

Implement both reviewed bounds on the actual Wild terms, using rational
modewise majorants for bound one and weighted real evaluated norms for bound
two. Reuse the exact integral representation and finite support invariants of
task 068. Handle the zero output mode before dividing by its Laplacian rate,
keep strict geometric endpoints, and certify the requested window/tail/band
without reading exponential-polynomial coefficient absolute sums. Add the
three-mode rational regressions and axiom audits, then full/optional builds,
three-role panel review and CI. Classical realization and dissipation remain
task 070.

## Conversation

The owner authorized all three fluid stages without further permission. Task
068 is implemented, locally validated and panel-approved in Asgard PR33. This
dependent worktree starts from that reviewed commit while CI runs. Releases
and merges remain ordered: replay repair, generalized Euler consumer, task068,
then these bounds. No dependent release is published ahead of its prerequisite.


## Progress

Both bounds are implemented on physical evaluations of the actual Wild
stream. The weighted real Fourier induction compiles for every nonnegative
viscosity. Rational modewise majorants give the Catalan bound at positive
viscosity, with explicit zero-mode handling in the heat absorption proof.
The shared field layer proves absolute convergence, sharp shifted tails and
bands; the three-mode constants and exact-zero/general-boundary regressions
are implemented. The default build passed 7005 jobs, and all four optional
executables passed (6811 jobs). New axiom reports contain only propext,
Classical.choice and Quot.sound; no warnings or placeholder proofs remain.
All three panel roles passed: mathematical correctness, circuit/output
semantics, and integration/documentation. The future consumer must retain
convergence in Certified when using the band predicate. PR33 passed CI; this
bounds PR remains dependent on it and publication stays behind replay/Euler.
No classical/PDE/dissipation claim is made in this task.
