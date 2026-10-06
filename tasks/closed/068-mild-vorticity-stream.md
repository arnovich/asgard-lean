---
title: The mild vorticity stream — exponential-polynomial coefficients, the Duhamel map and Wild's expansion over the shift axis
state: closed
priority: medium
labels: [streams, lean, research]
related: ["065", "066", "067"]
---

# The mild vorticity stream — exponential-polynomial coefficients, the Duhamel map and Wild's expansion over the shift axis

## Context

For `ν > 0` the power series in `t` of the vorticity stream (task 065) is the
wrong object: `gevrey_one` bounds its coefficients by `Cⁿ n!` and no radius is
certified. gimle-forseti's `docs/mild-stream-design.md` (2026-10-05) fixes the
right one: the mild formulation
`ω̂_k(t) = e^{−ν|k|²t} ω̂_k(0) − ∫₀ᵗ e^{−ν|k|²(t−s)} B(ω, ω)_k(s) ds` expanded in
the number of interactions,

    ω_0 = e^{νΔt} ω₀,   ω_{n+1} = −Σ_{m+l=n} D(B(ω_m, ω_l)),

whose terms are trigonometric polynomials with **exponential polynomials in
`t`** as coefficients — rational combinations of `tᵐ e^{−νλt}`, `λ ∈ ℕ` — a
monoid algebra closed under products and under the Duhamel map `D_μ` by
integration by parts. At `ν = 0` the terms are `tⁿ` times the Taylor
coefficients of `NS.stream`, so the Euler files are the `ν = 0` case after
evaluation. The axis is the interaction degree with the plain shift, the shape
of `trigAxis .egf`. gimle-forseti's spike `docs/spikes/219-mild-stream`
checks the Duhamel closure, the termwise equations, the `ν = 0` agreement and
the pairings exactly, and is the reference for every number.

Two traps the note records: the by-parts formula divides by `c = ν(μ − λ)`,
so `duhamel` must split on `c = 0` (`ν = 0` or `λ = μ`), never on `λ = μ`,
or Lean's `x / 0 = 0` makes it silently wrong at `ν = 0`; and the by-parts
representation cancels (coefficient sums of `10` to `8·10⁶` against sups of
`10⁻⁴` to `10⁻³²` for the three-mode start), so no bound may ever read the
carrier's coefficients — this task computes, task 069 estimates.

## Outcome

- `Streams/ExpPoly.lean`: the carrier as a monoid algebra (either
  `AddMonoidAlgebra ℚ (ℕ × ℕ)` indexed by `(λ, m)`, or `AddMonoidAlgebra ℚ[X] ℕ`
  with a polynomial in `t` per `λ`, evaluated by `liftNCAlgHom` with
  `Polynomial.aeval` and `λ ↦ exp(−νλt)`; the note prefers the second), `eval`
  as a `ℚ`-algebra map, `deriv`, `duhamel` split on `c = 0`, and the theorems
  `deriv_duhamel : (D_μ e)' + νμ • D_μ e = e`, `eval_duhamel_zero` and
  `eval_mul`; the ring is `ν`-free, the operations are not
- `Streams/Mild.lean`: `MildPoly := (ℤ × ℤ) →₀ ExpPoly`; `transport` restated
  on it beside `Torus.lean` (not a generalisation of `Torus`), with
  `transport_apply`, `transport_single_single` and the mean-zero, parity and
  `SizeLE` invariants; `laplacian`, `heat`, the modewise `duhamel`; a
  `shiftAxis C : Causal.Axis (ℕ → C)` written once; the stream as
  `Causal.solution` with `wild_succ`, `wild_recursion_unique` (named for what
  it is), the invariants along the stream, the exact termwise equation
  `deriv_wild_succ : ω_{n+1}' = νΔω_{n+1} − Σ_{m+l=n} B(ω_m, ω_l)` and
  `wild_eval_zero : eval 0 (wild n) t = tⁿ • stream .ogf 0 b n` — the only tie
  to the Euler files
- `Streams/MildTable.lean`: a list-based computable mirror after
  `VorticityTable.lean` (product a monoid-algebra convolution, `duhamel`
  mapping each entry to `m + 2` entries), `stream_eq_table`, the three-mode
  start's terms read by `decide +kernel` to degree 2, and the degree-3 cost
  measured and recorded in the docs
- tests after `Tests/Vorticity.lean`, including `deriv_duhamel` at `ν = 0`
  and a term at `ν = 0` against the Euler stream; a `docs/formal-streams.md`
  section saying what the carrier is for and that nothing here estimates;
  audited; a release

## Notes

Sized in the design note against task 065 (1943 lines, of which 423 tests):
about 1500–1700 lines, no new mathematics; the `c ≠ 0` Duhamel identity is
the one fiddly proof, and the polynomial-coefficient carrier replaces its
factorial telescoping by `c·Q + Q' = p` for `Q = Σ_j (−1)ʲ p⁽ʲ⁾/cʲ⁺¹`, with
`D_μ(p · Xᵏ) = Q · Xᵏ − Q(0) · Xᵐ`. `Torus.lam` is `ℤ`-valued and the index is
`ℕ`, so a bridging lemma is needed. `trigAxis .egf = shiftAxis TrigPoly` is
propositional and needs an `ext` lemma on `Causal.Axis`; a remark, not a
requirement.

## Circuit integration

The owner authorized the complete viscous arc as the third stage of the fluid
circuit work. In addition to the original mathematical outcomes, this task
builds a typed Mild circuit language, verified expression compilation, and a
feedback circuit with boundary data as its only external input. Heat, transport,
Duhamel and an interaction-degree shift are explicit primitives; no opaque
solution primitive is allowed. Prove its relation equivalent to the unique
Wild expansion. Later Forseti contracts state classical and quantitative
properties of that actual output.

## Plan

Implement and test the exponential-polynomial carrier first, including rational
resonance subtraction and both zero-resonance branches. Then the generic shift
axis, MildPoly operations and causal Wild expansion, typed circuit/compiler and
relation theorems, and computable tables. Preserve the original termwise PDE,
zero-viscosity agreement, invariants and measured kernel-computation outcomes.
Run full/optional builds and axiom audits, three-role panel review and CI before
merge. Independent construction overlaps the earlier CI queue; release merges
remain ordered after the repair and generalized Euler stages.

## Progress

- Exact `ExpPoly` algebra, rational resonance split (including negative rate
  difference and zero viscosity), derivative, zero initial value and the
  heat-kernel integral interpretation compile with standard axiom reports.
- Generic `shiftAxis`, Mild heat/transport/Duhamel operators, causal Wild
  recursion and uniqueness, termwise positive-degree equation, mean-zero,
  parity and support-size propagation compile.
- Typed `Mild.Circuit` and expression compiler compile. The feedback relation
  is proved equivalent to the unique Wild output for every boundary stream.
- The physical initial-term equation and initial-value theorem, evaluated
  zero-viscosity agreement, computable table mirror and kernel coefficients
  through degree two are implemented and pass their regression builds.
- Degree three is measured: the coefficient at (1,0), rate 1, degree 0 is
  -5247629/15375360; counts are 52 modes and 382 entries. Three kernel checks
  took 20.45 seconds and about 5.25 GiB peak RSS, so CI runs them separately.
- Circuit/adversarial proofs and documentation are implemented. All three
  panel judges pass: mathematics, circuit architecture and computation/integration.
  The full build (6,994 jobs), four optional executables (6,811 jobs), and separate
  degree-three regression pass without warnings. Standard axiom audits and
  whitespace checks pass. PR CI and ordered merge/release remain; this increment
  follows the preceding repair and generalized Euler releases.

## Conversation

### note · codex/fluid_contracts · 2026-10-06T03:47:54Z

Merged https://github.com/arnovich/asgard-lean/pull/33 at `efffaa5f3caa4941d22e92b5cb86b5095f9489d8`. Published v1.17.0 from the audited merged tree. Typed mild gates, causal uniqueness and exact exponential-polynomial computations through degree three pass the complete/optional builds, regression proofs, independent panel review and PR CI.
