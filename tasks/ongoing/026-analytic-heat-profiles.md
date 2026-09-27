---
title: Heat streams for analytic initial profiles with certified coefficient majorants
state: ongoing
claimed_by: claude-026
claimed_at: 2026-09-27T00:00:00Z
branch: feat/analytic_heat_profiles
priority: medium
labels: [streams, heat, analysis, certificates]
depends_on: ["024", "025"]
related: ["gimle-forseti/135"]
---

## Context

`Streams.Heat` (024) constructs the heat reconstruction only for polynomial
profiles, so every output stream it produces is finite and its tail is zero.
`Streams.Tail` (025) certifies the truncation error of an infinite stream, but
only for a stream that is shown to satisfy an explicit coefficient majorant.
Nothing yet connects the two. So an analytic-tail claim about the heat
reconstruction, such as the initial profile `e^x`, has no Lean statement to
check. gimle-forseti's streams lane answers it `UNKNOWN` ("analytic tails need a
certified majorant", gimle-forseti 135).

For a profile given by its raw EGF coefficients `g_j` (so `p(x) = Σ g_j x^j/j!`),
the formal heat solution has raw EGF coefficients `u_(n,k) = g_(k+2n)`. A
geometric bound `|g_j| ≤ M·ρ^(−j)` therefore transfers to the decoded
(ordinary) coefficients: `|u_(n,k)|/(n!·k!) ≤ M·(ρ²)^(−n)·ρ^(−k)`. That is exactly
a `Majorizes` premise for `TailCertificate`.

## Outcome

- [ ] An analytic profile is an infinite formal stream on the spatial axis,
      given in either basis. Its heat stream is defined on axes `[t, x]`, and
      its coefficients are stated in both bases.
- [ ] The heat stream of an analytic profile satisfies the existing heat
      `circuit` relation with that profile as the full boundary input
      (`circuit_rel_iff`). For a polynomial profile it agrees with 024's
      `Heat.stream`.
- [ ] A certified profile bound `|g_j| ≤ M·ρ^(−j)` (exact `M ≥ 0`, `ρ > 0`)
      yields `Majorizes` for the heat output with majorant `(M, [ρ², ρ])`, and
      hence a `TailCertificate` on every box strictly inside those radii.
- [ ] Worked example: the profile `e^x` (`g_j = 1`, `M = ρ = 1`) has output
      `e^(x+t)`. It gets a certified truncation bound at a concrete window,
      computed exactly by `decide +kernel`, and the analytic field equals
      `exp (x + t)` on the box.
- [ ] Hostile tests: a profile violating its claimed bound gets no
      certificate, and a box on or beyond the radii is rejected. Every public
      theorem has a `#guard_msgs` axiom audit allowing only `propext`,
      `Classical.choice` and `Quot.sound`.
- [ ] `lake build` is clean and `docs/formal-streams.md` states the new
      theorems. There is no release tag: the release is batched with
      gimle-forseti 083 into v1.4.0.
