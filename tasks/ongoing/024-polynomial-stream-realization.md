---
title: Relate finite polynomial streams to analytic fields and heat evolution
state: ongoing
priority: high
labels: [streams, pde, semantics, analysis]
related: ["023", "025"]
claimed_by: claude-024
claimed_at: 2026-09-26T00:00:00Z
branch: feat/polynomial_stream_realization
---

# Relate finite polynomial streams to analytic fields and heat evolution

## Context

This builds on the existing formal stream implementation in `Gimle/Asgard/Streams/`.

The formal heat fixture is an exact coefficient theorem. It does not currently
connect that stream to an evaluated real field and its analytic derivatives.
The first bridge can be fully constructive for finite polynomials, without
assuming convergence of arbitrary power series or solving general PDEs.

This task connects the existing formal interpretation to real polynomial
functions, including an explicit finite-support witness for the *whole* decoded
stream. A finite sample or window is not such a witness. Property contracts over
these fields belong to downstream property systems.

## Outcome

- [ ] Represent finite polynomial streams using existing mathlib polynomial
      data and an exact embedding into `Streams.Stream d`; prove the embedding
      and real evaluation agree coefficient by coefficient. Preserve OGF/EGF
      factorial conversion on every named axis.
- [ ] Prove evaluation correspondence for routing, constants, axis variables,
      addition and product, and for selected-axis formal differentiation and
      integration with the full boundary profile at that axis's origin. Analytic
      derivatives/integrals refer to the evaluated field, not coefficient shifts.
      Reuse `Streams.Circuit.Rel` and its compilation theorems.
- [ ] Construct heat evolution for any finite rational polynomial boundary
      `p(x)` on axes `[t,x]` by the finite sum
      `u(t,x) = Σ_k t^k/k! · (D_x^(2k) p)(x)`, stopping when the derivatives
      vanish. Derive the degree cutoff from `p`, with constants and zero handled.
- [ ] Prove the constructed stream satisfies the original formal derivative/
      integration circuit and full initial profile, and its evaluated polynomial
      field satisfies `∂_t u = ∂_x² u` and `u(0,x)=p(x)` for every real `t,x`.
      Prove uniqueness within the finite bivariate polynomial solution class
      from coefficient recurrence. Do not claim uniqueness among all smooth fields.
- [ ] Worked regressions include `p=x²` giving `x²+2t`, `p=x⁴` giving
      `x⁴+12tx²+12t²`, and affine boundaries remaining fixed. Check both bases,
      axis transport and a changed boundary/coefficient that invalidates the
      original correspondence. No hand-supplied second model may replace the
      original stream circuit in the theorem.
- [ ] A same-prefix/different-tail example cannot use finite support or the
      finite-polynomial evaluation theorem without its full-stream hypothesis.
      State explicitly what is proved for a supplied candidate field and what
      is proved for the constructed polynomial solution family.
- [ ] `lake build` and an executable transitive standard-axiom audit pass;
      document the construction, interpretation bridge, solution class and
      examples in `docs/formal-streams.md`. No Python or downstream property-system
      core dependency.

## Plan

1. Prove the polynomial embedding and finite real evaluation laws, with OGF/EGF
   and boundary-slice tests before connecting circuit operations.
2. Construct the heat polynomial from a supplied boundary and prove recurrence,
   initial data and uniqueness in the stated finite-polynomial class.
3. Derive the analytic PDE theorem through the evaluation bridge, instantiate
   the fixtures, and review analytic/formal correspondence and scope.

## Scope

No general infinite-series summation, PDE maximum principle, spatial-domain
boundary-value solver, numerical integrator or error claim. Here the initial
profile is given on the whole spatial line; bounds on a compact strip are
properties of this explicit solution, not additional PDE boundary conditions.
Infinite analytic realization from a checked majorant belongs to task 025.
