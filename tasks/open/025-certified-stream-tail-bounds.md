---
title: Certify analytic stream truncation from explicit coefficient majorants
state: open
priority: medium
labels: [streams, approximation, analysis, certificates]
related: ["023", "024"]
---

# Certify analytic stream truncation from explicit coefficient majorants

## Context

This builds on the existing formal stream implementation in `Gimle/Asgard/Streams/`.

A simulator may keep finite coefficient grids, while exact formal streams are
infinite. Finite agreement and a simulator's estimated radius do not prove an
analytic approximation bound.

Deliver one exact theorem from an explicit *proved* coefficient majorant to
analytic convergence and rectangular truncation error. This is independent of
the first finite-polynomial baseline in 024 and does not block its use.

## Contract

Use decoded OGF coefficients `a_α`, including when the stored basis is EGF.
For a finite named axis set, supplied rational `M ≥ 0`, `R_i > 0` and
`0 ≤ r_i < R_i`, require a proof for every multi-index of

```text
|a_α| ≤ M · ∏_i R_i^(−α_i).
```

On the box `|z_i| ≤ r_i`, define the analytic field through the resulting
absolutely convergent sum. For positive rectangular window sizes `N_i`, prove
a uniform absolute tail bound. One acceptable conservative rational bound is

```text
q_i = r_i / R_i
ε = M · (Σ_i q_i^N_i) · ∏_i (1 − q_i)^(−1).
```

This union bound may overcount omitted coefficients; it must bound the entire
tail, not just the next coefficient. The quantity is uniform absolute error of
an evaluated scalar field on the declared box, not coefficientwise error or
statistical confidence. For multiple output ports, state how individual bounds
combine into the chosen output norm.

## Outcome

- [ ] Exact majorant data and explicit proof premises imply absolute convergence
      and equality with the specified analytic sum; no convergence claim follows
      from the formal stream type alone.
- [ ] A theorem bounds the difference between that sum and evaluation of its
      rectangular coefficient truncation uniformly on the stated box. Prove
      OGF/EGF invariance, zero-radius handling and the zero-axis case; reject
      boundary radii `r_i ≥ R_i` in this contract.
- [ ] The two-axis geometric stream `a_(m,n)=1` is a full worked example on
      `|t|,|x| ≤ 1/2`, with `M=R_t=R_x=1`. At window `(N,N)`, check the bound
      `8·2^(−N)` and its agreement with the exact geometric sum.
- [ ] Tests distinguish full-stream majorant evidence from matching finitely
      many coefficients. An arbitrarily large unobserved tail cannot be certified
      by a finite-prefix check or a numerical radius estimate.
- [ ] Name the original stream, basis, axes, domain, window, norm and majorant
      in the conclusion so downstream proofs can transport a field
      property through this bound. A missing majorant leaves an unproved premise.
- [ ] `lake build`, an executable standard-axiom audit and the regression suite
      pass. Document which hypotheses must be supplied and the exact error metric.

## Plan

1. Prove multivariate geometric summability and the finite-box remainder bound.
2. Transport the coefficient majorant to convergence/error for the existing
   decoded stream and prove representation invariance.
3. Instantiate the geometric example and hostile-prefix tests; review the
   summation interchange and uniformity arguments.

## Scope

No automatic majorant discovery, certified JAX/binary64 execution, roundoff
budget, time-window re-expansion, or claim that differentiation/substitution is
stable at the same bound. Each of those requires its own checked hypotheses.
This task certifies mathematical truncation only; numerical execution remains
evidence until an independent execution-error theorem is supplied.
