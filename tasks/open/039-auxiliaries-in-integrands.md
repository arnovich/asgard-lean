---
title: Read auxiliaries in integrands along the trajectory
state: open
priority: low
labels: [compiler, isolation]
related: ["035", "036"]
---

## Context

`SourceBody.Solves` reads integrals, and derivatives of non-chains, along the whole
trajectory (`SourceBody.trajectory`, `Term.along`). That reading names only states
and bound parameters: an auxiliary `z := f` has no trajectory reading, so
`int(z, t)` has no value in `Solves`. Lowering therefore rejects every integrand
naming an auxiliary, both in an inverse pair (`diff(f,t) = diff(int(z,t),t)`,
`unsupportedIntegral` with reason `integrand`, task 035) and in a declared integral
state (`dF : F = int(z, t)`, task 036). The pinned Python compiler (gimle-asgard
`fba931e`) substitutes the auxiliary and accepts both.

An auxiliary's trajectory reading would be its assignment's reading along the
trajectory. That is well defined for an acyclic auxiliary whose right-hand side is
itself read along the trajectory, and continuous whenever the right-hand side is
tame. Adding it changes what `Solves` means for integrands with auxiliaries, which
today have no value, so it has to be stated and proved against the end-to-end
theorems.

## Outcome

- The trajectory reading gives an acyclic auxiliary the reading of its assignment,
  and `Lowered.solves_iff`, `SourceContinuousModel.solves_iff_realizes`,
  `classical_iff_realizes` and `solves_iff_classical` keep their statements.
- `diff(f,t) = diff(int(z,t),t)` with `z := f` lowers to `df := f` (or `df := z`),
  and `dF : F = int(z, t)` to `dF := z`, each with a proof of preservation.
- Auxiliary cycles and auxiliaries whose right-hand side has no trajectory reading
  stay rejected with a named reason, and the Python parity fixtures move from
  "differs" to "same" where Lean now agrees.
