---
title: Declare integral states for nested and non-polynomial integrands
state: ongoing
claimed_by: claude-a036
claimed_at: 2026-09-28T14:43:41Z
branch: feat/integral_states_richer_integrands
priority: low
labels: [compiler, isolation, migration]
related: ["034", "035"]
---

## Context

Task 034 lets a source declare an integral state, `integrals% { dF : F =
int(X, t); }`, whose declared initial value must be `0`, and reads `int(X,t)` as
`F` at atom positions (`Boundary.integral`, `Term.cancelAtom` in
`Model.Integral`). The declaration is lowered to `dF := X`, and its correctness
along a trajectory needs `X.eval` at one time to agree with the reading of `X`
along the trajectory, so `X` is restricted to `Term.continuous`: a polynomial in
states and bound parameters. The match between a written integral and a
declaration is syntactic `Term` equality.

So these stay rejected with `unsupportedIntegral` although their meaning is
exact:

- Python's `diff(f,t) = int(int(f,t),t)` (accepted at gimle-asgard `fba931e`
  with two hidden zero-start states): the outer integrand `int(f,t)` holds an
  integral, and a declaration `dG : G = int(int(f,t),t)` is rejected at its
  integrand even when `dF : F = int(f,t)` is declared. Reading an integrand
  through earlier declarations would give `dG := F`.
- Python's `diff(f,t) = diff(int(int(f,t),t),t)`, accepted at `fba931e`: with
  `F` declared it is `F`, but the inverse pair's integrand `int(f,t)` is not
  tame, so it is rejected.
- An integrand with first-order state derivatives, `int(diff(g,t) + f, t)`,
  which `Term.tame` already admits for the inverse rewrites.
- An integrand with applied lambdas or auxiliaries (the same gap 035 names for
  inverse rewrites).
- A written integral that differs from the declared one only syntactically,
  such as `int(1 * f, t)` against a declared `int(f, t)`.

## Outcome

- `diff(f,t) = int(int(f,t),t)`, with both integrals declared as zero-start
  states, lowers to `df := G`, `dG := F`, `dF := f`, with a proof that each
  declared state equals the source's reading of its integral along every
  solution; the fixture in `Tests/IntegralStates.lean` moves from "differs"
  towards "same" (Lean still requires the declarations).
- Each other form above is either accepted with the same guarantees or kept
  rejected with a documented reason in `docs/models.md`.
- `Lowered.solves_iff`, `SourceContinuousModel.solves_iff_realizes`,
  `classical_iff_realizes` and `solves_iff_classical` keep their statements;
  full `lake build` is clean and axiom audits show only standard axioms.
