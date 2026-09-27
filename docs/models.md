# Models and proof coverage

## Declare and compile

| Entry point | Purpose |
| --- | --- |
| [`Model.Declaration`](../Gimle/Asgard/Model/Declaration.lean) | Polynomial or continuous model, exact parameters, ordered observations |
| [`Model.Compiler`](../Gimle/Asgard/Model/Compiler.lean) | `compilePolynomial`: validate, schedule, specialize, compile |
| [`Model.Continuous`](../Gimle/Asgard/Model/Continuous.lean) | `compileContinuous`: compile the field and initialized feedback |
| [`Model.Linear`](../Gimle/Asgard/Model/Linear.lean) | Recognize homogeneous linear systems and prove forward existence/uniqueness |
| [`Model.Source`](../Gimle/Asgard/Model/Source.lean) | `compileSourcePolynomial` / `compileSourceContinuous`: applied lambdas and implicit first-order ODEs, lowered to a `Body` |

- Use `equations%` from `Gimle.Asgard.Compile.Syntax` for named polynomial assignments.
- Syntax: variables, naturals, `rat(n,d)` with positive denominator, `+`, `-`, `*`, natural powers.
- Bind parameters, states, derivatives, and initial values by explicit stable IDs.
- Declare observation order and continuous axis/start explicitly; names infer nothing.
- Model compilation accepts forward references and shared auxiliaries; auxiliary cycles fail.
- Lower-level `Program.compile` requires assignments already in dependency order.
- Declaration validation alone does not compile equations or reject auxiliary cycles.

Start with [ThreeState.lean](../Gimle/Asgard/Examples/ThreeState.lean) for a complete
model; [ModelCompiler.lean](../Gimle/Asgard/Tests/ModelCompiler.lean) covers rejected inputs.

## Source equations: lambdas and differential isolation

A `SourceBody` holds the same ports, parameters and observations as a `Body`,
with source terms (`term%`, `assignments%`, `differentials%` from
`Gimle.Asgard.Model.SourceSyntax`). Lowering produces an ordinary `Body`, which the
compiler above then handles unchanged.

| Accepted | Lowered to |
| --- | --- |
| `z := (λ w => body)(arg)` in any derivative-free term | Beta-normalized `NamedExpr`; inner binders first, no capture |
| `dx : q * diff(x, t) + r = rhs` or `rhs = q * diff(x, t) + r` | `dx := (rhs - r) / q`, every residual term kept in source order |

- `q` is an exact nonzero signed literal product: `3`, `-2 * rat(1,4)`, `diff(x,t) / 2`.
- `r` and `rhs` are derivative-free terms; lambdas are allowed there.
- `x` is a declared state, `t` the evolution axis name, and `dx` the derivative port
  its `StateBinding` names.
- Axis, start and initial values stay in the unchanged `Evolution`. There is no integral,
  so no inverse rewrite can drop a boundary term.

| Rejected form | Diagnostic |
| --- | --- |
| `0 * diff(x,t)` | `zeroScale` |
| Atoms on both sides | `competingDerivative` |
| Two atoms on one side, including `diff(x,t) - diff(x,t)` | `repeatedDerivative` |
| Non-literal factor: `x * diff(x,t)`, `a * diff(x,t)`, `(2 + 3) * diff(x,t)` | `nonlinearDerivative` |
| `diff(diff(x,t),t)` | `higherOrderDerivative` |
| Another axis, or a mixed chain | `mixedDerivative` |
| `diff(x + y, t)`, a non-state, `2 * (diff(x,t) + x)`, a derivative in a lambda or an explicit assignment | `unsupportedDerivative` |
| No atom, or the atom of another state | `missingDerivative` |

A rejection names unsupported structure, not an unsatisfiable model.

The source relation `SourceBody.Solves` reads `diff(x, t)` as the value of `x`'s
derivative port, and requires that value to be the actual derivative on `t ≥ start`
(`Solves.derivative_denotes`). It never evaluates a lowered term or a circuit.

| Theorem | Statement |
| --- | --- |
| `Term.beta_correct` | Beta normalization preserves meaning in every environment |
| `Isolated.correct` | The isolated assignment holds exactly when the source equation does |
| `Lowered.solves_iff` | Source solutions are the lowered body's solutions, with the same `Evolution` |
| `SourceContinuousModel.solves_iff_realizes` | Source solutions are the compiled initialized feedback's realizations |
| `SourceContinuousModel.constrained_iff` | Any further trajectory obligation is carried unchanged |
| `SourceContinuousModel.observations_correct` | Observed source solutions are observed realizations |
| `SourcePolynomialModel.correct` | Lambda-bearing polynomial sources against compiled outputs |

The pinned Python compiler turns `3 * diff(x,t) + x = y` into
`diff(x,t) = (0.3333333333333333 * (y - x))`; Lean yields `rat(1,3) * (y - x)`.
[DifferentialIsolation.lean](../Gimle/Asgard/Examples/DifferentialIsolation.lean)
also proves the unique solution `x = 2 + 3e^(-t/3)`. The
[regression file](../Gimle/Asgard/Tests/DifferentialIsolation.lean) restates the Python
accept/reject cases. The fragments deliberately differ in two ways:

- Lean `^ n` is repeated multiplication, so `(2 ^ 3) * diff(x,t)` and `diff(x,t) ^ 1`
  are accepted. Python rejects both.
- Scales are exact rationals, so Python's binary64 overflow rejections have no Lean
  counterpart.

Not yet in the source grammar (open tasks):

- higher-order chains such as `diff(diff(f,t),t) = g` (027);
- integrals and `diff(int(X,t),t)` (028);
- multi-axis equations such as heat (029);
- real atomics, division by expressions and decimal literals (030).

Time-varying drivers remain outside the autonomous continuous adapter.

## Guarantees and limits

| Feature | Proved | Conditions / limits |
| --- | --- | --- |
| Polynomial compilation | Original equations ↔ compiled outputs | Exact rationals; guarantee starts at the Lean AST, not arbitrary text parsing |
| Continuous feedback | Original initialized ODE ↔ compiled solution relation | Autonomous polynomial models on `t ≥ start`; compilation alone gives no existence, uniqueness, or stability |
| Linear analysis | Existence and uniqueness on `t ≥ start` | Accepted autonomous homogeneous rational linear systems; no stability claim |
| [Normalization / isolation](../Gimle/Asgard/Examples/VariableIsolation.lean) | Scoped substitution and conditional equation isolation preserve values/constraints | Isolation needs affine recognition and a proved polynomial inverse witness; no general equation solver |
| [Differential isolation](../Gimle/Asgard/Examples/DifferentialIsolation.lean) | Original implicit first-order ODE ↔ compiled feedback, same initial data | One atom `q*D_t(x)`, exact nonzero literal `q`, derivative-free residuals; see [Source equations](#source-equations-lambdas-and-differential-isolation) |
| [Real atomics](../Gimle/Asgard/Examples/RealAtomics.lean) | Compilation and rewrites preserve values **and domains** | `sqrt`: nonnegative; `log` and rational/real powers: positive base; division: nonzero denominator |
| [External components](../Gimle/Asgard/Examples/ExternalBlend.lean) | Pointwise contracts and finite weighted partitions | Fixed explicit environment; all branches defined, weights nonnegative and sum to one; no certification of external code |
| [Stochastic translation](../Gimle/Asgard/Examples/StochasticJump.lean) | Source/process-circuit correspondence | Same supplied integral interpretation; no general SDE existence, Itô formula, or probability bounds |
| [Approximation](../Gimle/Asgard/Examples/Approximation.lean) | Uniform coordinate error bounds on a stated region | Feedforward real circuits; nonnegative budgets, coverage, and Lipschitz premises for composition |

Partial operations stay undefined even when their result is discarded or
multiplied by zero. Trace hides internal signals; it does not guarantee a solution.
Formal streams use a [separate coefficient interpretation](formal-streams.md).

## Three-state example

```text
x' = -x/3 + y - z
y' = -x - y/2 + z
z' =  x - y - 2z
V  = x² + y² + z²
```

At `t=2`, state `(1,2,-1)` has field `(8/3,-3,1)` and energy `6`.
The exact Euler step of size `1/8` is `(4/3,13/8,-7/8)`.
The example proves compiled-field and observation identities and linear
existence/uniqueness. A whole-trajectory energy bound needs a separate proof.

## Check proofs

`lake build` checks all examples and regressions in
[`Gimle/Asgard/Tests/`](../Gimle/Asgard/Tests/). Axiom reports should contain only
`propext`, `Classical.choice`, and `Quot.sound`. Python execution, floating-point
accuracy, and numerical integration error are not certified by these proofs.
