# Models and proof coverage

## Declare and compile

| Entry point | Purpose |
| --- | --- |
| [`Model.Declaration`](../Gimle/Asgard/Model/Declaration.lean) | Polynomial or continuous model, exact parameters, ordered observations |
| [`Model.Compiler`](../Gimle/Asgard/Model/Compiler.lean) | `compilePolynomial`: validate, schedule, specialize, compile |
| [`Model.Continuous`](../Gimle/Asgard/Model/Continuous.lean) | `compileContinuous`: compile the field and initialized feedback |
| [`Model.Linear`](../Gimle/Asgard/Model/Linear.lean) | Recognize homogeneous linear systems and prove forward existence/uniqueness |

- Use `equations%` from `Gimle.Asgard.Compile.Syntax` for named polynomial assignments.
- Syntax: variables, naturals, `rat(n,d)` with positive denominator, `+`, `-`, `*`, natural powers.
- Bind parameters, states, derivatives, and initial values by explicit stable IDs.
- Declare observation order and continuous axis/start explicitly; names infer nothing.
- Model compilation accepts forward references and shared auxiliaries; auxiliary cycles fail.
- Lower-level `Program.compile` requires assignments already in dependency order.
- Declaration validation alone does not compile equations or reject auxiliary cycles.

Start with [ThreeState.lean](../Gimle/Asgard/Examples/ThreeState.lean) for a complete
model; [ModelCompiler.lean](../Gimle/Asgard/Tests/ModelCompiler.lean) covers rejected inputs.

## Guarantees and limits

| Feature | Proved | Conditions / limits |
| --- | --- | --- |
| Polynomial compilation | Original equations ↔ compiled outputs | Exact rationals; guarantee starts at the Lean AST, not arbitrary text parsing |
| Continuous feedback | Original initialized ODE ↔ compiled solution relation | Autonomous polynomial models on `t ≥ start`; compilation alone gives no existence, uniqueness, or stability |
| Linear analysis | Existence and uniqueness on `t ≥ start` | Accepted autonomous homogeneous rational linear systems; no stability claim |
| [Normalization / isolation](../Gimle/Asgard/Examples/VariableIsolation.lean) | Scoped substitution and conditional equation isolation preserve values/constraints | Isolation needs affine recognition and a proved polynomial inverse witness; no general equation solver |
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
