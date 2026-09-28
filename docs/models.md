# Models and proof coverage

## Declare and compile

| Entry point | Purpose |
| --- | --- |
| [`Model.Declaration`](../Gimle/Asgard/Model/Declaration.lean) | Polynomial or continuous model, exact parameters, ordered observations |
| [`Model.Compiler`](../Gimle/Asgard/Model/Compiler.lean) | `compilePolynomial`: validate, schedule, specialize, compile |
| [`Model.Continuous`](../Gimle/Asgard/Model/Continuous.lean) | `compileContinuous`: compile the field and initialized feedback |
| [`Model.Linear`](../Gimle/Asgard/Model/Linear.lean) | Recognize homogeneous linear systems and prove forward existence/uniqueness |
| [`Model.Source`](../Gimle/Asgard/Model/Source.lean) | `compileSourcePolynomial` / `compileSourceContinuous`: applied lambdas, implicit first-order ODEs and higher-order ODEs over declared velocities, lowered to a `Body` |

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
with source terms (`term%`, `assignments%`, `differentials%`, `velocities%` from
`Gimle.Asgard.Model.SourceSyntax`). Lowering produces an ordinary `Body`, which the
compiler above then handles unchanged.

- `term%` adds `diff(e, t)`, `(λ w => body)(arg)` at its application site only, unary `+`,
  `/` by a positive numeral, and `^` by a positive numeral.
- A binder shadows a state of the same name, for derivatives too.

| Accepted | Lowered to |
| --- | --- |
| `z := (λ w => body)(arg)` in any derivative-free term | Beta-normalized `NamedExpr`; inner binders first, no capture |
| `dx : side = rhs` or `dx : rhs = side`, one side holding the only atom | `dx := (rhs - r) / q`, every residual term kept in source order |
| `velocities% { dx : diff(x, t) = v; }` | `dx := v`; declares the state `v` as the velocity of `x` |

```text
side := A | side + r | r + side | side - r | r - side | -side
A    := D | lit * A | A * lit | A / n | -A
D    := diff(x, t) | diff(D', t)      where D' is a chain of the same shape
lit  := numeral | rat(n, d) | -lit | lit * lit | lit / n
```

- `q` is the product of the literals and signs around the atom, and must be nonzero.
  A literal factor wraps only a residual-free `A`; a negation may wrap a whole side.
- `r` and `rhs` are derivative-free terms, lambdas allowed. A lambda that reduces to a
  literal is not a scale.
- A first-order atom is `diff(x, t)`: `x` is a declared state, `t` the evolution axis
  name, and `dx` the derivative port its `StateBinding` names; `dx` may not be
  referenced in its own equation.
- A chain of `k + 1` derivatives of `x`, all on `t`, needs declared velocities
  `x = x0, x1, ..., xk`, each `x(m+1)` declared as the velocity of `xm`. It is read as
  `diff(xk, t)`, so the equation defines `xk`'s derivative port. A second-order
  `dv : q * diff(diff(x,t),t) + r = rhs` with `dx : diff(x,t) = v` lowers to the
  first-order system `dx := v`, `dv := (rhs - r) / q`.
- A velocity declaration `dx : diff(x, t) = v` names the state `x` whose derivative port
  is `dx`, the evolution axis, and a velocity `v`. The first input named `v` must be a
  state; it has its own `StateBinding`, derivative port and initial value, all declared
  explicitly. Nothing is inferred from names or from the shape of other equations: the
  same equation written in `differentials%` declares no velocity.
- The interface (ports, bindings, axis) is validated before any term is read.
- Axis, start and initial values stay in the unchanged `Evolution`. There is no integral,
  so no inverse rewrite can drop a boundary term.

| Rejected form | Diagnostic |
| --- | --- |
| `0 * diff(x,t)` | `zeroScale` |
| Atoms on both sides | `competingDerivative` |
| Two atoms on one side, including `diff(x,t) - diff(x,t)` | `repeatedDerivative` |
| Non-literal factor: `x * diff(x,t)`, `a * diff(x,t)`, `(2 + 3) * diff(x,t)` | `nonlinearDerivative` |
| `diff(diff(x,t),t)` with no declared velocity of `x`, or a longer chain missing one | `higherOrderDerivative` |
| Another axis, or a mixed chain, declared velocities or not | `mixedDerivative` |
| A lower-order atom beside the top one, `diff(diff(x,t),t) + diff(x,t)` (write `v`) | `repeatedDerivative` |
| A velocity that is not a state port | `unsupportedRole` |
| Missing velocity initial value or `StateBinding` | `missingBinding` |
| `diff(x + y, t)`, a non-state, `2 * (diff(x,t) + x)`, a derivative in a lambda or an explicit assignment | `unsupportedDerivative` |
| Any differential equation or velocity in a polynomial declaration | `unsupportedDerivative` |
| `dx` named inside its own equation | `repeatedDerivative` |
| No atom, or the atom of a state whose derivative port is not `dx` | `missingDerivative` |
| A name outside its binder's scope, even in an unused argument | `unknownReference` |

A rejection names unsupported structure, not an unsatisfiable model.

The source relation `SourceBody.Solves` reads `diff(x, t)` as the value of `x`'s
derivative port, and requires that value to be the actual derivative on `t ≥ start`
(`Solves.derivative_denotes`). A chain of `k + 1` derivatives of `x` is read through the
declared velocities as the port of `xk`. Because every velocity declaration is itself a
source equation, in any solution the coordinate of `xm` is the `m`-th derivative of `x`
on `t ≥ start`, the chain denotes the `k + 1`-th derivative there, and the declared
initial value of `xm` is the `m`-th derivative at `start`. `Solves` never evaluates a
lowered term or a circuit.

| Theorem | Statement |
| --- | --- |
| `Term.beta_correct` | Beta normalization preserves meaning in every environment |
| `Isolated.correct` | The isolated assignment holds exactly when the source equation does |
| `Term.collapse_eval` | Reading a declared chain as `diff(xk, t)` preserves meaning in every environment |
| `Solves.lift_eqOn` | In a solution, the coordinate of `xm` equals `iteratedDerivWithin m x` on `t ≥ start` |
| `Solves.chain_denotes` | In a solution, a chain of `k + 1` derivatives denotes the derivative of `iteratedDerivWithin k x` |
| `Solves.initial_iterated` | The declared initial value of `xm` is the `m`-th derivative of `x` at `start` |
| `SourceContinuousModel.realizes_iterated` | The same three facts for every realization of the compiled model |
| `Lowered.solves_iff` | Source solutions are the lowered body's solutions, with the same `Evolution` |
| `SourceContinuousModel.solves_iff_realizes` | Source solutions are the compiled initialized feedback's realizations |
| `SourceContinuousModel.constrained_iff` | Corollary: any further predicate on the trajectory is preserved |
| `SourceContinuousModel.observations_correct` | Observed source solutions are observed realizations |
| `SourcePolynomialModel.correct` | Lambda-bearing polynomial sources against compiled outputs |

The pinned Python compiler turns `3 * diff(x,t) + x = y` into
`diff(x,t) = (0.3333333333333333 * (y - x))`; Lean yields `rat(1,3) * (y - x)`.
[DifferentialIsolation.lean](../Gimle/Asgard/Examples/DifferentialIsolation.lean)
also proves the unique solution `x = 2 + 3e^(-t/3)`. The
[regression file](../Gimle/Asgard/Tests/DifferentialIsolation.lean) restates the Python
accept/reject cases. The fragments deliberately differ in two ways:

- Lean `^ n` is repeated multiplication, so `(2 ^ 3) * diff(x,t)` and `diff(x,t) ^ 1`
  are accepted. Python rejects both. Both refuse `^ 0`.
- Scales are exact rationals, so Python's binary64 overflow rejections have no Lean
  counterpart.

For higher-order chains
([HigherOrderIsolation.lean](../Gimle/Asgard/Tests/HigherOrderIsolation.lean)):

- Python turns `diff(diff(f,t),t) = g` into Form-A `f = int(int(g,t),t) + f0`, with one
  initial wire; the velocity's initial value is silently zero. Lean requires the
  velocity declared, with its own initial value.
- Python rejects scaled or residual chains such as `2 * diff(diff(f,t),t) = f`; Lean
  accepts them over a declared velocity.

[HigherOrderIsolation.lean](../Gimle/Asgard/Examples/HigherOrderIsolation.lean) proves
the unique solution `x = cos(t/2)` of `4 * diff(diff(x,t),t) + x = 0`, `x(0) = 1`,
`x'(0) = 0`, and reads its second derivative back as `derivWithin` of `derivWithin`.

Not yet in the source grammar (open tasks):

- lower-order atoms beside the top one, such as `diff(diff(f,t),t) + diff(f,t) = g`
  (032);
- integrals and `diff(int(X,t),t)` (028);
- multi-axis equations such as heat (029);
- real atomics, division by expressions, literal products or negative numerals, and
  decimal literals (030);
- time-varying drivers, such as Python's `diff(a,t) = diff($z,t)` (031).

## Guarantees and limits

| Feature | Proved | Conditions / limits |
| --- | --- | --- |
| Polynomial compilation | Original equations ↔ compiled outputs | Exact rationals; guarantee starts at the Lean AST, not arbitrary text parsing |
| Continuous feedback | Original initialized ODE ↔ compiled solution relation | Autonomous polynomial models on `t ≥ start`; compilation alone gives no existence, uniqueness, or stability |
| Linear analysis | Existence and uniqueness on `t ≥ start` | Accepted autonomous homogeneous rational linear systems; no stability claim |
| [Normalization / isolation](../Gimle/Asgard/Examples/VariableIsolation.lean) | Scoped substitution and conditional equation isolation preserve values/constraints | Isolation needs affine recognition and a proved polynomial inverse witness; no general equation solver |
| [Differential isolation](../Gimle/Asgard/Examples/DifferentialIsolation.lean) | Original implicit first-order ODE ↔ compiled feedback, same initial data | One atom `q*D_t(x)`, exact nonzero literal `q`, derivative-free residuals; see [Source equations](#source-equations-lambdas-and-differential-isolation) |
| [Higher-order isolation](../Gimle/Asgard/Examples/HigherOrderIsolation.lean) | Original higher-order ODE ↔ compiled feedback of the augmented system; chains denote iterated derivatives, velocity initial values the initial derivatives | Every lower level has an explicitly declared velocity state with its own initial value; one top atom per equation |
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
