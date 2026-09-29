# Models and proof coverage

## Declare and compile

| Entry point | Purpose |
| --- | --- |
| [`Model.Declaration`](../Gimle/Asgard/Model/Declaration.lean) | Polynomial, continuous or driven model, exact parameters, declared drivers, ordered observations |
| [`Model.Compiler`](../Gimle/Asgard/Model/Compiler.lean) | `compilePolynomial`: validate, schedule, specialize, compile |
| [`Model.Continuous`](../Gimle/Asgard/Model/Continuous.lean) | `compileContinuous`: compile the field and initialized feedback |
| [`Model.Driven`](../Gimle/Asgard/Model/Driven.lean) | `compileDriven`: a continuous model whose field also reads declared drivers, closed with those drivers as external input |
| [`Model.Linear`](../Gimle/Asgard/Model/Linear.lean) | Recognize homogeneous linear systems and prove forward existence/uniqueness |
| [`Model.Source`](../Gimle/Asgard/Model/Source.lean) | `compileSourcePolynomial` / `compileSourceContinuous`: applied lambdas, implicit first-order ODEs, higher-order ODEs over declared velocities, source integrals and declared integral states, lowered to a `Body` |
| [`Model.DrivenSource`](../Gimle/Asgard/Model/DrivenSource.lean) | `compileSourceDriven`: source equations with declared drivers and driver derivatives, lowered by `Model.Source` |
| [`Model.Integral`](../Gimle/Asgard/Model/Integral.lean) | The trajectory reading of integrals from the declared start, the inverse rewrites that keep boundary terms, and the reading of declared integral states |
| [`Algebraic.Declaration`](../Gimle/Asgard/AlgebraicDeclaration.lean) | `compile`: simultaneous affine algebraic loops with a checked supplied inverse, eliminated to a feedforward circuit on admitted inputs; see [Algebraic loops](#algebraic-loops) |

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
with source terms (`term%`, `assignments%`, `differentials%`, `velocities%`,
`integrals%` from `Gimle.Asgard.Model.SourceSyntax`). Lowering produces an ordinary
`Body`, which the compiler above then handles unchanged.

- `term%` adds `diff(e, t)`, `int(e, t)`, `(λ w => body)(arg)` at its application site only,
  unary `+`, `/` by a positive numeral, and `^` by a positive numeral.
- A binder shadows a state of the same name, for derivatives too.

| Accepted | Lowered to |
| --- | --- |
| `z := (λ w => body)(arg)` in any term that is derivative-free once atoms are read as velocities (below) | Beta-normalized `NamedExpr`; inner binders first, no capture |
| `dx : side = rhs` or `dx : rhs = side`, one side holding the only atom | `dx := (rhs - r) / q`, every residual term kept in source order |
| `velocities% { dx : diff(x, t) = v; }` | `dx := v`; declares the state `v` as the velocity of `x` |
| `dv : diff(diff(x,t),t) + c * diff(x,t) + k * x = rhs`, with `v` declared as above | `dv := rhs - (c*v + k*x)`: the lower-order atom is read as `v` |
| `dy : diff(y,t) + c * diff(x,t) = rhs`, with `v` declared as above | `dy := rhs - c*v`: another state's atom is read the same way |
| `w := c * diff(x,t) + x`, with `v` declared as above | `w := c*v + x`: an explicit assignment reads its atoms the same way |
| `integrals% { dF : F = int(X, t); }`, with `F(start) = 0` declared | `dF := X`; `int(X, t)` is read as the state `F` wherever it occurs (below) |

```text
side := A | side + r | r + side | side - r | r - side | -side
A    := D | lit * A | A * lit | A / n | -A
D    := diff(x, t) | diff(D, t)
lit  := numeral | rat(n, d) | -lit | lit * lit | lit / n
```

- `q` is the product of the literals and signs around the atom, and must be nonzero.
  A literal factor wraps only a residual-free `A`; a negation may wrap a whole side.
- `r` and `rhs` are derivative-free terms, lambdas allowed, once lower-order atoms are
  read as velocities (below). A lambda that reduces to a literal is not a scale.
- A first-order atom is `diff(x, t)`: `x` is a declared state, `t` the evolution axis
  name, and `dx` the derivative port its `StateBinding` names; `dx` may not be
  referenced in its own equation.
- A chain of `k + 1` derivatives of `x`, all on `t`, needs declared velocities
  `x = x0, x1, ..., xk`: `x1` declared as the velocity of `x0`, `x2` of `x1`, and so on. It is read as
  `diff(xk, t)`, so the equation defines `xk`'s derivative port. A second-order
  `dv : q * diff(diff(x,t),t) + r = rhs` with `dx : diff(x,t) = v` lowers to the
  first-order system `dx := v`, `dv := (rhs - r) / q`.
- Every other atom, meaning any evolution-axis atom except the one being isolated
  (lower-order atoms of the same state included), is read as the declared velocity of
  its state: `diff(x, t)` as `v` when `v` is declared as the
  velocity of `x`, and a lower chain as the velocity one level above its collapsed state.
  Either side may hold it, under any factor, so `c * diff(x,t)` with a parameter `c` is
  the polynomial term `c * v`; scale, linearity and zero-scale rules apply only to the
  isolated atom. The atom of a state with no declared velocity on `t` stays a second
  atom. Velocity declarations themselves are never read this way.
- Explicit assignments read atoms the same way, after the same chain collapse:
  `w := diff(x,t)` is `w := v`, and `w := diff(diff(x,t),t)` over declared `x' = v`,
  `v' = a` is `w := a`. The reading has the same premise as in a differential, the
  velocity equations, which the declarations discharge for the whole system, so
  `Lowered.equations` holds in every environment. An atom the reading leaves, such as
  one whose state has no declared velocity or one on another axis, is rejected
  (`unsupportedDerivative`), whatever its shape.
- An atom inside a lambda application, body or argument, is never read, in any
  equation: a binder named like the velocity would capture the name substituted for
  the atom, and no capture-safe reading is proved.
- A velocity declaration `dx : diff(x, t) = v` names the state `x` whose derivative port
  is `dx`, the evolution axis, and a velocity `v`. The first input named `v` must be a
  state; it has its own `StateBinding`, derivative port and initial value, all declared
  explicitly. Nothing is inferred from names or from the shape of other equations: the
  same equation written in `differentials%` declares no velocity.
- Each velocity declaration is its own source equation, so sharing one velocity between
  states, cycles such as `f' = v, v' = f`, and `f' = f` mean exactly what they state.
- Checks run in order: interface, scopes, velocity roles, integral declarations, then
  explicit assignments and equations in declaration order (differentials before velocity
  declarations), then that no two integral declarations name the same integral.
- The interface (ports, bindings, axis) is validated before any term is read.
- Axis, start and initial values stay in the unchanged `Evolution`. Integrals are removed
  before isolation by inverse rewrites that keep every boundary term (below).

| Rejected form | Diagnostic |
| --- | --- |
| `0 * diff(x,t)` on the isolated atom | `zeroScale` |
| Atoms on both sides, neither read as a declared velocity | `competingDerivative` |
| Two atoms on one side, not read as declared velocities, including `diff(x,t) - diff(x,t)` | `repeatedDerivative` |
| Non-literal factor on the isolated atom: `x * diff(x,t)`, `a * diff(x,t)`, `(2 + 3) * diff(x,t)` | `nonlinearDerivative` |
| `diff(diff(x,t),t)` of a state with no declared velocity, or a longer chain missing one | `higherOrderDerivative` |
| A chain over a non-state, such as `diff(diff(p,t),t)` or `diff(diff(x + y,t),t)` | `unsupportedDerivative` |
| Another axis, or a mixed chain, declared velocities or not | `mixedDerivative` |
| A lower-order atom whose state has no declared velocity, `diff(diff(x,t),t) + diff(y,t)` | `repeatedDerivative` |
| A velocity that is a declared non-state port (parameter or output) | `unsupportedRole` |
| A velocity that is not a source name, such as an initial port | `unknownReference` |
| Missing velocity initial value or `StateBinding` | `missingBinding` |
| A velocity declared twice for one state | `duplicateId` |
| A declared velocity whose own derivative port no equation defines | `unknownReference` |
| `diff(x + y, t)`, a non-state, `2 * (diff(x,t) + x)`, a derivative in a lambda | `unsupportedDerivative` |
| A derivative in an explicit assignment, whatever its shape, that is not read as a declared velocity | `unsupportedDerivative` |
| Any differential equation or velocity in a polynomial declaration | `unsupportedDerivative` |
| `dx` named inside its own equation | `repeatedDerivative` |
| No atom, or the atom of a state whose derivative port is not `dx` | `missingDerivative` |
| A name outside its binder's scope, even in an unused argument | `unknownReference` |
| An integral no inverse rewrite removes and no declaration reads: `int(f,t)` undeclared, `int(int(diff(f,t),t),t)`, a chain with an undeclared level such as `int(diff(diff(g,t),t),t)`, `int(diff(p,t),t)` of a non-state, an integral under a lambda, a pair under a further derivative such as `diff(diff(int(int(f,t),t),t),t)` | `unsupportedIntegral`, `no inverse rewrite` |
| An integral, or an inverse pair, on another axis | `unsupportedIntegral`, `axis` |
| An integral declaration with a declared initial value other than `0` | `nonzeroInitial` |
| An integral declaration on another axis, or whose integrand is not pointwise (an auxiliary, a higher-order chain, a chain over a non-state such as `int(diff(p,t),t)`, a lambda holding an atom) or keeps an integral no declaration reads | `unsupportedIntegral` |
| An integral declaration whose integrand keeps a derivative of a non-chain, such as `int(diff(f + g,t),t)` | `unsupportedDerivative` |
| An integral state that is a parameter or an auxiliary, or not a source name | `unsupportedRole`, `unknownReference` |
| An integral state with no `StateBinding` or no initial value | `missingBinding` |
| A second declaration of the same integral | `duplicateId` |
| `diff(int(X,t),t)` with `X` not tame, once rewritten: `f * diff(f,t)`, an auxiliary, a lambda holding an atom | `unsupportedIntegral`, `integrand` |
| Any integral or integral declaration in a polynomial declaration (`integral without an evolution axis`) | `unsupportedIntegral` |

A rejection names unsupported structure, not an unsatisfiable model. An
`unsupportedIntegral` diagnostic names its reason as its reference: `axis`,
`integrand` or `no inverse rewrite` (`Term.integralReason`) for an equation or explicit
assignment, and `axis` or `integrand` for an integral declaration.

### Integrals

`int(X, t)` is the integral over the evolution axis from the declared start. Inverse
rewrites remove integrals before collapse and isolation, at the atom positions of sums,
products and negations, in differential equations and explicit assignments alike, and
inside the integrand of an inverse pair `diff(int(X,t),t)` before the pair itself; any
integral that remains is rejected unless a declared integral state reads it (below).

| Written | Rewritten to | Condition |
| --- | --- | --- |
| `diff(int(X, t), t)` | `X'`, the integrand after rewriting | `X'` tame: a polynomial in states and bound parameters, first-order `diff(x, t)` of states, their sums and negations, multiples by a polynomial in literals and bound parameters, and applied lambdas that beta-normalize to a polynomial in states and bound parameters |
| `diff(…diff(int(x, t), t)…, t)`, `m ≥ 2` derivatives | the chain of `m - 1` derivatives of `x` | `x` and its declared velocities up to the level `m - 2` are states with declared initial values |
| `int(diff(x, t), t)` | `x - x0` | `x` a state with the declared initial value `x0` |
| `int(diff(…diff(x, t)…, t), t)`, `k + 1` derivatives | `y - y0` | `y` the state `k` declared velocities above `x`, with the declared initial value `y0`; every level between has one too |

The boundary term is never dropped: `int(diff(x,t),t)` is `x - x(start)`, and
`x(start)` is the declared initial value, which `Solves` pins. With `x0 = 2`,
`2 * diff(f,t) = int(diff(f,t),t)` lowers to `df := rat(1,2) * (f - 2)`. Through a chain
it is the velocity's: with `v` declared as the velocity of `f` and `v(0) = 5`,
`int(diff(diff(f,t),t),t)` lowers to `v - 5` (`Solves.integral_chain`). A chain written
as `diff(diff(diff(int(f,t),t),t),t)` becomes `diff(diff(f,t),t)`, which isolation then
reads through the declared velocities. A bound parameter factor is tame because it is
constant along the trajectory; a state factor is not, since `f * diff(g,t)` need not
have an antiderivative. An integrand naming an auxiliary has no trajectory reading
(below), so it stays rejected.

**Declared integral states.** An integral no inverse rewrite removes is kept only
through an explicit declaration, never a hidden state:

```lean
differentials := differentials% { df : diff(f, t) = int(f, t); }
integrals := integrals% { dF : F = int(f, t); }
```

The declaration names a state `F`, whose `StateBinding` gives it the derivative port
`dF`, and the integrand `X` over the evolution axis. `F` has its own initial port and
value, declared explicitly, and that value must be `0`: with `F(start) = q`, `F` is
`q + int(X,t)`, not `int(X,t)`, so a nonzero value is rejected (`nonzeroInitial`) rather
than silently dropped.

The source reads the declaration as its own equation `D_t(F) = X`, and lowering reads
every `int(X, t)` at an atom position, in differential equations and explicit
assignments, as `F`. The match is syntactic: `int(1 * f, t)` is not the declared
`int(f, t)`, and stays rejected, because a semantic match needs a proof that the two
integrands read the same at every time. The inverse rewrites apply first, so
`diff(int(f,t),t)` is still `f`.

`X` must be pointwise (`Term.pointwise`): its reading at one time, with atoms read along
the trajectory, is its trajectory reading (`Term.pointwise_agrees`). That is what makes
the declaration's one-time equation `D_t(F) = X` say that `F` is an antiderivative of
the trajectory reading of `X`. Pointwise terms are polynomials in states and bound
parameters, first-order `diff(g,t)` of states, integrals, derivatives of non-chains,
and applied lambdas that beta-normalize to a polynomial in states and bound parameters.
The declaration is lowered to `dF := X'`, where `X'` is `X` after the inverse rewrites and
the reading of declared integral states, with each first-order `diff(g,t)` read as the
name of `g`'s derivative port (`Term.readPorts`, exact in every environment):

| Declared | Lowered to |
| --- | --- |
| `dG : G = int(int(f,t),t)` beside `dF : F = int(f,t)` | `dG := F`, in either declaration order |
| `dF : F = int(diff(g,t) + f, t)` | `dF := dg + f` |
| `dF : F = int((λ w => w * w)(f), t)` | `dF := f * f` |
| `dF : F = int(diff(int(f,t),t) + p, t)` | `dF := f + p` |
| `df : diff(f,t) = diff(int(int(f,t),t),t)` beside `dF : F = int(f,t)` | `df := F`: the pair's integrand is read as `F` first |

So `diff(f,t) = int(int(f,t),t)`, with both integrals declared, lowers to `df := G`,
`dG := F`, `dF := f`. Pointwise is necessary, not sufficient: after lowering, an
integral left in the integrand must be declared and a derivative left in it must have
been rewritten away. Still rejected, each for a stated reason:

- an integrand naming an auxiliary: the trajectory reading names only states and bound
  parameters, so the integral would have no value in `Solves` while the lowered state
  would;
- a higher-order chain in an integrand, such as `int(diff(diff(f,t),t),t)`: it is read
  through velocities that only a solution ties to the iterated derivative, so it is not
  pointwise;
- a lambda holding an atom, or a nested integral that no declaration reads;
- a derivative of a non-chain that no rewrite removes, such as `int(diff(f + g,t),t)`
  (`unsupportedDerivative`);
- an integrand whose ports name the declaration's own port, such as
  `int(diff(F,t) + f, t)` for `F` (`repeatedDerivative`).

`SourceBody.Solves` never reads `F` for the integral: `int(X,t)` keeps its trajectory
reading, the antiderivative from the start. The two agree in every solution
(`Solves.integral_state`): the declaration makes `F` an antiderivative of `X`, its
initial value `0` makes it the one that vanishes at the start, and that one is unique
(`primitiveFrom_iff`). The lowered body has the same solutions (`Lowered.solves_iff`),
so in every realization of the compiled model each declared state is its integral
(`SourceContinuousModel.integral_states`).

`SourceBody.Solves` reads integrals, and derivatives of anything but a chain, along the
whole trajectory (`SourceBody.atoms`, `Term.along`): names from the inputs, chains as
iterated derivatives, `int(X,t)` at `t` as `F(t)` for the antiderivative `F` of the
reading of `X` on `t ≥ start` with `F(start) = 0`, and `diff(Y,t)` of a non-chain as the
derivative within `t ≥ start` of the reading of `Y`. No integral is totalized: an
integrand that is undefined somewhere on the half-line, or is not a derivative there,
has no integral, so an equation using it has no solution. For a continuous integrand
the antiderivative is the interval integral (`primitiveFrom_eq_integral`); an integrand
without an antiderivative has none even if Lebesgue-integrable, and no tame integrand is
such. Under a lambda binder, an integral mentioning the binder has no value. The reading
names only states and bound parameters, so an integrand naming an auxiliary or a
derivative port has no value; lowering rejects such integrands. (A lowered declaration
may name a port, `dF := dg + f`, but only where the source wrote `diff(g,t)`.)

`Lowered.equations`, `Lowered.source` and `Lowered.observes` hold wherever the atoms
read each rewritten shape as its rewrite does (`Context.Cancels`). `SourceBody.cancels_at`
discharges that at every time of a signal with differentiable states, its declared
initial values, its integral and velocity declarations at every time
(`SourceBody.IntegralsAlong`, `SourceBody.VelocitiesAlong`) and ports carrying the actual
derivatives; every solution of the source or of the lowered body is one. Each rewrite
preserves the trajectory reading at every time (`Term.cancelAtom_along`), so rewriting
inside an integrand does too (`Term.cancel_along`), and the rewritten term reads the
same at one time as along the trajectory (`Term.cancelAtom_agrees`). The velocity
declarations make each state climbed through a chain the iterated derivative of its
base (`Trajectory.Regular.iterated`), which is what the chain rewrites need; they are
lowered with no premise, so both sides supply them (`Solves.velocitiesAlong`,
`Lowered.velocitiesAlong`). A declared integral needs the whole signal, not one time.
A declaration's own correspondence (`Lowered.integrals`) therefore needs only the
rewrites of shapes no larger than its integrand (`Context.CancelsUpTo`), and those
need only the declarations of smaller integrands along the signal
(`SourceBody.regular_below`, `Context.cancelsUpTo`). So the declarations are
discharged from a lowered solution by induction on the size of the integrand, and
both sides of `Lowered.solves_iff` supply
them (`Solves.integralsAlong`, `Lowered.integralsAlong`).
`SourceBody.ObservedSolution` reads the atoms along the signal, with ports carrying the
actual derivatives, as `Solves` does. `SourceBody.Observes`
has no signal, so it reads no integral; `Context.cancels_none` discharges the premise in
polynomial declarations, which rewrite nothing.

The source relation `SourceBody.Solves` reads `diff(x, t)` as the value of `x`'s
derivative port, and requires that value to be the actual derivative on `t ≥ start`
(`Solves.derivative_denotes`). A chain of `k + 1` derivatives of `x` is read through the
declared velocities as the port of `xk`. Because every velocity declaration is itself a
source equation, in any solution the coordinate of `xm` is the `m`-th derivative of `x`
on `t ≥ start`, the chain denotes the `k + 1`-th derivative there, and the declared
initial value of `xm` is the `m`-th derivative at `start`. `Solves` never evaluates a
lowered term or a circuit.

`SourceBody.SolvesClassical` drops the port reading: every chain of `k` derivatives of
`x` is `iteratedDerivWithin k x` on `t ≥ start`, and every derivative port carries the
actual derivative. The declared velocities only decide which chains are admitted. Both
relations have the same solutions (`solves_iff_classical`), so a higher-order source
read with actual derivatives has exactly the realizations of the lowered first-order
system (`classical_iff_realizes`). Derivatives are taken within `t ≥ start`, so at
`start` they are right derivatives.

| Theorem | Statement |
| --- | --- |
| `Term.beta_correct` | Beta normalization preserves meaning in every environment |
| `Isolated.correct` | The isolated assignment holds exactly when the source equation does |
| `Term.collapse_eval` | Reading a declared chain as `diff(xk, t)` preserves meaning in every environment |
| `Term.readVelocities_eval` | Reading other atoms, in differentials and explicit assignments, as declared velocities preserves meaning wherever the velocity equations hold (`Context.VelocitiesHold`) |
| `SourceBody.velocitiesHold` | The source's velocity declarations discharge that premise, so `Lowered.equations` holds wherever the atoms read the integral rewrites (`Context.Cancels`) |
| `Solves.lift_eqOn` | In a solution, the coordinate of `xm` equals `iteratedDerivWithin m x` on `t ≥ start` |
| `Solves.chain_denotes` | In a solution, a chain of `k + 1` derivatives denotes the derivative of `iteratedDerivWithin k x` |
| `Solves.initial_iterated` | The declared initial value of `xm` is the `m`-th derivative of `x` at `start` |
| `Solves.chain_at` | The chain reading at each time, stated from a solution as `derivative_at` is |
| `SourceBody.solves_iff_classical` | The port reading and the iterated-derivative reading have the same solutions |
| `SourceContinuousModel.classical_iff_realizes` | Iterated-derivative source solutions are exactly the compiled realizations, same initial data |
| `SourceContinuousModel.realizes_iterated` | The same facts for every realization of the compiled model |
| `primitiveFrom_eq` | An integral is the unique antiderivative from the start on the half-line |
| `primitiveFrom_eq_integral` | For a continuous integrand it is the interval integral |
| `primitiveFrom_iff` | `g` is the integral at every time exactly when `g(start) = 0` and `g' = X`: a declared state with initial value `0` is `I_t(X)` |
| `Term.along_integral` | Whenever `int(X,t)` has a value, it is an antiderivative of `X` vanishing at the start |
| `Term.along_derivative_integral` | `diff(int(X,t),t)` reads as `X` wherever `X` has an antiderivative |
| `Term.along_integral_derivative` | `int(diff(x,t),t)` reads as `x(t) - x(start)` |
| `integral_derivative_ne` | Dropping the boundary term is wrong: `int(diff(x,t),t) ≠ x` on `x = 1` |
| `Term.cancel_eval` | The inverse rewrites preserve meaning wherever the atoms read them (`Context.Cancels`) |
| `Term.cancelAtom_along`, `Term.cancel_along` | Each rewrite, and rewriting inside an integrand, preserves the trajectory reading at every time |
| `Term.cancelAtom_agrees` | A rewritten term reads the same at one time as along the trajectory |
| `Solves.integral_chain` | In a solution, `int(diff(…diff(x,t)…,t),t)` reads `y - y0` through the declared velocities |
| `Context.cancels`, `SourceBody.cancels_at` | That premise holds along every regular signal, so in every solution |
| `Solves.integral_derivative`, `Solves.derivative_integral` | The two rewrites, stated from a solution |
| `Term.pointwise_agrees` | A pointwise integrand reads the same at one time as along the trajectory |
| `Term.readPorts_eval` | Reading a first-order atom as its derivative port preserves meaning in every environment |
| `Context.cancelsUpTo` | Along a trajectory whose declarations below a size hold, the atoms up to that size read the rewrites |
| `SourceBody.regular_below`, `Lowered.integralsAlong` | Declarations are discharged from a lowered solution by induction on the integrand's size |
| `Solves.integral_state` | In a solution, `int(X,t)` reads the state declared for it at every time |
| `SourceContinuousModel.integral_states` | In every realization, each integral declaration's state is its integral |
| `Lowered.solves_iff` | Source solutions are the lowered body's solutions, with the same `Evolution` |
| `SourceContinuousModel.solves_iff_realizes` | Source solutions are the compiled initialized feedback's realizations |
| `SourceContinuousModel.constrained_iff` | Corollary: any further predicate on the trajectory is preserved |
| `SourceContinuousModel.observations_correct` | Observed source solutions are observed realizations |
| `SourcePolynomialModel.correct` | Lambda-bearing polynomial sources against compiled outputs |

`Solves.lift_eqOn`, `Solves.initial_iterated`, `Solves.chain_denotes`, `Solves.chain_at`
and `solves_iff_classical` assume `SourceBody.VelocityStates` (each declared velocity is
a state port), which lowering checks; `Solves.integral_chain` needs no such premise, and
`realizes_iterated` takes it from the compiled model.

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
- Python rejects the scaled chain `2 * diff(diff(f,t),t) = f`; Lean accepts it, and
  residual forms, over a declared velocity.
- Python rejects a lower-order atom beside the chain, such as the damped oscillator
  `diff(diff(f,t),t) + c * diff(f,t) + k * f = 0` (probed at `fba931e`); Lean reads it
  as the declared velocity.
- Python has no explicit assignment: it reads `w = diff(h,t)` as an equation for `h`,
  `h = int(w,t) + h0` with `w` a forcing input (probed at `fba931e`). Lean's
  `w := diff(h,t)` defines `w`, and reads the atom as `h`'s declared velocity.

[HigherOrderIsolation.lean](../Gimle/Asgard/Examples/HigherOrderIsolation.lean) proves
the unique solution `x = cos(t/2)` of `4 * diff(diff(x,t),t) + x = 0`, `x(0) = 1`,
`x'(0) = 0`, and reads its second derivative back as `derivWithin` of `derivWithin`.
[DampedOscillator.lean](../Gimle/Asgard/Examples/DampedOscillator.lean) lowers
`diff(diff(x,t),t) + c * diff(x,t) + k * x = 0` to `dv := 0 - (c*v + k*x)` and, for
`c = 3`, `k = 2`, `x(0) = 1`, `x'(0) = 0`, proves the unique solution
`x = 2e^(-t) - e^(-2t)` and `x'' = -(3x' + 2x)` with actual derivatives.

For integrals ([SourceIntegrals.lean](../Gimle/Asgard/Tests/SourceIntegrals.lean), probed at
`fba931e`):

- Python rejects `2 * diff(f,t) = int(diff(f,t),t)` and `diff(f,t) = int(diff(f,t),t)`
  (competing derivative); Lean accepts both, reading `int(diff(f,t),t)` as `f - f0` with
  the declared initial value.
- Python accepts `diff(f,t) = int(f,t)` through a hidden integral state whose initial
  value is silently zero; Lean rejects it (`unsupportedIntegral`) unless the state is
  declared, with initial value `0`
  ([IntegralStates.lean](../Gimle/Asgard/Tests/IntegralStates.lean)). Declared, it
  lowers to `df := F`, `dF := f`, and Python's other integral cases lower once
  declared, such as `diff(f,t) = int(f,t) * f` to `df := F * f`. Python's
  `diff(f,t) = int(int(f,t),t)`, with two hidden states, lowers once both are declared,
  as do `diff(f,t) = int(diff(g,t) + f, t)` and `diff(f,t) = int(apply(λw.w * w, f), t)`.
  Python also accepts `diff(f,t) = int(1 * f, t)` against nothing declared; Lean requires
  the declaration as written. Python accepts `diff(f,t) = int(diff(g + h,t),t)` and
  `diff(f,t) = int(diff(diff(g,t),t),t)`, and rejects them only when the derivative is of
  the isolated state (competing derivatives); Lean rejects both shapes as declared
  integrands. Both reject a lambda holding a derivative.
- Python cancels inverse pairs on any axis, so it accepts `diff(f,t) = diff(int(f,x),x)`;
  Lean gives integrals off the evolution axis no value and rejects it (`axis`). Both
  rewrite inside an inverse pair's integrand, so `diff(f,t) = diff(int(diff(int(f,t),t),t),t)`
  is `f' = f` in both, and both accept `diff(f,t) = diff(int(apply(λw.w*w, f),t),t)`.
- Python accepts `diff(f,t) = diff(int(p * diff(g,t),t),t)` with `diff(g,t)` a forcing
  input. Lean rewrites the pair to `p * diff(g,t)`, a bound parameter factor being tame,
  and then needs `g`'s atom read through a declared velocity.
- Python accepts `diff(diff(diff(int(f,t),t),t),t) = f` and the fourth-order form with
  hidden zero-start velocities; Lean lowers them once the velocities are declared. Python
  rejects `diff(g,t) = int(diff(diff(f,t),t),t)`; Lean reads it as `g' = v - v(0)` over the
  declared velocity `v` of `f`.
- The listed D-of-I fixtures, such as `2 * diff(diff(int(f,t),t),t) = f` and
  `diff(int(2 * diff(f,t) + f,t),t) = 0`, lower to the same rates in both.

[SourceIntegrals.lean](../Gimle/Asgard/Examples/SourceIntegrals.lean) proves the unique
solution `f = 2e^(-t/2)` of `diff(int(2*diff(f,t) + f,t),t) = 0`, `f(0) = 2`, and the
solution `x = 3 - e^(-t)` of `diff(x,t) + int(diff(x,t),t) = 1`, `x(0) = 2`; there the
integral reads `x - 2`, and the solution `1 + e^(-t)` of the boundary-dropped equation
does not solve the source.
[IntegralStates.lean](../Gimle/Asgard/Examples/IntegralStates.lean) proves the unique
solution `f = cosh t`, `F = sinh t` of `diff(f,t) = int(f,t)`, `f(0) = 1`, with
`dF : F = int(f,t)` and `F(0) = 0`, and that in every solution the source's integral
reads `F`.
[NestedIntegralStates.lean](../Gimle/Asgard/Examples/NestedIntegralStates.lean) proves
the unique solution of `diff(f,t) = int(int(f,t),t)`, `f(0) = 1`, with both integrals
declared: `f = (eᵗ + 2e^(-t/2) cos(√3t/2))/3`, and in every solution `int(f,t)` reads
`F` and `int(int(f,t),t)` reads `G`.

### Drivers

A driver is a `.driver` port declared by a `DriverBinding` and compiled with
`compileSourceDriven`; nothing is inferred from a name or a `$` prefix, and the
other compilers reject every `.driver` port. A driver reads as a value in residuals
and explicit assignments. `D_t(z)` has a value only when `z` is declared
differentiable with a derivative port `dz`, and is read as `dz`; the derivative of a
driver without one, of a parameter, or a second derivative of a driver is rejected.
Python's `diff(a,t) = diff($z,t)` is declared as `da : diff(a, t) = diff(z, t)` with
`⟨"driver-z", some "driver-dz"⟩` and lowers to `da := dz`.

The driver signal is part of the relation (`SourceBody.SolvesDriven`): it must be
admitted (`Evolution.Admitted`), meaning every driver is continuous on `t ≥ start`
and every derivative port carries its driver's actual derivative there, so a
derivative port is never an unconstrained input. The coordinates are the driver
ports, then the states, and `SourceDrivenModel.solves_iff_realizes` relates the
source, for each admitted signal, to `Dynamics.close` of the compiled field with the
drivers as its external input. A derivative port need not be continuous, so a
contract that needs existence or uniqueness states that regularity itself.
[DrivenForcing.lean](../Gimle/Asgard/Examples/DrivenForcing.lean) solves
`diff(x,t) + x = diff(u,t) + u` for `u = sin`, `du = cos`, and shows that `u = sin`
with `du = 0` is not admitted, so nothing solves the source with it.
[Drivers.lean](../Gimle/Asgard/Tests/Drivers.lean) restates the Python fixtures.

Not yet in the source grammar (open tasks):

- integrands naming auxiliaries, in inverse pairs and declared integral states alike:
  the trajectory reading of `Solves` names only states and bound parameters (039);
- rewriting inside a pair under further derivatives or inside a chain's integral, such
  as Python's `diff(f,t) = diff(diff(int(int(f,t),t),t),t)` (040);
- a declared integral matched up to the meaning of its integrand, such as `int(1 * f, t)`
  against a declared `int(f, t)` (038);
- multi-axis equations such as heat in the continuous ODE adapter. They belong
  to the stream interpretation, where `2 * diff(u,t) = diff(diff(u,x),x)` is
  [isolated](formal-streams.md#isolating-a-scaled-derivative) to the declared
  `D_t u = 1/2 · D_x(D_x(u))` with its boundary kept (029);
- real atomics, division by expressions, literal products or negative numerals, and
  decimal literals (030). An atomic that feeds a continuous model's field may now be
  admitted through [partial-field feedback](#guarantees-and-limits), which keeps its
  domain at every time of the trajectory;
- integrals in a driven declaration: the driven relation reads no integral, and every
  integral there is rejected (053).

## Algebraic loops

The common compiler rejects every cycle as `cyclicDependency`.
[`Algebraic.Declaration`](../Gimle/Asgard/AlgebraicDeclaration.lean) declares a
stateless affine loop instead: ports in coordinate order [loop, external] (`.state`
loop ports, `.input` or `.parameter` external ports, `.output` outputs), the exact
rational `Problem` `z = M z + b(u)`, `y = C (z ++ u) + c`, a supplied inverse of
`1 - M`, a loop domain, admitted inputs, and the **membership obligation**
`∀ u, admitted u → domain (solution u)`. The obligation is a proof carried by the
declaration value, not a validator check: when it is false the declaration cannot
be written down. `validate` checks the ports and then both products of the supplied
inverse; a failing product is refused with `invalidInverse` (`left` or `right`), so
a singular loop is refused whatever it supplies and is never solved. `compile`
returns an `AlgebraicModel` carrying the checked `Inverse`.

| Theorem | Statement |
| --- | --- |
| `Declaration.solves_iff_rel` | every input, every declaration: source equations ↔ `Rel` of the compiled loop and output circuits (`compile_correct`); no existence or uniqueness |
| `AlgebraicModel.eliminate_correct` | accepted declaration, admitted input: exactly one loop point in the domain, and `Rel` holds of exactly the eliminated circuit's output (`Problem.eliminate_correct`) |
| `AlgebraicModel.solves_iff_eliminated` | the two combined: on an admitted input the source holds of exactly the eliminated output |
| `Declaration.coordinates_loop`, `.coordinates_external` | coordinates `0 … n-1` are the loop ports and carry the loop point, `n … n+d-1` the external ports and the input |

Nothing is said about inputs outside `admitted`. Only affine loops are declared;
nonlinear elimination is out of scope, and `compile_correct`'s set-level relation is
the only nonlinear claim. The declaration is a type of its own rather than a case of
`Model.Declaration`, which is plain data whose polynomial `Body` the common compiler
schedules; this one carries predicates and a proof.
[DeclaredAlgebraic.lean](../Gimle/Asgard/Examples/DeclaredAlgebraic.lean) declares
`halfLoop`, `z = z/2 + u` and `y = z` with inverse `2`, `u ∈ [-1, 1]` and
`z ∈ [-2, 2]`, whose source holds of exactly `y = 2u` (`half_declared`).
[AlgebraicDeclarations.lean](../Gimle/Asgard/Tests/AlgebraicDeclarations.lean) refuses
`z = z + 1` for every supplied inverse (`unit_rejected`) and shows that `z = z/2 + 1`
on `z ∈ [-1, 1]` cannot be completed: the obligation is false for the true inverse
(`off_obligation_false`), and any declaration that admits an input is refused
(`off_rejected`). There are no *same* Python parity fixtures: the pinned Python
equation compiler accepts all three as unguarded `trace` circuits, whose stream
runtime does not compute the algebraic fixed point, and its multi-equation algebraic
layering refuses a cycle; the test file records each case as *differs*.

## Guarantees and limits

| Feature | Proved | Conditions / limits |
| --- | --- | --- |
| Polynomial compilation | Original equations ↔ compiled outputs | Exact rationals; guarantee starts at the Lean AST, not arbitrary text parsing |
| Continuous feedback | Original initialized ODE ↔ compiled solution relation | Autonomous polynomial models on `t ≥ start`; compilation alone gives no existence, uniqueness, or stability |
| Linear analysis | Existence and uniqueness on `t ≥ start` | Accepted autonomous homogeneous rational linear systems; no stability claim |
| [Normalization / isolation](../Gimle/Asgard/Examples/VariableIsolation.lean) | Scoped substitution and conditional equation isolation preserve values/constraints | Isolation needs affine recognition and a proved polynomial inverse witness; no general equation solver |
| [Differential isolation](../Gimle/Asgard/Examples/DifferentialIsolation.lean) | Original implicit first-order ODE ↔ compiled feedback, same initial data | One atom `q*D_t(x)`, exact nonzero literal `q`, derivative-free residuals once other atoms are read through declared velocities; see [Source equations](#source-equations-lambdas-and-differential-isolation) |
| [Source integrals](../Gimle/Asgard/Examples/SourceIntegrals.lean) | Original source with integrals ↔ compiled feedback, same initial data; integrals denote antiderivatives from the start | Only the inverse rewrites `D(I(X)) = X` (tame `X`, rewritten inside first), `D^m(I(x)) = D^(m-1)(x)` and `I(D^(k+1)(x)) = y - y0` through declared velocities, and [declared integral states](../Gimle/Asgard/Examples/IntegralStates.lean) for pointwise `X`, [nested](../Gimle/Asgard/Examples/NestedIntegralStates.lean) through the declarations of their inner integrals, with initial value `0`; every other integral is rejected |
| [Higher-order isolation](../Gimle/Asgard/Examples/HigherOrderIsolation.lean) | Original higher-order ODE ↔ compiled feedback of the augmented system; chains denote iterated derivatives, velocity initial values the initial derivatives | Every lower level has an explicitly declared velocity state with its own initial value; one top atom per equation, lower-order atoms only through declared velocities |
| [Driven isolation](../Gimle/Asgard/Examples/DrivenForcing.lean) | Original driven source ↔ compiled driven feedback, for each admitted driver signal, same initial data | Declared drivers only; continuous drivers, derivative ports bound to actual derivatives; no integrals; no existence claim, and nothing about sampled or held driver signals |
| [Real atomics](../Gimle/Asgard/Examples/RealAtomics.lean) | Compilation and rewrites preserve values **and domains** | `sqrt`: nonnegative; `log` and rational/real powers: positive base; division: nonzero denominator |
| [Partial-field feedback](../Gimle/Asgard/Examples/PartialFeedback.lean) | `RealAtomics.Circuit.CloseRel` ↔ the initialized ODE with the field `Defined` along the state at every `t ≥ start` (`Circuit.close_correct`, `Expr.close_correct`) | A `RealAtomics` field over [drivers, state]; generators read time; relation only, with no declaration case yet (030); no existence or uniqueness claim |
| [Algebraic loops](../Gimle/Asgard/Examples/DeclaredAlgebraic.lean) | Source ↔ `Rel` for every input; on admitted inputs a unique loop point in the domain and exactly the eliminated output | Affine loops with an exact rational inverse of `1 - M`, both products checked; membership of every admitted input's solution in the domain is a proof obligation of the declaration; no nonlinear elimination |
| [External components](../Gimle/Asgard/Examples/ExternalBlend.lean) | Pointwise contracts and finite weighted partitions | Fixed explicit environment; all branches defined, weights nonnegative and sum to one; no certification of external code |
| [Stochastic translation](../Gimle/Asgard/Examples/StochasticJump.lean) | Source/process-circuit correspondence | Same supplied integral interpretation; no general SDE existence, Itô formula, or probability bounds |
| [Approximation](../Gimle/Asgard/Examples/Approximation.lean) | Uniform coordinate error bounds on a stated region | Feedforward real circuits; nonnegative budgets, coverage, and Lipschitz premises for composition |

Partial operations stay undefined even when their result is discarded or
multiplied by zero. Inside an ODE this holds at every time of the forward domain:
the partial-field relation carries `Defined` itself, so a trajectory that leaves the
domain once, or a fixed point of the totalized `value` only, has no relation output.
Trace hides internal signals; it does not guarantee a solution.
Formal streams use a [separate coefficient interpretation](formal-streams.md), with
[their own declarations](formal-streams.md#declared-stream-equations).

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
