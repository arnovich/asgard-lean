# Formal streams

Exact rational coefficients over finitely many ordered axes; the stream itself
is infinite. Import [`Streams.Named`](../Gimle/Asgard/Streams/Named.lean) for
named compilation and [`Streams.Reindex`](../Gimle/Asgard/Streams/Reindex.lean)
for explicit axis permutations.

| Basis | Series represented by raw coefficients `a` |
| --- | --- |
| OGF | `Σ a_α X^α` |
| EGF | `Σ a_α X^α / (α₁!⋯α_d!)` |

- One basis applies to all axes. EGF decoding divides by the full multi-factorial.
- Product is Cauchy convolution after decoding; raw EGF coefficients use binomial weights.
- OGF derivative: `(D_i a)[α] = (α_i+1) a[α+e_i]`; EGF derivative: `a[α+e_i]`.
- Integration reverses that shift and retains the **whole boundary slice** at axis degree zero.
- Checked laws: `D(I(a,b))=a` and `I(D(a),a)=a`.
- Axis IDs and input IDs are separate; permutations require an explicit bijection.

## Declared stream equations

[`Streams.Declaration`](../Gimle/Asgard/Streams/Declaration.lean) declares
equations `D_along u = F(u)` rather than hand-building `NamedExpr` values. A
`Declaration` names:

- the **basis**, a field of the value and part of the model's identity: an OGF
  and an EGF declaration differ, and resolve to `Expr .ogf` and `Expr .egf`;
- the **ordered axes**, by stable ID; position is declared order;
- the **inputs**: unknowns are `.state` ports, boundary profiles `.boundary`
  ports, and anything else `.parameter` ports read as arbitrary streams;
- the **equations** `⟨unknown, along, boundary, rhs⟩`: the boundary profile is a
  declared input on the named axis `along`.

The **boundary** of an equation along axis `i` is the whole zero slice
`{α | α_i = 0}` of the unknown, the slice `integral` reads from its boundary
argument; the boundary input's other coefficients are ignored by the boundary
condition, although a right-hand side may read them.

`Declaration.validate` reports the first error as a `Diagnostic`: empty or
repeated axis and input IDs or names, input roles, an unknown that is not a
`.state` input, a boundary that is not a `.boundary` input, an unknown axis or
name in an equation, an unestablished substitution (`unestablishedCompose`), a
derivative of the unknown along its own axis on the right-hand side
(`NamedExpr.selfDerivative`: `competingDerivative` for `D_t u = D_t u + 1`,
`higherOrderDerivative`, `mixedDerivative` for `D_x(D_t u)` or `D_t(D_x u)`),
and unknowns or boundaries bound by no equation or by two. The derivative check
also refuses `D_t(I_t(u, u0))` on the right-hand side, although it means `u`, and
concerns only an equation's own unknown: a system such as `D_t u = D_t v`,
`D_t v = D_t u + 1` is accepted and may be implicit or have no solution; nothing
here claims existence. `compile` returns a
`StreamModel`: the equations resolved in declared order, with the evidence.
Every refusal names an unsupported form, never an unsatisfiable model:
`unestablishedCompose` refuses a substitution whose inner argument is not
syntactically known to have zero constant coefficient, even when it has one for
semantic reasons. An accepted substitution is defined (`StreamModel.rhs_defined`)
but, like every `seriesCompose`, is not lowered to a coefficient window.

`Streams.Declaration` is a type of its own rather than a case of
`Model.Declaration`, whose `body` is a polynomial `Body` that stream equations do
not have; the model-family contract's "declaration case" is met by this type.
There are no Python parity fixtures here: the pinned Python compiler has no
stream-declaration counterpart; the heat fixture's parity is recorded under
*Isolating a scaled derivative* below.

| Theorem | Statement |
| --- | --- |
| `derivative_iff_integral` | `D_i u = f` and `u = b` on the zero slice along `i` ↔ `u = I_i(f, b)` |
| `Equation.solves_iff_integral` | an accepted equation holds (named meaning of `F`, derivative, boundary slice) ↔ `∃ v, rhs.compile.Rel x ![v] ∧ u = I(v, b)`; `F` is read through the relation of `Context.compiled_iff` |
| `Equation.solves_iff_rebuilt` | the same ↔ the compiled `I(F(u), b)` circuit returns `u` |
| `StreamModel.solves_iff`, `.solves_iff_integral` | a declaration holds ↔ every equation's reconstruction returns its unknown; with no domain left, `u = I(F(x), b)` along each declared axis |
| `StreamModel.rhs_defined` | every accepted right-hand side is defined on every input |
| `Equation.resolve_ids` | the resolved axis and inputs sit at the declared positions of their IDs |

Nothing is claimed about existence or uniqueness; a declaration's solution set
may be empty or large. `seriesCompose` is accepted only where `CanCompose` is
**established** syntactically: the inner argument is `0`, an axis variable, a
sum of such, a product with such a factor, or an integral whose boundary is such
(`NamedExpr.composable_sound`, `canCompose_iff`: a zero raw coefficient at the
origin). An input is never evidence. Anywhere else, even when the substitution's
value is discarded or multiplied by zero, the declaration is refused. A
repeated axis ID is refused by validation and by resolution (`resolve = none`).

[DeclaredHeat.lean](../Gimle/Asgard/Examples/DeclaredHeat.lean) declares
`D_t u = D_x² u` with boundary `u_at_t0` on `time`. It resolves to
`FormalHeat.rhs` and `FormalHeat.circuit`, and with boundary `x²` its solution
set is exactly `u = x² + 2t` (`solutions`). Declared with axes `[space, time]` it
resolves along axis 1, and its solution set is the permuted stream
(`swapped_solutions`). The tests lower the declared circuit as `heat_lowers`
does, and refuse `0 · u(t ↦ 1)` and a repeated axis ID with diagnostics.

```sh
lake build Gimle.Asgard.Tests.StreamDeclarations
```

## Isolating a scaled derivative

[`Streams.Isolation`](../Gimle/Asgard/Streams/Isolation.lean) states a stream
equation in source terms and isolates it to a declared `Equation`. A
`SourceEquation` names the unknown, the axis `along` and the boundary input, and
two sides written in the `term%` notation; `sourceEquation% (u, t, u0) 2 *
diff(u, t) = diff(diff(u, x), x)` is one. A `SourceDeclaration` has the basis,
ordered axes and inputs of a `Declaration` and a list of source equations.

- **Meaning.** Each side is read as a `NamedExpr` (`NamedExpr.ofTerm`: a name is
  an input, `*` the stream product, `-a` the product with `-1`, `diff(a, i)` the
  formal derivative on axis `i`, `/ n` the product with `1/n`) and through
  `Context.meaning`. `SourceEquation.Solves`: both sides are defined and equal,
  and the unknown equals the boundary input on the whole zero slice along
  `along`, exactly the boundary of `Equation.Solves`.
- **Isolation.** One side is read as `q * D_along(u) + r` with an exact nonzero
  literal product `q` and a remainder `r`; the other side `o` and `r` hold no
  derivative of `u` along `along`, while derivatives on other axes may appear in
  both. The result is `⟨u, along, boundary, (o - r)/q⟩`, written without a unit
  factor, with every term kept: the residual form gives
  `1/2 · (0 + -1 · (-1 · D_x² u))`, not a simplified `1/2 · D_x² u`.
- **Rejected**, each with a diagnostic naming an unsupported form, never an
  unsatisfiable model: no such derivative (`missingDerivative`), one on each side
  (`competingDerivative`), two on one side (`repeatedDerivative`),
  `D_t(D_t u)` (`higherOrderDerivative`), `D_x(D_t u)` and `D_t(D_x u)`
  anywhere (`mixedDerivative`), `D_t` of another operand reading `u` or a scale
  around a sum (`unsupportedDerivative`), a non-literal factor
  (`nonlinearDerivative`), a zero scale (`zeroScale`), and integrals
  (`unsupportedIntegral`) and lambda applications (`unsupportedApplication`),
  which have no stream reading here. A name is always an input; axis variables
  are not written in this form.

| Theorem | Statement |
| --- | --- |
| `NamedExpr.affine_means` | a recognized side means `q · D_along(u) + r` in every environment |
| `SourceEquation.Isolated.solves_iff` | a point solves the source equation ↔ it solves the isolated `Equation` (both directions) |
| `SourceEquation.Isolated.keeps` | the isolated equation has the source's unknown, axis and boundary input |
| `SourceEquation.Isolated.explicit_rhs` | the isolated right-hand side has no derivative of `u` along `along` |
| `SourceDeclaration.solves_iff` | a point solves the source declaration ↔ it solves the isolated `Declaration` |

`Equation.solves_iff_integral` then gives the solution set `u = I((o - r)/q, b)`.
`SourceDeclaration.compile` isolates, then validates and resolves the isolated
declaration.

[HeatIsolation.lean](../Gimle/Asgard/Examples/HeatIsolation.lean) obtains the
declared heat of `DeclaredHeat` from `diff(u, time) = diff(diff(u, space), space)`,
in either axis order. It restates the pinned Python fixture
`test_affine_heat_preserves_half_diffusivity` (gimle-asgard `fba931e`): the four
forms `2 * diff(u,t) = diff(diff(u,x),x)`, reversed, with the spatial term as a
residual `… - diff(diff(u,x),x) = 0`, and both, in the EGF basis with the
boundary `x²` (`[0, 0, 2, 0]`). Each isolates, the first two to exactly
`D_t u = 1/2 · D_x(D_x(u))`, and each has the single solution `x² + t`
(`fixture_solutions`), the field the Python test observes: **same**. Python
`2 * diff(diff(f,x),t) = f`, `2 * diff(f,t) = diff(f,t) + f` and
`2 * diff(diff(u,t),t) = diff(diff(u,x),x)` stay rejected, as mixed, competing
and higher-order.

```sh
lake build Gimle.Asgard.Tests.StreamIsolation
```

## Substitution and truncation

- `seriesCompose` substitutes one selected variable. The inner series must have
  **zero entire multivariate constant coefficient**: `t ↦ x` is valid; `x ↦ 1+x` is rejected.
- Invalid substitutions remain invalid through discard and multiplication by zero.
- The `convolution` aliases mean this substitution, not discrete-kernel convolution.
- `truncate_inside` proves agreement only inside the requested coefficient window.
  Derivatives may need coefficients beyond it; substitution may move degrees between axes.
- On its own this implies no analytic convergence, Taylor identification or numerical
  truncation bound; *Certified analytic truncation* below derives one from a proved majorant.

## Finite observations

[`Streams.Lowering`](../Gimle/Asgard/Streams/Lowering.lean) connects finitely many
exact coefficients of a stream circuit to a feedforward rational-polynomial
circuit, so a finite certificate can speak about the original stream circuit.

- A `Manifest` lists slots — a port and a degree vector — with the ordered axis
  IDs and port IDs; the basis is part of its type. `Manifest.rectangle` builds a
  window `degree < w` (empty if any `w_i = 0`). Duplicate output slots, and empty
  or repeated axis or port IDs, are refused. The input manifest takes the
  output's axes, since a stream circuit has one ordered set of axes
  (`lower_names`); `dependencyPoint_extract` ties its input to `Manifest.extract`.
- `lowerRaw c j k` is an exact polynomial `Term` in input coefficients for output
  coefficient `k` of port `j`, and `lowerRaw_correct` proves it equal for every
  input stream. `lower` collects the dependency slots, compiles the terms with the
  polynomial compiler, and `lower_correct` states the result for the original
  circuit, its basis and both manifests.
- Dependencies are exact, not windowed: a derivative reads one coefficient past
  the observed one (OGF factor `α_i+1`, EGF factor 1), a product reads every split
  of the index along every axis (EGF with multinomial weights), and an integral
  reads the boundary slot at degree zero along its axis, at the other axes' degrees.
- **Derivative counterexample:** `x²` and `0` agree on the window `degree ≤ (1,1)`,
  but coefficient `(0,0)` of `D_x²` is 2 for one and 0 for the other, because it
  reads `(0,2)`. Observing a window of an output needs a *larger* window of the
  input, which the lowering computes.
- `seriesCompose` is refused anywhere in the circuit (`Failure.unsupported`), even
  in a branch whose output is discarded. `lowerChecked` stops as soon as any term
  or partial result would exceed the size limit, before expanding further, and a
  product whose split count alone exceeds it is refused before listing splits:
  `Failure.resourceLimit` is distinct from unsupported structure. Forty nested
  squarings, about 2⁴⁰ nodes if expanded, are refused at once.

Supported: routes, constants, axis variables, addition, product, selected-axis
derivatives and integrals, sequential and parallel composition. The theorem is
about selected exact coefficients; it says nothing about the full stream beyond
them, analytic values, or numerical error.

```sh
lake build Gimle.Asgard.Tests.StreamLowering
```

## Polynomial realization

[`Streams.Realization`](../Gimle/Asgard/Streams/Realization.lean) connects finite
streams to mathlib `MvPolynomial (Fin d) ℚ` (`Poly d`) and their real fields.

- `ofPoly basis p` embeds `p` exactly: OGF raw coefficients are `coeff n p`,
  EGF raw ones `α₁!⋯α_d! · coeff n p` on every axis (`ofPoly_ogf_apply`,
  `ofPoly_egf_apply`); `ofPoly_injective`.
- `Realizes basis a p` means the **whole** stream is `ofPoly basis p`.
  `finiteSupport_iff`: a stream is realized iff all its raw coefficients have
  finite support. Agreement on a finite window is not a witness.
- `field p x` is real evaluation; `field_eq_sum` writes it as the finite sum of
  the decoded stream coefficients against monomials, in either basis.
- Every circuit maps realized inputs to realized outputs: `Circuit.polyValue`
  is the wire-for-wire polynomial semantics, and `Circuit.rel_ofPoly` restates
  the original `Circuit.Rel`: outputs are exactly `ofPoly ∘ polyValue`, under
  `PolyDefined` (only substitution has a side condition, zero constant term).
- Analytic meaning, on the evaluated field rather than coefficient shifts:
  `hasDerivAt_field` (selected-axis `pderiv` is the real partial derivative),
  `field_integralPoly` (`U(x) = B(x|ᵢ₌₀) + ∫₀^{xᵢ} P(x|ᵢ₌ₛ) ds`, with the full
  boundary profile on `xᵢ = 0`), `field_composePoly`, and the `field_C/X/add/mul`
  laws. `slice_iff` equates coefficients on the zero slice with values on `xᵢ = 0`.

## Polynomial heat evolution

[`Streams.Heat`](../Gimle/Asgard/Streams/Heat.lean), axes `[t, x]`. For any
rational profile `p` (`Profile = Polynomial ℚ`):

`solution p = Σ_{k ≤ cutoff p} t^k/k! · (D^(2k) p)(x)`, `cutoff p = natDegree p / 2`.

Later terms vanish (`term_eq_zero`, `solution_eq_sum`); constant, zero and affine
profiles are stationary (`solution_of_natDegree_le_one`).

| Object | Proved |
| --- | --- |
| Constructed `stream basis p` | `circuit_solution`: the original `D_x²`/`I_t` heat circuit returns `[D_x² u, u]` on `[u, p, _]`, both bases |
| Its field `solution p` | `solution_pde`: `∂_t u = ∂_x² u` at every real `(t,x)`; `solution_initial`: `u(0,x) = p(x)` |
| Supplied stream `a` | `candidate_stream`: if the circuit reconstructs `a` from `p`, then `a = stream basis p` |
| Supplied polynomial `q` | `field_unique`: PDE and initial profile everywhere imply `q = solution p` |
| Arbitrary smooth field | nothing |

`formal_unique` proves uniqueness from the coefficient recurrence
(`t`-degree `k+1` from `k`) among all formal streams, hence within the finite
polynomial class (`poly_unique`). `reconstructs_iff`: reconstruction by
integration is exactly `D_t u = D_x² u` plus the whole `t = 0` slice.

[PolynomialHeat.lean](../Gimle/Asgard/Examples/PolynomialHeat.lean) checks
`x² ↦ x²+2t`, `x⁴ ↦ x⁴+12tx²+12t²`, stationary affine profiles, EGF
coefficients, the `[x,t]` axis swap, and that a changed boundary or coefficient
fails. `FormalHeat.circuit` *is* `Heat.circuit .ogf`, and `FormalHeat.heat` is
derived as the constructed stream by uniqueness from its own circuit theorem.
A stream equal to `x²+2t` on the window `degree < (5,5)` but with an infinite
tail along `t = 0` has no finite support, so it is not realized
(`tailed_not_realized`) and no field theorem applies to it.

Scope: no infinite-series summation, spatial boundary-value problem, maximum
principle or numerical claim; bounds on a strip are properties of this explicit
solution. Infinite streams with a proved majorant are covered by *Certified
analytic truncation* below, and infinite (analytic) profiles by *Analytic heat
profiles*.

```sh
lake build Gimle.Asgard.Tests.StreamRealization
```

## Certified analytic truncation

[`Streams.Tail`](../Gimle/Asgard/Streams/Tail.lean) turns an explicit, proved
coefficient majorant into analytic convergence and a uniform rectangular
truncation error. The stream type alone gives neither.

**Hypotheses the caller supplies**, bundled as `TailCertificate basis a`:

| Field | Meaning |
| --- | --- |
| `majorant : Majorant d` | exact rationals `M ≥ 0`, `R_i > 0`, one per ordered axis |
| `box : Box d` | exact radii `r_i ≥ 0` (zero allowed); the domain is the closed box `\|x_i\| ≤ r_i` |
| `inside` | `r_i < R_i` for every axis; boundary radii `r_i ≥ R_i` are rejected |
| `majorizes : Majorizes basis a majorant` | a proof that **every** decoded OGF coefficient obeys `\|a_α\| ≤ M · ∏ᵢ R_i^(−α_i)` |

Coefficients are always decoded (EGF raw values are divided by `α₁!⋯α_d!`), so
the majorant, the field and the error depend only on the OGF series. Without a
`majorizes` proof there is no certificate and no conclusion.

**Conclusion.** With `q_i = r_i / R_i` and a window `N : Fin d → ℕ`
(`α_i < N_i` on every axis):

```text
tailBound = M · (Σᵢ q_i^N_i) · ∏ᵢ (1 − q_i)⁻¹             (exact ℚ)
TruncationBound basis a box N ε  :=
  ∀ x, box.Mem x → |analyticField basis a x − windowField basis N a x| ≤ ε
```

| Theorem | Statement |
| --- | --- |
| `TailCertificate.summable_norm`, `.hasSum` | on the box, `Σ_α a_α x^α` converges absolutely, to `analyticField` |
| `TailCertificate.truncationBound c N` | `TruncationBound basis a c.box N (c.error N)`, where `c.error N = tailBound c.majorant c.box N` |
| `abs_analyticField_sub_windowField_le` | the same bound, from the premises unbundled |
| `TruncationBound.lower`, `.upper`, `.mono` | transport a bound on the window field to the analytic field |
| `truncationBound_ports` | per-port bounds `ε_j` on a shared box give `‖F − W‖ ≤ B` in the sup norm of `ℝⁿ` for any `B ≥ 0` with `ε_j ≤ B` |
| `truncationBound_iff_of_decode`, `TailCertificate.transport`, `analyticField_encode` | OGF/EGF invariance: equal decoded series have the same field, window, premise and error |
| `truncate_realizes`, `field_windowPoly`, `analyticField_truncate` | the truncated stream is realized by `windowPoly`, whose real `field` is `windowField` |
| `prefix_cannot_certify` | with at least one axis, any finite set of observed coefficients is shared by a stream violating any given majorant |

The error metric is the **absolute difference of the evaluated real scalar
field, uniform over the closed box**. It is not a coefficientwise error or a
statistical confidence. The union bound over axes counts some omitted indices
more than once, but it bounds the whole tail, not just the next coefficient.
Degenerate cases: a zero-radius box admits only the origin, where the field is
the constant coefficient (`analyticField_zero`) and positive windows have
`tailBound = 0` (`tailBound_radius_zero`); with zero axes the error is `0`
(`tailBound_axes_zero`).

[GeometricTail.lean](../Gimle/Asgard/Examples/GeometricTail.lean) certifies
`a_(m,n) = 1` on `|t|, |x| ≤ 1/2` with `M = R_t = R_x = 1`. At window `(N, N)`
the error is `8·2^(−N)` (`error_eq`, `bound`; `error_ten` evaluates `N = 10` to
`1/128` in the kernel). The field is `1/((1−t)(1−x))` and at the corner
`(1/2, 1/2)` the true error is `8·2^(−N) − 4·4^(−N)` (`corner_error`): the bound
overcounts exactly the doubly omitted corner block. The EGF copy, with raw
coefficients `m!·n!`, carries the same certificate.

The tests build a stream equal to that one on the whole window `(N, N)` but with
coefficients `4^m` along `x`-degree 0. Its series diverges at `(1/2, 0)`, so no
certificate of any majorant covers that point (`hostile_uncertifiable`).
Neither a finite prefix nor a radius estimated from one certifies anything.

Scope: no majorant discovery, floating-point or JAX execution, roundoff budget,
time-window re-expansion, or stability of the bound under differentiation or
substitution. Numerical execution remains evidence.

```sh
lake build Gimle.Asgard.Tests.StreamTail
```

## Analytic heat profiles

[`Streams.AnalyticHeat`](../Gimle/Asgard/Streams/AnalyticHeat.lean), axes
`[t, x]`, connects the heat circuit to certified truncation. An analytic profile
is given by its raw EGF coefficients `g : ℕ → ℚ` (`p(x) = Σ g_j x^j/j!`,
`g_j = p^(j)(0)`); as a one-axis stream in either basis it is `profile basis g`,
and `coeffs basis p` recovers `g` from any one-axis stream (`coeffs_profile`,
`profile_coeffs`). The heat stream is `stream basis g`, the boundary input
`boundary basis g` (the profile on `t = 0`, zero at positive `t`-degree):

| Basis | Coefficient at `(n, k)` of `stream basis g` | Theorem |
| --- | --- | --- |
| EGF | `g_(k+2n)` | `stream_egf_apply` |
| OGF | `g_(k+2n) / (n!·k!)` | `stream_ogf_apply` |

| Theorem | Statement |
| --- | --- |
| `stream_pde`, `stream_slice` | `D_t u = D_x² u`; on `t = 0` the stream is the boundary |
| `circuit_stream` | `(Heat.circuit basis).Rel ![stream basis g, boundary basis g, unused] ![D_x² (stream basis g), stream basis g]` |
| `candidate_stream` | any `a` the circuit reconstructs from `boundary basis g` is `stream basis g` |
| `stream_ofPolynomial`, `boundary_ofPolynomial` | for a polynomial `p` and `g_j = j!·p_j` (`ofPolynomial p`), exactly `Heat.stream basis p` and `Heat.boundary basis p` |
| `majorizes_stream` | `ProfileBound g M ρ` (`∀ j, \|g_j\| ≤ M·ρ^(−j)`, exact `M ≥ 0`, `ρ > 0`) gives `Majorizes basis (stream basis g) (heatMajorant M ρ _ _)`: bound `M`, radii `[ρ², ρ]` |
| `certificate`, `truncationBound` | with a box strictly inside `[ρ², ρ]` (`inside_iff`: `r_t < ρ²`, `r_x < ρ`), a `TailCertificate` and `TruncationBound basis (stream basis g) box N (tailBound (heatMajorant M ρ _ _) box N)` at every window `N` |
| `profileBound_expSum` | for `expSum terms` (`g_j = Σᵢ cᵢ·aᵢ^j`, the profile `Σᵢ cᵢ·e^(aᵢx)`), `ProfileBound _ (Σᵢ \|cᵢ\|) ρ` whenever `expSumFits terms ρ` (every `\|aᵢ\|·ρ ≤ 1`, a `Bool` the kernel decides) |
| `circuit_truncation` | every `a` the heat circuit reconstructs from `boundary basis g` satisfies `TruncationBound basis a box N ε`, given a profile bound, a box inside `[ρ², ρ]` and `tailBound … box N ≤ ε` |
| `expSum_truncation` | `circuit_truncation` for an exponential sum, with every side condition (`0 < ρ`, the fit, the box, `tailBound ≤ ε`) decidable, so a root claim closes by `decide +kernel` |

The transfer drops the factorials (`n!·k! ≥ 1`): decoded coefficients satisfy
`|g_(k+2n)|/(n!·k!) ≤ M·ρ^(−(k+2n)) = M·(ρ²)^(−n)·ρ^(−k)`. It is sound but
conservative. A bound on *raw EGF* coefficients says the profile is entire of
exponential type at most `1/ρ`; a profile with a finite radius of convergence,
such as `1/(1 − 4x)` (`g_j = j!·4^j`), has none, and its heat series diverges at
`(0, 1/2)`, so no certificate of any majorant covers that point
(`hostile_uncertifiable`, `hostile_not_bounded`).

[ExpHeat.lean](../Gimle/Asgard/Examples/ExpHeat.lean) takes `e^x`: `g_j = 1`,
`M = ρ = 1`, radii `[1, 1]`. Every raw EGF coefficient of the output is `1`
(`stream_egf`), and at every real point its analytic field is `exp (x + t)`
(`analyticField_eq`). On the box `|t| ≤ 1/4`, `|x| ≤ 1/2` at window `(8, 16)`:

```text
ε = 1 · (4^(−8) + 2^(−16)) · (4/3) · 2 = 1/12288        (error_eq, decide +kernel)
exp_bound : box.Mem y → |exp (y 1 + y 0) − windowField basis ![8, 16] (stream basis g) y| ≤ 1/12288
```

The tests also reject a claimed bound the profile violates (`2^j` with
`M = ρ = 1`), boxes on or beyond the radii, and a box with `ρ > r_t ≥ ρ²`.

Scope: no majorant discovery, no statement that the analytic field solves the
PDE as a real function (only the formal circuit relation and the certified
convergence), and no finite-radius profiles.

```sh
lake build Gimle.Asgard.Tests.AnalyticHeat
```

## Causal equations and the formal Burgers stream

[`Streams.Causal`](../Gimle/Asgard/Streams/Causal.lean) is the formal
Cauchy–Kowalevski lemma. A right-hand side `F` is *causal* along an axis
(`IsCausal axis F`) when `F a` and `F b` agree up to degree `k` on that axis
whenever `a` and `b` do (`AgreeBelow axis k`). Derivatives along other axes,
sums and Cauchy products are causal (`derivative_causal`, `add_causal`,
`product_causal`), so every polynomial right-hand side in the unknown and its
spatial derivatives is. Integration along the axis raises the degree it reads
by one and reads the boundary only on the zero slice (`integral_agree`).

| Theorem | Statement |
| --- | --- |
| `solution basis axis F boundary` | Picard iteration: `approx (n+1) = I_axis (F (approx n)) boundary`; coefficient `m` is read from the iterate of its own degree |
| `solution_reconstructs`, `solution_pde`, `solution_slice` | `I_axis (F u) b = u`, hence `D_axis u = F u`, and `u = b` on the zero slice |
| `formal_unique` | two formal solutions with the same zero slice are equal: strong induction on the degree with `integral_agree` |
| `reconstructs_iff` | reconstruction by integration is exactly the equation plus the slice, for any causal or non-causal `F` |

Nothing is said about convergence: the constructed series may diverge, and
often does.

[`Streams.Burgers`](../Gimle/Asgard/Streams/Burgers.lean), axes `[t, x]`,
instantiates it for `D_t u = −u·D_x u + ν·D_x² u` with a rational viscosity
`ν` (`rhs basis ν`, causal by `rhs_causal`). `stream basis ν boundary` is the
formal solution from any boundary stream; `formal_unique`, `eq_stream`,
`stream_pde` and `stream_slice` are the instances. The circuit
`circuit basis ν : Circuit basis 2 3 2` compiles the same right-hand side and
its `t`-integral on inputs `[u, boundary, unused]`:

| Object | Proved |
| --- | --- |
| Constructed `stream basis ν b` | `circuit_solution`: the circuit returns `[rhs u, u]` on `[u, b, _]`, any `b`, both bases |
| Supplied stream `a` | `candidate_stream`: if the circuit reconstructs `a` from `b`, then `a = stream basis ν b` |
| Polynomial boundary `ofPoly basis b` | `approx_ofPoly`: every Picard iterate is `ofPoly` of `picard ν b n`, with `picard (n+1) = integralPoly 0 (rhsPoly ν (picard n)) b`; `stream_ogf_coeff`: the OGF coefficient at `t`-degree `n` is a coefficient of `picard ν b n` |
| `integralPoly` | `integralPoly_eq`: a polynomial with the right `t`-derivative and zero slice is the integral, so iterates are evaluated by exhibiting them |
| Convergence, the real-field PDE, shocks | nothing |

The stream from a polynomial profile is not polynomial: the `x`-degree grows
by `deg − 1` per `t`-degree. For a profile of degree at least two with `ν ≠ 0`
the `t`-series is expected to diverge (the classical Cole–Hopf argument, with
the coefficient growth checked numerically); that is proved nowhere here.
Only the boundary's `t = 0` slice enters the stream (`stream_congr_slice`),
and the Picard construction reproduces the closed-form heat stream
(`Tests/Burgers.lean`).

[BurgersSquare.lean](../Gimle/Asgard/Examples/BurgersSquare.lean) takes
`ν = 1/10` from `u(0, x) = x²`. The first two iterates are

```text
picard 1 = x² + t (1/5 − 2x³)
picard 2 = x² + t (1/5 − 2x³) + t² (−4x/5 + 5x⁴) + t³ (2x²/5 − 4x⁵)
```

and the stream's coefficients `[t] = 1/5` (the viscous term alone),
`[t x³] = −2` (the nonlinearity alone), `[t² x] = −4/5` and `[t² x⁴] = 5`
follow (`coeff_t`, `coeff_t_x3`, `coeff_t2_x`, `coeff_t2_x4`). The `t³` term
of `picard 2` is an artefact of the iteration, not the stream's coefficient,
exactly as `Causal` says; `picard_three` gives the true `t³` slice
`16x²/5 − 14x⁵` and artefacts up to `t⁷`. Without viscosity the
`t`-coefficient is `0` (`coeff_t_inviscid`). Affine data `x` gives `x − t x`
as the first iterate of `x/(1 + t)`. The tests also show that the heat stream
from `x²` is not the Burgers stream and that the circuit refuses it.

Scope: no convergence, no real-field PDE, no shocks; the certified truncation
of a *convergent* Burgers stream, the Cole–Hopf quotient, is the next section.

```sh
lake build Gimle.Asgard.Tests.Burgers
```

## Cole–Hopf: a certified Burgers truncation

[`Streams/Majorant.lean`](../Gimle/Asgard/Streams/Majorant.lean) gives the
geometric majorant of *Certified analytic truncation* a calculus, in the OGF
reading: `majorizes_mono` (smaller radii, larger bound), `majorizes_C_mul`
(scaling), `majorizes_mul` (a Cauchy product: bounds multiply, radii halve,
since the antidiagonal of `α` has `∏ (α_i + 1) ≤ 2^|α|` terms) and
`majorizes_inv` (the inverse of a stream with constant term `c` and the rest
majorized by `M` at radii `R`: bound `1/|c|` at any radii `r < R` with
`(M/|c|)·(∏ (1 − r_i/R_i)⁻¹ − 1) ≤ 1`, by well-founded induction on the index
through `MvPowerSeries.coeff_inv`). It also gives the ordinary derivative its
algebra — `ogfD_add`, `ogfD_mul` (Leibniz, proved by cancelling `X_i`), `ogfD_comm`,
`ogfD_inv` — so identities between quotients close by `ring`.

[`Streams/ColeHopf.lean`](../Gimle/Asgard/Streams/ColeHopf.lean) applies it.
`heatSeries ν g` is the heat stream `D_t φ = ν D_x² φ` of a profile with raw
EGF coefficients `g` (`ν^n g_(k+2n)/(n! k!)`, majorant radii `[ρ²/ν, ρ]` for `ν > 0`);
`quotient ν φ = −2ν · D_x φ · φ⁻¹`, and `quotient_pde` proves that it solves
`Burgers.rhs` whenever `φ` solves the heat equation and is invertible — after
the derivation rules the identity is polynomial in `D_x φ`, `D_x² φ`, `D_x³ φ`
and `φ⁻¹`. For an exponential-sum profile `Σ cᵢ e^(aᵢ x)`:

| Theorem | Statement |
| --- | --- |
| `ogfD_expSumHeat` | `D_x φ` is the heat stream of `Σ cᵢ aᵢ e^(aᵢ x)` |
| `rest_heatSeries`, `profileBoundFrom_expSum` | away from the constant term only the `aᵢ ≠ 0` terms count: the inverse's `M` is `Σ_{aᵢ≠0} \|cᵢ\|` |
| `majorizes_front` | for `r` inside `[ρ²/ν, ρ]` with `smallEnough`, `front ν terms = quotient ν φ` is majorized by `\|2ν\|·(Σ \|cᵢ aᵢ\|)/\|Σ cᵢ\|` at radii `r/2` |
| `candidate_quotient` | the Burgers circuit reconstructs the front from its `t = 0` slice and nothing else (060's `candidate_stream`) |
| `constantCoeff_front`, `circuit_front`, `certificate` | the front's value at the origin `−2ν (Σ cᵢaᵢ)/(Σ cᵢ)`; the circuit relates the front to its own slice; its named `TailCertificate` |
| `front_truncation` | with `Σ cᵢ ≠ 0`, a box inside `r/2` and `tailBound ≤ ε`, every reconstruction satisfies `TruncationBound .ogf a box N ε`; every side condition (`expSumFits`, `Σ cᵢ ≠ 0`, the radii, `smallEnough`, the box, `tailBound ≤ ε`) is decidable |

[BurgersFront.lean](../Gimle/Asgard/Examples/BurgersFront.lean) takes
`φ(0, x) = 1 + e^(−x)`, `ν = 1/2` — the front `u = 1/(1 + e^(x − t/2))` — with
`ρ = 1`, `r = (2/3, 1/2)` (so `(1/2)·(3 − 1) = 1`, the inverse's condition is
tight), majorant bound `1/2` at radii `(1/3, 1/4)`, and on `|t| ≤ 1/6`,
`|x| ≤ 1/8` at window `16 × 16`:

```text
ε = 1/2 · (2 · (1/2)^16) · 2 · 2 = 1/16384        (error_eq, decide +kernel)
```

The bound is loose on purpose: factorials are dropped in the heat majorant,
the inverse costs the ratio tail, the product halves the radii. The true error
on that box is many orders smaller; the certificate is a proof, not a
measurement.

### The analytic field of the front

[`Streams/AnalyticField.lean`](../Gimle/Asgard/Streams/AnalyticField.lean)
says what the field of a product and an inverse *is* where both factors are
majorized: `analyticField_mul` (Mathlib's Cauchy product over
`Finsupp.antidiagonal`, from the absolute convergence `Tail.lean` proves on a
box strictly inside both majorants), `analyticField_C_mul`,
`analyticField_one`, and `analyticField_inv` — the field of `φ⁻¹` is the
inverse of the field of `φ`, which is therefore nonzero there — as the
corollary of `φ⁻¹ * φ = 1`. In `ColeHopf.lean`,
`analyticField_heatSeries_expSum` sums the heat stream of `Σ cᵢ e^(aᵢ x)` to
`expSumField ν terms = Σ cᵢ e^(ν aᵢ² t + aᵢ x)` at every real point (one
exponential is a product of two one-axis exponential series, `hasSum_index_prod`),
and `analyticField_front` combines them: under `front_truncation`'s premises,
on a box strictly inside `r/2`, the front's field is
`−2ν (Σ cᵢ aᵢ e^(…)) / (Σ cᵢ e^(…))` and the denominator does not vanish.

For the worked front this is `front_field_eq`: on `|t| ≤ 1/6`, `|x| ≤ 1/8` the
analytic field is `1/(1 + e^(x − t/2))`. From `s + 1 ≤ e^s` alone, `band`
proves `2/5 ≤ u ≤ 3/5` there for every stream the circuit reconstructs from
the front's slice, and `not_below` refutes `u ≤ 27/50` at the corner
`(1/6, −1/8)`, where `u = 1/(1 + e^(−5/24)) > 29/53`.

Scope: the identification is of the formal stream's analytic field with a
closed form on the box; nothing is claimed about the real Burgers equation or
its classical solutions. The formal stream from a polynomial profile stays
divergent and uncertified; no majorant discovery.

```sh
lake build Gimle.Asgard.Tests.ColeHopf
```

## Example

[FormalHeat.lean](../Gimle/Asgard/Examples/FormalHeat.lean) checks `u=x²+2t`,
`u_t=u_xx=2`, and `u(0,x)=x²`. The compiled circuit returns `[2,u]` using the
supplied boundary; *Declared stream equations* above declares the same equation
and proves its solution set. On its own this is a formal coefficient theorem; the analytic
bridge for every polynomial profile is in *Polynomial heat evolution* above.

```sh
lake build Gimle.Asgard.Tests.Streams
```

Python lowering, JAX execution, mixed per-axis bases, stochastic shuffle algebra,
and delayed feedback are outside this interpretation.
