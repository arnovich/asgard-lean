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

## Substitution and truncation

- `seriesCompose` substitutes one selected variable. The inner series must have
  **zero entire multivariate constant coefficient**: `t ↦ x` is valid; `x ↦ 1+x` is rejected.
- Invalid substitutions remain invalid through discard and multiplication by zero.
- The `convolution` aliases mean this substitution, not discrete-kernel convolution.
- `truncate_inside` proves agreement only inside the requested coefficient window.
  Derivatives may need coefficients beyond it; substitution may move degrees between axes.
- No analytic convergence, Taylor identification, or numerical truncation bound is implied.

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
solution. Analytic realization from a checked majorant is task 025.

```sh
lake build Gimle.Asgard.Tests.StreamRealization
```

## Example

[FormalHeat.lean](../Gimle/Asgard/Examples/FormalHeat.lean) checks `u=x²+2t`,
`u_t=u_xx=2`, and `u(0,x)=x²`. The compiled circuit returns `[2,u]` using the
supplied boundary. On its own this is a formal coefficient theorem; the analytic
bridge for every polynomial profile is in *Polynomial heat evolution* above.

```sh
lake build Gimle.Asgard.Tests.Streams
```

Python lowering, JAX execution, mixed per-axis bases, stochastic shuffle algebra,
and delayed feedback are outside this interpretation.
