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
