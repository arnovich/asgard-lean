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

## Example

[FormalHeat.lean](../Gimle/Asgard/Examples/FormalHeat.lean) checks `u=x²+2t`,
`u_t=u_xx=2`, and `u(0,x)=x²`. The compiled circuit returns `[2,u]` using the
supplied boundary. This is a formal coefficient theorem, not analytic PDE existence.

```sh
lake build Gimle.Asgard.Tests.Streams
```

Python lowering, JAX execution, mixed per-axis bases, stochastic shuffle algebra,
and delayed feedback are outside this interpretation.
