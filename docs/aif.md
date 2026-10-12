# AIF source and feedback circuits

[`Examples/AIF.lean`](../Gimle/Asgard/Examples/AIF.lean) compiles the physical
species equations in order `(x1,x2,z1,z2)`:

```
x1' = z1 - x1
x2' = x1 - x2
z1' = 2 - eta*z1*z2
z2' = x2 - eta*z1*z2
```

The named source fixes plant gain one and reference two. The field's five input
coordinates are `(eta,x1,x2,z1,z2)`. Eta is a real runtime input; it is not
restricted to a rational specialization. The source-satisfaction theorem and
`field_equations` identify the compiled primitive circuit with these equations.

`feedback` closes this same compiled field through four integrators.
`Realizes eta state` fixes the eta driver to one constant signal and all initial
species to zero. `realizes_iff` proves equivalence with the component ODEs on
the forward half-line, including within-domain derivatives at time zero.
`output` reads the physical plant species x2.

The [tests](../Gimle/Asgard/Tests/AIF.lean) check the exact startup velocity,
sequestration, parameter dependence, initial-state extraction and output index.
These are semantic equivalences, not existence or uniqueness theorems. They do
not prove nonnegative species, startup tube membership or an output bound.
Those property obligations belong to Forseti's ongoing Task 248 research.

Validation passed on Lean 4.32.1: the full build (7,024 jobs, 566 axiom reports)
and all four required optional executable targets (6,811 jobs, 51 reports).
The six new implementation lemmas and two named regressions use only the
permitted standard axioms. Mathematical, integration and evidence review found
no blockers after the final source/artifact and compiler/import audit.
Verification SHA-256:
`d51ad168225cbd611db6db16cadc3e26159674ed778688f7163d4332858fa93a`.
This research checkpoint does not change Forseti's dependency pin or enroll a
new production checking environment.
