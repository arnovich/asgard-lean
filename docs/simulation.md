# Optional Python simulation

Requires Linux or macOS and a separately supplied Python Asgard wheel containing
`gimle.asgard.lean_worker` with v1/v2 support. The worker is **not bundled here**.
Core proofs and diagrams do not need it.

## Install and run

Install a compatible wheel in a dedicated environment (not an editable checkout):

```sh
python3 -m venv /absolute/path/to/venv
/absolute/path/to/venv/bin/python -m pip install /path/to/gimle_asgard.whl
lake build simulation_demo rational_simulation_demo three_state_demo
lake exe simulation_demo /absolute/path/to/venv/bin/python
```

Select a trusted interpreter by absolute path. The client uses isolated Python,
request/response limits, deadlines, and process-group cleanup; it is not a sandbox.

## Protocols and guarantees

| Protocol | Exact request data | Numerical execution |
| --- | --- | --- |
| v1 | Integer coefficients with magnitude at most `2^53` | Point evaluation or simultaneous Euler steps |
| v2 | Canonical rational coefficients; exact initial state/start for Euler | Converts to binary64; unsupported or nonfinite conversions fail |

- Responses must match the original request, shapes, finite values, and time grid.
- Euler returns the initial row plus one row per step; observations preserve declared order.
- Structural codec proofs do not certify JSON parsing, Python/JAX execution, or Euler accuracy.
- Samples are observations, not error certificates or trajectory proofs.

See [RationalExecution.lean](../Gimle/Asgard/Examples/RationalExecution.lean) for model
adapters; [`Simulation/`](../Gimle/Asgard/Simulation/) contains the protocol and client.

## Three-state output

```sh
mkdir -p .lake/build/three-state
.lake/build/bin/three_state_demo /absolute/path/to/venv/bin/python > .lake/build/three-state/run.json
```

The demo produces 33 rows from `t=2` to `t=6`, including energy returned by
the compiled observation circuit. Generated output stays in ignored `.lake/`.
