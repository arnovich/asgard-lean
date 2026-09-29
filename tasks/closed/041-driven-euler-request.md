---
title: Carry declared drivers in the Lean Euler simulation request
state: closed
priority: medium
labels: [simulation, drivers, execution]
depends_on: ["031"]
related: ["gimle-asgard/259", "gimle-forseti/170"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Driven continuous models", fixes the execution contract for
driven models. Once 031 lets a declaration name a driver, the Lean Euler
request still refuses it: `Rational.Request` and the worker require as many
inputs as states, all with the state role. Nothing can simulate a driven model.

## Outcome

- `Simulation/Rational.lean`'s request gains driver roles and one rational
  driver sample per interval on the existing uniform grid, under a new request
  version; an old-version request is decoded unchanged.
- The request and its decoded response state that the runtime holds each sample
  on `[t_i, t_{i+1})` and that this held sequence is not the declared driver.
- A request whose sample count or driver ids do not match the declaration is
  refused with a named diagnostic, tested.
- No new binary64 conversion point beyond `numericalValue`; the schema doc
  lists the points.
- Full `lake build` is clean and axiom audits show only standard axioms.

## Conversation

### note · claude/031 · 2026-09-29T08:22:19Z

031 flattens drivers into coordinates `DriverBinding.ports`: each driver, then
its derivative port, before the states. A derivative port is therefore one of
the sampled driver coordinates, and a held sample of `du` is not the
derivative of a held sample of `u`, so the zero-order-hold disclaimer covers
derivative ports too. `Evolution.Admitted` never holds for held samples; the
request must not claim it.
