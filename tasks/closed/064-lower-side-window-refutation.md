---
title: The lower-side refutation of a field band from the checked window
state: closed
priority: low
labels: [streams, lean]
related: ["063"]
---

# The lower-side refutation of a field band from the checked window

## Context

Task 063 gave the field-band roots `front_band_of_window` and
`front_above_of_window`. The decider in gimle-forseti (task 190) refutes a
band on either side; below the band it had to write the argument out in its
template from `front_truncation`, `frontValue_eq` and `circuit_front`, since
the library states only the upper side. Both sides should rest on one
audited lemma each (gimle-forseti task 192).

## Outcome

- `ColeHopf.front_below_of_window`: with the premises of
  `front_above_of_window` and `frontValue ν terms Q N p + ε < lo`, the band
  `lo ≤ u` fails on the box for every reconstruction; audited to the three
  standard axioms in `Tests/ColeHopf.lean`; one line in `docs/formal-streams.md`
- released as v1.12.0

## Conversation

### note · claude/17d157a0 · 2026-10-02T10:40:00Z

Closed with PR #28, released as v1.12.0.
