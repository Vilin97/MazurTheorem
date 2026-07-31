# Architecture

The project separates proof, contracts, coordination, and presentation.

```text
Mathlib / attributed exact-pin ports
                 │
                 ▼
       MazurTorsion checked library
                 │
        named consumer declarations
                 │
                 ▼
        final cardinality endpoint

Challenge/ ── immutable open contracts
coordination/program.json ── weighted DAG and claims
blueprint/ ── mathematical exposition
site/ ── generated public coordination view
upstream/tauceti/ ── separate pin and interfaces
```

Checked implementation never imports `Challenge`. Challenge statements import
only the minimum implementation or Mathlib modules needed to state the
contract. When solved, the implementation is public in `MazurTorsion/` and
the challenge becomes a one-line bridge.

The coordination JSON is the source for progress, readiness, cards, and
dependency edges. The site is a view, not a second database.

Contract identifiers, imports, signatures, mathematical meaning,
destinations, and published acceptance consumers are immutable across pull
requests (additional consumers may be appended). A solved contract remains in
the ledger with `status: "done"` and `claimable: false`; only its proof body
and lifecycle/completion fields change.
