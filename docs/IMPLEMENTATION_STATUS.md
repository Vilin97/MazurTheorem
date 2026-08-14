# Implementation status

This page is a compact view of the checked boundary. The canonical live record
is [`coordination/program.json`](../coordination/program.json); node status,
credit, dependencies, and execution assignments should be read there.

## Release boundary

The project target is the full group-structure theorem
`MazurTorsion.rationalTorsion_hasMazurClassification`. It says that the
rational torsion subgroup is isomorphic to one of the eleven cyclic groups or
four bicyclic groups in Mazur's classification.

`Challenge.Mazur.torsion_ncard_le` is an immutable sibling endpoint. It is a
useful numerical corollary, and it may also be proved through the direct
finite/infinite split, but it does not replace the full classification.

## Ledger-derived snapshot

- Integrated completion is **15.7%**: 157 of the fixed 1,000 points.
- Ecosystem readiness is **16%**.
- The audited baseline contains **1,879 Lean modules** and **1,805,762 Lean
  lines**.

Module and line counts describe the checked source surface; they are not
progress credit. The current credited foundation includes the imported Mazur
baseline, curve order support and product formula, product dimension for
abelian varieties, the finite-flat group-scheme base, the local prime-at-five
reduction chain, the ten-point enumeration over `F_5`, and the shared-pin
migration. Many later nodes already contain substantial checked infrastructure
without yet satisfying their named integration consumer.

## Current execution

The schema-v4 execution plan has a work-in-progress limit of three and selects
one current package in each lane:

| Lane | Current package | Exit criterion |
|---|---|---|
| Canonical curve cohomology to Jacobians | `WP-MT-TC-B1-COHERENT-COHOMOLOGY-COHERENT-CORE` | A represented Jacobian and pointed Abel--Jacobi morphism compile with base-change consumers. |
| Represented `X₀(N)` vertical slice | `WP-MT-X0-MODULI-REPRESENTED-MODULI` | An exact-order-49 point reaches an honest represented `X₀(49)` point without a supplied point-equivalence shadow. |
| Néron specialization and Eisenstein witness | `WP-MT-NERON-BASE-MAPPING-PROPERTY` | The private Eisenstein constructor produces the route-neutral degree-one witness consumed at 5. |

Package status is scheduling metadata. Only the three
`current_work_package` entries above are selected WIP; other packages marked
`active` are merely ready to run. Work-package weights partition their parent
node and award no independent credit.

## Open boundary

Release still requires the represented modular-curve and Jacobian foundations,
the Néron/Eisenstein formal-immersion witness, the remaining finite endpoints,
the prime-order argument, and final assembly of finiteness, point-order, and
group-structure results. The ncard corollary is assembled alongside, not in
place of, that theorem.

Six published contracts are intentionally paused:

- `MT-X11-COSET`, `MT-X13-NONCUSP`, and `MT-X18-NONCUSP`;
- `MT-O25-EXCLUDE` and `MT-O35-EXCLUDE`; and
- `MT-CYCLOTOMIC-UNRAMIFIED`.

Their declarations remain immutable and compiled, but they are unclaimable and
receive no maintainer proof volume while the canonical foundation lanes are
unfinished.

## Navigation

- [Owner queue](../coordination/OWNER_QUEUE.md): selected execution work only.
- [Progress method](PROGRESS_METHOD.md): the fixed accounting rules.
- [Claiming](CLAIMING.md): contributor leases and paused-contract policy.
- [Blueprint](../blueprint/README.md): mathematical DAG projection.
- [Informal proof](INFORMAL_PROOF.md): proof narrative.
- [Route audit](ROUTE_AUDIT.md): formal-immersion route decision.
- [Prior art](PRIOR_ART.md): provenance and source audit.

For local proof work, build the smallest affected module with
`LEAN_NUM_THREADS=1`; the repository quality gates remain the acceptance
authority.
