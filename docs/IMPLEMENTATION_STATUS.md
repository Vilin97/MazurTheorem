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

- Integrated completion is **17.2%**: 172 of the fixed 1,000 points.
- Ecosystem readiness is **18%**.
- The audited baseline contains **1,870 Lean modules** and **1,788,023 Lean
  lines**.

Module and line counts describe the checked source surface; they are not
progress credit. The current credited foundation includes the imported Mazur
baseline, curve order support and product formula, product dimension for
abelian varieties, the finite-flat group-scheme base, the local prime-at-five
reduction chain, exact-order specialization at good reduction, the ten-point
enumeration over `F_5`, and the shared-pin migration. Many later nodes already
contain substantial checked infrastructure without yet satisfying their named
integration consumer.

## Current execution

The schema-v4 execution plan has a work-in-progress limit of three and selects
two current packages:

| Lane | Current package | Exit criterion |
|---|---|---|
| Canonical curve cohomology to Jacobians | `WP-MT-TC-B1-COHERENT-COHOMOLOGY-COHERENT-CORE` | A represented Jacobian and pointed Abel--Jacobi morphism compile with base-change consumers. |
| Represented `X₀(N)` vertical slice | `WP-MT-EC-ISOGENY-WEIL-WEIERSTRASS-GROUP-SCHEME` | An exact-order-49 point reaches an honest represented `X₀(49)` point without a supplied point-equivalence shadow. |

Package status is scheduling metadata. Only the two `current_work_package`
entries above are selected WIP; one slot is intentionally unused. The generic
Néron mapping-property and admissible-filtration packages are integrated, but
their Eisenstein instantiation is blocked until the actual quotient and Néron
models exist. Other packages marked `active` are merely ready to run.
Work-package weights partition their parent node and award no independent
credit.

Execution revision `canonical-foundations-v4` records three checked foundation
slices without changing the 172-point headline:

- In coherent cohomology, multiplication by global functions now gives a
  canonical cover-independent action in every degree, and the structure map
  gives canonical field-linear `H¹` functoriality. The 11-point affine-cover
  Čech comparison package is marked `integrated` because its genuine `H¹`
  comparison is consumed by finite-generation transfer. The 12-point core
  remains `active`: the existing `H⁰` and proper-curve finiteness results use
  transported actions, their compatibility with the canonical actions is open,
  and proper coherent `H⁰` finiteness and linear connecting maps are missing.
  The first genuine Riemann--Roch consumer belongs to B2. The final 12-point
  finiteness/base-change package remains `blocked`; no proper-cohomology
  base-change theorem is present.
- In the Weierstrass group-scheme package, the universal secant formula now
  defines genuine affine and projective morphisms on one explicit chart. The
  package remains `active` because the product-open identification, tangent and
  infinity charts, overlap proofs, gluing, and group laws are still missing.
- The represented polynomial cusp chart now has the genuine sections
  `sectionAt`, their checked closed-point collision, and the named consumer
  `valuation_j_le_one_of_polynomialCuspSectionAtFive`. These are local chart
  facts only: they construct neither represented `X₀`, its generalized-elliptic
  compactification, nor the missing `Γ₀` classifier. Both `MT-X0-MODULI` and
  `MT-X0-INTEGRAL` therefore remain `blocked`.

## Open boundary

Release still requires the represented modular-curve and Jacobian foundations,
the Néron/Eisenstein formal-immersion witness, the remaining finite endpoints,
the prime-order argument, and final group-structure assembly. The two-point
`MazurTorsion.rationalTorsion_finite` package is integrated: rational Northcott
and the approximate parallelogram law feed Mathlib's direct finite-torsion
descent theorem, without full Mordell--Weil or finite generation. A separate
four-point generic finite-abelian rank-two package is integrated from the
finite-abelian decomposition, allowed orders, and exactly `c2Cube`, `c3Square`,
`c5Square`, and `c7Square`. Its cross-module rational adapter compiles
conditionally, but its two-point WP remains blocked on the point-order, `h55`,
and `h77` inputs owned by API integration. The later classification
additionally consumes `c4Square`, `c2c10`, and `c2c12`, then the ncard bridge
follows as a corollary, not a replacement for the classification theorem.

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
