# Current integration queue

This is a compact operational view of
[`program.json`](program.json), not a second roadmap or a history log. The
schema-v4 ledger is canonical for assignment, dependencies, status, and
credit. This page should be rewritten when execution selection changes rather
than accumulating old snapshots.

## Release boundary

The canonical endpoint is
`MazurTorsion.rationalTorsion_hasMazurClassification`, the full rational
torsion group classification. `Challenge.Mazur.torsion_ncard_le` is a sibling
challenge corollary. Closing the numerical challenge alone does not complete
the classification endpoint.

## Selected WIP

The current execution revision has a WIP limit of three. Two honest packages
are selected, leaving one slot unused:

| Lane | Node slice | Current package | Current WP exit criterion | Lane goal |
|---|---|---|---|---|
| Canonical curve cohomology to Jacobians | `MT-TC-A3-DIVISOR-LINE-BUNDLE`, `MT-TC-B1-COHERENT-COHOMOLOGY`, `MT-TC-B2-RR-SERRE`, `MT-TC-C1-RELATIVE-COHOMOLOGY`, `MT-TC-C2-SYMMETRIC-POWERS`, `MT-TC-D1-PICARD-FUNCTOR`, `MT-TC-D2-PICARD-REPRESENTABILITY`, `MT-TC-E1-JACOBIAN-VARIETY`, `MT-TC-F1-ABEL-JACOBI` | `WP-MT-TC-B1-COHERENT-COHOMOLOGY-COHERENT-CORE` | Deliver a cover-independent canonical `K`-linear `H⁰`/`H¹` API, including `H⁰`/global-sections compatibility and coefficient-morphism and connecting-map linearity, to the proper-curve finiteness package. | A represented Jacobian and pointed Abel--Jacobi morphism compile with base-change consumers. |
| Represented `X₀(N)` vertical slice | `MT-EC-ISOGENY-WEIL`, `MT-X0-MODULI`, `MT-X0-INTEGRAL`, `MT-X0-JACOBIAN`, `MT-O49-TOWER` | `WP-MT-EC-ISOGENY-WEIL-WEIERSTRASS-GROUP-SCHEME` | Extend the glued affine-pair addition morphism over input points at infinity, prove the group laws and coordinate-point compatibility, and remove the supplied shadows from the named order-49 consumer. | An exact-order-49 point reaches an honest represented `X₀(49)` point without a supplied point-equivalence shadow. |

Only these two `current_work_package` values count as selected WIP. Other
packages whose status is `active` are ready, not assigned. Package weights
partition their parent node's fixed weight and award no independent credit.
The current-WP column is the immediate acceptance boundary; the lane goal is
the later end-to-end outcome and must not be read as the current package's exit
criterion.

For the group-law lane, `B₁₂ := y₁ + y₂ + a₁x₁ + a₃` and
`A₁₂ := x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄ - a₁y₂`. The identity
`(y₁ - y₂)B₁₂ = (x₁ - x₂)A₁₂` is now checked: `A₁₂/B₁₂` agrees with the
secant slope on the genuine intersection, the restricted projective addition
morphisms agree there, and the diagonal restriction agrees with tangent
doubling. All six pairwise restrictions of the four charts agree on their
exact pullbacks, and the resulting cover is glued to an actual affine-pair
addition morphism. The remaining work is projective-input infinity coverage,
the group laws, and coordinate-point compatibility.

The represented-moduli package now waits on the exact-torsion finite-flat
subgroup package. The generic Néron mapping-property and
admissible-filtration packages are integrated. Their Eisenstein-quotient
instantiation requires the actual Eisenstein quotient and its Néron model, so
it is blocked and does not occupy the spare WIP slot.

## Contributor-facing contracts

The ledger currently exposes two claimable contracts:

| Node | Mode | Scope |
|---|---|---|
| `MT-O49-TOWER` | ordinary, exclusive lease | Bridge exact order 49 to the represented and classified `X₀(49)` curve. |
| `MT-TC-A3-DIVISOR-LINE-BUNDLE` | nonexclusive research intention | Complete the divisor--line-bundle dictionary and Picard comparison. |

These contracts still obey their ledger dependencies and the process in
[`docs/CLAIMING.md`](../docs/CLAIMING.md). A contributor claim does not silently
expand the maintainer WIP selection.

## Paused contracts

| Node | Published contract |
|---|---|
| `MT-X11-COSET` | Five-coset bound on `X₁(11)` |
| `MT-X13-NONCUSP` | Noncuspidal rational points on `X₁(13)` |
| `MT-X18-NONCUSP` | Noncuspidal rational points on the order-18 curve |
| `MT-O25-EXCLUDE` | Exclusion of exact rational order 25 |
| `MT-O35-EXCLUDE` | Exclusion of exact rational order 35 |
| `MT-CYCLOTOMIC-UNRAMIFIED` | Cyclotomic unramified character extensions |

These declarations remain immutable and compiled, but they are unclaimable and
receive no maintainer proof volume until the canonical foundation lanes are
finished. Pausing does not delete, weaken, or complete a contract.

## Handoff rule

Every selected package must leave a small checked boundary, a named consumer,
and evidence sufficient for the ledger's completion rules. Scope, dependencies,
package status, and lane selection change only in `program.json`; generated and
narrative projections must then be synchronized.

Navigate via the [implementation status](../docs/IMPLEMENTATION_STATUS.md),
[progress method](../docs/PROGRESS_METHOD.md), [Blueprint](../blueprint/README.md),
or [coordination site](../site/README.md).
