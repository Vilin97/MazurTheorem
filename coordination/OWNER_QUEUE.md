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
| Canonical curve cohomology to Jacobians | `MT-TC-A3-DIVISOR-LINE-BUNDLE`, `MT-TC-B1-COHERENT-COHOMOLOGY`, `MT-TC-B2-RR-SERRE`, `MT-TC-C1-RELATIVE-COHOMOLOGY`, `MT-TC-C2-SYMMETRIC-POWERS`, `MT-TC-D1-PICARD-FUNCTOR`, `MT-TC-D2-PICARD-REPRESENTABILITY`, `MT-TC-E1-JACOBIAN-VARIETY`, `MT-TC-F1-ABEL-JACOBI` | `WP-MT-TC-B1-COHERENT-COHOMOLOGY-CURVE-FINITENESS` | Using the canonical core actions, expose proper coherent `H⁰`/`H¹` finite-dimensionality and `Hⁿ`-vanishing for `n ≥ 2` together with the exact low-degree cohomology base-change comparison consumed downstream. | A represented Jacobian and pointed Abel--Jacobi morphism compile with base-change consumers. |
| Represented `X₀(N)` vertical slice | `MT-EC-ISOGENY-WEIL`, `MT-X0-MODULI`, `MT-X0-INTEGRAL`, `MT-X0-JACOBIAN` | `WP-MT-EC-ISOGENY-WEIL-WEIERSTRASS-GROUP-SCHEME` | Regularize the checked secant and doubling triples on the three projective-pair members meeting infinity, prove the overlaps and global gluing, then prove the group laws and coordinate-point compatibility and remove the supplied shadows from the named order-49 consumer. | Represented `X₀(N)` geometry reaches the integral-model and Jacobian layers without supplied point-equivalence shadows. |

Only these two `current_work_package` values count as selected WIP. Other
packages whose status is `active` are ready, not assigned. Package weights
partition their parent node's fixed weight and award no independent credit.
The current-WP column is the immediate acceptance boundary; the lane goal is
the later end-to-end outcome and must not be read as the current package's exit
criterion.

The coherent core package is integrated. Multiplication by global functions
now acts canonically in every degree, coefficient maps are linear, and
naturality of the genuine Ext connecting class makes the boundary map of every
short exact sequence linear. The proper-curve layer consumes its
ground-field-linear `H⁰ → H¹` specialization and proves the image
finite-dimensional for a pointed smooth proper curve. The selected next
package must supply proper coherent `H⁰` finiteness and the exact low-degree
base-change comparison; `H¹` finiteness and vanishing above degree one are
already checked.

For the group-law lane, `B₁₂ := y₁ + y₂ + a₁x₁ + a₃` and
`A₁₂ := x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄ - a₁y₂`. The identity
`(y₁ - y₂)B₁₂ = (x₁ - x₂)A₁₂` is now checked: `A₁₂/B₁₂` agrees with the
secant slope on the genuine intersection, the restricted projective addition
morphisms agree there, and the diagonal restriction agrees with tangent
doubling. All six pairwise restrictions of the four charts agree on their
exact pullbacks, and the resulting cover is glued to an actual affine-pair
addition morphism. The full projective product now has its actual four-member
coordinate-chart cover, and its standard-by-standard member is identified
with that affine-pair source. Every member is also identified with the spectrum
of the tensor product of its two chart coordinate rings. The checked formula
constructor turns a `K`-algebra map into an automatically over-base scheme
morphism, and its two projection consumers verify the orientation. Each chart
also carries its normalized universal homogeneous point; after tensoring, both
universal inputs satisfy the mapped cubic equation. For elliptic curves, the
four tensor rings are integral domains. The evaluated homogeneous secant triple
and both doubling triples satisfy the cubic equation, while the secant output
`Z` coordinate obeys the exact cubic cross-difference denominator identity.
Because those raw triples can still vanish on their base loci, the remaining
work is to regularize them on principal opens, supply the three local morphisms
through the coordinate interface, prove all new overlap equalities and global
gluing, then prove the group laws and coordinate-point compatibility.

The represented-moduli package now waits on the exact-torsion finite-flat
subgroup package. The generic Néron mapping-property and
admissible-filtration packages are integrated. Their Eisenstein-quotient
instantiation requires the actual Eisenstein quotient and its Néron model, so
it is blocked and does not occupy the spare WIP slot.

## Contributor-facing contracts

The ledger currently exposes one claimable contract:

| Node | Mode | Scope |
|---|---|---|
| `MT-TC-A3-DIVISOR-LINE-BUNDLE` | nonexclusive research intention | Complete the divisor--line-bundle dictionary and Picard comparison. |

These contracts still obey their ledger dependencies and the process in
[`docs/CLAIMING.md`](../docs/CLAIMING.md). A contributor claim does not silently
expand the maintainer WIP selection.

## Paused contracts

| Node | Published contract |
|---|---|
| `MT-X11-COSET` | Five-coset bound on `X₁(11)` |
| `MT-X13-NONCUSP` | Noncuspidal rational points on `X₁(13)` |
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
