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
| Represented `X₀(N)` vertical slice | `MT-EC-ISOGENY-WEIL`, `MT-X0-MODULI`, `MT-X0-INTEGRAL`, `MT-X0-JACOBIAN` | `WP-MT-EC-ISOGENY-WEIL-WEIERSTRASS-GROUP-SCHEME` | Finish the remaining projective-pair overlaps and glue the checked local addition laws globally, then prove the group laws and coordinate-point compatibility and remove the supplied shadows from the named order-49 consumer. | Represented `X₀(N)` geometry reaches the integral-model and Jacobian layers without supplied point-equivalence shadows. |

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
with that affine-pair source. The standard tensor ring and the four-coordinate
affine-pair ring are now explicitly equivalent as `K`-algebras: all four
universal affine coordinates and the secant denominator are identified, the
induced spectrum map is proved equal to the canonical geometric comparison,
and the raw homogeneous addition triple transports across that equivalence.
On the raw output-`Z` localization, the denominator cube gives a canonical map
to the checked secant chart. Both its source map and its cubic-valued formula
agree exactly, so the normalized raw morphism is now proved to be the
restriction of the globally glued standard-pair addition law.
The universal secant denominator is now also proved nonzero. This makes the
exact output-`YZ` overlap dense in the raw output-`Y` open; separatedness over
the coefficient field extends the overlap equality to that entire open. Thus
both raw output normalizations on the standard input pair are checked
restrictions of the same standard-pair addition law.
The standard and infinity cubic charts now also meet through a checked exact
`D(YZ)` quotient: the two chart equations generate the same overlap ideal,
both restriction maps are principal open immersions, and their composites into
the concrete cubic agree. Tensoring this overlap with an unchanged second
chart proves that the first normalized input changes by `Y/Z` and that the raw
addition triple changes by `(Y/Z)²`. Tensoring on the other side now proves
the symmetric statement for the second input and the same square-scaling law
for the raw triple. Tensor localization now realizes all four restrictions as
actual open immersions into the adjacent pair charts; projection
factorizations prove that the two descriptions of each factorwise overlap
have the same composite into the full projective product. On both selected
secant output opens of every factorwise overlap, the transition coordinate is
a unit, the two source restrictions are open immersions with the same map into
the full product, and cancellation of its square proves equality of the
normalized points and genuine cubic-valued morphisms. A sharper primewise
cover now replaces the non-additive doubling opens: each mixed chart is
covered by its transition-to-standard locus and secant output `Z`, while the
infinity pair is covered by the both-standard locus, `D(B∞)`, and secant
output `Z`. The both-standard locus now has its exact scheme model: the tensor
square of the cubic overlap is proved to be the required principal
localization of both the standard and infinity pair rings, and its maps to
both pair charts are open immersions. Their two intrinsic overlap projections
agree with both chart descriptions, so the induced maps into the full
projective product are equal. The infinity pair now has an actual finite open
cover by this double-standard source, the genuine regular output-`Y` source,
and the secant output-`Z` source. The residual prime calculation shows that
the regular output is `-1` whenever the other two opens miss, and an indexed
family selects the genuine local addition morphism on every member. Both mixed
pair charts now also have actual two-member scheme covers: their exact
transition-to-standard sources carry the transported standard-pair law, while
their secant output-`Z` sources carry the normalized secant law. Indexed
families select these genuine local morphisms. On each mixed chart, the exact
input/output localization is now identified with the categorical pullback of
the two cover members. The local laws are compatible there and glue to a
genuine morphism on the entire mixed chart, with both transition and secant
restrictions checked. Compatibility on the infinity-pair cover and global
four-chart gluing are the next atlas step.
Every member is also identified with the spectrum
of the tensor product of its two chart coordinate rings. The checked formula
constructor turns a `K`-algebra map into an automatically over-base scheme
morphism, and its two projection consumers verify the orientation. Each chart
also carries its normalized universal homogeneous point; after tensoring, both
universal inputs satisfy the mapped cubic equation. For elliptic curves, the
four tensor rings are integral domains. The evaluated homogeneous secant triple
and both doubling triples satisfy the cubic equation, while the secant output
`Z` coordinate obeys the exact cubic cross-difference denominator identity.
A normalized-point constructor now turns either quotient output chart into a
`K`-algebra map. After inverting the secant output `Y` or `Z` coordinate, this
supplies actual over-base morphisms from both principal opens of every pair
member into the cubic. The same construction supplies actual over-base
morphisms from the two output-coordinate principal opens of the first-input
doubling triple. A primewise fraction-field argument now proves that these four
principal opens jointly cover every pair member, and the two secant
normalizations agree as actual cubic-valued morphisms on their exact `YZ`
overlap. First-input doubling agrees with addition only on the diagonal, so
its unrestricted principal opens are a nonvanishing certificate rather than
an addition atlas. On the infinity-by-infinity member, the two cubic equations
now give `(z₁ - z₂) B∞ = (x₁ - x₂) A∞`; the localization `D(B∞)` carries the
regular slope `A∞ / B∞`. Its denominator restricts on the diagonal to the
projective `Z` partial derivative, while a checked evaluation through the
localization shows that `(O, O)` lies in this neighborhood and has slope zero.
A denominator-free third-intersection calculation turns that slope into an
addition triple satisfying the homogeneous cubic without cancelling
`x₁ - x₂` or its new homogeneous coordinate. Localizing at its output `Y`
coordinate gives an actual open neighborhood containing `(O, O)` and a genuine
over-base addition morphism into the cubic. The old secant triple pulls back to
`(x₁ - x₂)³` times the regular triple, and on `D(B∞ · Ysec)` the two source
restrictions are open immersions with equal normalized points and equal actual
cubic-valued morphisms. The remaining work is to prove pairwise compatibility
on the actual infinity-pair addition cover, establish compatibility of the
four full chart morphisms, and perform global gluing, then prove the group laws
and coordinate-point compatibility.

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
