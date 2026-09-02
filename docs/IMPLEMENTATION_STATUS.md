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

- Integrated completion is **20.0%**: 200 of the fixed 1,000 points.
- Ecosystem readiness is **20%**.
- The audited baseline contains **1,948 Lean modules** and **1,965,336 Lean
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

| Lane | Current package | Current WP exit criterion | Lane goal |
|---|---|---|---|
| Canonical curve cohomology to Jacobians | `WP-MT-TC-B1-COHERENT-COHOMOLOGY-COHERENT-CORE` | Deliver a cover-independent canonical `K`-linear `H⁰`/`H¹` API, including `H⁰`/global-sections compatibility and coefficient-morphism and connecting-map linearity, to the proper-curve finiteness package. | A represented Jacobian and pointed Abel--Jacobi morphism compile with base-change consumers. |
| Represented `X₀(N)` vertical slice | `WP-MT-EC-ISOGENY-WEIL-WEIERSTRASS-GROUP-SCHEME` | Construct addition on the three remaining members of the full projective-product cover, prove the overlaps and global gluing, then prove the commutative group laws and coordinate-point compatibility and remove the supplied group-object and point-compatibility shadows from the named order-49 consumer. | An exact-order-49 point reaches an honest represented `X₀(49)` point without a supplied point-equivalence shadow. |

Package status is scheduling metadata. Only the two `current_work_package`
entries above are selected WIP; one slot is intentionally unused. The generic
Néron mapping-property and admissible-filtration packages are integrated, but
their Eisenstein instantiation is blocked until the actual Eisenstein quotient
and its Néron model exist. Other packages marked `active` are merely ready to run.
Work-package weights partition their parent node and award no independent
credit.

Execution revision `canonical-foundations-v4` records checked foundation
slices without changing the 172-point headline:

- In coherent cohomology, multiplication by global functions now gives a
  canonical cover-independent action in every degree. The `H⁰` comparison
  with global sections is canonically linear, and the older transported `H⁰`
  action is proved equal to that canonical action. The affine-cover Čech
  comparison is canonically linear in `H¹`, and a rational section now gives
  proper-curve `H¹` finite-dimensionality for the canonical structure-map field
  action. The 12-point core remains `active` because proper coherent `H⁰`
  finiteness and linear connecting maps are missing. The first genuine
  Riemann--Roch consumer belongs to B2. The final 12-point finiteness/base-change
  package remains `blocked`; no proper-cohomology base-change theorem is
  present.
- The all-degree zero-section-normalized relative Picard presheaf now has its
  associated fppf sheafification. For a smooth proper integral curve over a
  field and a supplied divisor-class/Picard equivalence, the checked
  residue-degree map gives an actual absolute Picard degree homomorphism, its
  exact degree-zero kernel, and a splitting from a rational section. The
  rational-section Abel--Jacobi consumer factors through that kernel before
  entering the sheafification at the base test object. This does not prove
  descent for the source presheaf, define a pullback-compatible relative degree
  or relative `Pic⁰`, construct a representing scheme, or remove the supplied
  divisor-class/Picard equivalence.
- In the Weierstrass group-scheme package, the universal secant formula defines
  an over-base morphism on the actual `D(x₁ - x₂)` open in the affine scheme
  product, and the tangent formula defines over-base doubling on
  `D(2y + a₁x + a₃)`. The complementary product-neighbourhood formula now
  defines addition on the actual open `D(B₁₂)`, where
  `B₁₂ := y₁ + y₂ + a₁x₁ + a₃`. On the exact intersection
  `D(B₁₂ * (x₁ - x₂))`, its restricted affine and projective morphisms
  agree with secant addition, and its diagonal restriction agrees with tangent
  doubling. Two denominator-cleared infinity-output morphisms now agree with
  those affine formulas on their exact intersections and with each other on
  their exact common principal open. The two cross-chart equalities are also
  checked, elliptic nonsingularity proves that the resulting four principal
  opens cover the entire affine-pair presentation, and the six compatible
  restrictions are glued to an actual affine-pair addition morphism.
  The full projective product is covered by the four products of the genuine
  `Y ≠ 0` and `Z ≠ 0` cubic charts; its standard-by-standard member is
  canonically identified with the affine-pair source and consumes that glued
  morphism. Addition on the other three members, their overlap equalities and
  global gluing, the group laws, and coordinate-point compatibility remain
  missing.
- The generic finite-translation layer constructs the actual quotient of a
  supplied commutative group scheme from an affine diagonal, a finite section
  action, an invariant affine atlas, and scheme-theoretic freeness. Geometric
  integrality descends from a geometrically integral source. Over an affine
  noetherian base, properness descends from a proper source, while smoothness
  follows separately from a flat, locally finite-type, geometrically reduced
  source. Its field-level abelian-variety wrapper is the named consumer. No
  canonical Weierstrass source, exact-torsion subgroup, arithmetic cyclic
  quotient instance, or arbitrary-base-change kernel law is inferred.
- For an actual proper commutative group model over a valuation ring,
  properness now identifies terminal integral points with points of an
  identified generic fibre. The specialization reducer and its prime-five
  consumer compile, but torsion-specialization injectivity remains a supplied
  hypothesis. No canonical cyclic or Eisenstein proper quotient model is
  instantiated, and neither the proper-model result nor the generic
  finite-translation quotient geometry provides the Néron mapping property for
  arbitrary smooth test schemes.
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

The order-eighteen endpoint is now unconditional. An explicit elliptic quotient
of the `X₁(18)` sextic over the real cubic field is controlled by a checked
dyadic `x-T` descent; triviality of its descent image gives rank zero and
finiteness. Reduction at a degree-one prime above seventeen, visible
seven-torsion, exclusion of three-torsion, and the checked quotient fibers then
rule out every noncuspidal rational point. The resulting exact-order-eighteen
theorem is consumed directly by the rational-torsion point-order reduction.

The checked route-neutral prime collision is
`MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_formalImmersionAtFive`.
`DegreeOneFormalImmersionWitness` and its private Eisenstein constructor remain
proposed packaging, not checked declarations. The quotient construction and
Néron specialization are independent prerequisites of the final collision;
the quotient no longer carries the redundant dependency on the downstream
specialization node.

For order `35`, the explicit infinity chart over `ZMod 11` now reaches an
unconditional local theorem:
`InfinityChartCuspAtEleven.quotientMorphism_isFormalImmersionAt_cusp` proves
formal immersion for the actual affine `Spec` quotient map at the selected
cusp. The remaining gap is not its cusp algebra; it is the represented modular
classifying map and special-fibre chart comparison, followed by the global
quotient and specialization inputs.

For order `25`, normalization at the fivefold multiple now puts a hypothetical
point of exact order twenty-five on the diagonal order-five Tate family. An
explicit paired Vélu calculation constructs its degree-five quotient, proves
the quotient discriminant, and defines the denominator-safe point map. Checked
homogeneous doubling identities, kernel-translation invariance, and negation
compatibility then prove that the transported order-twenty-five point maps to
a rational point of exact order five on the quotient. This produces the second
rational five-level structure needed for a direct parameter comparison without
asserting that a Fricke involution preserves a rational generator. The next gap
on this route is to normalize the quotient image and extract the resulting
arithmetic relation between the two order-five parameters.

The checked Lécacheux orbit route also recovers the invariant
parameter from the five orbit coordinates and proves that the six cyclic
relations force the two selected coordinates to satisfy Lehmer's quintic.
Consequently `no_orderTwentyFiveBrunaultOrbit_of_threeIntegral` rules out the
orbit as soon as its recovered invariant is integral at three, without taking
the two root facts as assumptions. Exact-order separation already proves
`x₀ ≠ 1`, and `orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order`
together with `orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order` now
proves two of the five cyclic relations for the explicit Tate cross-ratios,
and `orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order` proves a third,
while `orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order` proves the
fourth independent relation, all by kernel-checked coefficient certificates.
The remaining cyclic relation follows algebraically from those four and norm
one.
`orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order` also proves their
norm-one relation. Thus
`no_orderTwentyFive_marked_order_of_orbitParameter_threeIntegral` discharges
the order-25 exclusion whenever the recovered parameter is integral at three.
The remaining endpoint gap is the Fricke transport used when `5/n`, rather
than `n`, is the integral parameter.

Five published contracts are intentionally paused:

- `MT-X11-COSET` and `MT-X13-NONCUSP`;
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
