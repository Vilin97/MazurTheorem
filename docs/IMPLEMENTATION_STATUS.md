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
- The audited baseline contains **1,992 Lean modules** and **2,072,616 Lean
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
| Canonical curve cohomology to Jacobians | `WP-MT-TC-B1-COHERENT-COHOMOLOGY-CURVE-FINITENESS` | Using the canonical core actions, expose proper coherent `H⁰`/`H¹` finite-dimensionality and `Hⁿ`-vanishing for `n ≥ 2` together with the exact low-degree cohomology base-change comparison consumed downstream. | A represented Jacobian and pointed Abel--Jacobi morphism compile with base-change consumers. |
| Represented `X₀(N)` vertical slice | `WP-MT-EC-ISOGENY-WEIL-WEIERSTRASS-GROUP-SCHEME` | The canonical commutative projective group object and coordinate-point addition compatibility are checked; remove the supplied group-object and point-compatibility shadows from the named order-49 consumer. | An exact-order-49 point reaches an honest represented `X₀(49)` point without a supplied point-equivalence shadow. |

Package status is scheduling metadata. Only the two `current_work_package`
entries above are selected WIP; one slot is intentionally unused. The generic
Néron mapping-property and admissible-filtration packages are integrated, but
their Eisenstein instantiation is blocked until the actual Eisenstein quotient
and its Néron model exist. Other packages marked `active` are merely ready to run.
Work-package weights partition their parent node and award no independent
credit.

Execution revision `canonical-foundations-v4` records checked foundation
slices without changing the 200-point headline:

- In coherent cohomology, multiplication by global functions now gives a
  canonical cover-independent action in every degree. The `H⁰` comparison
  with global sections is canonically linear, and the older transported `H⁰`
  action is proved equal to that canonical action. The affine-cover Čech
  comparison is canonically linear in `H¹`, and a rational section now gives
  proper-curve `H¹` finite-dimensionality for the canonical structure-map field
  action. Coefficient morphisms are linear in `H¹`, and naturality of the
  actual Ext connecting class makes every short-exact-sequence boundary linear
  over global functions. Its canonical ground-field `H⁰ → H¹` specialization
  has a pointed proper-curve finite-dimensional-image consumer. The 12-point
  core is therefore integrated. The final 12-point finiteness/base-change
  package is active: proper coherent `H⁰` finiteness and the exact low-degree
  base-change comparison remain missing, while vanishing above degree one is
  already checked. The first genuine Riemann--Roch consumer belongs to B2.
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
  morphism. The standard tensor coordinate ring is now explicitly equivalent
  as a `K`-algebra to the four-coordinate affine-pair ring. This comparison
  identifies all four universal affine coordinates and the secant denominator,
  its spectrum map is exactly the canonical geometric identification, and it
  transports the raw homogeneous addition triple. On the raw output-`Z`
  localization, the resulting denominator cube induces the canonical map to
  the checked secant chart; both the source factorization and addition formula
  commute, proving that the normalized raw morphism is exactly the restriction
  of the glued standard-pair addition. The universal denominator is nonzero,
  so the exact output-`YZ` overlap is dense in the raw output-`Y` open.
  Separatedness of the cubic over the coefficient field extends equality from
  that overlap, proving that the entire output-`Y` morphism is the other
  restriction of the same standard-pair addition law. The standard and
  infinity cubic charts now have an exact common `D(YZ)` quotient: their
  mapped cubic ideals agree, both restriction maps are principal open
  immersions, and the resulting cubic-valued morphisms coincide. After
  tensoring with an unchanged second chart, the first universal input scales
  by `Y/Z` and the raw homogeneous addition triple scales by `(Y/Z)²`.
  Tensoring the same overlap on the right proves the symmetric second-input
  transition and the same square-scaling law. Localization survives both
  tensor constructions, giving four actual open immersions into adjacent pair
  charts. The two descriptions of each factorwise overlap are proved to have
  equal composites into the full projective product. On either selected
  secant output open of every factorwise overlap, cancellation of the
  invertible square transition factor proves equality of the normalized
  points. Both restrictions are open immersions with equal maps into the full
  product and equal genuine cubic-valued morphisms. A primewise replacement
  cover now avoids treating the doubling formulas as addition: each mixed
  chart is covered by its transition-to-standard locus and the secant
  output-`Z` locus; the infinity pair is covered by the both-standard locus,
  the regular `D(B∞)` neighborhood, and secant output `Z`. The both-standard
  term is now an actual affine scheme: the tensor square of the exact cubic
  overlap is a principal localization of both adjacent pair rings, so its
  maps to the standard-by-standard and infinity-by-infinity charts are open
  immersions. Both maps recover the same intrinsic factor projections, and
  pullback extensionality proves that their composites into the full
  projective product agree. The infinity-pair refinement is now an actual
  three-member scheme open cover: the exact double-standard source, the
  regular output-`Y` neighborhood, and the secant output-`Z` source. Outside
  the first and third opens both inputs reduce to infinity, where the regular
  output `Y` is proved to be `-1`; an indexed family assigns the corresponding
  genuine addition morphism to each cover member. Each mixed pair chart now
  also has an actual two-member scheme cover by its exact
  transition-to-standard source and secant output-`Z` source. The former
  transports the standard-pair addition law, the latter uses the normalized
  secant law, and indexed families supply the genuine local morphisms. The
  exact first- or second-input/output localization is proved to be the
  categorical pullback of those members. Their laws are compatible and glue
  to genuine morphisms on both entire mixed charts; named restriction
  theorems recover both the transported standard law and normalized secant
  law. On the infinity-pair cover, the regular-origin/secant-`Z`,
  double-standard/secant-`Z`, and double-standard/regular-origin intersections
  are identified with the exact categorical pullbacks. The local laws are
  compatible on every ordered pair and glue to a genuine morphism on the
  whole infinity-by-infinity chart, with named restriction theorems for all
  three cover members. The four resulting chart morphisms agree on all six
  categorical intersections. The full sixteen-case compatibility family now
  glues to a global addition morphism on the projective cubic fibre square;
  its restriction to every chart and its compatibility with the structural
  morphism to `Spec K` are checked. Every
  product member is now identified with the spectrum of the
  tensor product of its two chart coordinate rings. A checked constructor
  turns each `K`-algebra coordinate formula into an automatically over-base
  scheme morphism, and its left/right inclusion consumers recover the two
  geometric projections. Each quotient chart has a normalized universal
  homogeneous point, and both tensor-embedded inputs satisfy the mapped cubic
  equation in every pair ring. Those pair rings are integral domains for an
  elliptic cubic. The evaluated homogeneous secant triple and both doubling
  triples satisfy the mapped cubic equation, and the secant output `Z`
  coordinate obeys the exact cubic cross-difference denominator identity.
  A normalized-point quotient-chart constructor turns either selected output
  chart into a `K`-algebra map. Inverting the secant output `Y` or `Z`
  coordinate therefore gives actual over-base morphisms from both principal
  opens of every pair member into the cubic. The same construction gives
  actual over-base morphisms from both output-coordinate principal opens of
  the first-input doubling triple. A primewise fraction-field argument proves
  that these four opens jointly cover every pair member. The two secant output
  normalizations also agree as actual cubic-valued morphisms on their exact
  `YZ` overlap. Since first-input doubling agrees with addition only on the
  diagonal, its unrestricted opens are not an addition atlas. On the
  infinity-by-infinity member, a checked factorization of the two cubic
  equations makes `A∞ / B∞` regular on `D(B∞)`. The denominator is the
  projective `Z` partial derivative along the diagonal, and explicit
  evaluation through the localization proves that this neighborhood contains
  `(O, O)` with slope zero. A denominator-free third-intersection calculation
  gives homogeneous addition coordinates satisfying the cubic throughout this
  neighborhood. Their output-`Y` principal open is an actual neighborhood of
  `(O, O)` carrying a genuine over-base addition morphism. The pulled-back raw
  secant triple is exactly `(x₁ - x₂)³` times this regular triple. On the
  exact principal overlap `D(B∞ · Ysec)`, both source restrictions are open
  immersions into the same pair chart, their normalized output points agree,
  and the two actual cubic-valued morphisms are equal. Global addition is now
  constructed. The projective infinity section is now proved to be its
  categorical left and right unit by explicit mixed-chart calculations and
  dense-chart extension. Swapping the two tensor factors negates the raw
  secant triple by one common scalar, so normalization and a second dense-open
  extension prove categorical commutativity. On the dense principal open where
  the universal vertical derivative is invertible, adding the universal point
  to its checked negation is the infinity section; separatedness extends the
  result globally, and commutativity supplies the symmetric inverse law.
  Associativity and coordinate-point compatibility are now checked; the
  remaining package step is to remove their supplied shadows from the named
  order-49 consumer.
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
asserting that a Fricke involution preserves a rational generator. A reusable
exact-order-five normalization now preserves the discriminant and `c₄` scales,
and its explicit marked-point version proves that the particular normalization
at `5P` has equal, nonzero Tate parameters;
applied to that quotient image, it eliminates the scale and proves an explicit
cleared equation between two noncuspidal rational order-five parameters. Its
complete factorization is checked: the quadratic component has no rational
points because its discriminant has the nonsquare class of five, while the two
quintic components are exchanged by `d ↦ -1/d`. Thus every hypothetical
order-twenty-five point reaches one fixed oriented quintic component. Forgetting
the two chosen generators maps that component to an explicit `X₀(25)`
degeneracy equation. A checked rational inverse recovers its Hauptmodul with no
exceptional rational pole on the curve, and direct identities prove that
`n ↦ 5/n` exchanges the two `X₀(5)` degeneracy values with reciprocal factor
`125`. Both degeneracy values for the actual marked point have now been
identified with the same signed Lécacheux orbit Hauptmodul. More precisely,
the Tate parameter at `5P` is `k^5` for a nonzero rational `k`, and the signed
Hauptmodul is `k - 1/k - 1`. This is a generator-level fifth-power lift of the
second degeneracy map, not an assertion that Fricke preserves a rational
generator.

The checked Lécacheux orbit route also recovers the invariant
parameter from the five orbit coordinates and proves that the six cyclic
relations force the two selected coordinates to satisfy Lehmer's quintic.
The same six relations now rule out the pole in Lécacheux's smaller
two-consecutive-root recovery formula and prove, for the actual marked Tate
point, that it equals the symmetric five-root parameter. This isolates the raw
comparison to two orbit coordinates rather than five.
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
In the residual exact-order case, the checked fifth-power bridge forces `k`
to be a non-three-unit while `-5/(k - 1/k - 1)` is three-integral. The remaining
parameter substitution has now been made explicit: multiplying Lehmer's
quintic by `k^4` produces a fixed integral polynomial `P(k,x)`, and the actual
marked point supplies a rational solution with `x ≠ 0,1`. The checked deck
transformation `k ↦ -1/k` preserves both the Hauptmodul and vanishing of
`P`. The remaining endpoint gap is the rational-point exclusion on this
generator-marked Kummer cover, via a twist-aware descent or an equivalent
genus-four Jacobian rank-zero and cusp classification.

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
