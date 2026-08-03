import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "03 — Shared algebraic geometry and isogenies" =>

:::group "shared_geometry"
Reusable divisor, cohomology, Picard, Jacobian, Abel–Jacobi, and isogeny
infrastructure, developed upstream where possible. Stage weight: 300 points.
:::

:::theorem "MT-TC-A1-ORDER-SUPPORT" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, done, integrated, tau-ceti") (priority := "high") (effort := "large")
*Finite support of orders of rational functions.* A nonzero rational function
on a Noetherian integral scheme has nonzero order at only finitely many
codimension-one points.

*Status:* `done`. The permanent theorem is
`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.finite_support_orderAt`, with
checked challenge bridge `MazurTauCetiChallenge.finite_support_orderAt`. It is
consumed by the permanent scheme-theoretic
`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem` and by the exact-pin
contract consumer `MazurTauCetiChallenge.orderSystem`.
:::

:::theorem "MT-TC-A2-PRODUCT-FORMULA" (parent := "shared_geometry") (uses := "MT-TC-A1-ORDER-SUPPORT") (tags := "upstream, open, compiled, tau-ceti") (priority := "high") (effort := "large")
*Degree-zero product formula.* Every principal divisor on a proper smooth
geometrically integral curve has residue-degree-weighted degree zero.

*Status:* `open`; *scope:* exact compiled challenge contract. The bridge
`MazurTheorem.Challenge.divisorProductFormula` pins the abstract order system to
scheme-theoretic orders of vanishing and states the residue-degree-weighted result consumed by
the checked absolute degree-zero Picard API.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderSystem_isWeightedDegreeZero`
  State and prove the residue-degree-weighted product formula for every nonzero
  rational function on a proper smooth curve.
:::

:::theorem "MT-TC-E0-PRODUCT-DIM" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, done, integrated, tau-ceti") (priority := "high") (effort := "medium")
*Dimension of a product of abelian varieties.* Tau Ceti's abelian-variety
dimension is additive under its product construction.

*Status:* `done`; *scope:* integrated Tau Ceti theorem and checked challenge
bridge. The proof lifts arbitrary prime chains through faithful integral
extensions, applies Noether normalization to tensor products, proves matching
affine-chart bounds for products of nonempty finite-type schemes, and is
consumed by `TauCeti.AlgebraicGeometry.AbelianVariety.prod_dim` and
`MazurTauCetiChallenge.prod_self_dim`.
:::

:::definition "MT-TC-A3-DIVISOR-LINE-BUNDLE" (parent := "shared_geometry") (uses := "MT-TC-A2-PRODUCT-FORMULA") (tags := "upstream, research-open, compiled, tau-ceti") (priority := "high") (effort := "large")
*Divisor–line-bundle dictionary.* Construct the Picard group of line bundles
and identify divisor classes with line bundles on a smooth curve.

*Status:* `research_open`; *scope:* exact compiled existence-and-equivalence challenge
contract. The bridge `MazurTheorem.Challenge.divisorLineBundleDictionary`
contains the remaining global dictionary: chosen line-bundle representatives, exact principal
kernel, Picard surjectivity, and the resulting divisor-class/Picard equivalence. Checked code
derives principal-divisor line-bundle triviality and the full local-rank-one/tensor-unit Picard
comparison from those data. Conversely, it constructs the complete tensor-additive dictionary
from the full Picard comparison and divisor-class equivalence, proving these are exactly the two
irreducible global outputs. It also proves the basic-open tilde restriction isomorphism and
derives global tilde invertibility from Mathlib's finite free-localization cover and Tau Ceti
local trivializations. The checked local API supplies the unconditional affine Dedekind class
equivalence, tensor-additive module representatives, tilde line bundles detecting linear
equivalence exactly, and an absolute degree-zero D1 consumer; none is credited as the missing
global result. The localized tensor comparison is assembled into an affine tilde tensor-product
isomorphism, proving that tilde sends invertible modules to tensor units and inducing a canonical
injective module-Picard/scheme-Picard homomorphism. Consequently, the affine Dedekind divisor map
has exactly the principal divisors as kernel, descends to divisor classes, and gives an
unconditional equivalence from those classes to its scheme-Picard range; the actual tilde line
bundles are tensor-additive. The chosen Picard representative is moreover linearly equivalent
to the explicit inverse fractional ideal attached to the divisor. On a same-chart principal
open, coefficient equality on `D(f)` now proves equality of the localized inverse ideals,
equivalently equality after common-field extension, and yields a checked isomorphism of the
chosen restricted tilde bundles. For two charts mapping to a common affine overlap,
`AffineDivisorLocalization.Boundary.OverlapInverseIdealExtensionEq` isolates equality of the two
extended inverse ideals, while
`AffineDivisorLocalization.CommonExtension.RestrictionIdentifiesExtendedInverseIdeal` isolates
the restriction/base-change comparison for each chosen chart bundle. Affine tilde base change
and flat epimorphic tensor/span comparison prove that comparison for every affine open immersion,
without a classical localization presentation. Across two distinct chart rings, the
extension equality is now proved for principal divisors defined by the same rational function,
and for arbitrary divisors on any common Dedekind affine overlap from contracted coefficient
equality. Open-immersion prime extension replaces the classical-localization hypothesis. For
restrictions of one ambient divisor, compatible coordinate maps to the curve identify the
contracted ambient points and automatically produce the coefficient equality, extended-ideal
equality, and actual restriction isomorphism. All routes have checked actual-restriction
consumers. For two divisors on the same chart,
coefficient agreement now gives the actual principal-open restriction isomorphism directly.
A chosen common Dedekind affine subopen canonically supplies all algebra maps, open immersions,
scalar towers, and ambient-map compatibilities needed for the arbitrary-divisor comparison.
On a separated integral scheme, the full intersection of two nonempty affine charts is affine
and nonempty, and the comparison is constructed there once its coordinate ring is Dedekind.
For a proper morphism to the spectrum of a field, relative properness supplies the absolute
separatedness input automatically. For a smooth relative curve, the existing mapwise normality
contract supplies the intersection's Dedekind instance and hence the actual comparison.
Proving that normality condition, transporting the isomorphisms to the chosen descent
pullbacks, and proving normalized diagonal and triple-cocycle coherence remain missing.
The API also
characterizes existence of the full affine scheme-level
dictionary by the full comparison for arbitrary sheaves alone: canonical Picard surjectivity is
equivalent to the reverse tensor-unit/local-rank-one comparison. The forward affine gap is
isolated as reflection of invertibility through tilde, and a checked consumer turns that precise
localization predicate into the forward tensor-inverse comparison. The chart API canonically
identifies height-one primes of a Dedekind affine coordinate ring with the ambient
codimension-one points lying in the chart. It now proves equality of the Dedekind and scheme
order homomorphisms from the Dedekind-domain instance, constructing
`AffineChart.DedekindOrderCompatibility` automatically. The remaining coordinate-ring boundary
is exactly dimension at most one plus integral closedness.
`AffineChart.SmoothRelativeCurveRingConditions` packages these consequences as a conditional
mapwise predicate. Over a field, the dimension-at-most-one consequence is now proved from local
standard smoothness and relative dimension one, so `AffineChart.SmoothRelativeCurveNormality`
is the exact remaining part. Its checked consumer assumes normality on the concrete affine
`appLE` map and constructs the required Dedekind order compatibility; no universal implication
over an arbitrary base is asserted. Whole principal divisors are related by reindexing and the induced
local divisor-to-scheme-Picard map has exactly those principal divisors as kernel. It therefore
descends injectively to chart divisor classes and identifies them with its scheme-Picard range.
Pullback
along the chart scheme isomorphism is already an equivalence of module categories; the API
isolates strong monoidality of that pullback as `PicardIso.PullbackMonoidalData`. Given this
upstream-compatible sufficient datum, it constructs `Pic(Spec Γ(X, U)) ≃ Pic(U)` and
transports the exact principal kernel, injective class descent, and range equivalence to the open
subscheme. The resulting Picard equivalence is proved independent of the chosen monoidal
structure and its inverse is identified with pullback along the inverse scheme isomorphism. The
pinned upstream AINTLIB source proves monoidality for general pullback, but its unported cone
uses source-level options forbidden in this task. The descent API now packages specified
pairwise overlap isomorphisms, diagonal normalization, and the triple cocycle as Mathlib module
descent data. It separates object effectivity, cover-wide module effectivity, essential
injectivity on objects, and fully faithful module descent instead of asserting a stack theorem.
The companion locality module refines chartwise rank-one trivialization atlases and proves that
Tau Ceti invertibility is local on every scheme open cover. Consequently ordinary module
effectivity alone globalizes locally invertible descent data. A checked bridge consumes a
scheme-module prestack instance to produce fully faithful descent and hence the exact
object-separation property, while the current dependency graph supplies no such instance. On a
canonical coordinate cover, the curve-divisor API restricts a global divisor, constructs the
actual affine `O(D)` line bundle on every chart, preserves addition, and proves local triviality
for principal divisors. On a single chart, ambient coefficient equality on a principal open now
constructs the actual restriction isomorphism between two such bundles.
`CurveDivisorDescent.DivisorCocycle` is the exact remaining cross-chart overlap input for these
specified line bundles. Object-specific effective invertible descent then constructs a global
line bundle
with a checked isomorphism from each restriction to the corresponding `O(D)`. The companion
`CurveDivisorPicardDescent` API packages a divisor-indexed family of such cocycles. Objectwise
effectivity, tensor-additivity, and triviality of the zero-divisor bundle construct an actual
additive divisor-to-Picard map. The bundle of `-D` explicitly inverts the bundle of `D`, so this
route requires no `TensorInverseComparison X` for unrelated invertible sheaves. Coherent
triviality of principal cocycles supplies zero triviality and, with object separation, descends
the construction to divisor classes. Exact principal kernel identifies those classes with the
actual Picard range. Under coherent principal triviality and object separation, checked code
identifies exactness with `ExplicitInverse.TrivialLineBundleDetectsPrincipal`: a descended
divisor line bundle is globally trivial only for a principal divisor. A global trivialization is
proved to make the divisor principal on every chart.
The witness-level condition
`ExplicitInverse.TrivialDescendedLineBundleHasGlobalPrincipalWitness` says that one rational
function gives all chart restrictions. Under agreement of the chosen global and scheme orders,
checked code proves it equivalent to principal detection in both directions, so it is not a
separate gluing input. Constructing compatible rational data from the explicit line-bundle
cocycle remains absent. Surjectivity then gives the full divisor-class/Picard equivalence. Only
the stronger dictionary package, which compares every
invertible sheaf with a Picard unit, retains the global tensor-inverse hypothesis. No inhabitant
of the divisor cocycle system, chosen-pullback/intersection transport, coherent overlap system,
module-effectivity, coherent-principal-triviality,
prestack/object-separation, rationally normalized cocycle data,
geometric-principal-detection, exact-kernel, surjectivity, or global tensor-inverse comparison is
claimed. Thus global
proper-curve gluing and Picard surjectivity remain open.
`AffineTilde.TildeReflectsInvertibility`, the field-base smooth-curve normality condition,
and the cover-wide `CurveDivisorDescent.DivisorCocycle` and effectivity packages are precise
compiled conditional boundaries subsumed by the unchanged registered A3 Challenge rather than
separately registered Challenge declarations. Their discharge remains part of that Challenge.
No additional localization Challenge is needed. The weighted product formula remains the
separately registered A2 prerequisite in the roadmap; the affine and local A3 modules here do not
import it. Artifact state
`contract` records a compiled conditional API and does not assert that these predicates are
inhabited or that A3 is solved.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PicardGroup`
  Expose line bundles modulo isomorphism as the Picard group of a smooth proper curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.classEquivPicard`
  Identify Weil divisors modulo principal divisors with the line-bundle Picard group.
* `structure` (`contract`): `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary`
  Record the exact forward tensor-inverse comparison, chosen line-bundle representatives,
  principal kernel, and surjectivity needed for the global equivalence; derive principal
  line-bundle triviality and the reverse Picard comparison in checked code.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.nonempty_lineBundle_iso_iff_linearlyEquivalent`
  Detect linear equivalence exactly by isomorphism of the chosen divisor line bundles.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.picardComparison`
  Recover the full equivalence between local rank-one sheaves and tensor units.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.ofClassEquivalence`
  Construct all chosen divisor line bundles from the full Picard comparison and class
  equivalence.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.nonempty_iff_picardComparison_and_classEquivalence`
  Characterize existence of the dictionary by precisely those two global outputs.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.lineBundle_add_iso`
  Identify divisor addition with tensor product of the chosen line bundles up to isomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.UniversalBasicOpenTildeTriviality`
  Package the checked restriction isomorphism on a free basic-open localization.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.universalTildeInvertibility`
  Prove global tilde invertibility from the basic-open comparison.
* `definition` (`contract`): `MazurTorsion.AlgebraicGeometry.AffineDedekind.classEquivPicard`
  Give the unconditional standard-sign affine Dedekind divisor-class/module-Picard equivalence.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.localizedTensorEquivOfIsLocalization`
  Identify the tensor of two localized modules with the localization of their tensor over an
  arbitrary chosen localization ring.
* `definition` (`contract`): `MazurTorsion.AlgebraicGeometry.AffineTilde.tildeTensorIso`
  Assemble the local fraction comparison into the objectwise tilde tensor-product isomorphism
  on an affine scheme.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.tilde_isTensorInvertible`
  Send every invertible module to a tensor-invertible tilde sheaf.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.modulePicToSchemePic`
  Give the canonical tilde-induced homomorphism from module Picard classes to scheme Picard
  classes.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.modulePicToSchemePic_injective`
  Prove that the canonical affine Picard comparison is injective.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.modulePicToSchemePic_surjective_iff_tensorUnitLocalTriviality`
  Identify surjectivity of the canonical affine Picard map exactly with the reverse
  tensor-unit/local-rank-one comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.TildeReflectsInvertibility`
  Isolate the missing localization reflection from an invertible tilde sheaf to an invertible
  module.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.tensorInverseComparison_of_tildeReflectsInvertibility`
  Consume the localization reflection to construct tensor inverses for arbitrary affine
  invertible sheaves.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineTilde.picardComparison_iff_tensorInverseComparison_and_modulePic_surjective`
  Characterize the full affine Picard comparison by its forward tensor-inverse component and
  surjectivity of the canonical tilde map.
* `definition` (`contract`): `MazurTorsion.AlgebraicGeometry.AffineDedekind.lineBundle`
  Package its chosen module representative unconditionally as a Tau Ceti line bundle.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_lineBundleModule_add_equiv`
  Identify `O(D + E)` with `O(D) ⊗ O(E)` as invertible modules, unconditionally.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_lineBundle_add_iso`
  Identify `O(D + E)` with `O(D) ⊗ O(E)` for the actual tilde line bundles.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.classToSchemePic`
  Descend the canonical affine divisor construction to an injective divisor-class map into the
  scheme Picard group.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.classEquivSchemePicRange`
  Identify affine Dedekind divisor classes with the range of their canonical scheme-Picard
  realization.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.classEquivSchemePicOfTensorUnitLocalTriviality`
  Upgrade the range equivalence to the full scheme Picard group under exactly the reverse
  comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.divisorToSchemePic`
  Construct the canonical affine divisor-to-scheme-Picard homomorphism through divisor classes.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.divisorToSchemePic_kernel`
  Prove that the canonical divisor-to-scheme-Picard map has exactly the principal divisors as
  its kernel.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_lineBundle_iso_iff_linearlyEquivalent`
  Detect affine Dedekind linear equivalence exactly by isomorphism of the chosen tilde line
  bundles.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_dictionary_iff_picardComparison_and_modulePicardEquivalence`
  Record the abstract two-input rewrite through a full Picard comparison and an additive
  module-Picard/scheme-Picard equivalence.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDedekind.nonempty_dictionary_iff_picardComparison`
  Sharpen the affine Dedekind boundary: the full Picard comparison alone supplies the canonical
  divisor-class equivalence and hence the exact dictionary.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.affineOpenHeightOneSpectrumEquiv`
  Identify height-one primes of a Dedekind affine coordinate ring with the ambient
  codimension-one points in the chart.
* `structure` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility`
  Isolate equality of the affine Dedekind valuations and scheme order homomorphisms on a chart.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.affineOpen_order_eq`
  Prove that the normalized Dedekind valuation agrees with the scheme order on every nonempty
  affine chart whose coordinate ring is Dedekind.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.dedekindOrderCompatibilityOfIsDedekindDomain`
  Construct the complete order-compatibility package from the Dedekind-domain instance alone.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.affineOpen_isDedekindDomain_iff`
  Reduce the remaining coordinate-ring boundary to dimension at most one and integral
  closedness; domain and Noetherianity already follow from the ambient hypotheses.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.SmoothRelativeCurveRingConditions`
  Package mapwise, behind the local standard-smooth premise, the required dimension-at-most-one
  and integral-closedness consequences without asserting them uniformly over arbitrary bases.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.dimensionLEOne_of_locallyStandardSmoothRelDimOne_over_field`
  Prove that a locally standard-smooth relative-dimension-one domain over a field has dimension
  at most one.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.SmoothRelativeCurveNormality`
  Isolate integral closedness as the exact remaining field-base chart-ring condition.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.smoothRelativeCurveRingConditions_iff_normality_of_field`
  Identify the two-part smooth curve ring boundary with the normality-only boundary over a
  field-domain chart.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurveRingConditions`
  Consume the map-specific smooth-curve ring conditions to construct the Dedekind order
  compatibility required by the chart divisor API.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.dedekindOrderCompatibilityOfSmoothRelativeCurveNormality`
  Construct the chart order compatibility from the normality-only input for a smooth relative
  curve over a field.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility.principalDivisor_reindex_eq_ambientPrincipalDivisor`
  Transport the whole affine principal divisor to the ambient chart points.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility.divisorToSchemePic_principalDivisor`
  Construct and consume the chart divisor-to-scheme-Picard map, proving principal triviality.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility.divisorToSchemePic_kernel`
  Prove that the chart divisor-to-Picard map has exactly the ambient principal divisors as its
  kernel.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility.classEquivSchemePicRange`
  Give the strongest unconditional conclusion from the chart compatibility: divisor classes
  are equivalent to the range of their canonical scheme-Picard realization.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardIso.PullbackMonoidalData`
  Isolate strong monoidality of sheaf pullback as an upstream-compatible sufficient input for
  transporting the AINTLIB Picard group across a scheme isomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardIso.equivOfPullbackMonoidal`
  Construct the Picard equivalence across a scheme isomorphism from that monoidality datum.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardIso.equivOfPullbackMonoidal_independent`
  Prove that the Picard equivalence is independent of the chosen strong monoidal structure.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardIso.equivOfPullbackMonoidal_symm_apply_val`
  Identify the inverse Picard equivalence on isomorphism classes with pullback along the inverse
  scheme isomorphism.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility.divisorToOpenPic_kernel`
  Preserve the exact principal kernel after transporting the chart divisor map to `Pic(U)`.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineChart.DedekindOrderCompatibility.classEquivOpenPicRange`
  Identify chart divisor classes with their canonical range in the Picard group of the open
  subscheme.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.EffectiveInvertible`
  State object-specific effectivity of a coherent module descent datum by a global invertible
  sheaf, without asserting a stack theorem.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.EffectiveInvertible.restrictionIso`
  Recover the isomorphism between the descended global line bundle and every local chart object.
* `structure` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.LineBundleCocycle`
  Package specified pairwise overlap isomorphisms, diagonal normalization, and the triple
  cocycle for actual local invertible sheaves.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.LineBundleCocycle.toDescentData`
  Convert the chosen-overlap cocycle into Mathlib coherent module descent data.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.InvertibleEffectiveDescentFor`
  Isolate effective descent for all locally invertible data on one specified open cover.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.invertibleEffectiveDescentFor_of_moduleEffectivity_of_locality`
  Derive invertible effectivity from ordinary module effectivity and locality of invertibility.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.ModuleDescentEssentiallyInjectiveFor`
  Isolate the exact object-separation input needed to lift a trivialization of descent data.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.moduleDescentEssentiallyInjectiveFor_of_fullyFaithful`
  Derive the exact object-separation property from fully faithful module descent.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundle`
  Construct the actual affine `O(D)` from the restriction of a global curve divisor.
* `lemma` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localDivisor_coeff`
  Identify a coordinate-divisor coefficient with the global coefficient at the corresponding
  ambient codimension-one point.
* `lemma` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.contractedPoint_eq_of_commonMap`
  Prove that two compatible coordinate maps from one common affine overlap contract a
  height-one prime to the same ambient codimension-one point.
* `lemma` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.openImmersionCoefficientEq_localDivisor_of_commonMap`
  Derive contracted coefficient equality for the two chart restrictions of one ambient divisor.
* `lemma` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.overlapInverseIdealExtensionEq_localDivisor_of_commonMap`
  Prove equality of the two extended inverse ideals directly from a compatible common affine
  overlap map.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleRestrictionIsoOfCommonMap`
  Construct the actual arbitrary-divisor restriction isomorphism from an explicitly compatible
  common Dedekind affine-overlap presentation.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.restrictionAlgebra`
  Equip the coordinate ring of an affine subopen with the algebra structure induced by section
  restriction.
* `lemma` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.restrictionExtensionMap_comp_fromSpec`
  Identify the composite of the restriction-induced spectrum map and the chart map with the
  canonical map from the affine subopen.
* `lemma` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.restrictionExtensionMapIsOpenImmersion`
  Prove that section restriction to an affine subopen induces an open immersion on spectra.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleRestrictionIsoOnCommonAffineOpen`
  Construct the arbitrary-divisor restriction isomorphism canonically on every chosen common
  nonempty Dedekind affine subopen of two charts.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleRestrictionIsoOnIntersection`
  Construct the arbitrary-divisor restriction isomorphism on the full intersection of two
  nonempty affine charts under separatedness and the Dedekind condition for its coordinate ring.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleRestrictionIsoOnProperCurveIntersection`
  Derive separatedness from properness over a field and construct the same full-intersection
  arbitrary-divisor restriction isomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleRestrictionIsoOnProperSmoothCurveIntersectionOfNormality`
  On a proper smooth relative curve, consume the existing mapwise normality condition to derive
  the intersection Dedekind instance and construct the full-overlap isomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleRestrictIsoOfCoeffEq`
  Construct the actual same-chart principal-open restriction isomorphism from ambient
  coefficient equality.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundle_principal_iso_trivial`
  Prove that every global principal divisor gives a trivial line bundle on each compatible
  affine chart.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycle`
  Specialize the exact overlap-cocycle boundary to the constructed chartwise `O(D)` bundles.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.globalLineBundleRestrictionIso`
  Consume effective descent to identify every restriction of the global bundle with its actual
  affine divisor line bundle.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.globalLineBundle_principal_iso_trivial`
  Descend coherent principal triviality to a global trivialization under essential injectivity
  on objects for module descent.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.classEquivPicardRange`
  Identify divisor classes with the actual range of any divisor-to-Picard homomorphism having
  exactly the principal kernel, without assuming Picard surjectivity.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.moduleDescentFullyFaithfulForOfIsPrestack`
  Consume a scheme-module prestack instance to obtain fully faithful descent on a specified
  Zariski open cover.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DescendedZeroTrivial`
  Isolate the minimal unit input saying that the descended bundle of the zero divisor is
  globally trivial.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.descendedTensorInverseIso`
  Exhibit the descended bundle of `-D` as a tensor inverse to the descended bundle of `D`.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.divisorToPic`
  Construct the divisor-to-Picard homomorphism from zero triviality and tensor additivity,
  without a global comparison for arbitrary invertible sheaves.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.classToPic`
  Descend the explicit-inverse divisor map to divisor classes using coherent principal
  triviality and object separation.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.TrivialLineBundleDetectsPrincipal`
  Isolate the geometric injectivity boundary that a globally trivial descended divisor line
  bundle comes only from a principal divisor.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.restrictDivisor_mem_principal_of_descendedLineBundle_iso_trivial`
  Prove that a global trivialization makes the divisor principal on every coordinate chart.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.TrivialDescendedLineBundleHasGlobalPrincipalWitness`
  Record the witness-level form of principal detection: one rational function gives every chart
  restriction of a divisor whose descended line bundle is trivial.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness`
  Turn a global principal witness into geometric principal detection.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.globalPrincipalWitness_of_trivialLineBundleDetectsPrincipal`
  Produce the global chart witness from geometric principal detection.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.globalPrincipalWitness_iff_trivialLineBundleDetectsPrincipal`
  Identify the witness-level formulation exactly with geometric principal detection when the
  chosen global order agrees with the scheme order.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.hasPrincipalKernel_iff_trivialLineBundleDetectsPrincipal`
  Identify exactness of the divisor Picard map with the geometric principal-detection boundary
  under coherent principal triviality and object separation.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.classEquivPicardRange`
  Identify divisor classes with the actual range of the explicit divisor-generated Picard map
  under the exact-principal-kernel hypothesis.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.classEquivPicard`
  Give the strongest conditional full equivalence: exact principal kernel plus surjectivity,
  with no global tensor-inverse comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.classEquivPicardOfTrivialLineBundleDetection`
  Under coherent principal triviality and object separation, replace the abstract exact-kernel
  input by geometric principal detection and combine it with Picard surjectivity.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.classEquivPicardOfGlobalPrincipalWitness`
  Build the full conditional divisor-class/Picard equivalence from the witness-level form of
  principal detection and Picard surjectivity, retaining coherent principal triviality and
  object separation as explicit hypotheses.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.dictionary`
  Package the explicit divisor map and descended line bundles into the stronger all-sheaves
  dictionary once the separate global tensor-inverse comparison is supplied.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.explicitDivisorToPic_eq_divisorToPic_of_tensorInverseComparison`
  Prove that the explicit divisor map equals the earlier comparison-based construction whenever
  the global tensor-inverse comparison is available.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.divisorToPic`
  Construct an additive divisor-to-Picard homomorphism from objectwise effective,
  tensor-additive divisor cocycles and the forward tensor-inverse comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.classToPic`
  Descend the Picard homomorphism built using the forward tensor-inverse comparison to divisor
  classes using coherent principal triviality and object separation.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.dictionary`
  Upgrade effective tensor-additive cocycles and the forward tensor-inverse comparison to the
  full divisor-line-bundle dictionary under exact kernel and surjectivity.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.classEquivalence`
  Extract the full additive divisor-class/Picard equivalence from the exact cocycle-built
  dictionary, which uses the forward tensor-inverse comparison.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.ExplicitIdeal.lineBundleModuleEquivInverseIdeal`
  Identify the chosen affine Picard representative with the explicit inverse fractional ideal
  attached to the divisor.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.ExplicitIdeal.divisorFractionalIdeal_principalDivisor`
  Identify the explicit ideal of a principal divisor with the corresponding principal
  fractional ideal.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.InverseIdealLocalizationEq`
  Name equality of two explicit inverse ideals after localization at a same-chart principal
  open; coefficient equality now supplies this condition.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.inverseIdealLocalizationEq_of_coeff_eq_away`
  Prove localized inverse-ideal equality from coefficient equality on `D(f)`, including `f = 0`.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.overlapInverseIdealExtensionEq_away_of_coeff_eq`
  Prove common-field extension equality from coefficient equality on a compatible nonempty
  principal open.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.inverseIdealLocalizationEq_iff_overlapExtensionEq_away`
  Identify abstract localized-ideal equality with common-field extension equality on a
  compatible nonempty principal open.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.OverlapInverseIdealExtensionEq`
  Require compatible maps into a common function field and equality of the two inverse divisor
  ideals after extension to a common affine-overlap ring.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.overlapInverseIdealExtensionEq_principal`
  Prove the cross-chart extension equality for principal divisors defined by the same rational
  function on two distinct Dedekind chart rings.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.underHeightOneOpenImmersion`
  Contract a height-one prime through an affine open immersion of Dedekind spectra.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.map_underHeightOneOpenImmersion`
  Prove that extending the contracted height-one prime recovers the original overlap prime.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.OpenImmersionCoefficientEq`
  State equality of chart-divisor coefficients after contraction through two arbitrary affine
  open immersions from a common Dedekind overlap.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.overlapInverseIdealExtensionEq_of_openImmersion_coeff_eq`
  Prove arbitrary-divisor cross-chart extension equality from contracted coefficient equality,
  without classical localization presentations.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.underHeightOne`
  Contract a height-one prime through a localization whose denominators are non-zero-divisors.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.LocalizationCoefficientEq`
  State equality of chart-divisor coefficients after contracting every height-one prime of a
  common localization ring.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.overlapInverseIdealExtensionEq_of_localization_coeff_eq`
  Prove arbitrary-divisor cross-chart extension equality from two localization structures and
  contracted coefficient equality.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.RestrictionIdentifiesExtendedInverseIdeal`
  Isolate identification of a chosen chart line-bundle restriction with tilde of its inverse
  divisor ideal extended to the common overlap.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.RestrictionGlobalSectionsEquivExtendedInverseIdeal`
  Reduce arbitrary-overlap restriction/base change to a linear equivalence between affine
  global sections and the extended inverse ideal.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.restrictionIdentifiesExtendedInverseIdeal_iff_globalSectionsEquiv`
  Prove that the sheaf-level and affine-global-sections overlap comparisons are equivalent.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion`
  Discharge the sheaf-level restriction comparison on every affine open immersion by flat
  epimorphic tensor/span base change.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.restrictionGlobalSectionsEquivExtendedInverseIdeal_of_isOpenImmersion`
  Identify affine global sections of every restricted chosen divisor bundle with the extended
  inverse ideal.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.restrictionIdentifiesExtendedInverseIdeal_of_isLocalization`
  Discharge the sheaf-level restriction comparison when the spectrum map is an open immersion
  and the overlap ring is a classical submonoid localization of the chart ring.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.restrictionGlobalSectionsEquivExtendedInverseIdeal_of_isLocalization`
  Derive the corresponding affine-global-sections comparison from the localization theorem.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIso`
  Combine extension equality and both restriction identifications into an isomorphism of the
  actual chosen chart line-bundle restrictions.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoOfOverlapExtensionEq`
  Construct the actual cross-chart restriction isomorphism from the packaged extended-ideal and
  scalar-tower compatibility on an affine overlap.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoOfGlobalSectionsEquiv`
  Construct the actual cross-chart restriction isomorphism from the two module-level
  global-sections comparisons and extended-ideal equality.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoPrincipal`
  Construct the actual cross-chart principal-divisor restriction isomorphism once both
  restriction/base-change identifications are supplied.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoPrincipalOfIsOpenImmersion`
  Construct the principal-divisor restriction isomorphism on every common affine overlap without
  localization presentations.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoPrincipalOfIsLocalization`
  Construct the principal-divisor restriction isomorphism directly from two localization
  presentations and compatible common-fraction-field maps.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoOfOpenImmersionCoeffEq`
  Construct the actual arbitrary-divisor restriction isomorphism from contracted coefficient
  equality on any common Dedekind affine overlap.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoOfLocalizationCoeffEq`
  Construct the actual arbitrary-divisor cross-chart restriction isomorphism from localization
  coefficient compatibility; affine-open base change supplies both restriction comparisons.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.restrictionIdentifiesExtendedInverseIdeal_away`
  Prove the restriction/base-change identification on every nonempty principal open with a
  compatible common fraction field.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoAway`
  Consume the principal-open identification and extension equality to identify the actual
  chosen restricted divisor line bundles.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary.overlapInverseIdealExtensionEq_away`
  Convert same-chart localized inverse-ideal equality into equality of the corresponding
  extensions inside a compatible common fraction field.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension.chosenLineBundleRestrictionIsoAwayOfLocalizationEq`
  Produce the actual chosen principal-open restriction isomorphism directly from same-chart
  localized inverse-ideal equality.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Chain.chosenTildeRestrictIsoOfInverseIdealEq`
  Consume equality of localized inverse ideals to identify the restrictions of the chosen
  affine divisor line bundles.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Chain.chosenTildeRestrictIsoOfCoeffEq`
  Construct the chosen same-chart restriction isomorphism directly from coefficient equality
  on a principal open.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.invertibilityIsLocal`
  Prove that Tau Ceti invertibility is local on every scheme open cover.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.invertibleEffectiveDescentFor_of_moduleEffectivity`
  Upgrade ordinary module effectivity to effective descent for locally invertible data using
  the proved locality theorem.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.globalLineBundleOfModuleEffectivity`
  Construct a global divisor line bundle directly from a coherent cocycle and ordinary module
  effectivity on the coordinate cover.
:::

:::definition "MT-TC-B1-COHERENT-COHOMOLOGY" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Coherent cohomology of proper curves.* Build finite-dimensional coherent
cohomology, affine acyclicity, and vanishing above degree one.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.CurveCohomology`
  Define degree-zero and degree-one coherent cohomology for sheaves on proper curves.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.CurveCohomology.finiteDimensional`
  Prove finite dimensionality, affine acyclicity, and vanishing above degree one in
  the required scope.
:::

:::theorem "MT-TC-B2-RR-SERRE" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Riemann–Roch and Serre duality for curves.* Define genus through $`H^1` and
prove Riemann–Roch, Serre duality, and the degree of the dualizing sheaf.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.genus`
  Define the genus of a proper smooth curve from the dimension of first coherent
  cohomology.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.riemannRoch`
  Provide the Riemann-Roch formula for divisors or line bundles on a proper smooth
  curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.serreDuality`
  Provide Serre duality and the resulting degree formula for the dualizing sheaf.
:::

:::definition "MT-TC-C1-RELATIVE-COHOMOLOGY" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Relative cohomology and base change.* Provide proper-flat pushforward,
cohomology-and-base-change, and semicontinuity in the form needed by Picard.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology`
  Package derived pushforward data for coherent sheaves in a proper flat family of
  curves.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology.baseChange`
  Prove the base-change comparison required by the relative Picard construction.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology.upperSemicontinuous`
  Prove upper semicontinuity of fibrewise cohomology dimensions in the required
  setting.
:::

:::definition "MT-TC-C2-SYMMETRIC-POWERS" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE, MT-TC-C1-RELATIVE-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Relative effective divisors and symmetric powers.* Represent degree-$`d`
effective divisors by $`\operatorname{Sym}^d X` and construct relative Abel
maps.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeEffectiveDivisor`
  Represent flat families of effective divisors of a fixed relative degree.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.SymmetricPower`
  Construct the relative symmetric power that represents effective divisors of degree
  d.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.relativeAbelMap`
  Construct the relative Abel map from the symmetric power to the degree-d Picard
  functor.
:::

:::definition "MT-TC-D1-PICARD-FUNCTOR" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE, MT-TC-C1-RELATIVE-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Rigidified relative Picard functor.* Define the fppf Picard sheaf, its
degree-zero subfunctor, rigidification, and Poincaré line bundle.

*Status:* `blocked`.

The checked A3 downstream adapter already transports weighted divisor degree zero to an
absolute subgroup of `Scheme.Pic`. It can consume either the full dictionary or directly the
explicit-inverse curve-descent equivalence; the dictionary route also chooses a Tau Ceti
invertible-sheaf representative for each element. This is a genuine absolute precursor only;
it does not claim the relative fppf functor or representability.

The absolute Abel--Jacobi adapter now also transports Tau Ceti's weighted point and divisor
classes into this subgroup, proves its normalization and collision formulas, and gives a chosen
dictionary line-bundle consumer. These declarations fix the point-level formulas that the
future relative functor must represent; they do not change this node's blocked status.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativePicardFunctor`
  Define the rigidified fppf sheaf of line bundles modulo pullbacks from the base.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativePicardFunctor.degreeZero`
  Define the degree-zero subfunctor used to construct the relative Jacobian.
* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PoincareBundle`
  Package the normalized universal line bundle on the curve times its Picard space.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.degreeZero`
  Transport weighted degree-zero divisor classes to the absolute scheme Picard group.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.degreeZeroRepresentative`
  Choose an actual invertible-sheaf representative for every transported degree-zero class.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.degreeZero`
  Consume the strongest cocycle-built divisor-class/Picard equivalence directly to construct
  the absolute degree-zero subgroup, without first packaging the all-sheaves dictionary.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.divisorToPic_mem_degreeZero_iff`
  Characterize membership of a divisor-generated Picard class in the absolute degree-zero
  subgroup exactly by vanishing of its weighted divisor degree.
:::

:::theorem "MT-TC-D2-PICARD-REPRESENTABILITY" (parent := "shared_geometry") (uses := "MT-TC-B2-RR-SERRE, MT-TC-C2-SYMMETRIC-POWERS, MT-TC-D1-PICARD-FUNCTOR") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Representability and properness of $`\mathrm{Pic}^0`.* Represent the
degree-zero Picard functor and prove that its group scheme is proper and
geometrically connected.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme`
  Package a group scheme representing the degree-zero relative Picard functor.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme.representsDegreeZero`
  Prove the representing equivalence between points of PicardScheme and the degree-
  zero Picard functor.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme.proper_geometricallyConnected`
  Prove properness and geometric connectedness of the represented degree-zero
  component.
:::

:::definition "MT-TC-E1-JACOBIAN-VARIETY" (parent := "shared_geometry") (uses := "MT-TC-D2-PICARD-REPRESENTABILITY, MT-TC-E0-PRODUCT-DIM") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Jacobian variety and sanity checks.* Bundle $`\mathrm{Pic}^0` as an abelian
variety, prove that its dimension is the genus, and recover an elliptic curve
from its pointed genus-one Jacobian.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian`
  Package the represented Picard degree-zero component as an abelian variety.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.dimension_eq_genus`
  Identify the dimension of the Jacobian with the genus of the curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.ellipticCurveEquiv`
  Prove the pointed genus-one sanity check identifying an elliptic curve with its
  Jacobian.
:::

:::theorem "MT-TC-F1-ABEL-JACOBI" (parent := "shared_geometry") (uses := "MT-TC-C1-RELATIVE-COHOMOLOGY, MT-TC-E1-JACOBIAN-VARIETY") (tags := "upstream, blocked, nouns-missing, tau-ceti") (priority := "high") (effort := "large")
*Abel–Jacobi universal property and base change.* Construct the Abel–Jacobi
morphism, prove its universal property and base-change compatibility, and show
it is a closed immersion in positive genus.

*Status:* `blocked`.

The checked `PicardAbelJacobi` adapter supplies the absolute group-valued point and divisor
classes, including the base-point, linear-equivalence collision, point-difference, and chosen
line-bundle formulas. It is a normalization consumer for the future morphism, not a morphism of
schemes and not a proof of the universal property, base change, or closed immersion.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi`
  Construct the pointed Abel-Jacobi morphism from a curve to its Jacobian.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_universal`
  Prove the universal factorization property for pointed morphisms to abelian
  varieties.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_baseChange`
  Prove compatibility of the Abel-Jacobi construction with base change.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_closedImmersion`
  Prove that Abel-Jacobi is a closed immersion for curves of positive genus.
:::

:::definition "MT-EC-ISOGENY-WEIL" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, planned, nouns-missing, mathlib") (priority := "high") (effort := "large")
*Cyclic subgroup quotients and classifying data.* Package exactly the cyclic
quotient and base-change laws consumed by $`X_0(N)` and the existing order-49
lane.  Dual isogenies and a general Weil-pairing library are no longer
prerequisites of the prime theorem.

*Status:* `planned`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `EllipticCurve.CyclicSubgroup`
* `definition` (`proposed`): `EllipticCurve.Isogeny.quotientByCyclic`
* `theorem` (`proposed`):
  `EllipticCurve.Isogeny.quotientByCyclic_baseChange`
:::
