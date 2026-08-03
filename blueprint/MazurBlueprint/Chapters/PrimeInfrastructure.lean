import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "04 — Prime-level infrastructure" =>

:::group "prime_infrastructure"
The minimal Néron, finite-flat, modular-Jacobian, Hecke, Eisenstein rank-zero,
and formal-immersion infrastructure needed at auxiliary prime five, with the
same squarefree-level interfaces reused at eleven for level thirty-five.
The inherited cyclotomic contract remains a release obligation but is not an
input to the theorem. Stage weight: 400 points.
:::

:::definition "MT-NERON-BASE" (parent := "prime_infrastructure") (uses := "MT-TC-E1-JACOBIAN-VARIETY, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, blocked, nouns-missing, neron") (priority := "high") (effort := "large")
*Néron models for the two surviving consumers.* Build only the generality
used by the Eisenstein rank-zero criterion and elliptic reduction at five.

*Status:* `blocked`.

* `structure` (`proposed`): `AlgebraicGeometry.NeronModel`
* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.sectionExtension`
:::

:::definition "MT-NERON-COMPONENTS" (parent := "prime_infrastructure") (uses := "MT-NERON-BASE") (tags := "infrastructure, blocked, nouns-missing, neron") (priority := "high") (effort := "large")
*Identity components and tame elliptic fibres.* Supply the toric level fibre
used by rank zero and the additive component bound used at five.

*Status:* `blocked`.

* `definition` (`proposed`): `AlgebraicGeometry.NeronModel.identityComponent`
* `definition` (`proposed`): `AlgebraicGeometry.NeronModel.componentGroup`
* `theorem` (`proposed`):
  `EllipticCurve.NeronModel.additive_componentGroup_card_le_four_of_residueChar_gt_three`
* `theorem` (`proposed`):
  `ModularCurve.Jacobian.completelyToricReductionAtLevel`
:::

:::theorem "MT-NERON-SPECIALIZATION" (parent := "prime_infrastructure") (uses := "MT-NERON-COMPONENTS") (tags := "infrastructure, blocked, nouns-missing, neron") (priority := "high") (effort := "large")
*Torsion specialization for the quotient and prime five.* Expose the exact
sequence, prime-to-residue injection, and the $`e<p-1` formal-kernel lemma.

*Status:* `blocked`.

* `theorem` (`proposed`):
  `AlgebraicGeometry.NeronModel.torsionSpecialization_exact`
* `theorem` (`proposed`):
  `AlgebraicGeometry.NeronModel.primeToResidue_torsion_injective`
* `theorem` (`proposed`):
  `AlgebraicGeometry.NeronModel.torsion_eq_zero_of_specializes_zero_of_ramification_lt`

The checked partial boundary
`MazurTorsion.EllipticCurve.TameAdditiveFiltrationData` records the exact two
finite quotients and torsion-free formal kernel needed after the geometric
maps exist. Its separate characteristic-five and order-35 consumers compile,
but it neither constructs a Néron model nor changes this node's blocked status.
:::

:::definition "MT-FFGS-BASIC" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, done, integrated, group-schemes") (priority := "high") (effort := "large")
*Finite-flat commutative group schemes for Eisenstein rank zero.* The checked
category, honest kernel presentations, affine Hopf realization,
constant/diagonalizable examples, $`\mu_n` multiplication kernel,
constant-rank point-exponent consumer, and constant-group quotients are now
joined to an exact supplied fppf quotient interface. Certified kernels,
quotient presentations, and the named constant/multiplicative factors commute
with arbitrary base change.

*Status:* `done`; the base-changed admissible-filtration $`p^2`-exponent
consumer compiles.

* `structure` (`integrated`): `AlgebraicGeometry.FiniteFlatCommGroupScheme`
* `theorem` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernelPresentation_exists_of_finite_flat`
* `theorem` (`integrated`):
  `AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.point_pow_eq_one_of_constantRank`
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernel`
* `structure` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation`
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.KernelPresentation.baseChange`
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.baseChangePresentation`
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleSimpleFactor.baseChange`
* `theorem` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltrationStep.baseChange_point_pow_sq_eq_one`
:::

:::theorem "MT-FFGS-CONNECTED-ETALE" (parent := "prime_infrastructure") (uses := "MT-FFGS-BASIC") (tags := "infrastructure, planned, compiled, group-schemes") (priority := "high") (effort := "large")
*Admissible filtrations and fppf cohomology.* Formalize the exact filtration
and cohomology estimate used in Mazur's rank-zero proof, rather than an
unconsumed general connected--étale library.

*Status:* `planned`; the completed finite-flat exact-presentation layer now
supports honest recursive admissible filtrations, their base-change exponent
bound, and the elementary low-degree finite-group estimate. Genuine relative
global fppf `H¹` over `Scheme.Over X` now compiles as a common-refinement
quotient. Pointwise commutative Čech cocycle operations descend to its
canonical group law; refinement pullback is multiplicative, products can be
computed on any common refinement, and the representable finite-flat
specialization feeds the existing finite-p-group consumer. Natural
transformations of commutative coefficients now induce global homomorphisms,
and actual finite-flat group-scheme maps consume this functoriality. Certified
kernels are exact on test-scheme points. Genuine supplied local lifts produce
a kernel-valued Čech boundary class independent of the lifts and cover. An
actual checked fppf quotient now supplies its tautological local lifts and
connecting homomorphism. If that boundary vanishes, a common-refinement gauge
makes the lifts compatible and subcanonical descent glues them globally, so
exactness at quotient-valued global sections is checked. If a kernel `H¹`
class becomes trivial in the middle group, a common-refinement zero-cochain
has compatible quotient images; gluing those images and reusing the
zero-cochain as local lifts proves exactness at kernel `H¹`. A quotient-valued
trivializing gauge also lifts on a genuine refinement, proving the reverse
inclusion at middle `H¹`. Over `Spec ℤ`, the constant order-`p` factor has `p`
global sections and the odd multiplicative factor has one; these checked
cardinal certificates feed a reusable quotient bound with one admissible
elementary kernel, and the two-elementary-factor step consumes that recursive
interface. This finite-flat API does not yet represent Mazur's two quasi-finite
closures at the primes dividing the level. The represented coefficient and
global `H¹` construction now extends to every ambient commutative group scheme.
Ambient group-scheme morphisms induce canonical maps on represented points and
`H¹` with checked identity and composition laws. Their canonical kernel is
constructed as the pullback against the identity in internal groups, identified
with the scheme-theoretic pullback, and proved to represent the pointwise kernel
on every test scheme. A checked wrapper packages the flat, quasi-finite,
separated, finite-presentation case, consumes those maps and the ambient kernel,
and agrees definitionally with the finite-flat coefficient, morphism, and
canonical-kernel APIs. The next
kernel boundary is now explicit: a quasi-finite presentation supplies an
actual quasi-finite flat group scheme together with its group-scheme
identification with the ambient kernel, yielding pointwise exactness. The
canonical finite-flat kernel is a checked adapter, and every certified
finite-flat kernel has a geometric adapter that preserves its chosen
inclusion. The common proof is now factored through a finiteness-free ambient
kernel presentation with a compatible chosen inclusion, unique point lifts,
and represented-point exactness. A supplied quasi-finite fppf quotient now records its fppf
projection and geometric kernel, proves represented-point exactness, and
embeds the checked finite-flat quotient presentations compatibly. A reusable
principal-open Hopf localization now constructs the actual bad-level constant
factor `(Z/pZ)^flat` with coefficient `p` separate from level `N`; its realized
typed inclusion has the advertised componentwise principal-open range and
contains the full constant family over `D(N)`. Every integral global section
at a nonunit level is now proved to be the identity, and a prime-level
specialization packages this as cardinality `1 = p^0`. The connecting-class
construction now also lives over arbitrary ambient commutative group schemes;
its quasi-finite wrapper and the finite-flat quotient layer are compiled
consumers. The multiplicative-flat factor is now constructed by an explicit
Hopf localization, packaged as a quasi-finite flat commutative group scheme,
and included into `mu_p` by a typed open immersion whose exact range contains
the whole model over `D(N)`. The Fermat specialization is a concrete consumer.
At odd coefficient every integral global section is the identity; a
distinct-prime-level specialization packages this as cardinality `1 = p^0`,
and the low-degree Euler length bound consumes the endpoint.
Actual pointwise categorical cokernel presheaves now compile for represented
additive point maps, with objectwise-surjective projections and exact short
complexes. Universe lifting to `AddCommGrp` and fppf sheafification now supply
the actual cokernel terms in categorically exact short complexes. The
canonical projections from the represented ambient point sheaves are genuinely
fppf-locally surjective and hence epic; both typed bad-level inclusions are
downstream consumers. Open-immersion factorization now proves point-map
surjectivity and objectwise cokernel vanishing on every test scheme over
`D(level)`. Continuous restriction of the relative fppf site is compared with
sheafification, so both actual bad-level cokernel sheaves restrict to zero over
`D(level)`. They are therefore honestly supported on the bad fibre, without
any representability claim. The supported sheaf localization sequences remain open, followed by the
quasi-finite admissible-filtration exact sequences, bad-level multiplicative
`H⁰`/`H¹` comparisons, and middle-`H¹` finiteness. The supported bad-fibre
quotients are not being represented as quasi-finite flat group schemes.

* `structure` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiniteFlatGroup`
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.FppfHOne`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointPresheaf_isFppfSheaf`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.FppfHOne`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.fppfHOneMap`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointKernelMulEquiv`
* `structure` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.KernelPresentation`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.KernelPresentation.mapPoint_eq_one_iff_exists_kernelPoint`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.fppfHOneMulEquivOfFiniteFlat`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.fppfHOneMap_ofFiniteFlat_eq`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.canonicalAmbientKernel_pointMulEquiv`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.canonicalKernel_point_mulExact`
* `structure` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.KernelPresentation`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.KernelPresentation.pointKernelMulEquiv`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.KernelPresentation.point_mulExact`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.KernelPresentation.ofFiniteFlatCanonical_inclusion`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.KernelPresentation.commGroupSchemeKernelIso`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.KernelPresentation.ofFiniteFlat_inclusion`
* `structure` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.FppfQuotientPresentation`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.FppfQuotientPresentation.ofFiniteFlat_kernel_inclusion`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.FppfQuotientPresentation.project_point_eq_one_iff`
* `definition` (`contract`):
  `HopfLocalizationAway.hopfAlgebra`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlat`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatInclusionMap_hom`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatInclusionMap_opensRange`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatInclusionMap_contains_levelOpen`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.mazurConstantFlat`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatBasePoint_eq_one`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.mazurConstantFlatBasePointCertifiedDataOfPrimeLevel`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.muFlatBasePoint_eq_one`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.fermatMuFlatBasePointCertifiedDataOfPrimeLevel`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.middleHOne_length_le_of_fermatMuFlatKernelHZero`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom_mapPoint`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.muFlat`
* `definition` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.fermatMuFlatInclusionMap`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.fermatMuFlatInclusion_opensRange`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.fermatMuFlatInclusion_contains_levelOpen`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelPresheaf`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelProjection_app_surjective`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelSequence_exact`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatPointCokernelSequence_exact`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.muFlatPointCokernelSequence_exact`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelFppfSheaf`
* `definition` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.representedPointCokernelFppfProjection`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.representedPointCokernelFppfProjection_isLocallySurjective`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.representedPointCokernelFppfProjection_epi`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelFppfSequence_exact`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatPointCokernelFppfSequence_exact`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.muFlatPointCokernelFppfSequence_exact`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.mapPoint_surjective_of_base_preimage_eq_top`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelPresheaf_obj_isZero_of_base_preimage_eq_top`
* `theorem` (`contract`):
  `AlgebraicGeometry.CommGroupScheme.pointCokernelFppfSheafOverOpen_isZero`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.constantFlatPointCokernelFppfSheafAway_isZero`
* `theorem` (`contract`):
  `AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme.muFlatPointCokernelFppfSheafAway_isZero`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOne`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.fppfHOneClass_pullback`
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.FppfHOne.commGroup`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.fppfHOneClass_mul_of_commonRefinement`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FinitePGroup.ofFiniteFlatFppfHOne`
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.FppfHOne.mapHom`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.fppfHOneMap`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.KernelPresentation.point_mulExact`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.KernelPresentation.LocalLift.boundaryClass`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.KernelPresentation.LocalLift.boundaryClass_eq`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.locallyLiftable`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.boundaryHom`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.exact_project_boundaryHom`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.exact_boundaryHom_fppfHOneMap`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.exact_fppfHOneMap_inclusion_project`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.ofFppfQuotientPresentation`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.fppfHOne_natCard_le_pow_ofFppfQuotientPresentation`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.constantBasePointCertifiedDataInt`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.muBasePointCertifiedDataIntOfOdd`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleSimpleFactor.basePointCertifiedDataInt`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.fppfHOne_natCard_le_pow_of_admissibleKernelInt`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltrationStep.fppfHOne_natCard_le_pow_int`
* `theorem` (`proposed`):
  `AlgebraicGeometry.AdmissibleFiniteFlatGroup.hOne_sub_hZero_le`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltration.baseChange_point_pow_eq_one`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.UnitKummerClasses.pow_eq_one`
* `structure` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.middleHOne_natCard_le_pow`

The exact-sequence certificate exposes all six finite p-groups, five maps,
left injectivity, and four exactness proofs. It therefore cannot be populated
by a cardinal bound alone. The repository now supplies the fixed-universe
global colimit over actual relative fppf covers, including refinement-choice
independence, a type-level eliminator, its canonical commutative group law,
functorial coefficient maps, and a choice-independent local-lift connecting
class. The quotient-derived lifts and boundary homomorphism now compile.
Independent common-refinement arguments prove exactness at quotient `H⁰`,
kernel `H¹`, and middle `H¹`: quotient gauges are lifted on genuine fppf
refinements, and certified kernel uniqueness produces the required kernel
cocycle. All three proofs feed the concrete low-degree constructor, which
accepts no exactness hypotheses. A checked downstream consumer now applies the
exact maps directly: five endpoint finite-cardinality certificates and mere
finiteness of the middle global `H¹` imply its cardinal bound. It no longer
assumes the exact cardinal of the group being bounded. The two elementary
`H⁰` endpoint certificates in a one-step admissible quotient are now concrete:
constant global sections are indexed by `Z/pZ`, while `mu_p(ℤ)` is trivial for
odd `p`. A one-elementary-kernel quotient theorem leaves quotient certificates
explicit for recursive finite-flat use, and the actual two-factor theorem is
its compiled consumer. Ambient commutative-group-scheme `H¹` and the structural
quasi-finite wrapper now compile and agree definitionally with the finite-flat
API. Geometric kernel and fppf quotient presentations now extend this
compatibility to arbitrary certified finite-flat kernels and quotient
projections, including their chosen inclusions. The actual bad-level
constant-flat factor now compiles as a principal-open Hopf localization with
distinct coefficient and level parameters, a typed realized range and
level-open consumer, and certified trivial integral global sections. The
multiplicative-flat factor and its typed inclusion now compile, as do the raw
point-cokernel presheaves and concrete bad-level consumers. Their point maps
are surjective above `D(level)`, their point-cokernel presheaves vanish there,
and continuous site restriction carries this through sheafification to zero of
the actual fppf cokernel sheaves. The multiplicative factor's trivial
odd-coefficient `H⁰` and the low-degree Euler endpoint consumer also compile. The supported sheaf localization sequences,
quasi-finite admissible-filtration exact sequences, both bad-level `H¹`
comparisons, middle-`H¹` finiteness proof, and focused rank-zero specialization
are still absent, so no node credit is claimed.
:::

:::theorem "MT-FFGS-OORT-RAYNAUD" (parent := "prime_infrastructure") (uses := "MT-FFGS-CONNECTED-ETALE, MT-NERON-COMPONENTS") (tags := "infrastructure, blocked, nouns-missing, group-schemes") (priority := "high") (effort := "large")
*Raynaud uniqueness and the Eisenstein rank-zero criterion.* Extend the
constant and multiplicative constituents over an unramified DVR, then apply
the bounded Kummer cohomology calculation to the modular quotient.

*Status:* `blocked`.

* `theorem` (`proposed`):
  `AlgebraicGeometry.Raynaud.primeOrder_uniqueness_unramified`
* `theorem` (`proposed`):
  `AbelianVariety.rank_eq_zero_of_admissible_torsion`
:::

:::definition "MT-X0-MODULI" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, planned, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*The $`X_0(N)` point attached to rational prime torsion.* Define the
$`\Gamma_0` moduli problem and its classifying point from a rational cyclic
subgroup.

*Status:* `planned`.

* `definition` (`proposed`): `ModularCurve.XZeroModuli`
* `theorem` (`proposed`):
  `ModularCurve.XZeroModuli.pointOfRationalCyclicSubgroup`

* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.variableChange`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.VariableChangeClass`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.VariableChangeClass.lift`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.divisorSubgroup`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.VariableChangeClass.forgetToDivisor`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroThirtyFive.subgroup_five_sup_seven`
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.FiniteLocallyFreeSubgroup`
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.SplitCyclicSubgroup`
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassGroupSchemeInterface`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassGroupSchemeInterface.splitGammaZeroDatumOfTorsion`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.splitGammaZeroDatumOfRationalCyclicSubgroup`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.rationalDatumPointHom_range`
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassAbelianVarietyComparison`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassAbelianVarietyComparison.ofProjectivePointEquiv`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassAbelianVarietyComparison.splitGammaZeroDatumOfProjectivePointComparison`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassAbelianVarietyComparison.splitGammaZeroDatumPointHom_range`
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.polynomial_isHomogeneous`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.scheme`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.scheme_isReduced`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.range_inclusion`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.pointOfNonsingularRepresentative`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.ambientPoint_comp_projectivePlaneStructureMap`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.structureMap_isProper`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.toAbelianVariety`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePointToAbelianVarietyRationalPoint`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePointToAbelianVarietyRationalPoint_injective`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.chartLiftOfOverPoint_fac`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coordinateRepresentativeOfOverPoint`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coordinateRepresentativeOfOverPoint_chartIndex`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.eval_coordinateRepresentativeOfOverPoint_polynomial_eq_zero`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePointOfOverPoint`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.recoveredPointOverMorphism`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.chartRingHom_ext`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.recoveredPointOverMorphism_eq`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePointOverMorphism_surjective`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePointOverMorphism_bijective`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalProjectivePointEquivOfGroupLaw`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalProjectivePointEquiv`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.splitGammaZeroDatumOfProjectiveCubic`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.splitGammaZeroDatumOfCanonicalProjectiveCubic`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardChartRingEquiv`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardChartIdeal_isPrime`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardAffineChartScheme_isIntegral`
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.StandardChartBaseChangeWitness`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.geometricallyIntegral_of_standardChartBaseChangeWitness`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardChartSplitGammaZeroPackage_hasConstantOrder`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.affineEquationToStandardChartRingEquiv`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalStandardOpenMap_opensRange_eq_preimage_basicOpen`
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.StandardChartComparison`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.geometricallyIntegral_of_standardChartComparison`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.toAbelianVarietyOfStandardChartComparison`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveGradedCoefficientMap_irrelevant_le`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePlaneBaseChangeProjection`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardAway_comp_projectivePlaneBaseChangeProjection`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveSpectrum_comap_mem_weierstrassZeroLocus_iff`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.StandardChartComparison.IsAmbientCompatible`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.StandardChartComparison.canonicalStandardOpenMap_opensRange_eq_preimage_mapped`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePlaneBaseChange_isPullback`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePlanePullbackIso`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePlanePullbackIso_mem_mappedWeierstrassZeroLocus_iff`

The generated split rational subgroup and raw datum compile. Admissible
Weierstrass changes transport both the curve and subgroup, and checked code
quotients by the generated equivalence and descends every
presentation-invariant function. Intrinsic divisor subgroups, split
divisor-level degeneracy maps, and reconstruction from the order-five and
order-seven carriers at level 35 also compile. The scheme layer packages an
actual finite-locally-free closed subgroup, arbitrary base change, and an
identification with the constant cyclic group. Exact rational torsion gives a
genuine split Γ₀ source datum relative to a narrow Weierstrass group-scheme
interface, and a checked consumer identifies its rational point range with
the existing carrier. More generally, every supplied split rational cyclic
subgroup directly produces such a finite-flat datum: its intrinsic carrier is
the constant source, its point homomorphism is exactly subgroup inclusion, and
choice of a cyclic generator occurs only in the splitness isomorphism. Raw
rational Γ₀ data is a checked downstream consumer with exact point range. A genuine Tau Ceti abelian variety plus a comparison of
its rational points with Mathlib's projective Weierstrass points now supplies
that interface and feeds the same consumer. The homogeneous cubic now also
defines an actual reduced closed subscheme of projective two-space, with
reducedness checked affine-locally from its radical vanishing ideals, its closed
immersion, exact zero-locus range, and proper structure map. Nonsingular
coordinate triples now give actual morphisms from `Spec K` to the cubic, and
the canonical affine normalization gives a forward map from Mathlib projective
points to cubic `K`-points. Homogeneous linear vanishing equations recover the
normalized coordinates, proving this forward map injective. The compiled
canonical finite-flat consumer therefore reduces point comparison to the group-law
compatibility of this explicit map. In the reverse direction,
the coordinate basic opens now give an actual affine-chart factor for every
scheme-valued cubic point; the induced homogeneous-localization ring map
extracts a normalized nonzero coordinate triple, fixes base-field constants,
and evaluates every homogeneous fraction through those ratios. The extracted
triple now satisfies the cubic equation and, under ellipticity, is proved
nonsingular, yielding an actual Mathlib projective point and a compiled forward
recovered-point morphism. Chart-ring extensionality and invariance of the ambient
closed point under affine normalization prove that this recovered morphism equals
the original. The canonical projective-point map is therefore surjective and,
together with the earlier injectivity proof, bijective. The standard `Z ≠ 0`
homogeneous localization is explicitly equivalent to the affine bivariate
polynomial ring; the localized cubic becomes the affine Weierstrass
polynomial, its equation ideal is prime, and the quotient chart is integral. A
second equivalence identifies the affine equation quotient with that localized
homogeneous chart. For every field extension, the canonical standard open of
the actual pullback is constructed by pulling back `Proj.awayι`; it is an open
immersion whose range is exactly the inverse image of `D₊(Z)`. A checked
comparison structure isolates the remaining projective base-change
isomorphism, chart/open isomorphism, and density. Its projective isomorphism
derives target reducedness, and its consumer reaches both geometric
integrality and Tau Ceti's abelian-variety constructor; the earlier split-`Γ₀`
consumer then reaches constant geometric order. Graded coefficient extension
now constructs the ambient map `P²_L ⟶ P²_K`; the required irrelevant-ideal
inclusion is proved from the coordinate generators. This map fixes the three
coordinates, carries the cubic polynomial to the mapped equation, has the
checked `D₊(Z)` away-chart square, and preserves the cubic zero locus on
projective-spectrum points. An explicit ambient-compatibility predicate for the
still-open target isomorphism has a compiled consumer identifying the actual
pullback's canonical-open range with the mapped cubic's coordinate open. The
three normalized affine coordinate charts are now proved to be pullbacks and
glued over their open cover, so the complete ambient projective-plane square is
a pullback. Its canonical isomorphism with `P²_L` satisfies both projection
laws, and a cubic zero-locus consumer identifies the mapped equation with the
inverse image of the original equation. Restriction of that ambient
isomorphism to an ambient-compatible reduced cubic is still open. The chart/open
isomorphism and density, the scheme group law and compatibility, `E/C`, the coarse modular
point, and the required Atkin--Lehner geometry remain open, so this node
receives no completion credit.
:::

:::definition "MT-X0-INTEGRAL" (parent := "prime_infrastructure") (uses := "MT-X0-MODULI") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*Integral $`X_0(N)`, cusp completions, and auxiliary q-parameters.* Build the
smooth cusp neighbourhood at the prime-to-level auxiliary characteristics
five and eleven, and only the additional level-$`N` geometry consumed by
toric reduction of the modular Jacobian.

*Status:* `blocked`.

* `structure` (`proposed`): `ModularCurve.IntegralXZero`
* `definition` (`contract`): `AlgebraicGeometry.IsFormalImmersionAt`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.sourceFinrank_eq_one_of_smoothRelativeCurve`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.residueFieldMap_isIso_at_rationalPoint`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.QExpansionFirstCoefficient.coeff_one_completion_eq_zero_of_mem_maximalIdeal_sq`
* `theorem` (`contract`):
  `AlgebraicGeometry.IsFormalImmersionAt.spec_ext_of_stalkClosedPointTo`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.CompleteDVRCoordinate.ringEquiv`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.CompleteDVRStalk.rationalSectionStalkCompletionRingEquiv`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.CompleteDVRStalk.descResidueField_isIso_of_rationalSection`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.CompleteDVRStalk.descResidueField_isIso_of_rationalSection_comp`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.CompleteDVRStalk.isFormalImmersionAt_of_rationalSection_overBaseStalkDVR_heckeEigenQExpansion`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.CompleteDVRStalk.spec_eq_of_rationalSectionStalkDVR_normalizedQExpansion_of_comp_eq`
* `theorem` (`proposed`):
  `ModularCurve.IntegralXZero.completedLocalRingAtInfinity_of_auxiliaryPrime`

The functorial completed-stalk map and the actual formal-immersion predicate
now compile with identity and composition consumers. The canonical
stalk-cotangent map and its residue-honest first-order criterion also compile.
The finite-maximal-ideal Nakayama consequence and surjectivity modulo the
square compile with a modular degree-one consumer. The residue/cotangent
criterion now implies surjectivity on completed stalks under finite maximal
ideals, and locally Noetherian schemes supply those finiteness instances. At a
non-generic point of a smooth integral relative curve, the checked DVR theorem
supplies cotangent dimension one; literal rationality of the point and its
image supplies the residue-field isomorphism. A genuine completed-stalk
power-series coordinate now transports membership in the square of the stalk
maximal ideal to vanishing of the first q-coefficient. A complete domain DVR
with a coefficient field and irreducible uniformizer now constructs the
coordinate in the opposite direction. For an actual rational section, the
structural map now supplies the coefficient algebra, the section equation
retracts it and proves the source residue field is the base field, and the
over-base quotient equation proves the image residue field is also the base.
A nonzero simultaneous Hecke eigen-expansion now feeds the actual formal
immersion predicate and separates arbitrary Noetherian local sections with
equal quotient image. The integral cusp model, its non-generic section and
uniformizer, and the actual modular q-expansion remain open, so this node
receives no completion credit.
:::

:::definition "MT-X0-CUSPS" (parent := "prime_infrastructure") (uses := "MT-X0-INTEGRAL") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*Cusps, Atkin--Lehner transport, and reduction type.* Move a squarefree-level
cusp to infinity and identify cusp specialization with potentially
multiplicative reduction at a prime-to-level auxiliary prime.

*Status:* `blocked`.

* `definition` (`proposed`): `ModularCurve.XZero.infinityCusp`
* `definition` (`proposed`): `ModularCurve.XZero.atkinLehner`
* `theorem` (`proposed`):
  `ModularCurve.XZero.specializesToCusp_iff_potentiallyMultiplicative`
:::

:::definition "MT-X0-JACOBIAN" (parent := "prime_infrastructure") (uses := "MT-X0-INTEGRAL, MT-TC-E1-JACOBIAN-VARIETY, MT-TC-F1-ABEL-JACOBI") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*The modular Jacobian and cusp-based Abel--Jacobi map.* Normalize the map by
$`x\mapsto[x]-[\infty]` and expose the base-change interface used downstream.

*Status:* `blocked`.

* `structure` (`proposed`): `ModularCurve.ModularJacobian`
* `definition` (`proposed`): `ModularCurve.XZero.abelJacobiAtInfinity`
:::

:::definition "MT-X0-HECKE" (parent := "prime_infrastructure") (uses := "MT-X0-JACOBIAN, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, blocked, nouns-missing, hecke") (priority := "high") (effort := "large")
*Hecke action and cotangent q-expansions.* The Hecke recursions make the first
Fourier coefficient detect every nonzero simultaneous eigenvector in the
cotangent space of a nontrivial quotient.

*Status:* `blocked`.

* `definition` (`proposed`): `ModularCurve.HeckeOperator`
* `theorem` (`proposed`):
  `ModularCurve.HeckeOperator.qExpansion_firstCoefficient_ne_zero`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_normalizedQExpansion`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.specMap_fromStalk_eq_of_normalizedQExpansion`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.specMap_fromStalk_eq_of_completeDVR_normalizedQExpansion`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.HeckeFirstCoefficient.coeff_one_ne_zero_of_simultaneousEigenvector`
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.isFormalImmersionAt_of_heckeEigen_qExpansion`

The checked `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate` is the
provisional target for this calculation: it requires a residue-field
isomorphism, dimension one over the actual source residue field, and one
vector detected by the canonical semilinear cotangent map. A target local
parameter whose completed pullback is `c*q + q^2*F`, with `c` nonzero, now
instantiates that certificate and proves actual completed-stalk formal
immersion. Named consumers carry both a supplied coordinate and the constructed
complete-DVR coordinate through to equality of canonical local-spectrum maps.
The abstract first-coefficient argument now proves that a nonzero simultaneous
eigen-expansion has nonzero coefficient in degree one and feeds that result to
the real completed-stalk formal-immersion theorem. The missing Hecke work is
the modular/Jacobian action and its checked expansion identity at auxiliary
characteristics five and eleven.
:::

:::definition "MT-X0-EISENSTEIN-ALGEBRA" (parent := "prime_infrastructure") (uses := "MT-X0-HECKE, MT-X0-INTEGRAL") (tags := "proof, blocked, nouns-missing, formal-immersion") (priority := "high") (effort := "large")
*Optimal quotients and formal immersion at the cusp.* Prove Mazur's
Proposition 3.1 away from characteristic two.  The prime proof consumes its
characteristic-five instance and the order-35 endpoint consumes eleven.

*Status:* `blocked`.

* `structure` (`proposed`): `ModularCurve.OptimalNewQuotient`
* `theorem` (`proposed`):
  `ModularCurve.OptimalNewQuotient.formalImmersionAtInfinity_of_residueChar_ne_two`
:::

:::theorem "MT-X0-EISENSTEIN-QUOTIENT" (parent := "prime_infrastructure") (uses := "MT-X0-CUSPS, MT-X0-EISENSTEIN-ALGEBRA, MT-NERON-SPECIALIZATION, MT-FFGS-OORT-RAYNAUD") (tags := "proof, blocked, nouns-missing, eisenstein") (priority := "high") (effort := "large")
*A nontrivial rank-zero Eisenstein quotient.* Construct it for $`N=11` or
prime $`N\ge17`, prove finite rational points, and instantiate the formal-
immersion theorem.  Exact cusp order is intentionally not an acceptance API.

*Status:* `blocked`.

* `structure` (`proposed`): `ModularCurve.EisensteinQuotient`
* `theorem` (`proposed`):
  `ModularCurve.EisensteinQuotient.nontrivial_of_level_eleven_or_ge_seventeen`
* `theorem` (`proposed`):
  `ModularCurve.EisensteinQuotient.mordellWeil_finite`
* `theorem` (`proposed`):
  `ModularCurve.EisensteinQuotient.formalImmersionAtInfinity_modFive`
:::

:::theorem "MT-CYCLOTOMIC-UNRAMIFIED" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "proof, research-open, compiled, number-theory, release-obligation") (priority := "high") (effort := "large")
*Inherited cyclotomic Challenge closure.* Finish the checked Kummer--Artin
pipeline as an independent reusable result. It remains mandatory for project
release, but no theorem arrow runs from it into the formal-immersion proof.

*Status:* `research_open`; *scope:* the immutable compiled Challenge.

* `definition` (`proposed`):
  `NumberTheory.CyclotomicCharacter.inverseExtension`
* `theorem` (`proposed`):
  `NumberTheory.CyclotomicCharacter.unramifiedAtFinitePlaces`
* `theorem` (`proposed`):
  `NumberTheory.CyclotomicCharacter.noEverywhereUnramified`
* `theorem` (`contract`):
  `NumberTheory.CyclotomicCharacter.locallyPrimaryPseudoUnitKummerReciprocityPrinciple`
:::
