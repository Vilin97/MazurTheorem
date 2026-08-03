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
exactness at quotient-valued global sections is checked. The next boundary is
the two reverse `H¹` exactness inclusions and the resulting Kummer sequence.

* `structure` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiniteFlatGroup`
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.FppfHOne`
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
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.ofFppfQuotientPresentation`
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
class. The quotient-derived lifts, boundary homomorphism, and exactness at the
quotient `H⁰` term now compile and feed the concrete low-degree constructor.
The two reverse `H¹` exactness inclusions are still absent; no node credit is
claimed.
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
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalProjectivePointEquiv`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.splitGammaZeroDatumOfProjectiveCubic`
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.splitGammaZeroDatumOfCanonicalProjectiveCubic`

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
the existing carrier. A genuine Tau Ceti abelian variety plus a comparison of
its rational points with Mathlib's projective Weierstrass points now supplies
that interface and feeds the same consumer. The homogeneous cubic now also
defines an actual reduced closed subscheme of projective two-space, with
reducedness checked affine-locally from its radical vanishing ideals, its closed
immersion, exact zero-locus range, and proper structure map. Nonsingular
coordinate triples now give actual morphisms from `Spec K` to the cubic, and
the canonical affine normalization gives a forward map from Mathlib projective
points to cubic `K`-points. Homogeneous linear vanishing equations recover the
normalized coordinates, proving this forward map injective. The compiled
canonical finite-flat consumer therefore reduces point comparison to group-law
compatibility and surjectivity of this explicit map. The scheme group law,
geometric integrality, surjectivity, `E/C`, the coarse modular point, and the
required Atkin--Lehner geometry remain open, so this node receives no completion
credit.
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
