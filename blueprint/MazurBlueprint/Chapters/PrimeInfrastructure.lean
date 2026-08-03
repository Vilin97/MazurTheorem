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

:::definition "MT-FFGS-BASIC" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, planned, compiled, group-schemes") (priority := "high") (effort := "large")
*Finite-flat commutative group schemes for Eisenstein rank zero.* Retain the
checked category, honest kernel presentations, affine Hopf realization,
constant/diagonalizable examples, $`\mu_n` multiplication kernel,
constant-rank point-exponent consumer, and constant-group quotients. Finish
the generic quotient/base-change boundary only through the
admissible-filtration consumer.

*Status:* `planned`; partial compiled work earns no completion credit.

* `structure` (`contract`): `AlgebraicGeometry.FiniteFlatCommGroupScheme`
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernelPresentation_exists_of_finite_flat`
* `theorem` (`contract`):
  `AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.point_pow_eq_one_of_constantRank`
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernel`
* `definition` (`proposed`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.quotient`
* `theorem` (`proposed`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange`
* `definition` (`proposed`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.constantAndMu`
:::

:::theorem "MT-FFGS-CONNECTED-ETALE" (parent := "prime_infrastructure") (uses := "MT-FFGS-BASIC") (tags := "infrastructure, blocked, nouns-missing, group-schemes") (priority := "high") (effort := "large")
*Admissible filtrations and fppf cohomology.* Formalize the exact filtration
and cohomology estimate used in Mazur's rank-zero proof, rather than an
unconsumed general connected--étale library.

*Status:* `blocked`.

* `definition` (`proposed`): `AlgebraicGeometry.AdmissibleFiniteFlatGroup`
* `definition` (`proposed`):
  `AlgebraicGeometry.AdmissibleFiniteFlatGroup.fppfHOne`
* `theorem` (`proposed`):
  `AlgebraicGeometry.AdmissibleFiniteFlatGroup.hOne_sub_hZero_le`
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
:::

:::definition "MT-X0-INTEGRAL" (parent := "prime_infrastructure") (uses := "MT-X0-MODULI") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*Integral $`X_0(N)`, cusp completions, and auxiliary q-parameters.* Build the
smooth cusp neighbourhood at the prime-to-level auxiliary characteristics
five and eleven, and only the additional level-$`N` geometry consumed by
toric reduction of the modular Jacobian.

*Status:* `blocked`.

* `structure` (`proposed`): `ModularCurve.IntegralXZero`
* `definition` (`proposed`): `AlgebraicGeometry.IsFormalImmersionAt`
* `theorem` (`proposed`):
  `ModularCurve.IntegralXZero.completedLocalRingAtInfinity_of_auxiliaryPrime`
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
