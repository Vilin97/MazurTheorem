import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "04 — Prime-level infrastructure" =>

:::group "prime_infrastructure"
Néron models, finite-flat group schemes, integral modular curves, Hecke
operators, and the Eisenstein quotient. Stage weight: 400 points.
:::

:::definition "MT-NERON-BASE" (parent := "prime_infrastructure") (uses := "MT-TC-E1-JACOBIAN-VARIETY, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, blocked, nouns-missing, neron") (priority := "high") (effort := "large")
*Néron models over discrete valuation rings.* Construct the smooth separated
model of an abelian variety, recover its generic fibre, and expose the Néron
mapping property.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `AlgebraicGeometry.NeronModel`
  Package a smooth separated model over a discrete valuation ring together with its
  generic fibre.
* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.genericFiberEquiv`
  Identify the generic fibre of a Neron model with the original smooth group variety.
* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.mappingProperty`
  State the Neron mapping property as a unique extension theorem for smooth test
  schemes.
:::

:::definition "MT-NERON-COMPONENTS" (parent := "prime_infrastructure") (uses := "MT-NERON-BASE") (tags := "infrastructure, blocked, nouns-missing, neron") (priority := "high") (effort := "large")
*Identity components and component groups.* Construct the open identity
component of a Néron model and the finite component group of its special fibre.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `AlgebraicGeometry.NeronModel.identityComponent`
  Define the open identity component of the special fibre of a Neron model.
* `definition` (`proposed`): `AlgebraicGeometry.NeronModel.componentGroup`
  Define the finite component group of the special fibre.
* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.specializationExact`
  Expose the exact sequence relating integral points, the identity component, and the
  component group.
:::

:::theorem "MT-NERON-SPECIALIZATION" (parent := "prime_infrastructure") (uses := "MT-NERON-COMPONENTS") (tags := "infrastructure, blocked, nouns-missing, neron") (priority := "high") (effort := "large")
*Torsion specialization through Néron models.* Prime-to-residue-characteristic
torsion specializes injectively into the identity component plus component
group, in exactly the form consumed by Mazur's argument.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.primeToResidueTorsion_injective`
  Prove injectivity of specialization on torsion prime to the residue characteristic.
* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.torsion_componentGroup`
  Relate torsion points outside the identity component to the special-fibre component
  group.
:::

:::definition "MT-FFGS-BASIC" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, planned, nouns-missing, group-schemes") (priority := "high") (effort := "large")
*Finite-flat commutative group schemes.* Build the category, kernels,
quotients, and base change, tested on constant groups, $`\mu_p`, and
multiplication kernels.

*Status:* `planned`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme`
  Package finite flat commutative group schemes over an arithmetic base.
* `definition` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernel`
  Construct kernels of morphisms in the finite-flat group-scheme category.
* `definition` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.quotient`
  Construct quotients by finite-flat closed subgroup schemes.
* `theorem` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.baseChange`
  Prove compatibility of kernels and quotients with the required base changes.
:::

:::theorem "MT-FFGS-CONNECTED-ETALE" (parent := "prime_infrastructure") (uses := "MT-FFGS-BASIC") (tags := "infrastructure, blocked, nouns-missing, group-schemes") (priority := "high") (effort := "large")
*Connected–étale sequence.* Every finite-flat commutative group scheme in the
required local setting has a functorial connected–étale exact sequence,
compatible with base change.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.connectedComponent`
  Define the connected identity component of a finite-flat commutative group scheme.
* `definition` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.etaleQuotient`
  Define the maximal etale quotient in the connected-etale sequence.
* `theorem` (`proposed`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.connectedEtale_exact`
  Prove exactness, functoriality, and base-change compatibility of the connected-etale
  sequence.
:::

:::theorem "MT-FFGS-OORT-RAYNAUD" (parent := "prime_infrastructure") (uses := "MT-FFGS-CONNECTED-ETALE") (tags := "infrastructure, blocked, nouns-missing, group-schemes") (priority := "high") (effort := "large")
*Oort–Tate classification and Raynaud uniqueness.* Classify finite-flat
group schemes of prime order and prove the uniqueness statements controlling
extensions of generic-fibre subgroup schemes.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `theorem` (`proposed`): `AlgebraicGeometry.OortTate.classification`
  Classify finite-flat commutative group schemes of prime order over the required
  arithmetic bases.
* `theorem` (`proposed`): `AlgebraicGeometry.Raynaud.primeOrder_uniqueness`
  Prove the uniqueness theorem for finite-flat prime-order models used in the
  semistability argument.
:::

:::definition "MT-X0-MODULI" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, planned, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*The $`\Gamma_0` modular-curve moduli problem.* Define elliptic curves with
cyclic finite-flat subgroups and their isomorphisms, families, and base change.

*Status:* `planned`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `ModularCurve.GammaZeroStructure`
  Package an elliptic curve together with a cyclic finite-flat subgroup of order N.
* `definition` (`proposed`): `ModularCurve.XZeroModuli`
  Define the Gamma-zero moduli functor with its isomorphisms and base-change action.
:::

:::definition "MT-X0-INTEGRAL" (parent := "prime_infrastructure") (uses := "MT-X0-MODULI") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*Integral compactified $`X_0(N)`.* Construct the compactification used by
Mazur and prove its generic-fibre and reduction interfaces.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `ModularCurve.IntegralXZero`
  Package the proper integral compactification of the Gamma-zero moduli problem.
* `theorem` (`proposed`): `ModularCurve.IntegralXZero.genericFiber`
  Identify the generic fibre with the characteristic-zero modular curve $`X_0(N)`.
* `theorem` (`proposed`): `ModularCurve.IntegralXZero.reductionCompatibility`
  Expose the reduction and specialization interfaces consumed by Mazur's argument.
:::

:::definition "MT-X0-CUSPS" (parent := "prime_infrastructure") (uses := "MT-X0-INTEGRAL") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*Cusps and the rational cusp divisor.* Construct the rational cusps, their
specializations, and the degree-zero difference of the zero and infinity cusps.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `ModularCurve.XZero.cusp`
  Define the rational cusp sections on the integral modular curve.
* `definition` (`proposed`): `ModularCurve.XZero.cuspDifference`
  Define the degree-zero divisor class given by the difference of the two rational
  cusps.
* `theorem` (`proposed`): `ModularCurve.XZero.cusp_specialization`
  Prove the cusp sections and their divisor class specialize compatibly at the
  required primes.
:::

:::definition "MT-X0-JACOBIAN" (parent := "prime_infrastructure") (uses := "MT-X0-INTEGRAL, MT-TC-E1-JACOBIAN-VARIETY, MT-TC-F1-ABEL-JACOBI") (tags := "infrastructure, blocked, nouns-missing, modular-curves") (priority := "high") (effort := "large")
*The modular Jacobian $`J_0(N)`.* Instantiate the shared Jacobian and
Abel–Jacobi APIs on $`X_0(N)`, compatibly with the integral model.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `ModularCurve.ModularJacobian`
  Instantiate the shared Jacobian construction on the modular curve $`X_0(N)`.
* `definition` (`proposed`): `ModularCurve.ModularJacobian.abelJacobi`
  Define the Abel-Jacobi map from $`X_0(N)` using a chosen rational cusp.
* `theorem` (`proposed`): `ModularCurve.ModularJacobian.integralCompatibility`
  Prove compatibility of the modular Jacobian and Abel-Jacobi map with the integral
  model.
:::

:::definition "MT-X0-HECKE" (parent := "prime_infrastructure") (uses := "MT-X0-JACOBIAN, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, blocked, nouns-missing, hecke") (priority := "high") (effort := "large")
*Hecke correspondences on $`J_0(N)`.* Construct the correspondences and their
endomorphism action, including base-change and composition laws.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `ModularCurve.HeckeCorrespondence`
  Package the two finite maps defining a Hecke correspondence on $`X_0(N)`.
* `definition` (`proposed`): `ModularCurve.ModularJacobian.heckeOperator`
  Construct the induced Hecke endomorphism of the modular Jacobian.
* `theorem` (`proposed`): `ModularCurve.ModularJacobian.hecke_comp`
  Prove the required composition, base-change, and isogeny compatibility laws.
:::

:::definition "MT-X0-EISENSTEIN-ALGEBRA" (parent := "prime_infrastructure") (uses := "MT-X0-HECKE") (tags := "proof, blocked, nouns-missing, eisenstein") (priority := "high") (effort := "large")
*The Eisenstein ideal and Hecke quotient.* Define the Eisenstein ideal and
prove the finite-quotient and local-principality interfaces used by the
arithmetic quotient.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `ModularCurve.EisensteinIdeal`
  Define the ideal in the Hecke algebra generated by the Eisenstein relations.
* `definition` (`proposed`): `ModularCurve.EisensteinHeckeQuotient`
  Define the finite Hecke-algebra quotient cut out by the Eisenstein ideal.
* `theorem` (`proposed`): `ModularCurve.EisensteinIdeal.locallyPrincipal`
  Prove the local-principality input required to control the associated quotient of
  $`J_0(N)`.
:::

:::theorem "MT-X0-EISENSTEIN-QUOTIENT" (parent := "prime_infrastructure") (uses := "MT-X0-CUSPS, MT-X0-EISENSTEIN-ALGEBRA, MT-NERON-SPECIALIZATION, MT-FFGS-OORT-RAYNAUD") (tags := "proof, blocked, nouns-missing, eisenstein") (priority := "high") (effort := "large")
*Arithmetic of the Eisenstein quotient.* Construct the quotient and prove
that its rational Mordell–Weil group is finite, the cusp difference has the
expected exact order, and its image is nonzero.

*Status:* `blocked`.

*Canonical deliverables — these names are authoritative for this node:*

* `structure` (`proposed`): `ModularCurve.EisensteinQuotient`
  Construct the abelian-variety quotient of $`J_0(N)` determined by the Eisenstein
  ideal.
* `theorem` (`proposed`): `ModularCurve.EisensteinQuotient.mordellWeil_finite`
  Prove finiteness of the rational Mordell-Weil group of the Eisenstein quotient.
* `theorem` (`proposed`): `ModularCurve.EisensteinQuotient.cuspDifference_order`
  Compute the exact order of the rational cusp-difference class in the quotient.
* `theorem` (`proposed`): `ModularCurve.EisensteinQuotient.cuspDifference_ne_zero`
  Prove that the cusp-difference image is nonzero in the cases used by specialization.
:::

:::theorem "MT-CYCLOTOMIC-UNRAMIFIED" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "proof, research-open, compiled, number-theory") (priority := "high") (effort := "large")
*Cyclotomic unramified character extensions.* The inverse-character extension,
its ideal-local ramification criteria, and its class-group obstruction now have
checked interfaces. Integral one-sided Kummer reciprocity for locally-primary
pseudo-units remains the registered research contract; checked reductions turn
it into the principal Kummer--Artin product formula and descend the finite-prime
Artin map to the ideal class group over $`\mathbb{Q}(\zeta_p)`.

*Status:* `research_open`.

*Canonical deliverables — these names are authoritative for this node:*

* `definition` (`proposed`): `NumberTheory.CyclotomicCharacter.inverseExtension`
  Package the inverse-cyclotomic character extension over the p-th cyclotomic field.
* `theorem` (`proposed`): `NumberTheory.CyclotomicCharacter.unramifiedAtFinitePlaces`
  Give the local criterion showing that the relevant extension is unramified at every
  finite place.
* `theorem` (`proposed`): `NumberTheory.CyclotomicCharacter.noEverywhereUnramified`
  Exclude an everywhere-unramified inverse-cyclotomic extension using the required
  class-field input.
* `theorem` (`contract`):
  `NumberTheory.CyclotomicCharacter.locallyPrimaryPseudoUnitKummerReciprocityPrinciple`
  Prove integral one-sided Kummer reciprocity for locally-primary
  pseudo-units; checked comparison and normalization reductions then supply
  principal Artin reciprocity and the inverse-character class-group quotient.
:::
