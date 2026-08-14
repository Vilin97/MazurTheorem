import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "04 — Prime-level infrastructure" =>

:::group "prime_infrastructure"
Integral X₀(N), its Jacobian and Hecke action, a private Eisenstein witness constructor,
and the exact Néron/finite-flat specialization needed at 5. Stage weight: 400 points.
:::

:::theorem "MT-NERON-BASE" (parent := "prime_infrastructure") (uses := "MT-TC-E1-JACOBIAN-VARIETY, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Neron models for the two surviving consumers.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 40 points.

*Summary:* Construct Neron models and their mapping property in the exact generality
used by the Eisenstein rank-zero criterion and by elliptic-curve reduction at 5.

*Canonical artifacts:*

* `structure` (`proposed`): `AlgebraicGeometry.NeronModel`
  Package a smooth separated model with generic-fibre recovery and the Neron mapping
  property.
* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.sectionExtension`
  Extend the rational sections used by the rank-zero and prime-five consumers.

:::

:::theorem "MT-NERON-COMPONENTS" (parent := "prime_infrastructure") (uses := "MT-NERON-BASE") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Identity components and tame elliptic fibres.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 30 points.

*Summary:* Define genuine Neron identity components and component groups and prove
completely toric reduction at the modular level for the Eisenstein rank-zero criterion.

*Canonical artifacts:*

* `definition` (`proposed`): `AlgebraicGeometry.NeronModel.identityComponent`
  Define the fibrewise identity component used in both surviving consumers.
* `definition` (`proposed`): `AlgebraicGeometry.NeronModel.componentGroup`
  Define the component quotient and its specialization map.
* `theorem` (`proposed`):
  `EllipticCurve.NeronModel.additive_componentGroup_card_le_four_of_residueChar_gt_three`
  Bound the additive component group in the tame residue characteristics five and
  eleven.
* `structure` (`contract`): `MazurTorsion.EllipticCurve.TameAdditiveReductionData`
  Package the canonical component quotient, identity-component reduction map, and exact
  formal-kernel comparison, with a compiled conversion to the algebraic torsion
  filtration.
* `structure` (`contract`): `MazurTorsion.EllipticCurve.TameAdditiveReductionDataAtFive`
  Fix the reduction target to the actual five-adic residue field and derive component
  finiteness and formal-kernel torsion from checked exact-pin theorems.
* `structure` (`contract`):
  `MazurTorsion.EllipticCurve.TameAdditiveReductionDataAtEleven`
  Provide the analogous canonical eleven-adic handoff consumed by the order-35 route.
* `definition` (`contract`): `WeierstrassCurve.Affine.HasNonsingularReduction`
  Define the canonical domain: formal-kernel points reduce to infinity, while other
  local points have integral coordinates reducing to the nonsingular locus.
* `definition` (`contract`): `WeierstrassCurve.Affine.nonsingularReduction`
  Construct actual coordinatewise reduction from the canonical domain to nonsingular
  points of the reduced Weierstrass cubic.
* `theorem` (`proposed`): `ModularCurve.Jacobian.completelyToricReductionAtLevel`
  Supply the toric special-fibre hypothesis for the Eisenstein rank-zero criterion.

:::

:::theorem "MT-NERON-SPECIALIZATION" (parent := "prime_infrastructure") (uses := "MT-NERON-COMPONENTS") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Torsion specialization at the Eisenstein quotient and at five.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 30 points.

*Summary:* Prove the specialization exact sequence, prime-to-residue torsion injection,
and the unramified e \< p-1 kernel lemma; exercise them on the quotient section and the
marked elliptic point at 5.

*Canonical artifacts:*

* `theorem` (`proposed`): `AlgebraicGeometry.NeronModel.torsionSpecialization_exact`
  Give the torsion specialization sequence through the identity component and formal
  kernel.
* `theorem` (`proposed`):
  `AlgebraicGeometry.NeronModel.primeToResidue_torsion_injective`
  Inject torsion of order prime to the residue characteristic.
* `theorem` (`proposed`):
  `AlgebraicGeometry.NeronModel.torsion_eq_zero_of_specializes_zero_of_ramification_lt`
  Kill a torsion section in the formal kernel when e \< p - 1, including the unramified
  prime-five and prime-eleven cases.
* `theorem` (`contract`):
  `AlgebraicGeometry.NeronModel.finrank_genericBasePoint_eq_zero_of_powerKummer_kernelData`
  Transport the actual-kernel power-Kummer rank-zero theorem from integral model points
  to rational points of the supplied generic fibre through the checked Neron
  mapping-property equivalence.

:::

:::theorem "MT-FFGS-BASIC" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, done, integrated, mixed")
*Finite-flat commutative group schemes for Eisenstein rank zero.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 20 points.

*Summary:* The checked substrate packages finite-flat commutative group schemes,
certified scheme-theoretic kernels, affine Hopf realizations, constant and
diagonalizable examples, mu\_n multiplication kernels, constant-group quotients, and an
exact supplied fppf quotient presentation.

*Canonical artifacts:*

* `structure` (`integrated`): `AlgebraicGeometry.FiniteFlatCommGroupScheme`
  The checked finite-flat commutative group-scheme category over an arbitrary scheme
  base.
* `theorem` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernelPresentation_exists_of_finite_flat`
  Package inherited scheme-theoretic kernels under explicit finite-flat hypotheses.
* `theorem` (`integrated`):
  `AlgebraicGeometry.AffineFiniteFlatCommGroupScheme.point_pow_eq_one_of_constantRank`
  The checked Deligne-style point-exponent theorem is a real consumer of the affine
  finite-flat substrate.
* `definition` (`integrated`): `AlgebraicGeometry.FiniteFlatCommGroupScheme.kernel`
  Construct the inherited scheme-theoretic kernel under the exact finite and flat
  hypotheses required over an arbitrary base.
* `structure` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation`
  Package exactly the supplied finite-flat quotient, fppf projection, and certified
  scheme-theoretic kernel used by admissible filtrations; no unconsumed general quotient
  representability theorem is asserted.
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.KernelPresentation.baseChange`
  Construct the certified scheme-theoretic kernel of a pulled-back homomorphism and
  prove that both its scheme and inclusion are the geometric pullbacks of the original
  kernel data.
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientPresentation.baseChangePresentation`
  Pull the exact quotient presentation back along an arbitrary base morphism, using
  geometric stability of fppf morphisms and certified kernel base change.
* `definition` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleSimpleFactor.baseChange`
  Transport the named constant Z/p and mu\_p factor presentations across scalar
  extension.
* `theorem` (`integrated`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltrationStep.baseChange_point_pow_sq_eq_one`
  Compile the downstream rank-zero-oriented consumer: every affine point in a
  base-changed exact two-factor filtration step is killed by p^2.

:::

:::theorem "MT-FFGS-CONNECTED-ETALE" (parent := "prime_infrastructure") (uses := "MT-FFGS-BASIC") (tags := "infrastructure, planned, compiled, mixed")
*Admissible filtrations and fppf cohomology.*

*Status:* `planned`; *readiness:* `compiled`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 20 points.

*Summary:* The exact iterated constant-or-multiplicative filtration,
arbitrary-base-change exponent consumer, unit Kummer quotient, and finite-p-group
low-degree Euler estimate compile.

*Canonical artifacts:*

* `structure` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiniteFlatGroup`
  Package an honest recursive exact filtration whose graded kernels are the checked
  constant Z/p or multiplicative mu\_p factors.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.FppfHOne`
  Globalize relative cover-level nonabelian H1 over genuine fppf covers by the
  common-refinement quotient in Scheme.Over X.
* `theorem` (`contract`): `AlgebraicGeometry.CommGroupScheme.pointPresheaf_isFppfSheaf`
  Apply subcanonicity to the represented point presheaf of an arbitrary ambient
  commutative group scheme, without a finiteness hypothesis.
* `definition` (`contract`): `AlgebraicGeometry.CommGroupScheme.FppfHOne`
  Instantiate the checked common-refinement fppf H1 construction for an arbitrary
  represented commutative group-scheme coefficient.
* `definition` (`contract`): `AlgebraicGeometry.CommGroupScheme.fppfHOneMap`
  Apply an arbitrary ambient commutative group-scheme morphism to global fppf H1 by the
  represented point-presheaf natural transformation, with checked identity and
  composition laws.
* `theorem` (`proposed`):
  `AlgebraicGeometry.AdmissibleFiniteFlatGroup.hOne_sub_hZero_le`
  Prove Mazur's filtration estimate by reduction to the elementary graded pieces.

:::

:::theorem "MT-FFGS-OORT-RAYNAUD" (parent := "prime_infrastructure") (uses := "MT-FFGS-CONNECTED-ETALE, MT-NERON-COMPONENTS") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Raynaud uniqueness and the Eisenstein rank-zero criterion.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 40 points.

*Summary:* Prove the unramified order-p uniqueness theorem needed to extend admissible
Galois constituents, then assemble the bounded-Kummer-cohomology criterion that forces
the Eisenstein quotient to have Mordell-Weil rank zero.

*Canonical artifacts:*

* `theorem` (`proposed`): `AlgebraicGeometry.Raynaud.primeOrder_uniqueness_unramified`
  Extend constant and multiplicative generic fibres uniquely over an unramified DVR.
* `theorem` (`proposed`): `AbelianVariety.rank_eq_zero_of_admissible_torsion`
  Deduce rank zero from good reduction away from the level, toric level reduction, and
  admissible p-torsion.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.finrank_eq_zero_of_injective_kummer_of_card_le_torsion`
  Use the checked finitely generated index formula to force rank zero from an injective
  Kummer quotient and a cohomological cardinal bound by the p-torsion.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.finite_of_injective_kummer_of_card_le_torsion`
  Upgrade the numerical Kummer rank-zero conclusion to finiteness for the finitely
  generated abelian group.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltrationStep.finrank_eq_zero_of_fppfKummer_int`
  Consume the actual represented finite-flat H1 and its checked two-factor
  admissible-filtration bound in the Kummer rank-zero criterion over Spec Z.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltrationStep.finite_of_fppfKummer_int`
  Derive actual finiteness of the Mordell-Weil input from the same represented
  finite-flat H1 consumer.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteFlatCommGroupScheme.finrank_additive_basePoint_eq_zero_of_powerKummer_kernelData`
  Derive the p-torsion cardinality internally from certified base points of the actual
  scheme-theoretic multiplication kernel, then consume it in the represented
  power-Kummer rank-zero theorem.

:::

:::theorem "MT-X0-MODULI" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, planned, nouns-missing, mixed")
*The X\_0(N) moduli point attached to rational prime torsion.*

*Status:* `planned`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 30 points.

*Summary:* Construct the split rational cyclic subgroup generated by a torsion point,
its intrinsic divisor subgroups and degeneracy maps, and quotient raw Weierstrass data
by checked admissible variable changes.

*Canonical artifacts:*

* `definition` (`proposed`): `ModularCurve.XZeroModuli`
  Define elliptic curves with a finite locally free cyclic subgroup of level N.
* `theorem` (`proposed`): `ModularCurve.XZeroModuli.pointOfRationalCyclicSubgroup`
  Construct the X\_0(N)(Q) point consumed by the prime argument.
* `structure` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup`
  Package a finite rational cyclic subgroup of exact level N and construct it from a
  rational point of exact additive order N.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.variableChange`
  Transport a raw elliptic curve and cyclic-subgroup datum through a checked admissible
  Weierstrass variable change.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.VariableChangeClass`
  Quotient raw rational Gamma\_0 data by the equivalence relation generated by
  admissible changes of Weierstrass presentation.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalDatum.VariableChangeClass.lift`
  Descend every presentation-invariant function on raw cyclic-subgroup data to the
  checked variable-change quotient.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.divisorSubgroup`
  Construct the intrinsic order-d subgroup C\[d\] of a split rational cyclic subgroup of
  order N for d dividing N, with transport, nesting, and generator formulas.

:::

:::theorem "MT-X0-INTEGRAL" (parent := "prime_infrastructure") (uses := "MT-X0-MODULI") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Integral X\_0(N), cusp completions, and auxiliary q-parameters.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 30 points.

*Summary:* Compactify X\_0(N), identify the smooth cusp neighbourhood, and expose its
completed local ring and q-parameter at auxiliary primes 5 and 11.

*Canonical artifacts:*

* `structure` (`proposed`): `ModularCurve.IntegralXZero`
  Construct the compactified integral model with generic fibre X\_0(N).
* `definition` (`contract`): `AlgebraicGeometry.IsFormalImmersionAt`
  Define formal immersion by surjectivity on the functorial completed-stalk map; on
  locally Noetherian schemes, the checked residue-field and cotangent criterion implies
  this predicate.
* `structure` (`contract`): `IsLocalRing.QuotientCotangentCertificate`
  Package compatible source and target quotient ideals, target quotient maximal-ideal
  finiteness, the containment needed to lift quotient equality, and surjectivity of the
  induced quotient cotangent map.
* `theorem` (`contract`):
  `IsLocalRing.cotangentMap_surjective_of_quotientCotangentCertificate`
  Lift quotient cotangent surjectivity and a surjective residue-field map to
  surjectivity of the total local cotangent map.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Hom.isFormalImmersionAt_of_quotientCotangentCertificate`
  Consume a quotient cotangent certificate on the actual stalk map and a residue-field
  isomorphism to prove completed-stalk formal immersion.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Hom.isFormalImmersionAt_of_mappedIdealCotangentSurjective`
  Specialize the lift to quotienting the target stalk by one ideal and the source stalk
  by its extension, giving the characteristic-five special-fibre consumer.
* `theorem` (`proposed`):
  `ModularCurve.IntegralXZero.completedLocalRingAtInfinity_of_auxiliaryPrime`
  Identify the odd prime-to-level cusp completion with the q-power-series ring.

:::

:::theorem "MT-X0-CUSPS" (parent := "prime_infrastructure") (uses := "MT-X0-INTEGRAL") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Cusps, Atkin-Lehner transport, and reduction type.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 20 points.

*Summary:* Construct the rational cusp sections, transport formal immersion between them
by Atkin-Lehner, and prove that potentially multiplicative reduction at a prime-to-level
auxiliary prime sends the classifying point to a cusp.

*Canonical artifacts:*

* `definition` (`proposed`): `ModularCurve.XZero.infinityCusp`
  Construct the rational cusp used to normalize Abel-Jacobi.
* `definition` (`proposed`): `ModularCurve.XZero.atkinLehner`
  Transport either prime-level cusp to infinity.
* `theorem` (`proposed`):
  `ModularCurve.XZero.specializesToCusp_iff_potentiallyMultiplicative`
  Relate cusp specialization at an auxiliary prime to potentially multiplicative
  elliptic reduction.

:::

:::theorem "MT-X0-JACOBIAN" (parent := "prime_infrastructure") (uses := "MT-X0-INTEGRAL, MT-TC-E1-JACOBIAN-VARIETY, MT-TC-F1-ABEL-JACOBI") (tags := "infrastructure, blocked, nouns-missing, mixed")
*The modular Jacobian and cusp-based Abel-Jacobi map.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 20 points.

*Summary:* Construct J\_0(N) and the Abel-Jacobi morphism x |-\> \[x\]-\[infinity\],
with the base-change and Neron-model interfaces used by the quotient and local proof.

*Canonical artifacts:*

* `structure` (`proposed`): `ModularCurve.ModularJacobian`
  Specialize the generic Jacobian API to X\_0(N).
* `definition` (`proposed`): `ModularCurve.XZero.abelJacobiAtInfinity`
  Map x to the divisor class \[x\]-\[infinity\].

:::

:::theorem "MT-X0-HECKE" (parent := "prime_infrastructure") (uses := "MT-X0-JACOBIAN, MT-EC-ISOGENY-WEIL") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Hecke action and cotangent q-expansions.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 30 points.

*Summary:* Construct the Hecke action on J\_0(N) and prove its q-expansion recursion.

*Canonical artifacts:*

* `definition` (`proposed`): `ModularCurve.HeckeOperator`
  Construct prime-to-level Hecke correspondences and the level operator on J\_0(N).
* `theorem` (`proposed`):
  `ModularCurve.HeckeOperator.qExpansion_firstCoefficient_ne_zero`
  Use the Hecke recursions and q-expansion principle to detect a nonzero cotangent
  vector at infinity.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_normalizedQExpansion`
  Conclude actual completed-stalk formal immersion from a target local parameter whose
  pullback has normalized expansion c q plus q squared times a series with c nonzero.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.specMap_fromStalk_eq_of_normalizedQExpansion`
  Use a normalized first q-coefficient to cancel canonical local-spectrum points through
  the resulting formal immersion.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.specMap_fromStalk_eq_of_completeDVR_normalizedQExpansion`
  Construct the complete-DVR coordinate, prove the normalized-q formal immersion, and
  cancel its actual canonical local-spectrum points in one checked consumer.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.HeckeFirstCoefficient.coeff_one_ne_zero_of_simultaneousEigenvector`
  Use the first-coefficient Hecke recursion to prove that a nonzero simultaneous
  eigen-expansion cannot have zero q coefficient in degree one.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.isFormalImmersionAt_of_heckeEigen_qExpansion`
  Feed the detected first q coefficient to the real completed-stalk formal-immersion
  predicate as a named downstream consumer.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.DegreeOneCotangentCertificate.isFormalImmersionAt_of_rationalSection_heckeEigen_qExpansion`
  Apply the Hecke first-coefficient criterion to an actual rational section, using its
  derived non-genericity instead of a caller hypothesis.

:::

:::theorem "MT-X0-EISENSTEIN-ALGEBRA" (parent := "prime_infrastructure") (uses := "MT-X0-HECKE, MT-X0-INTEGRAL") (tags := "proof, blocked, nouns-missing, mixed")
*Optimal quotients and formal immersion at the cusp.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `proof`; *backend:* `mixed`;
*risk:* `extreme`; *weight:* 30 points.

*Summary:* Define Hecke-stable optimal quotients of the new modular Jacobian and prove
Mazur's Proposition 3.1 away from characteristic two, with consumers at 5 and 11.

*Canonical artifacts:*

* `structure` (`proposed`): `ModularCurve.OptimalNewQuotient`
  Package a connected-kernel quotient of the new part of J\_0(N) with its induced Hecke
  action.
* `theorem` (`proposed`):
  `ModularCurve.OptimalNewQuotient.formalImmersionAtInfinity_of_residueChar_ne_two`
  Prove the cusp Abel-Jacobi projection is a formal immersion in every residue
  characteristic other than two whenever the quotient is nontrivial.

:::

:::theorem "MT-X0-EISENSTEIN-QUOTIENT" (parent := "prime_infrastructure") (uses := "MT-X0-CUSPS, MT-X0-EISENSTEIN-ALGEBRA, MT-NERON-SPECIALIZATION, MT-FFGS-OORT-RAYNAUD") (tags := "proof, blocked, nouns-missing, mixed")
*A nontrivial rank-zero Eisenstein quotient.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `proof`; *backend:* `mixed`;
*risk:* `extreme`; *weight:* 40 points.

*Summary:* Construct an optimal Eisenstein quotient for N=11 or prime N at least 17,
prove that it is nontrivial and that its rational Mordell-Weil group is finite, and feed
it directly to the characteristic-five formal-immersion theorem.

*Canonical artifacts:*

* `structure` (`proposed`): `MazurTorsion.PrimeOrder.DegreeOneFormalImmersionWitness`
  Package only the normalized modular map, formal immersion at infinity modulo 5, and
  torsion of the particular image used by the collision theorem.
* `definition` (`proposed`):
  `ModularCurve.EisensteinQuotient.toDegreeOneFormalImmersionWitness`
  Construct the route-neutral witness privately from the nontrivial optimal Eisenstein
  quotient and its specialized finite-Mordell–Weil theorem.
* `structure` (`proposed`): `ModularCurve.EisensteinQuotient`
  Construct the nontrivial optimal quotient in exactly the levels used by the torsion
  theorem.
* `theorem` (`proposed`):
  `ModularCurve.EisensteinQuotient.nontrivial_of_level_eleven_or_ge_seventeen`
  Prove that the quotient is nonzero for N=11 and prime N at least 17.
* `theorem` (`proposed`): `ModularCurve.EisensteinQuotient.mordellWeil_finite`
  Apply the admissible finite-flat rank-zero criterion and Mordell-Weil finite
  generation.
* `theorem` (`proposed`):
  `ModularCurve.EisensteinQuotient.formalImmersionAtInfinity_modFive`
  Instantiate the optimal-quotient formal-immersion theorem at the quotient used
  downstream.

:::

:::theorem "MT-CYCLOTOMIC-UNRAMIFIED" (parent := "prime_infrastructure") (uses := "MT-BASE-INTEGRATED") (tags := "proof, paused, compiled, mathlib")
*Cyclotomic unramified character extensions.*

*Status:* `paused`; *readiness:* `compiled`; *kind:* `proof`; *backend:* `mathlib`;
*risk:* `extreme`; *weight:* 20 points.

*Summary:* Close the inherited locally-primary pseudo-unit reciprocity Challenge and
preserve the checked cyclotomic infrastructure as an independent release obligation.

*Canonical artifacts:*

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
  Prove integral one-sided Kummer reciprocity for locally-primary pseudo-units; checked
  comparison and normalization reductions then supply the inverse-character class-group
  quotient.
* `definition` (`contract`):
  `NumberTheory.CyclotomicCharacter.InverseExtension.capitulationHom`
  Extend ideal classes from the prime cyclotomic field to a supplied inverse extension
  through the genuine class-group extended-ideal homomorphism.
* `theorem` (`contract`):
  `NumberTheory.CyclotomicCharacter.InverseExtension.capitulationHom_equivariant`
  Prove that capitulation commutes with the cyclotomic action on the base class group
  and the chosen lifted action on the extension class group.
* `theorem` (`contract`):
  `NumberTheory.CyclotomicCharacter.InverseExtension.exists_nontrivial_p_torsion_capitulating_orbit`
  Use Hilbert 94 to produce a nontrivial exponent-p ideal class whose full cyclotomic
  Galois orbit capitulates in every finite-place-unramified inverse extension.
* `theorem` (`contract`):
  `MazurTorsion.PrimeOrder.divisionField_exists_nontrivial_p_torsion_capitulating_orbit`
  Consume the actual division-field unramifiedness datum in the equivariant exponent-p
  capitulation theorem without asserting the missing inverse-character quotient.

:::
