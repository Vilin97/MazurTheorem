import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option maxRecDepth 10000

#doc (Manual) "03 — Shared algebraic geometry and isogenies" =>

:::group "shared_geometry"
Canonical coherent cohomology, relative Picard, Jacobian, Abel–Jacobi, Néron
prerequisites, and elliptic isogenies, split into startable work packages. Stage weight:
300 points.
:::

:::theorem "MT-TC-A1-ORDER-SUPPORT" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, done, integrated, tau-ceti")
*Finite support of orders of rational functions.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `upstream`; *backend:* `tauceti`;
*risk:* `high`; *weight:* 15 points.

*Summary:* Tau Ceti proves finite support by restricting a rational function to a unit
on a nonempty affine open and controlling the Noetherian closed complement; its scheme
orderSystem is the compiled downstream consumer.

:::

:::theorem "MT-TC-A2-PRODUCT-FORMULA" (parent := "shared_geometry") (uses := "MT-TC-A1-ORDER-SUPPORT") (tags := "upstream, done, integrated, tau-ceti")
*Degree-zero product formula on a proper smooth curve.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `upstream`; *backend:* `tauceti`;
*risk:* `extreme`; *weight:* 15 points.

*Summary:* Tau Ceti extends a nonconstant rational function to a finite flat map to the
projective line, identifies its zero and infinity fibre multiplicities with orders of
vanishing and residue degrees, and proves every principal divisor on a smooth proper
integral curve has weighted degree zero; a quotient-to-PicZero equivalence and the
scheme-Picard subgroup are checked consumers.

*Canonical artifacts:*

* `theorem` (`contract`):
  `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.divisorProductFormula`
  The residue-degree-weighted product formula for every nonzero rational function on a
  smooth proper integral curve, consumed by properCurveDegreeZeroQuotientEquivPicZero
  and the Mazur scheme-Picard adapter.

:::

:::theorem "MT-TC-E0-PRODUCT-DIM" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, done, integrated, tau-ceti")
*Dimension of a product of abelian varieties.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `upstream`; *backend:* `tauceti`;
*risk:* `medium`; *weight:* 2 points.

*Summary:* Tau Ceti proves faithful integral extensions preserve Krull dimension,
derives tensor-product dimension additivity by Noether normalization, glues affine-chart
bounds for scheme products, and obtains abelian-variety product dimension as a checked
consumer.

:::

:::theorem "MT-TC-A3-DIVISOR-LINE-BUNDLE" (parent := "shared_geometry") (uses := "MT-TC-A2-PRODUCT-FORMULA") (tags := "upstream, research-open, compiled, tau-ceti")
*Divisor-line-bundle dictionary.*

*Status:* `research_open`; *readiness:* `compiled`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 18 points.

*Summary:* Construct the Picard group of line bundles and identify divisor classes with
line bundles on a smooth curve.

*Canonical artifacts:*

* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.pullbackOverlapHomOfModel`
  Transport an explicit fibre-product comparison canonically to Mathlib's chosen
  pairwise pullback through the module pseudofunctor.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.LineBundleDescent.pullHom_pullbackOverlapHomOfModel`
  Identify every further pullback of the canonical pairwise transport with pullback of
  the original explicit-model comparison along the composite map.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.localLineBundleChosenOverlapHomOnProperSmoothCurve`
  Real arbitrary-divisor consumer applying canonical pairwise pullback transport to the
  inverse-ideal comparison on a proper smooth curve.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.tripleOverlapComparisonToIntersection`
  Map Mathlib's chosen threefold overlap to the spectrum of the actual triple affine
  chart intersection.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.tripleOverlapComparisonToIntersection_comp_fromSpec`
  Verify that the triple-intersection comparison has the chosen threefold overlap's
  structural map to the curve; its three face-specific consumers are checked in the same
  module.
* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PicardGroup`
  Expose line bundles modulo isomorphism as the Picard group of a smooth proper curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.classEquivPicard`
  Identify Weil divisors modulo principal divisors with the line-bundle Picard group.

:::

:::theorem "MT-TC-B1-COHERENT-COHOMOLOGY" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Coherent cohomology of proper curves.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 35 points.

*Summary:* Build the coherent-cohomology results needed for proper smooth curves.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.CurveCohomology`
  Define degree-zero and degree-one coherent cohomology for sheaves on proper curves.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.CurveCohomology.finiteDimensional`
  Prove finite dimensionality for the same canonical field actions used by the
  curve-cohomology facade, together with affine acyclicity and vanishing above degree
  one in the required scope.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.zariskiFunctor`
  Apply Mathlib's native sheaf-cohomology functor to the underlying abelian sheaf of an
  actual scheme module on the Zariski opens site.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroEquivGlobalSections`
  Identify degree-zero cohomology with actual global sections at the top open through
  Mathlib's terminal-object theorem.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroEquivGlobalSections_naturality`
  Prove naturality of the H0/global-sections equivalence for genuine module morphisms.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.affineTildeHZeroEquiv`
  Consume the H0 boundary and Mathlib's affine tilde global-sections equivalence to
  recover the original coefficient module additively.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroModule`
  Transport the global-sections module structure to Ext-based H0 as an explicit opt-in
  compatibility action. Its agreement with the canonical all-degree cohomology action
  remains to be proved.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.globalSectionsCohomologyModule`
  Give genuine Ext-based sheaf cohomology in every degree its canonical
  cover-independent action by global functions, induced by multiplication endomorphisms
  of the coefficient module.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.cohomologyLinearMap`
  Bundle every coefficient-module morphism as a linear map for the canonical
  global-functions cohomology actions.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hOneCanonicalFieldModule`
  Restrict the canonical global-functions action on genuine H1 along the actual
  structure morphism to obtain the cover-independent ground-field action.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hOneCanonicalFieldLinearMap`
  Make genuine H1 functoriality ground-field linear for the canonical structure-map
  actions; no finite-dimensionality theorem yet uses this action.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.nativeBaseCechHOneForgetIso_of_affineOpenCover`
  Identify the underlying additive group of native base-Cech H1 with genuine Ext-based
  sheaf H1 for every affine open cover.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOneLinearEquivNativeBaseCech_of_affineOpenCover`
  Expose the affine-cover comparison linearly for the explicitly cover-transported
  action; this is not yet a comparison with the canonical action.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOne_finite_of_ordered_affineOpenCover`
  Consume the ordered/native and affine-cover comparisons to transfer finite generation
  to genuine H1 under the cover-transported action.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.smoothProperCurve_H_eq_zero`
  Prove genuine sheaf cohomology vanishes in every degree at least two on the required
  smooth proper integral curves.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOne_finiteDimensional_of_rationalSection`
  Prove H1 finite-dimensional for a pointed smooth proper integral curve using a
  finite-map-transported field action; comparison with the canonical field action
  remains open.

:::

:::theorem "MT-TC-B2-RR-SERRE" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Riemann-Roch and Serre duality for curves.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 25 points.

*Summary:* Define genus through H^1 and prove Riemann-Roch, Serre duality, and the
degree of the dualizing sheaf.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.genus`
  Define the genus of a proper smooth curve from the dimension of first coherent
  cohomology.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.riemannRoch`
  Provide the Riemann-Roch formula for divisors or line bundles on a proper smooth
  curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.serreDuality`
  Provide Serre duality and the resulting degree formula for the dualizing sheaf.

:::

:::theorem "MT-TC-C1-RELATIVE-COHOMOLOGY" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Relative cohomology and base change.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 30 points.

*Summary:* Prove proper-flat pushforward, cohomology and base change, and semicontinuity
in the form needed by the Picard construction.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology`
  Package derived pushforward data for coherent sheaves in a proper flat family of
  curves.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeCohomology.baseChange`
  Prove the base-change comparison required by the relative Picard construction.
* `theorem` (`proposed`):
  `TauCeti.AlgebraicGeometry.RelativeCohomology.upperSemicontinuous`
  Prove upper semicontinuity of fibrewise cohomology dimensions in the required setting.

:::

:::theorem "MT-TC-C2-SYMMETRIC-POWERS" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE, MT-TC-C1-RELATIVE-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Relative effective divisors and symmetric powers.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 15 points.

*Summary:* Represent degree-d effective divisors by Sym^d X and construct the relative
Abel maps.

*Canonical artifacts:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.RelativeEffectiveDivisor`
  Represent flat families of effective divisors of a fixed relative degree.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.SymmetricPower`
  Construct the relative symmetric power that represents effective divisors of degree d.
* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.relativeAbelMap`
  Construct the relative Abel map from the symmetric power to the degree-d Picard
  functor.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem`
  Transport the fixed-degree Abel--Jacobi fiber theorem through the checked
  divisor-class/Picard equivalence, identifying equality in absolute Picard degree zero
  with complete-linear-system membership.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.setOf_weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq`
  Give the set-level fixed-degree fiber formula for actual scheme-Picard classes.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.weightedAbelJacobiDivisorClass_one_ofSym_eq_iff_mem_completeLinearSystem`
  Prove the transported fiber formula on the formal symmetric power of the divisor index
  type.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.setOf_weightedAbelJacobiDivisorClass_one_ofSym_eq`
  Identify the symmetric-power equality fiber with the preimage of its complete linear
  system.

:::

:::theorem "MT-TC-D1-PICARD-FUNCTOR" (parent := "shared_geometry") (uses := "MT-TC-A3-DIVISOR-LINE-BUNDLE") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Rigidified relative Picard functor.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 35 points.

*Summary:* The checked all-degree zero-section-normalized Picard presheaf now has its
associated fppf sheafification and a rational-section class consumer at the base test
object; a pullback-compatible relative degree map, the relative degree-zero subfunctor,
Pic⁰ representability, and the universal Poincaré bundle remain missing.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativePicardFunctor`
  Define the rigidified fppf sheaf of line bundles modulo pullbacks from the base.
* `definition` (`proposed`):
  `TauCeti.AlgebraicGeometry.RelativePicardFunctor.degreeZero`
  Define the degree-zero subfunctor used to construct the relative Jacobian.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.Pic.map`
  Construct pullback on absolute scheme Picard groups from the checked general
  pullback-tensor monoidal comparison.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.Modules.picRelFunctor`
  Construct the all-degree zero-section-kernel relative Picard group as a contravariant
  group-valued functor on S-schemes.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.picRelFunctor_map_picRelProj`
  Prove that zero-section normalization of an absolute Picard class commutes with
  arbitrary base change through the actual relative Picard functor map.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.Modules.picRelFppfSheaf`
  Apply Mathlib's sheafification to the additive all-degree zero-section-normalized
  Picard presheaf on the fppf site; this is an associated sheafification, not relative
  Pic⁰ or a representing object.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.rationalSectionAbelJacobiPicRelFppfClass`
  Map the checked absolute rational-section Abel--Jacobi class at the identity test
  object into the associated fppf sheafification, still using the supplied
  DivisorPicard.ClassEquivalence.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.degreeZero`
  Transport the divisor degree-zero subgroup to an absolute subgroup of the scheme
  Picard group.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.DivisorPicard.Dictionary.degreeZeroRepresentative`
  Choose a Tau Ceti invertible-sheaf representative for every absolute degree-zero
  Picard class.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.degreeZero`
  Consume the strongest cocycle-built divisor-class/Picard equivalence directly to
  construct the absolute degree-zero subgroup without first packaging the all-sheaves
  dictionary.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse.divisorToPic_mem_degreeZero_iff`
  Characterize explicit divisor-generated degree-zero Picard classes exactly by
  vanishing of weighted divisor degree.

:::

:::theorem "MT-TC-D2-PICARD-REPRESENTABILITY" (parent := "shared_geometry") (uses := "MT-TC-B2-RR-SERRE, MT-TC-C2-SYMMETRIC-POWERS, MT-TC-D1-PICARD-FUNCTOR") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Represent Pic⁰ and construct its universal bundle.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 45 points.

*Summary:* Represent the degree-zero Picard functor, construct the normalized universal
Poincaré bundle, and prove the resulting group scheme proper and geometrically
connected.

*Canonical artifacts:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme`
  Package a group scheme representing the degree-zero relative Picard functor.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.PicardScheme.representsDegreeZero`
  Prove the representing equivalence between points of PicardScheme and the degree-zero
  Picard functor.
* `theorem` (`proposed`):
  `TauCeti.AlgebraicGeometry.PicardScheme.proper_geometricallyConnected`
  Prove properness and geometric connectedness of the represented degree-zero component.
* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.PoincareBundle`
  Package the normalized universal line bundle on the curve times its Picard space.

:::

:::theorem "MT-TC-E1-JACOBIAN-VARIETY" (parent := "shared_geometry") (uses := "MT-TC-D2-PICARD-REPRESENTABILITY, MT-TC-E0-PRODUCT-DIM") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Jacobian variety and sanity checks.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 20 points.

*Summary:* Bundle Pic^0 as an abelian variety and prove dimension equals genus and
Jac(E,O) is isomorphic to E in genus one.

*Canonical artifacts:*

* `structure` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian`
  Package the represented Picard degree-zero component as an abelian variety.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.dimension_eq_genus`
  Identify the dimension of the Jacobian with the genus of the curve.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.ellipticCurveEquiv`
  Prove the pointed genus-one sanity check identifying an elliptic curve with its
  Jacobian.

:::

:::theorem "MT-TC-F1-ABEL-JACOBI" (parent := "shared_geometry") (uses := "MT-TC-C1-RELATIVE-COHOMOLOGY, MT-TC-E1-JACOBIAN-VARIETY") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Abel-Jacobi universal property and base change.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 20 points.

*Summary:* Construct the Abel-Jacobi morphism, prove its universal property and
base-change compatibility, and prove it is a closed immersion in positive genus.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi`
  Construct the pointed Abel-Jacobi morphism from a curve to its Jacobian.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_universal`
  Prove the universal factorization property for pointed morphisms to abelian varieties.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_baseChange`
  Prove compatibility of the Abel-Jacobi construction with base change.
* `theorem` (`proposed`):
  `TauCeti.AlgebraicGeometry.Jacobian.abelJacobi_closedImmersion`
  Prove that Abel-Jacobi is a closed immersion for curves of positive genus.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.weightedBasepointChangeClass`
  Transport the weighted divisor class \[x0\]-\[y0\] into the actual scheme Picard
  degree-zero subgroup.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.coe_weightedBasepointChangeClass`
  Identify the underlying scheme-Picard class of the transported basepoint-change class.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.weightedAbelJacobiClass_change_base`
  Prove the exact translation formula for the scheme-Picard point class under a change
  of weight-one basepoint.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.weightedAbelJacobiClass_oldBase_eq_weightedBasepointChangeClass`
  Normalize the old basepoint in the new-basepoint Abel-Jacobi map to the transported
  translation class.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.weightedAbelJacobiDivisorClass_change_base`
  Prove the exact weighted-degree translation formula for the scheme-Picard divisor Abel
  class.

:::

:::theorem "MT-EC-ISOGENY-WEIL" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, blocked, nouns-missing, mixed")
*Cyclic subgroup quotients and classifying data.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 25 points.

*Summary:* Construct the canonical commutative group scheme on the concrete projective
Weierstrass cubic, the finite-flat cyclic subgroup generated by an exact-torsion point,
and the quotient with only the kernel and base-change laws exercised by the X\_0 and
order-49 consumers.

*Canonical artifacts:*

* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.PointQuotient`
  Form the abstract rational point-group quotient by the supplied cyclic subgroup
  without asserting scheme representability.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.quotientMap`
  Expose the canonical surjective point-group quotient map with kernel exactly the
  supplied subgroup.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.dualMap`
  Descend multiplication by the level through the cyclic point-group quotient.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.dualMap_comp_quotientMap`
  Identify the dual-after-quotient composite with multiplication by the level.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroModuli.RationalCyclicSubgroup.quotientMap_comp_dualMap`
  Identify the quotient-after-dual composite with multiplication by the level on the
  quotient.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantAdditionAffineMorphism`
  Construct the genuine affine-scheme morphism induced by the denominator-cleared
  universal secant formula on its explicit principal-open presentation.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantAdditionProjectiveMorphism`
  Map the checked secant chart into the actual reduced projective Weierstrass cubic
  through its standard affine open; this is one multiplication chart, not a global group
  law.
* `definition` (`proposed`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalCommGroupScheme`
  Equip the concrete reduced projective Weierstrass cubic with its canonical commutative
  group-scheme law and coordinate-point comparison after completing the tangent and
  infinity charts, product-open identification, overlaps, gluing, and group axioms.
* `structure` (`proposed`): `EllipticCurve.CyclicSubgroup`
  Package a finite cyclic subgroup with its order and rationality data.
* `definition` (`proposed`): `EllipticCurve.Isogeny.quotientByCyclic`
  Construct the cyclic quotient used by the X\_0 moduli and order-49 consumers.
* `theorem` (`proposed`): `EllipticCurve.Isogeny.quotientByCyclic_baseChange`
  Prove the kernel and base-change laws required by both named downstream consumers.

:::
