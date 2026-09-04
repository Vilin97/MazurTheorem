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
  Package the checked canonical H0 comparison, linear connecting maps, pointed-curve
  canonical-field H1 finite-dimensionality, affine acyclicity, and vanishing above
  degree one with the still-needed proper coherent H0 finiteness in the required
  curve-cohomology facade.
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
  compatibility action; its equality with the canonical all-degree action is checked
  below.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.globalSectionsCohomologyModule`
  Give genuine Ext-based sheaf cohomology in every degree its canonical
  cover-independent action by global functions, induced by multiplication endomorphisms
  of the coefficient module.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonicalLinearEquivGlobalSections`
  Upgrade the degree-zero/global-sections comparison to a linear equivalence for the
  canonical global-functions action on genuine H0.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroModule_eq_globalSectionsCohomologyModule`
  Prove that the opt-in global-sections-transported H0 action equals the canonical
  all-degree global-functions action in degree zero.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.cohomologyLinearMap`
  Bundle every coefficient-module morphism as a linear map for the canonical
  global-functions cohomology actions.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.cohomologyConnectingHom`
  Expose the genuine Ext connecting homomorphism for a short exact sequence of scheme
  modules after passage to the underlying additive sheaves.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.cohomologyConnectingLinearMap`
  Bundle the actual Ext connecting homomorphism linearly for the canonical
  global-functions actions, using naturality under simultaneous scalar multiplication on
  the short complex.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonicalFieldModule`
  Restrict the canonical global-functions action on genuine H0 along the actual
  structure morphism to obtain the opt-in ground-field action.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonicalFieldLinearEquivGlobalSections`
  Consume the canonical H0 comparison in the proper-curve layer and identify it linearly
  with global sections carrying the same structure-map field action.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hOneCanonicalFieldModule`
  Restrict the canonical global-functions action on genuine H1 along the actual
  structure morphism to obtain the cover-independent ground-field action.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hOneCanonicalFieldLinearMap`
  Make genuine H1 functoriality ground-field linear for the canonical structure-map
  actions; pointed proper-curve H1 finite-dimensionality now uses the same actions.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroHOneCanonicalFieldConnectingLinearMap`
  Restrict the canonical global-functions-linear connecting homomorphism to the
  structure-map field action in degrees zero and one.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroHOneCanonicalFieldConnecting_range_finiteDimensional_of_rationalSection`
  Consume the canonical field-linear connecting map and pointed proper-curve H1
  finiteness to prove its image finite-dimensional.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.nativeBaseCechHOneForgetIsoOfAffineOpenCover`
  Identify the underlying additive group of native base-Cech H1 with genuine Ext-based
  sheaf H1 for every affine open cover.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.nativeBaseCechHOneLinearEquivCanonicalOfAffineOpenCover`
  Upgrade the affine-cover comparison to a linear equivalence between native base-Cech
  H1 and the canonical global-functions action on genuine H1 restricted along the base
  morphism, without transporting a target module instance.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOneLinearEquivNativeBaseCechOfAffineOpenCover`
  Expose the affine-cover comparison linearly for the explicitly cover-transported
  action; retain this legacy facade alongside the canonical restricted-action linear
  comparison.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOne_finite_of_ordered_affineOpenCover`
  Consume the ordered/native and affine-cover comparisons to transfer finite generation
  to genuine H1 under the cover-transported action.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.ProjectiveLineCohomology.genuineSheafHOne_finite_canonical_of_finite_to_projectiveLine`
  Transfer native Cech finite generation along a finite map to the projective line to
  genuine H1 for the canonical base-global-sections action.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.smoothProperCurve_H_eq_zero`
  Prove genuine sheaf cohomology vanishes in every degree at least two on the required
  smooth proper integral curves.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOne_finiteDimensional_of_rationalSection`
  Prove H1 finite-dimensional for a pointed smooth proper integral curve using a
  finite-map-transported field action; retain this legacy facade alongside the
  canonical-field theorem.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOneCanonical_finiteDimensional_of_rationalSection`
  Use a rational section and the canonical Cech linear equivalence to prove genuine H1
  finite-dimensional for the canonical structure-map field action on a smooth proper
  integral curve.

:::

:::theorem "MT-TC-B2-RR-SERRE" (parent := "shared_geometry") (uses := "MT-TC-B1-COHERENT-COHOMOLOGY") (tags := "upstream, blocked, nouns-missing, tau-ceti")
*Riemann-Roch and Serre duality for curves.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 25 points.

*Summary:* Define genus through canonical H1 and prove Riemann-Roch, Serre duality, and
the degree of the dualizing sheaf.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.genus`
  Define the genus of a proper smooth curve from the dimension of first coherent
  cohomology.
* `theorem` (`proposed`): `TauCeti.AlgebraicGeometry.Curve.riemannRoch`
  Provide the first genuine Riemann-Roch formula for divisors or line bundles on a
  proper smooth curve, consuming B1's canonical proper coherent H0/H1 finiteness API
  without a shadow dimension structure.
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
*Normalized relative Picard functor.*

*Status:* `blocked`; *readiness:* `nouns_missing`; *kind:* `upstream`; *backend:*
`tauceti`; *risk:* `extreme`; *weight:* 35 points.

*Summary:* The checked zero-section-normalized all-degree Picard presheaf has its
associated fppf sheafification.

*Canonical artifacts:*

* `definition` (`proposed`): `TauCeti.AlgebraicGeometry.RelativePicardFunctor`
  Define the zero-section-normalized fppf sheaf of line bundles modulo pullbacks from
  the base.
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
  Factor the checked rational-section Abel--Jacobi class through the actual absolute
  Picard degree kernel before mapping it into the associated fppf sheafification at the
  identity test object; the construction still uses the supplied
  DivisorPicard.ClassEquivalence.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.properCurveDegreeHom`
  Transport the checked residue-degree divisor-class degree through an actual
  divisor-class/Picard equivalence to obtain an absolute Picard degree homomorphism.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.properCurveDegreeZero_eq_ker`
  Identify the transported absolute degree-zero Picard subgroup exactly with the kernel
  of the checked absolute degree homomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.properCurvePicardAddEquivDegreeZeroProdInt`
  Use a residue-degree-one point to split the absolute Picard group as its degree-zero
  subgroup times the integers.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.rationalSectionPicardAddEquivDegreeZeroProdInt`
  Consume an actual rational section as the residue-degree-one point in the checked
  absolute Picard splitting.
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.properCurveDegreeKernelToPicRelFppfAtBase`
  Map the actual absolute Picard degree kernel into the associated all-degree fppf
  Picard sheafification only at the identity test object.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.PicardGroup.rationalSectionAbelJacobiDegreeKernel`
  Give the rational-section Abel--Jacobi class as a value in the actual absolute Picard
  degree kernel.
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
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantProductOpen`
  Realize the secant localization as the actual principal open D(x₁ - x₂) in the affine
  fibre product of the concrete cubic with itself.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantAdditionOnProductOpen`
  Define the checked secant-addition morphism on that genuine product open.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantAdditionOnProductOpen_comp_structureMap`
  Prove that secant addition on the genuine product open lies over the base field.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.tangentChartToAffineCurve_opensRange`
  Identify the tangent localization with the actual affine principal open where 2y + a₁x
  + a₃ is invertible.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.tangentDoublingProjectiveMorphism`
  Map the checked tangent-doubling formula from that principal open into the concrete
  projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.tangentDoublingProjectiveMorphism_comp_structureMap`
  Prove that the projective tangent-doubling morphism lies over the base field.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.productNeighborhoodProductOpen`
  Realize the localization at B₁₂ as an actual principal open in the affine scheme
  product.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.productNeighborhoodAdditionOnProductOpen`
  Define the checked product-neighbourhood addition morphism on the genuine D(B₁₂)
  product open.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.productNeighborhoodAdditionProjectiveMorphism_comp_structureMap`
  Prove that product-neighbourhood addition into the projective cubic lies over the base
  field.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.productNeighborhoodAddition_secant_and_tangent_compatible`
  Package equality with secant addition on the exact projective overlap together with
  equality to tangent doubling along the diagonal as the named consumer for the next
  gluing slice.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.antidiagonalAdditionProjectiveMorphism`
  Map the denominator-cleared B₁₂-chart formula through the actual Y ≠ 0 chart into the
  concrete reduced projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.productAntidiagonalIntersection_additionProjective_eq`
  Prove scheme-level equality between D(B₁₂) addition and its infinity-output extension
  on their exact intersection.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.verticalAdditionProjectiveMorphism`
  Map the denominator-cleared ordinary-secant formula through the actual Y ≠ 0 chart
  into the concrete reduced projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantVerticalIntersection_additionProjective_eq`
  Prove scheme-level equality between ordinary secant addition and its vertical infinity
  extension on their exact intersection.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.infinityIntersection_additionProjective_eq`
  Prove that the two denominator-cleared infinity formulas agree as actual morphisms on
  D(Y\_anti Y\_vert), using exact homogeneous cross-products without cancelling either
  slope denominator.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.affinePairAdditionCharts_cover`
  Use elliptic nonsingularity to prove that the two affine-output charts and two
  infinity-output charts cover the entire affine-pair presentation.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.productVerticalIntersection_additionProjective_eq`
  Prove equality of product-neighbourhood and vertical infinity-output addition on their
  exact principal-open intersection.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantAntidiagonalIntersection_additionProjective_eq`
  Prove equality of ordinary secant and antidiagonal infinity-output addition on their
  exact principal-open intersection.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.affinePairAdditionMorphism`
  Glue the four checked principal-open formulas to an actual addition morphism from the
  entire affine-pair presentation into the concrete projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.affinePairAdditionMorphism_comp_structureMap`
  Prove that the globally glued affine-pair addition morphism lies over the coefficient
  field.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairOpenCover`
  Cover the actual projective cubic fibre product by the four products of its genuine Y
  ≠ 0 and Z ≠ 0 coordinate charts.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairIsoAffinePair`
  Identify the standard-by-standard member of the projective-product cover with the
  explicit four-coordinate affine-pair presentation.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairAdditionMorphism`
  Transport the checked glued affine-pair addition to the genuine standard-by-standard
  member of the full projective-product cover.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairCoordinateRingAlgEquiv`
  Identify the four-coordinate affine-pair ring with the tensor coordinate ring of the
  standard projective pair chart as K-algebras.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairCoordinateRingAlgEquiv_denominator`
  Transport the affine secant denominator to the difference of the two standard
  universal abscissas.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartIsoSpecTensor_hom_comp_standardPairCoordinateRingAlgEquiv_specMap`
  Prove that the contravariant spectrum map of the coordinate equivalence is exactly the
  canonical geometric standard-pair comparison.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairCoordinateRingAlgEquiv_additionCoordinates`
  Transport the raw homogeneous addition triple on the affine universal inputs to the
  projective standard-pair triple.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairOutputZToSecant`
  Construct the canonical map from the raw standard-pair output-Z localization to the
  checked secant chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairOutputZToSecant_comp_secantChartToPair`
  Identify the canonical output-to-secant map over the affine-pair source with the raw
  output open over the standard projective-pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairOutputZToSecant_comp_secantAdditionProjectiveMorphism`
  Prove that the checked affine secant formula pulls back to the normalized raw
  homogeneous standard-pair formula.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism`
  Identify the localized raw standard-pair addition morphism with the exact restriction
  of the globally glued affine-pair addition law.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.secantDenominator_ne_zero`
  Prove that the difference of the two universal affine abscissas is nonzero, using
  effective descent along the faithfully flat affine coordinate ring.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.standardPairOutputOverlapToInfinity_isDominant`
  Prove that the exact output-YZ overlap is dense in the standard-pair output-Y
  principal open.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityOutputOpen_comp_standardPairAdditionMorphism`
  Extend equality from the dense output-YZ overlap and identify the entire raw output-Y
  morphism with the restriction of the checked standard-pair addition law.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartIsoSpecTensor`
  Identify every member of the four-chart projective-pair cover with the spectrum of the
  tensor product of its two chart coordinate rings.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartMorphismOfCoordinateRingHom`
  Turn a K-algebra coordinate formula on any projective-pair chart into a morphism to a
  chosen output chart of the concrete cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartMorphismOfCoordinateRingHom_comp_structureMap`
  Prove automatically that every morphism produced by the coordinate-formula constructor
  lies over Spec K.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstInput_eq`
  Verify on every chart pair that the tensor-product left inclusion reconstructs the
  first geometric input projection.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartSecondInput_eq`
  Verify on every chart pair that the tensor-product right inclusion reconstructs the
  second geometric input projection.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartUniversalPoint`
  Construct the normalized universal homogeneous point in either quotient coordinate
  chart of the projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartUniversalPoint_equation`
  Prove directly from the quotient ideal that the normalized universal chart point
  satisfies the mapped homogeneous cubic equation.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstUniversalPoint_equation`
  Prove that the tensor-left universal input satisfies the cubic equation over every
  projective-pair chart ring.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartSecondUniversalPoint_equation`
  Prove that the tensor-right universal input satisfies the cubic equation over every
  projective-pair chart ring.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionCoordinates`
  Evaluate the raw homogeneous secant-addition triple on the two normalized universal
  inputs of every projective-pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionCoordinates_equation`
  Use the integral chart ring and its fraction field to prove that every evaluated
  secant triple satisfies the mapped homogeneous cubic equation.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionCoordinates_Z_mul_input_Z`
  Identify the secant output Z coordinate times both input Z coordinates with the cube
  of the cross-multiplied input X difference.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartOverlapScheme`
  Construct the exact cubic overlap D(YZ) shared by the standard and infinity coordinate
  charts.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartOverlap_isLocalization_standardChart`
  Identify the cubic overlap ring as the standard chart localized at Y/Z.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartOverlap_isLocalization_infinityChart`
  Identify the same cubic overlap ring as the infinity chart localized at Z/Y.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartOverlap_maps_eq`
  Prove that the two principal-open restrictions define the same morphism into the
  concrete projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition`
  After tensoring with an unchanged second chart, prove that changing the first
  normalized input scales the raw addition triple by the square of Y/Z.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondChartOverlap_standardSecondPoint_eq_smul_infinitySecondPoint`
  After tensoring the cubic overlap on the right, prove that the second normalized
  universal input changes by the transition scalar Y/Z.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition`
  With the first chart unchanged, prove that changing the second normalized input scales
  the raw addition triple by the square of Y/Z.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapToStandardPair`
  Embed the first-factor tensor overlap as a principal open in the adjacent
  standard-input pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapToInfinityPair`
  Embed the same first-factor overlap as a principal open in the adjacent infinity-input
  pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlap_maps_eq`
  Prove that the two first-factor overlap descriptions have equal composites into the
  full projective product.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapToStandardPair`
  Embed the second-factor tensor overlap as a principal open in the adjacent
  standard-input pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapToInfinityPair`
  Embed the same second-factor overlap as a principal open in the adjacent
  infinity-input pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlap_maps_eq`
  Prove that the two second-factor overlap descriptions have equal composites into the
  full projective product.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapAdditionOutputRing`
  Localize the exact first-factor input overlap at either selected infinity-side secant
  output coordinate.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapAdditionOutput_points_eq`
  Cancel the invertible square transition factor and prove equality of all three
  normalized secant coordinates.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapAdditionOutput_maps_eq`
  Prove that both localized first-factor restrictions have the same map into the full
  projective product.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapAdditionOutput_morphisms_eq`
  Prove equality of the genuine standard- and infinity-side secant morphisms on each
  localized first-factor overlap.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapAdditionOutputRing`
  Localize the exact second-factor input overlap at either selected infinity-side secant
  output coordinate.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapAdditionOutput_points_eq`
  Cancel the invertible square transition factor and prove equality of all three
  normalized secant coordinates.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapAdditionOutput_maps_eq`
  Prove that both localized second-factor restrictions have the same map into the full
  projective product.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapAdditionOutput_morphisms_eq`
  Prove equality of the genuine standard- and infinity-side secant morphisms on each
  localized second-factor overlap.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingCoordinates`
  Evaluate the homogeneous doubling triple on the first normalized universal input as
  the polynomial replacement on the diagonal base locus.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingCoordinates_equation`
  Prove that the first universal doubling triple satisfies the mapped homogeneous cubic
  equation over every projective-pair chart ring.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.coveringChartCoordinateRingAlgHomOfNormalizedPoint`
  Turn any normalized homogeneous solution of the mapped cubic equation into a K-algebra
  map from the corresponding quotient coordinate chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionOutputAlgHom`
  Normalize the universal secant triple after inverting a selected output coordinate and
  instantiate the quotient-chart algebra-map constructor.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionOutputOpen`
  Embed the selected secant output-coordinate principal localization as an actual open
  subscheme of its projective-pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionOutputMorphism`
  Define the regular secant-addition morphism from either output-coordinate principal
  open into the concrete projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionOutputMorphism_comp_structureMap`
  Prove that every localized secant output morphism lies over the structural morphism to
  Spec K.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingOutputPoint_equation`
  Prove that the normalized first-input doubling point satisfies the mapped cubic
  equation on either output-coordinate localization.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingOutputAlgHom`
  Instantiate the normalized-point quotient-chart constructor on the first universal
  doubling triple.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingOutputOpen`
  Embed either selected doubling-output localization as an actual open subscheme of its
  projective-pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingOutputMorphism`
  Define the regular first-input doubling morphism on either output-coordinate principal
  open.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartFirstDoublingOutputMorphism_comp_structureMap`
  Prove that every localized first-input doubling morphism lies over the structural
  morphism to Spec K.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionAndDoublingOutputOpens_cover`
  Prove that the two secant and two first-input doubling output-coordinate principal
  opens jointly cover every projective-pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionOutputOverlap_open_eq`
  Identify the two restriction maps from the exact secant-output YZ overlap into their
  common projective-pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartAdditionOutputOverlap_morphisms_eq`
  Prove that the Y- and Z-normalized secant formulas agree as actual cubic-valued
  morphisms on their exact overlap.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPair_addition_coordinate_identity`
  Factor the difference of the two universal infinity-chart cubic equations as `(z₁ -
  z₂) B∞ = (x₁ - x₂) A∞`.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairDiagonalAlgHom_B12`
  Identify `B∞` on the diagonal with the projective Z partial derivative at the
  universal infinity-chart point.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairNeighborhoodOriginAlgHom`
  Extend evaluation at `(O, O)` through `D(B∞)`, using the checked specialization `B∞(O,
  O) = 1`.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairNeighborhoodSlope_mul_sub`
  Prove on `D(B∞)` that the regular slope satisfies `slope * (x₁ - x₂) = z₁ - z₂`,
  including along the diagonal.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairNeighborhoodAdditionCoordinates_equation`
  Prove that the denominator-free third-intersection addition triple satisfies the
  mapped homogeneous cubic throughout `D(B∞)`, including on the diagonal.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairNeighborhoodAdditionCoordinates_at_origin`
  Specialize the local addition triple at `(O, O)` to `[0 : -1 : 0]`, the identity
  projective point.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairOriginAdditionOpen`
  Realize the successive `B∞` and output-Y localizations as an actual open neighborhood
  of `(O, O)` in the infinity-by-infinity projective-pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairOriginAdditionMorphism`
  Define the genuine regular addition morphism from the selected origin neighborhood
  into the concrete projective cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairOriginAdditionMorphism_comp_structureMap`
  Prove that the infinity-diagonal local addition morphism lies over the base field.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairNeighborhood_rawAdditionCoordinates_eq_smul`
  Identify the pulled-back raw secant triple with `(x₁ - x₂)³` times the regular
  infinity-neighborhood addition triple.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairSecantOverlap_localY_isUnit`
  Use the exact cubic scaling identity to prove that the regular formula's output Y
  coordinate is invertible on `D(B∞ · Ysec)`.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairSecantOverlap_outputPoints_eq`
  Prove coordinatewise equality of the Y-normalized regular and secant output points on
  their exact overlap.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairSecantOverlap_open_eq`
  Identify both source restrictions with the same intrinsic principal open of the
  infinity-by-infinity projective-pair chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairSecantOverlap_morphisms_eq`
  Prove that the regular infinity-neighborhood formula and the old secant formula agree
  as actual cubic-valued morphisms on `D(B∞ · Ysec)`.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteTranslationQuotient.structureMap_geometricallyIntegral`
  Descend geometric integrality from a supplied commutative group scheme to its actual
  finite free-translation quotient.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteTranslationQuotient.structureMap_isProper`
  Prove properness of the actual quotient over an affine noetherian base from properness
  of its source.
* `theorem` (`contract`):
  `AlgebraicGeometry.FiniteTranslationQuotient.structureMap_smooth_of_flat`
  Over an affine noetherian base, prove smoothness of the actual quotient from flatness,
  local finite type, and geometric reducedness of its source.
* `definition` (`contract`):
  `AlgebraicGeometry.FiniteTranslationQuotient.abelianVarietyOfAbelianVariety`
  Consume the generic quotient geometry to bundle a finite free-translation quotient of
  an actual abelian variety as an actual abelian variety.
* `definition` (`proposed`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalCommGroupScheme`
  Equip the concrete reduced projective Weierstrass cubic with its canonical commutative
  group-scheme law and coordinate-point comparison by gluing the checked four-chart
  affine-pair atlas, extending over input points at infinity, and proving the group
  axioms.
* `structure` (`proposed`): `EllipticCurve.CyclicSubgroup`
  Package a finite cyclic subgroup with its order and rationality data.
* `definition` (`proposed`): `EllipticCurve.Isogeny.quotientByCyclic`
  Construct the cyclic quotient used by the X\_0 moduli and order-49 consumers.
* `theorem` (`proposed`): `EllipticCurve.Isogeny.quotientByCyclic_baseChange`
  Prove the kernel and base-change laws required by both named downstream consumers.

:::
