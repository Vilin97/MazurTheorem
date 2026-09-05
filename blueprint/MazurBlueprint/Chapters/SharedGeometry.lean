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
  Package the checked unconditional canonical H0 finite-dimensionality, pointed
  canonical H1 finite-dimensionality, vanishing above degree one, and cover-independent
  low-degree field-extension base-change comparison for coherent modules on pointed
  smooth proper integral curves in one curve-cohomology facade.
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
* `definition` (`contract`): `TopCat.Sheaf.cechHomologyZeroIsoGlobalSectionsOfOpenCover`
  Identify native Cech homology in degree zero with global sections for every open cover
  by comparing the cycle kernel with the exact augmented Cech short complex.
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.baseCechHomologyZeroForgetIsoGlobalSectionsOfOpenCover`
  Transport the arbitrary-cover degree-zero comparison through the forgotten base-linear
  Cech complex, naturally in the coefficient module.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.nativeBaseCechHZeroLinearEquivCanonicalOfOpenCover`
  Upgrade native base-Cech H0 on any open cover to a linear equivalence with genuine
  Ext-based H0 carrying the canonical base-global-sections action.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.baseCechComplex_homology_zero_module_finite_of_orderedBaseCechComplex`
  Transfer finite generation from ordered Cech H0 to native all-tuples Cech H0 using the
  degree-zero alternating-extension retraction.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZero_finite_of_orderedBaseCechComplex`
  Transfer ordered Cech H0 finite generation through the canonical arbitrary-cover
  comparison to genuine sheaf H0.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZero_finite_of_coherentSupportComodels`
  Consume coherent support-decreasing comodels to obtain finite generation of genuine H0
  with its canonical base action.
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
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonicalFieldLinearMap`
  Bundle canonical H0 functoriality as a ground-field-linear map for the structure-map
  actions.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroBaseSectionsLinearEquivGlobalSections`
  Restrict the canonical H0/global-sections comparison linearly along an arbitrary base
  morphism.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroBaseSections_finite_of_globalSections_module_finite`
  Transfer finite generation of global sections over the source global-function ring to
  canonical base-linear H0 when the base morphism is finite on global functions.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_globalSections_module_finite`
  Use properness of an integral finite-type scheme to make canonical ground-field H0
  finite-dimensional from finite global sections over the source ring.
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
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonicalFieldLinearMap_exact`
  Express exactness at canonical H0 of the middle term of every short exact sequence
  using ground-field-linear maps.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroHOneCanonicalFieldLinearMap_exact`
  Express the canonical field-linear H0-to-H1 window of every short exact sequence as an
  exact pair.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_X2_of_shortExact`
  Transfer finite-dimensional canonical H0 from both ends of a short exact sequence to
  its middle term.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_X3_of_shortExact`
  Transfer finite-dimensional H0 of the middle term and H1 of the first term to
  canonical H0 of the third term.
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
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.genuineSheafHOneCanonicalBase_finite_of_rationalSection`
  Expose pointed proper-curve H1 finite generation for the canonical action of the base
  global-function ring used by Cech consumers.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite`
  Combine proper H0 and pointed-curve H1 finiteness with canonical Cech comparisons to
  prove ordered low-degree finiteness for a coherent sheaf with finite global sections.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.free_orderedBaseCechLowDegreeFinite_of_rationalSection`
  Certify finite free sheaves as coherent ordered low-degree-good targets on pointed
  smooth proper integral curves.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.IsCoherentLowDegreeSupportComodel.of_isIso_restrict`
  Assemble the exact coherent support-comodel from a low-degree-good target and a
  support-controlled comparison which is invertible on a support-meeting open.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.isCoherentLowDegreeSupportComodel_of_rationalSection_of_globalSections_module_finite`
  Apply the assembler on a pointed proper curve when the coherent target has finite
  global sections over the source global-function ring.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.finiteFreeTarget_isCoherentLowDegreeSupportComodel_of_isIso_restrict`
  Package a support-controlled open-local comparison to a finite free sheaf as the
  proper-curve support comodel consumed by closed-support induction.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.finite_closedStalkSupport_of_lt_top`
  Prove that strict closed stalk support on a smooth proper integral curve is a finite
  underlying set.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.CanonicalSupportThickening.finite_supportScheme_of_closedStalkSupport_lt_top`
  Transfer finite strict stalk support through the canonical closed immersion to make
  the support thickening's underlying type finite.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.CanonicalSupportThickening.isFinite_comp_structureMap_of_closedStalkSupport_lt_top`
  Upgrade the finite carrier of a strict canonical support thickening to a finite
  structure morphism over the ground field.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback_of_isAffineHom`
  Prove that scheme-module pullback along an affine morphism preserves quasicoherence by
  gluing the checked affine-spectrum base-change comparison.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback_of_isAffineHom`
  Prove that affine-morphism pullback preserves finite type for quasicoherent modules
  using finite local generators on inverse-image affine opens.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.CanonicalSupportThickening.modelModule_isQuasicoherent`
  Apply affine-morphism pullback coherence to the closed immersion defining the
  canonical support model.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.CanonicalSupportThickening.modelModule_isFiniteType`
  Apply affine-morphism finite-type preservation to the canonical support model consumed
  by finite pushforward.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.CanonicalSupportThickening.baseSections_finite_of_closedStalkSupport_lt_top`
  Factor strict-support base-linear sections through the coherent canonical model and
  its finite pushforward to the affine field spectrum.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.CanonicalSupportThickening.globalSections_module_finite_of_closedStalkSupport_lt_top`
  Prove finite generation of global sections over the curve's global-function ring for
  every coherent module with strict closed stalk support.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.CanonicalSupportThickening.hZeroCanonical_finiteDimensional_of_closedStalkSupport_lt_top`
  Expose finite-dimensional canonical degree-zero cohomology for every coherent module
  with strict closed stalk support.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.CanonicalSupportThickening.orderedBaseCechLowDegreeFinite_of_rationalSection_of_closedStalkSupport_lt_top`
  Expose ordered base-Cech finiteness in degrees zero and one for strict support on a
  pointed smooth proper integral curve.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.IsCoherentLowDegreeSupportComodel.identity`
  Make every already low-degree-finite coherent module its own support comodel through
  the identity comparison.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.isCoherentLowDegreeSupportComodel_of_rationalSection_of_fullSupport`
  On full support, assemble a low-degree support comodel from a finite-sections target
  and a comparison invertible on any nonempty open, with both support side conditions
  automatic.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.finiteFreeTarget_isCoherentLowDegreeSupportComodel_of_fullSupport`
  Specialize the full-support assembler to a finite free target and a nonempty
  open-local isomorphism.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.orderedBaseCechLowDegreeFinite_of_fullSupportComodels`
  Discharge the strict-support branch by canonical finite thickenings and identity
  comodels, reducing arbitrary coherent low-degree finiteness to full-support comodels
  only.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_fullSupportComodels`
  Expose finite-dimensional canonical H0 for every coherent module from the isolated
  full-support-only comodel producer boundary.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_strictCokernel`
  Derive finite-dimensional canonical H0 from a coherent map whose source has finite H0
  and whose cokernel has strict support, using pointed-curve H1 finiteness for the
  kernel.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.isZero_restrict_cokernel_image_ι_of_epi_map`
  Make the image cokernel vanish where the original module morphism restricts to an
  epimorphism.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.closedStalkSupport_cokernel_image_ι_lt_of_epi_map`
  Turn an open-local epimorphism meeting the source support into strict support decrease
  for its coherent cokernel residual.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.closedStalkSupport_eq_top_of_epi_restrict`
  Show that an open-local epimorphism from a coherent source to a full-support coherent
  target over a nonempty open of a preirreducible scheme forces the source to have full
  support.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_fullSupportSource_of_epi_restrict`
  Derive finite-dimensional canonical H0 from an H0-finite coherent full-support source
  which becomes epic onto the target on a nonempty open.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_mono_to_free`
  Prove canonical H0 finite for any module admitting a monomorphism into a finite free
  sheaf on an integral proper scheme.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_fullSupportLattice_of_epi_restrict`
  Reduce finite canonical H0 of a coherent target to a full-support coherent sublattice
  of a finite free sheaf which maps epically onto it on one nonempty open.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_fullSupportTarget_lattice_of_epi_restrict`
  For a full-support coherent target, reduce finite canonical H0 to a coherent submodule
  of a finite free sheaf mapping epically onto the target on one nonempty open, with
  source full support inferred automatically.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.Modules.AffineOpenPresentation`
  Package a coherent source with maps to a finite free sheaf and the target that become
  respectively monic and epic on one affine open.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.exists_affineOpenPresentation`
  Construct the affine-open presentation by transposing finite local generators through
  restriction--pushforward and pulling back against the adjunction unit.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_affineOpenPresentation`
  Use the strict-support kernel and finite-free image of an affine-open presentation to
  prove finite canonical H0 of a full-support coherent target.
* `theorem` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.hZeroCanonical_finiteDimensional_of_coherent`
  Prove canonical H0 finite-dimensional for every coherent module on a pointed smooth
  proper integral curve, with no supplied comparison hypothesis.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.specPullbackSectionsLinearMap_isBaseChange`
  Identify the canonical affine-spectrum pullback map on quasicoherent global sections
  as extension of scalars.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitTopLinearMap_isBaseChange_of_isAffine`
  Transport the affine-spectrum tensor comparison through canonical affine coordinates
  and prove that it is the geometric pullback-unit map.
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitBaseLinearMap`
  Bundle the pullback-unit map on top sections linearly over the base ring of a
  commutative scheme square.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitBaseLinearMap_isBaseChange_of_isPullback`
  For an affine Cartesian square, cancel the coordinate-ring pushout and prove that the
  canonical base-linear section map is extension of scalars along the opposite side.
* `definition` (`contract`):
  `ModuleCat.homologicalComplexExtendScalarsIsoOfIsBaseChange`
  Upgrade a componentwise extension-of-scalars morphism of cochain complexes to an
  isomorphism after scalar extension.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.Modules.baseChangeCechHom`
  Assemble the canonical Cartesian pullback maps on affine intersections into a morphism
  of base-linear Cech complexes.
* `theorem` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.baseChangeCechHom_component_isBaseChange`
  Prove every component of the canonical Cech morphism is extension of scalars by
  reducing its product factors to affine pullback.
* `definition` (`contract`): `AlgebraicGeometry.Scheme.Modules.baseChangeCechComplexIso`
  Identify the scalar extension of the source base-Cech complex with the pulled-back
  base-Cech complex.
* `definition` (`contract`):
  `AlgebraicGeometry.Scheme.Modules.baseChangeCechHomologyIso`
  Commute flat scalar extension with base-Cech homology through the componentwise
  base-change isomorphism.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.fieldExtensionLowDegreeBaseChange`
  Package the genuine H0 and H1 field-extension comparisons obtained from a supplied
  finite affine cover of a separated scheme.
* `definition` (`contract`):
  `MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology.properCurveFieldExtensionLowDegreeBaseChange`
  Choose the finite subcover of the canonical affine cover internally and expose
  cover-independent genuine H0/H1 field-extension base change for coherent modules on
  smooth proper integral curves.

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

:::theorem "MT-EC-ISOGENY-WEIL" (parent := "shared_geometry") (uses := "MT-BASE-INTEGRATED") (tags := "infrastructure, done, integrated, mixed")
*Cyclic subgroup quotients and classifying data.*

*Status:* `done`; *readiness:* `integrated`; *kind:* `infrastructure`; *backend:*
`mixed`; *risk:* `extreme`; *weight:* 25 points.

*Summary:* The canonical commutative group scheme on the concrete projective Weierstrass
cubic, its exact-torsion finite-flat cyclic subgroup, and its represented quotient now
expose the kernel and base-change laws exercised by the X\_0 and order-49 consumers.

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
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityTransitionAndSecantZOpens_cover`
  Cover the standard-by-infinity chart by its transition-to-standard open and the
  genuine secant output-Z open.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardTransitionAndSecantZOpens_cover`
  Cover the infinity-by-standard chart by its transition-to-standard open and the
  genuine secant output-Z open.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairStandardNeighborhoodAndSecantZOpens_cover`
  Cover the infinity pair by the both-standard locus, the regular D(B-infinity)
  neighborhood, and the secant output-Z open.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleChartOverlapCoordinateRing`
  Realize the exact both-standard locus of the infinity pair as the tensor square of the
  cubic chart-overlap ring.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlap_isLocalization_infinityPair`
  Identify the double-overlap ring as localization of the infinity-pair ring at the
  product of its two input Z coordinates.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlap_isLocalization_standardPair`
  Identify the same double-overlap ring as localization of the standard-pair ring at the
  product of its two input Y coordinates.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlapToStandardPair`
  Embed the exact double input overlap as the corresponding principal open of the
  standard-by-standard pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlapToInfinityPair`
  Embed the same exact double input overlap as the both-standard principal open of the
  infinity-by-infinity pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlapFst`
  Project the exact double input overlap to the first copy of the common cubic chart
  overlap.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlapSnd`
  Project the exact double input overlap to the second copy of the common cubic chart
  overlap.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlap_maps_eq`
  Prove that the standard-pair and infinity-pair descriptions of the exact double
  overlap have equal composites into the full projective product.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairActualAdditionOpens_cover`
  Refine the coarse infinity-pair cover to the exact double-standard, genuine regular
  output-Y, and secant output-Z source ranges.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairAdditionOpenCover`
  Package the three genuine addition sources as a finite scheme-theoretic open cover of
  the infinity-by-infinity pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairAdditionCoverMorphism`
  Select the transported standard, regular neighborhood, or secant morphism on each
  exact member of the infinity-pair addition cover.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityActualAdditionOpens_cover`
  Prove that the genuine second-input transition and secant output-Z source ranges cover
  the standard-by-infinity chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityAdditionOpenCover`
  Package the transition and secant sources as a scheme-theoretic open cover of the
  standard-by-infinity pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityAdditionCoverMorphism`
  Select the transported standard-pair law or secant output-Z law on each
  standard-by-infinity cover member.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardActualAdditionOpens_cover`
  Prove that the genuine first-input transition and secant output-Z source ranges cover
  the infinity-by-standard chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardAdditionOpenCover`
  Package the transition and secant sources as a scheme-theoretic open cover of the
  infinity-by-standard pair chart.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardAdditionCoverMorphism`
  Select the transported standard-pair law or secant output-Z law on each
  infinity-by-standard cover member.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityAdditionCoverMorphism_compatible`
  Identify the explicit second-input/output localization with the cover pullback and
  prove compatibility of all standard-by-infinity local laws.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityAdditionMorphism`
  Glue the compatible two-member atlas to a genuine addition morphism on the entire
  standard-by-infinity chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlapToInfinityPair_comp_standardInfinityAddition`
  Identify the transition restriction of the glued standard-by-infinity law with the
  transported standard-pair addition law.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinitySecantZOpen_comp_addition`
  Identify the secant-Z restriction of the glued standard-by-infinity law with the
  normalized secant morphism.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardAdditionCoverMorphism_compatible`
  Identify the explicit first-input/output localization with the cover pullback and
  prove compatibility of all infinity-by-standard local laws.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardAdditionMorphism`
  Glue the compatible two-member atlas to a genuine addition morphism on the entire
  infinity-by-standard chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlapToInfinityPair_comp_infinityStandardAddition`
  Identify the transition restriction of the glued infinity-by-standard law with the
  transported standard-pair addition law.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairInfinityStandardSecantZOpen_comp_addition`
  Identify the secant-Z restriction of the glued infinity-by-standard law with the
  normalized secant morphism.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairOriginSecantZ_compatible`
  Identify the exact regular-origin/secant-Z intersection with the categorical pullback
  and prove compatibility of its two genuine local laws.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairDoubleSecantZ_compatible`
  Identify the exact double-standard/secant-Z intersection with the categorical pullback
  and prove compatibility through the transported standard law.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairDoubleOrigin_compatible`
  Prove compatibility of the double-standard and regular-origin laws by transporting the
  standard raw output-Z nonvanishing result and extending equality from their dense
  triple overlap into the separated cubic.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairAdditionCoverMorphism_compatible`
  Prove all nine ordered compatibility cases for the genuine three-member infinity-pair
  addition cover.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairAdditionMorphism`
  Glue the compatible double-standard, regular-origin, and secant-Z laws to a genuine
  addition morphism on the entire infinity-by-infinity chart.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairDoubleOverlapToInfinityPair_comp_addition`
  Identify the double-standard restriction of the glued infinity-pair law with the
  transported standard-pair addition law.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairOriginAdditionOpen_comp_addition`
  Identify the regular-origin restriction of the glued infinity-pair law with the
  genuine local addition morphism around (O, O).
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveInfinityPairSecantZOpen_comp_addition`
  Identify the secant-Z restriction of the glued infinity-pair law with the normalized
  secant morphism.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairFirstOverlap_standardInfinity_infinity_addition_eq`
  Prove equality of the standard-by-infinity and infinity-by-infinity laws on their full
  explicit first-factor overlap by extending from the dense secant-Z localization.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairSecondOverlap_infinityStandard_infinity_addition_eq`
  Prove equality of the infinity-by-standard and infinity-by-infinity laws on their full
  explicit second-factor overlap by extending from the dense secant-Z localization.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairStandardInfinityDiagonal_compatible`
  Prove categorical compatibility of the standard-by-standard and infinity-by-infinity
  laws through the exact double input overlap.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairMixedDiagonal_compatible`
  Factor the exact double overlap through both mixed charts and prove their two glued
  laws agree on the diagonal categorical intersection.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairAdditionChartMorphism_compatible`
  Combine all six unordered chart intersections into the sixteen ordered compatibility
  cases for the four-member projective-pair cover.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionMorphism`
  Glue the standard, two mixed, and infinity-pair chart laws to an actual addition
  morphism on the full projective cubic fibre square.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectivePairChartMap_comp_projectiveAdditionMorphism`
  Recover the selected genuine local law by restricting global projective addition to
  any of the four pair-chart members.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionMorphism_comp_structureMap`
  Prove that globally glued projective addition is a morphism over Spec K.
* `definition` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionOver`
  Package globally glued projective addition as a morphism on the concrete cubic object
  in the slice over Spec K.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionOver_left`
  Identify the underlying scheme morphism of slice-level projective addition with the
  globally glued morphism.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.tensorProjectiveCubic_hom`
  Identify the tensor-square structure map in the slice with the concrete
  projective-pair structure map.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.infinitySectionOver_projectiveAdditionOver_left_unit`
  Prove that the projective infinity section is a categorical left unit for global
  projective addition.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.infinitySectionOver_projectiveAdditionOver_right_unit`
  Prove that the projective infinity section is a categorical right unit for global
  projective addition.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionOver_comm`
  Prove that global projective addition is invariant under the cartesian braiding in the
  slice over Spec K.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionOver_negation_right_inv`
  Prove that global projective addition sends a point and its checked Weierstrass
  negation to the projective infinity section.
* `theorem` (`contract`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveAdditionOver_negation_left_inv`
  Prove the symmetric categorical inverse equation using checked commutativity.
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
* `definition` (`integrated`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.projectiveGrpObj`
  Install the concrete reduced projective Weierstrass cubic as its canonical commutative
  group object using the globally glued addition, infinity section, negation, and
  checked group laws; canonicalPointGroupLawCompatibility and the order-49 consumer
  exercise its coordinate-point comparison.
* `definition` (`integrated`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalSplitGammaZeroDatumOfTorsion`
  Construct the canonical split finite-flat cyclic subgroup generated by an exact-order
  coordinate point; its checked consumers prove constant geometric order and recover the
  original rational Γ₀ datum.
* `definition` (`integrated`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalCyclicQuotientPresentation`
  Construct the represented fppf cyclic quotient directly from an exact-order coordinate
  point, with the order-49 quotient presentation as its named downstream consumer.
* `theorem` (`integrated`):
  `MazurTorsion.ModularCurve.XZeroFiniteFlatModuli.WeierstrassProjectiveCubic.canonicalCyclicQuotientPresentationBaseChange_kernel_exact`
  Prove that the canonical finite-flat subgroup remains exactly the scheme-theoretic
  kernel after arbitrary base change.

:::
