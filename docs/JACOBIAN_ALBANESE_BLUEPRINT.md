# Jacobian and Albanese blueprint

This document is the implementation plan for the algebraic-geometric
Jacobian challenge in `lean-eval`.  It deliberately separates checked input
from the mathematical theorems that still have to be formalized.  In
particular, an abstract Picard group, a supplied group scheme, or a theorem
whose hypotheses already contain the desired Jacobian is not counted as a
construction.

The target is the following statement.  Let `k` be an arbitrary field and
let `C → Spec k` be proper, smooth of relative dimension one, and
geometrically irreducible.  There is a smooth proper geometrically
irreducible group scheme `J → Spec k` of dimension

```text
g = dim_k H¹(C, O_C)
```

which exists without a `k`-rational point.  Given a rational point `P`, the
map

```text
a_P : C → J,        x ↦ O_C(x - P)
```

sends `P` to the identity and is initial among pointed maps from `C` to an
abelian variety.

## 1. Existing checked foundations

The implementation should reuse the following code rather than introduce a
parallel abstraction.

| Requirement | Existing checked API | Status |
| --- | --- | --- |
| Ground-field action on genuine sheaf `H¹` | `SchemeModuleCohomology.hOneCanonicalFieldModule` | available over every field |
| Finite-dimensional `H¹(O_C)` under the challenge hypotheses | `Jacobian.structureHOne_finiteDimensional` | checked, with no rational-point input |
| Finite-dimensional `H¹` for a coherent module | `genuineSheafHOneCanonical_finiteDimensional_of_codimensionOnePoint` | available after supplying a codimension-one point |
| Vanishing above the dimension of a curve | `CurveCohomologyGrothendieckVanishing` | available |
| Finite map to `P¹` from a non-global rational function | `rationalFunctionMorphismAt_isFinite` | available |
| Finite map to `P¹` under the exact challenge hypotheses | `FiniteMapToProjectiveLine.hom` and `overHom` | checked, with no rational-point input |
| Permutation action on a relative power | `PermutationPower.action` and `action_equivariant` | checked |
| Projectivity of nonempty finite powers of `P¹` | `ProjectiveFiniteOrbit.projectiveLinePower_isProjectiveFactorization` | checked via the scheme-level Segre embedding |
| Affine neighbourhoods of finite projective orbits | `ProjectiveFiniteOrbit.hasAffineOrbit_of_isProjectiveFactorization` | checked over every field |
| Finite-group quotient from affine orbit neighbourhoods | `FiniteGroupQuotient.quotient` | checked, with categorical universal property |
| Flat affine base change of finite-group quotients | `FiniteGroupQuotientFlatBaseChange.existsUnique_invariantsπ_lift_baseChange_spec_of_flat` | checked in arbitrary characteristic |
| Symmetric powers of challenge curves in positive degree | `SymmetricPower.curveSchemeSucc` and `curveProjectionSucc` | quotient checked; projection finite/surjective; target geometrically irreducible and universally closed |
| Ordered universal incidence family on `C × C^d` | `UniversalEffectiveDivisor.orderedIncidence` | checked as the scheme-theoretic union of the coordinate graphs, with invariant ideal and restricted permutation action |
| Open restriction of ordered incidence | `OrderedIncidenceOpenRestriction.idealSheaf_comap_finsetProd_of_isOpenImmersion`, `orderedIncidenceIdeal_comap_eq_prod_pullbackKernels`, and `PointedIncidenceDescent.curveOrderedIncidenceIdeal_comap_eq_prod_pullbackKernels` | checked: pullback along an open immersion preserves finite products of ideal sheaves because the affine restriction maps are ring equivalences; hence the restricted curve-level incidence ideal is exactly the product of the kernels of the pulled-back coordinate-graph immersions, retaining scheme-theoretic multiplicities |
| Quotient of the ordered incidence family | `UniversalEffectiveDivisor.curveOrderedIncidenceQuotientSucc` and `curveDescendedIncidenceιSucc` | checked quotient and descended morphism into `C × Sym^d(C)`; the ambient quotient comparison is an isomorphism; the descended morphism is proper, point-injective, locally quasi-finite, and finite; closed-immersion, flatness, rank, and Cartier proofs remain |
| Pointed symmetric-power comparison | `PointedIncidenceDescent.productSymmetricPowerToIncidenceQuotient` | checked scheme-theoretic insertion, equivariance, quotient descent, factorization over the field, and properness of `C × Sym^(d-1)(C) → D_d`; every target point has a chosen ordered-incidence lift and a common finite étale fpqc split chart carrying its exact ordered support; pointwise fpqc descent interfaces reduce the global isomorphism, flatness, and rank assertions to the remaining local monic-chart identifications |
| Étale diagonal and graph charts | `SmoothCurveReduced.etale_pullback_exists_diagonalCoproduct`, `EtaleGraphCoproduct.exists_graphCoproduct`, `exists_graphCoproduct_of_etale`, `baseChangedComponentInclusion`, and `exists_coproduct_of_isOpenImmersion_isClosedImmersion` | checked: an affine étale self-fiber product splits as the coproduct of the actual diagonal and a complementary sheet; for every separated étale scheme morphism, any compatible section after arbitrary base change is an open-and-closed graph and is exactly the first summand of a coproduct decomposition; arbitrary open-and-closed components remain such summands after the iterated pullback is transported to the direct base change, with both projections identified |
| Smooth-curve étale coordinate chart | `SmoothCurveEtaleCoordinate.PointChart`, `exists_pointChart`, `PointChart.FiniteNeighborhood`, and `PointChart.exists_isCompl_finiteEtale` | checked: every curve point has an affine one-variable étale coordinate morphism compatible with the ground-field structure; Zariski's main theorem then packages that exact point in an open-and-closed component finite étale over an étale base change of the coordinate line, together with its maps back to the chart and curve |
| Finite ordered-support coordinates | `FiniteEtaleRelativeProduct.exists_fin_product_preimage`, `product_isAffine`, `independentProductToRelativeProduct_comp_targets`, `FiniteEtaleCoproductPower.productToCoproductPower_comp_targetPower`, `SplitFiniteBaseChange.baseChangeSplitChartIso`, `familyCoproductSplitIso`, `SplitFiniteAffinePresentation.splitFiniteAffineOverIso`, `SplitFinitePowerPoint.splitPowerPointTuple`, `splitPowerPointComponent_sheetMultiplicity`, `FiniteSupportEtaleCoordinates.Charts`, `Neighborhoods`, `commonBase`, `commonComponentFamily`, `commonComponentFamilyPoint`, `coherentFpqcComponentFamilyOverGround`, `coherentFpqcFamilyCoproductPowerOverGround`, `coherentFpqcFamilyCoproductSplitIso`, `coherentFpqcFamilyCoproductAffineSchemeIso`, `coherentFpqcSupportSheetTuple`, `coherentFpqcSupportComponent`, `FiniteSupportCoordinateMaps.pulledComponentToCoordinatePullback`, `pulledComponent_exists_coordinatePullbackCoproduct`, `coherentPulledComponentToCoordinateLine_eq`, `coherentSplitSheetToCoordinateLine`, `coherentSplitSheetToChart_comp_schemeMap`, `coherentSplitSheet_exists_graphCoproduct`, `HasCommonSplitChartAtSupport`, `exists_commonSplitChartAtSupport`, `PointedIncidenceDescent.orderedSupportPulledComponent_exists_coordinatePullbackCoproduct`, `orderedSupportSplitSheet_exists_graphCoproduct`, and `incidenceQuotientPoint_exists_orderedSupportSplitChart` | checked: an ordered lift of a divisor supplies its actual coordinate points, including repetitions; their finite étale neighborhoods are pulled to one nonempty relative product base; prescribed component points assemble over one specified common-base point; a local-ring base-change argument gives a product point mapping to the exact original ordered-support point, including its residue-field correlation; restriction to the simultaneous rank neighborhood and the subsequent common finite étale fpqc split cover both retain such an exact support preimage; the independent family then maps coherently to a relative product over the product of its splitting bases; the coherent product base is affine; each affine split chart stays split under the projection to that common base, and the disjoint family is canonically one split finite object indexed by the total component sheet count, with an exact affine product-ring presentation; the exact point lies in the relative ordered power of that family with proved compatibility back to the ordered curve power and determines an actual sheet tuple and its canonical permutation-orbit component; component multiplicities are proved equal to the actual tuple's sheet-fiber cardinalities; every extracted sheet point lies over the same coherent base point; the chosen affine-line coordinate is tracked through restriction, fpqc pullback, and coherent base formation; before any splitting, the whole selected finite component is an open-and-closed summand of the base-changed coordinate chart and its two projections are exactly the original curve-chart map and common-base map; every split sheet maps back to the original affine curve chart with exactly its matching base coordinate, hence supplies the distinguished open-and-closed graph summand in the chart's equal-coordinate fiber product; every split sheet count equals the original fiber rank; the full dependent chart assertion is packaged and consumed directly at every point of the actual incidence quotient |
| Two-layer finite-support correction and assigned split chart | `FiniteSupportIndex.topologicalSupportFinset`, `topologicalCoordinateSupportIndex_eq_iff`, `sum_topologicalSupportMultiplicity`, `supportFinset`, `coordinateSupportIndex_eq_iff`, `residuePointToPower_comp_distinct_comp_repeat`, `FiniteSupportEtaleCoordinates.geometricResiduePoint_reconstruction`, `geometricDistinctCharts`, `geometricDistinctNeighborhoods`, `FiniteEtaleAssignedCoproductPower.productToAssignedProduct`, `SplitFiniteBaseChange.splitFamilySheetOwner`, `sheetInclusion_comp_familyCoproductSplitIso`, `GeometricSupportAssignedSplitChart.productToAssigned_comp_curvePower`, `exists_assignedCoproductPowerPoint_over_support`, `assignedSupportSheetTuple`, `assignedSupportSheetOwner_productPoint`, `assignedSupportComponent_sheetMultiplicity`, and `PointedIncidenceDescent.orderedSupportGeometricAssignedSheetOwner_productPoint` | checked: the topological finite image records which coordinates share an underlying curve point; separately, the finite image of actual coordinate morphisms from the residue-field spectrum identifies exactly the genuinely repeated coordinates, and representative selection followed by repetition recovers the original point; the geometric-support family has one member per distinct coordinate morphism, while its assigned ordered power retains all `d` occurrences; repeating the coherent geometric-support product and inserting it into the power of the single disjoint split family gives an exact preimage of the original ordered support; every such point determines an actual length-`d` split-sheet tuple and orbit component, whose sheet multiplicities are exactly the tuple-fiber cardinalities; after flattening the componentwise split family, the owner of the global sheet selected by coordinate `i` is exactly the geometric-support member assigned to `i`, so repeated graph factors land in the intended sheet blocks |
| Affine occurrence-wise block chart | `AssignedProductStabilizer.action`, `assignedMap_equivariant`, `productToAssignedProduct_invariant`, `FiniteSupportEtaleCoordinates.geometricAssignedCommonBaseToCoordinatePower`, `GeometricAssignedAffineChart.commonAffineBase`, `toCoordinatePower`, `action_fixed_commonAffineBasePoint`, `quotient`, and their `PointedIncidenceDescent` consumers | checked: equal geometric occurrences reuse one chosen finite-étale neighbourhood but remain independent factors in a degree-`d` relative product; its assignment stabilizer acts by reindexing precisely within equal-support blocks; after restricting each distinct finite-étale base to an affine open through its distinguished point, the full occurrence product is affine and maps equivariantly and étale to ordered affine-root space; its finite block quotient exists and is surjective; the central point is obtained by taking one correlated point per distinct support member and then repeating it, so it is fixed by the whole block stabilizer without incorrectly treating arbitrary coordinatewise scheme points as residue-field-compatible |
| Coherent component base change | `CoherentComponentBaseChange.coherentPulledComponent_isPullback`, `coherentPulledComponentDirectIso`, `coherentComponentToCoordinatePullback`, and `coherentComponent_exists_coordinatePullbackCoproduct`; `PointedIncidenceDescent.orderedSupportCoherentComponent_exists_coordinatePullbackCoproduct` | checked: restriction to the rank open, pullback to the fpqc splitting cover, and pullback along the matching projection from the coherent product base paste to one cartesian square; the nested component is canonically the direct base change of the original selected finite component; transporting its open-and-closed coordinate-chart inclusion through this comparison preserves the exact curve-chart and coherent-base projections and exhibits the whole coherent component as one coproduct summand at the actual ordered support |
| Finite étale point neighborhoods | `EtaleFiniteNeighborhood.exists_isCompl_finiteEtale` | checked from Mathlib's Zariski-main local structure theorem: after an étale base change, any selected point of an étale separated chart lies in an open-and-closed component that is finite étale over the new base |
| Finite étale relative products | `FiniteEtaleRelativeProduct.product_isFiniteEtale` and `product_nonempty` | checked: finite étale objects are closed under arbitrary finite products in a slice, and finite relative products of nonempty schemes over a nonempty one-point base remain nonempty |
| Constant-rank neighborhoods | `FiniteFlatConstantRankNeighborhood.rankOpen` and `morphismRestrict_finrank` | checked: the rank fiber through a chosen point is clopen, contains that point, and restriction of a finite flat finitely presented morphism to it has constant rank |
| Finite étale split chart | `EtaleSplitChart.splitProjection`, `EtaleSplitChart.splitProjection_finrank`, `EtaleSplitChart.exists_fpqc_splitCover`, `AffineFiniteEtaleSplitChart.exists_fpqc_splitCover`, `FiniteEtalePointSplitChart.exists_affineOpen_fpqc_splitCover`, `FiniteEtaleFamilySplitChart.exists_common_splitCover`, `AffineFiniteEtaleFamilySplitChart.exists_fpqc_common_splitCover`, and `FiniteEtaleFamilyPointSplitChart.exists_affineOpen_fpqc_common_splitCover` | checked: after a finite faithfully flat étale extension, a constant-rank finite étale algebra becomes a finite product of the base; a finite family has, around every common base point, one affine neighborhood in the intersection of all its clopen rank loci and one finite étale fpqc cover splitting every restricted member; the scheme isomorphisms commute with the projection to the fpqc base, and on the pointwise nonempty charts the number of split sheets is proved equal to the original fiber rank |
| Split symmetric quotient | `SplitFiniteSymmetricQuotient` | checked: the invariant ring of a split ordered power is the product ring on tuple orbits; every orbit component has sheet multiplicities summing to the divisor degree |
| Split monic-root family | `SplitMonicRootFamily` | checked: the product of the sheetwise monic root algebras is finite flat and has constant rank equal to the sum of the sheet multiplicities, hence the divisor degree |
| Split-component universal root | `SplitComponentUniversalRoot` | checked: the joint coefficient chart and sheetwise universal monic polynomials give a finite flat root family of constant rank equal to the symmetric-power degree |
| Split tuple stabilizer | `SplitTupleStabilizer.stabilizerEquivFiberPerm` | checked: the residual symmetry of a sheet-label component is the product of the symmetric groups of its sheet fibers |
| One-block symmetric invariants | `BlockSymmetricPolynomial.leftSymmetricAlgEquiv` and `mem_leftSymmetricSubalgebra_iff` | checked: after separating two variable blocks, elementary-symmetric coefficients freely generate precisely the polynomials fixed by permutations supported on the first block |
| Fiberwise elementary-symmetric map | `BlockPermutationInvariants.jointElementarySymmetricToFixedPoints` | checked: independent permutations of a finite family of fibers fix every fiberwise elementary-symmetric coefficient, so the joint coefficient map factors through the product-group invariant ring |
| Fixed coefficient induction | `MvPolynomialFixedCoefficients.fixedPointsEquivMvPolynomialFixedCoefficients` | checked: for a coefficientwise group action, fixed multivariable polynomials are exactly polynomials over the fixed coefficient subring |
| Coordinate/coefficient product invariants | `CoordinateCoefficientInvariants.coefficientCoordinateAlgEquiv` | checked: simultaneous coordinate permutations and an independent coefficient-ring action have invariant ring freely generated by elementary-symmetric coordinates over the coefficient fixed ring |
| Iterated block invariants | `IteratedBlockInvariants.jointBlockInvariantAlgEquiv` and `jointBlockInvariantSchemeIso` | checked: a finite recursive product of symmetric groups acting on joint root variables has a polynomial fixed ring, and its affine quotient is the corresponding elementary-symmetric coefficient space |
| Finite fiber invariant chart | `FiniteFiberPermutationInvariants.finiteFiberInvariantAlgEquiv`, `FiniteFiberMonicCoordinates.monicCoefficientInvariantAlgEquiv`, and `SplitSymmetricQuotientChart.componentStabilizerInvariantSchemeIso` | checked: sigma reindexing conjugates recursive block permutations to independent sheet-fiber permutations, sheetwise Vieta reversal gives the exact free-monic coordinates, and the actual residual tuple-stabilizer quotient of a split component is the coefficient scheme used by its universal monic root family |
| Split-component monic compatibility | `SplitComponentMonicCoordinates.sheetPolynomial_map_componentMonicCoefficientToRoots` | checked: after inclusion into ordered-root coordinates, every sheet's universal free-monic polynomial is exactly the product of that sheet's ordered linear root factors |
| Split-component ordered-incidence invariants | `SplitComponentOrderedIncidence.orderedIncidenceBaseChangeEquiv`, `invariantRootEquivOrderedIncidenceFixedPoints`, and `orderedIncidenceInvariantSchemeIso` | checked: tensor product commutes with the finite product of sheetwise root algebras, adjoining each root commutes with base change, flat invariant base change recovers the product universal-root algebra from the ordered-root incidence invariants, and the resulting affine quotient is finite flat of constant rank equal to the symmetric-power degree |
| Split-component graph-product ideal | `SplitComponentGraphIdeal.orbitAdaptedPositionEquivRootIndex`, `rootGraphEvaluation_ker`, `orderedGraphIdeal_eq_orderedRootLocusIdeal`, and `orderedGraphIdeal_eq_ker` | checked: an actual ordered tuple is reindexed by its sheet fibers using the permutation witnessing its relation to the component's arbitrary orbit representative; one root graph is exactly “select the owner sheet, then evaluate at the root,” with kernel the linear factor on that sheet and the unit ideal elsewhere; the product of all graph ideals is the exact kernel of simultaneous evaluation into the sheetwise ordered-root algebras, so repeated coordinates retain their scheme-theoretic factor multiplicity |
| Geometric assigned root specialization | `GeometricAssignedRootCoordinates.positionRootOwner_productPoint`, `rootSheetToChart_comp_schemeMap`, `rootSheet_exists_graphCoproduct`, `evaluatedRootGraphEvaluation_ker`, `evaluatedRootGraphEvaluation_orderedAmbientCoordinateHom`, and their `PointedIncidenceDescent` consumers | checked: only points inserted from the assigned component product are used, so every specialized root sheet belongs to the genuine support member assigned to that occurrence; the selected sheet maps to its actual curve chart with exactly the corresponding affine-line coordinate and is the graph summand of the equal-coordinate pullback; the universal component root ring is formed over the ground-field section ring and specializes to global functions on the coherent affine support base, where each universal graph factor and graph-evaluation square becomes the concrete owner-sheet linear graph equation. This validates the point and sheet indexing, but it is not a neighbourhood chart: repeated occurrences must retain independent root variables in the dimension-`d` local model |
| Invariant/free-monic root comparison | `SplitComponentInvariantRootComparison.componentProductRootAlgEquiv` and `componentProductRootSchemeIso_hom_comp_projection` | checked: coefficient change from the residual-stabilizer fixed ring to the free-monic coefficient presentation transports every sheetwise root algebra and their finite product, and the resulting affine-scheme isomorphism commutes with the two root-family projections |
| Fpqc finite-flat descent | `FpqcDescent` | checked: isomorphism, flatness, and a constant finite-flat rank descend from an fpqc chart; independently chosen pointwise fpqc charts first descend on their Zariski neighborhoods and then glue globally |
| Degree-one universal divisor | `UniversalEffectiveDivisorDegreeOne.overHom` | checked as a closed graph over `C × Sym¹(C)`; its parameter projection is finite flat of constant rank one |
| Symmetric powers of the affine line | `AffineLineSymmetricPower.coefficientEquivFixedPoints`, `AffineLineMonicCoordinates.monicCoefficientEquivFixedPoints`, and `coordinateQuotientProjection_existsUnique_lift` | checked: permutation invariants are freely generated by elementary symmetric functions, the signed reversal gives monic coefficient coordinates, and both give the categorical affine quotient |
| Affine-line universal root family | `UniversalRootFactorization.universalRootProjection` | checked finite flat of constant rank `n + 1` over every nontrivial commutative base ring |
| Arbitrary monic root families | `MonicRootFamily.projection` and `baseChangeProjection` | checked principal Cartier kernel, closed immersion, finite flat constant rank, and preservation under arbitrary scheme base change |
| Absolute Picard group | AINTLIB `Scheme.Pic` port | available, group-valued only |
| Relative Picard presheaf definitions | AINTLIB `RelativePic` port | available, not represented |
| Pullback/tensor and section base-change identities | `PicardSectionBaseChange` and upstream adapters | available |
| Divisor and point-difference Abel--Jacobi classes | `PicardAbelJacobi`, `PicardRationalSectionAbelJacobi` | available on classes, not a scheme morphism |
| Group objects in schemes over a base | Mathlib `GrpObj (Over S)` | available |
| Morphism-property descent | Mathlib fpqc/fppf descent APIs | available for the properties already registered there |
| Abstract abelian-variety wrappers and products | Tau Ceti | useful vocabulary, not a Jacobian construction |

The finite-cohomology repository integrated under
`MazurTorsion.Upstream.CoherentCohomologyFinite` is useful for comparison and
for characteristic-zero consumers.  The genus definition below uses the
canonical arbitrary-field action instead, because the challenge quantifies
over every field and must not depend on rationalizing an abelian group.

The repository audit found no checked representability theorem for the
relative Picard functor, no constructed `Pic⁰`, and no checked Albanese
universal property in Mathlib, LeanPool, Tau Ceti, or the other inspected
Lean developments.  Consequently those results are implementation work, not
imports to be discovered later.

## 2. Mathematical construction

### 2.1 Integral and cohomological preliminaries

Geometric irreducibility plus smoothness implies geometric reducedness, hence
geometric integrality.  In particular `C` is nonempty and integral.  The
checked construction chooses a standard-smooth affine chart of relative
dimension one and then a nonzero maximal ideal in its coordinate ring.  The
maximal ideal cannot be zero: otherwise the coordinate ring would be a field
finite over the ground field, while standard smoothness supplies an injective
étale map from a one-variable polynomial ring, contradicting its infinite
dimension.  The corresponding scheme point has codimension one.  At such a
point the local ring is a discrete valuation ring.  A uniformizer, viewed in
the function field and inverted, has order `-1`; it cannot be a global regular
function.  The associated rational-function morphism `C → P¹_k` is finite.

For a coherent module `M`, finite pushforward along this map and the checked
two-affine calculation on `P¹` show that genuine sheaf `H¹(C, M)` is a finite
dimensional `k`-vector space.  The scalar action is the canonical action
obtained by restricting the global-section action along `C → Spec k`; it is
independent of the chosen point and finite map.

For `M = O_C`, define

```text
genus(C) := finrank k H¹(C, O_C).
```

The choice of a codimension-one point occurs only inside the checked proof of
finiteness, not in this definition or its hypotheses.

### 2.2 The relative Picard fppf sheaf

For a `k`-scheme `T`, put `C_T = C ×_k T` and define the rigidified relative
Picard prestack by line bundles on `C_T`, with arrows the line-bundle
isomorphisms.  Passing to isomorphism classes and quotienting by pullbacks of
line bundles from `T` gives the usual presheaf

```text
T ↦ Pic(C_T) / Pic(T).
```

The quotient formulation is essential when `C(k)` is empty.  If a point is
available, rigidification along that section is equivalent to the quotient,
but the Jacobian itself may not depend on this extra datum.

Sheafify for the fppf topology.  Prove the following in this order:

1. pullback is functorial before quotienting;
2. tensor product and dual descend to the quotient;
3. line bundles and their isomorphisms satisfy fpqc descent;
4. the quotient presheaf maps to an fppf sheaf of abelian groups;
5. formation of this sheaf commutes with arbitrary field extension.

The degree map is defined fiberwise by Euler characteristic,

```text
deg(L) = χ(L) - χ(O_C),
```

and is fppf local on the base.  This avoids choosing a rational divisor.
Its kernel is the degree-zero relative Picard sheaf `Pic⁰_{C/k}`.  One must
also prove that this kernel agrees with the connected component of the
identity after geometric base change.

### 2.3 Representability

Representability is the main new theorem.  A suitable proof route is the
classical symmetric-power construction, which is concrete enough to expose
all Lean dependencies.

1. Construct `Sym^d(C)` as the quotient of `C^d` by the finite permutation
   action and identify it with effective relative Cartier divisors of degree
   `d` on `C`.
2. Construct the universal effective divisor on
   `C × Sym^d(C)` and its line bundle.
3. Define the Abel map `Sym^d(C) → Pic^d_{C/k}`.
4. Prove relative Riemann--Roch and cohomology-and-base-change for line
   bundles on `C`.
5. For `d ≥ 2g - 1`, prove that the Abel map is an fppf-locally nonempty
   projective-space bundle.  Its fibers are complete linear systems.
6. Use the equivalence relation induced by the two projections from
   `Sym^d(C) ×_{Pic^d} Sym^d(C)` and effective descent to construct the
   representing scheme.
7. Transport tensor product, dual, and the trivial bundle through Yoneda to
   obtain the group object.

The construction must first represent all degree components locally and then
select the identity component.  Defining the Jacobian from a point-normalized
Picard functor would incorrectly require `C(k)` to be inhabited.

The first quotient step is now factored into checked code.  Relative powers,
their permutation actions, componentwise equivariance, stable-affine
refinement, quotient gluing, and descent of the structure map are all
formalized.  For every positive degree, the affine-orbit hypothesis is also
checked over an arbitrary field.  A nonempty finite product of projective
lines is projective by iterating the checked scheme-level Segre embedding.
For a finite family of points in projective space, retain the inclusion-
maximal homogeneous point ideals.  For each ordered pair of distinct maximal
ideals `I,J`, choose a homogeneous element in `J \ I`; multiplying these
pairwise separators gives an element vanishing at every maximal point other
than `I` and nonvanishing at `I`.  Multiplication by a coordinate nonzero at
`I` raises all such elements to one common positive degree.  Their sum is
nonzero modulo every maximal point ideal and hence modulo every original
point ideal.  Its homogeneous basic open is affine and contains the entire
finite orbit.  Pullback along a projective closed embedding proves the claim
for projective schemes.  Finally, the selected finite map `C → P¹` induces a
finite componentwise map `C^d → (P¹)^d`; affine-orbit neighbourhoods transfer
back along this affine map.

Thus `Sym^d(C)` is available for every `d > 0` under exactly the challenge
hypotheses.  Degree zero is the terminal relative power and can be treated
separately when its quotient interface is needed.  The ordered power is
proper, geometrically irreducible, and universally open.  Geometric
irreducibility descends to the symmetric quotient through the universally
surjective projection, and universal closedness descends from the proper
ordered power.  The quotient projection is finite: on each stable affine
chart, base sections land in the invariant ring, finite generation passes
from the base to the invariants, and finite-group integrality makes the chart
ring module-finite over its invariants.  The descended structure map is
locally of finite type on the same charts: Artin--Tate makes the base-to-
invariants map finite type, and epimorphicity of the invariant-spectrum map
identifies the chart restriction with its `Spec` morphism.

The quotient is also separated.  More generally, if `X → Y` is finite and
surjective and `X → S` is proper, then `Y → S` is separated.  After
base-changing the diagonal of `Y/S` along
`X ×_S X → Y ×_S Y`, its source is `X ×_Y X`; the resulting
morphism into `X ×_S X` is proper.  The product cover is again finite and
surjective, so universal closedness of the pulled-back diagonal descends
without a flatness assumption.  Since every scheme diagonal is an immersion,
a universally closed diagonal is a closed immersion.  Combining
separatedness, universal closedness, and local finite type proves that every
positive symmetric power constructed above is proper over the ground field.

The ordered incidence family needed for the next step is also checked.  In
`C ×_S C^d`, its `i`-th component is the equalizer of the first
projection and the `i`-th coordinate of the second projection.  Since
`C → S` is separated, each graph is a closed immersion.  The product of
their ideal sheaves defines the scheme-theoretic union, including the empty
family in degree zero, and its support is exactly the union of the graph
supports.  Coordinate permutations act by ambient isomorphisms, carry the
graph indexed by `g i` isomorphically to the graph indexed by `i`, and
transport finite products of ideal sheaves multiplicatively.  Consequently
the ordered incidence ideal is invariant with its scheme-theoretic
multiplicities.  The remaining aim of this stage is to identify its quotient
with a closed family in `C × Sym^d(C)` and prove that family is a relative
effective Cartier divisor of degree `d`.

The scheme quotient part of this descent is now checked.  The invariant
ideal restricts the ambient permutation action to the ordered incidence
closed subscheme.  Both the ambient action and this restricted action have
affine orbit neighbourhoods: take the product of the selected finite map
`C → P¹` with its componentwise power, pull affine orbit neighbourhoods
back from the projective ordered ambient product of `P¹`, and then pull them
back once more along the incidence closed immersion.  Hence both finite-group
quotients exist.  Equivariance gives a canonical morphism from the incidence
quotient to the ambient quotient, and the invariant map
`C × C^d → C × Sym^d(C)` gives the descended incidence morphism
`D_d → C × Sym^d(C)`.  Pulling that morphism back to the ordered incidence
family recovers the original inclusion followed by the symmetric quotient.
Flat quotient base change now identifies the ambient quotient with
`C × Sym^d(C)`.  More precisely, the ordered ambient product is exhibited as
the pullback of `C^d → Sym^d(C)` along the second projection; the pullback
action is transported to the coordinate-permutation action; the two quotient
universal properties construct inverse morphisms; and epimorphicity of the
original and flat-base-changed quotient projections proves the inverse laws.
Thus the remaining local-algebra step is only the special incidence
calculation: show that the descended morphism is a relative effective Cartier
divisor with finite flat degree-`d` fibers.

The global finiteness part of that assertion is now checked independently of
the local equation.  The ordered incidence quotient is proper over the field:
its finite surjective quotient cover is proper, and separatedness plus
universal closedness descend.  The descended morphism into
`C × Sym^d(C)` is consequently proper because this target is separated over
the field.  Equality of two of its points lifts to the ordered incidence
family.  Equality in the ambient quotient says that the two lifted points
differ by one permutation; equivariance and injectivity of the original
closed immersion then identify them in the incidence quotient.  Thus the
descended morphism is point-injective, hence locally quasi-finite, and
proper plus locally quasi-finite makes it finite.  This argument deliberately
does not claim that invariants preserve the incidence quotient's defining
ideal: that is false for arbitrary invariant quotients in modular
characteristic and must instead follow here from the special monic local
equation.

The expected presentation of the total space is also now constructed
globally.  On ordered powers, insert the distinguished point as coordinate
zero in `C^(d)`.  The product incidence ideal is contained in the zeroth
coordinate-graph ideal, so this map factors scheme-theoretically through the
ordered incidence subscheme, not only through its support.  It is equivariant
for permutations of the other `d - 1` coordinates, extended by fixing zero.
Quotient descent and the checked ambient quotient isomorphism therefore give
a canonical proper comparison

```text
C × Sym^(d-1)(C) ⟶ D_d.
```

Its pullback to ordered coordinates is exactly insertion followed by the
incidence quotient projection, and its composite with the ground-field
structure map is the product structure map.  Proving this comparison is an
isomorphism is now the precise remaining local statement.  Once established,
the first projection makes `D_d` finite flat of rank `d`, while the monic
root equation identifies its map into `C × Sym^d(C)` as a relative effective
Cartier divisor.

The affine-line quotient and the basic characteristic-free local calculation
are now checked.  The coordinate-permutation fixed subring of a multivariable
polynomial ring is identified with Mathlib's symmetric-polynomial subalgebra;
the fundamental theorem of symmetric polynomials identifies it with a freely
generated coefficient ring.  On spectra the ordered-root projection has the
full categorical quotient universal property, so `Sym^n(A¹)` is affine
coefficient space over an arbitrary base.  The signed reversal from
increasing elementary-symmetric coordinates to the coefficient of `X^i` in
`Polynomial.freeMonic` is an explicit algebra automorphism.  Vieta's formula
is checked in these exact coordinates: the universal monic polynomial maps
to the product of the ordered linear root factors.  Mathlib's algebra classifying a
factorization of the universal monic
degree-`n + 1` polynomial into monic factors of degrees `1` and `n` is
explicitly equivalent, over the coefficient ring, to adjoining a root of the
universal polynomial.  The power basis of that root algebra proves that the
factorization map is finite free of rank `n + 1`; on spectra this gives the
finite flat constant-rank universal-root morphism.  Its embedding in the
ambient affine line is checked to have kernel generated by the universal
monic polynomial, which is a non-zero-divisor; thus the local family is a
principal effective Cartier divisor.  This computation has also been
generalized from the universal polynomial to every monic polynomial over an
arbitrary nontrivial commutative ring.  Its root algebra has exact kernel the
principal ideal generated by the polynomial, that ideal is an invertible
module, and the resulting closed finite-flat constant-rank family remains so
after arbitrary scheme base change.  The next step is to transport this model
through standard-smooth affine charts and their étale coordinates on a smooth
curve, identify it with the pointed symmetric-power/incidence morphism, and
descend the flat rank and Cartier properties from that local comparison.
The tensor-square input now remembers the relevant sheet: the chosen product
decomposition has first projection equal to tensor multiplication, and on
spectra the diagonal is exactly the first coproduct summand.  This has been
extended from the self-fiber product to arbitrary base change on one factor:
the evaluation map on the tensor-product coordinate ring is identified with
the categorical graph, and the graph is exactly the first summand in the
base-changed coproduct decomposition.  The affine restriction has now been
removed from the geometric statement: the graph of any compatible section
of a separated étale morphism is proved open and closed and splits the whole
fiber product as that graph plus its complementary open subscheme.  More
generally, base-changing any open-and-closed component of a fiber product and
transporting the iterated pullback to the direct base change preserves both
immersion properties.  The transported inclusion's two projections are
proved to be the original component projection and the new base projection,
and the component again splits off as a coproduct summand.
The standard-smooth curve chart has now been packaged as an actual étale
scheme morphism to the spectrum of a one-variable polynomial ring.  Mathlib's
Zariski-main local structure theorem applied to that morphism supplies the
required finite model at each curve point: after an étale base change of the
coordinate line, the selected point is contained in an open-and-closed
component finite étale over the new base.
The locally constant rank function supplies a clopen constant-rank
neighborhood of the lifted base point.  On an affine subneighborhood, the
finite étale component is affine, and the affine-scheme splitting wrapper
passes to global sections, invokes `EtaleSplitChart`, and transports the split
pullback back through `isoSpec`.  This construction is now packaged as a
pointwise theorem: every point of the base of a finite étale morphism lies in
an affine constant-rank open whose restricted morphism becomes a split finite
set after a finite étale fpqc cover.  Splitting over one common affine base
has also been assembled: recursively splitting the base changes of a finite
family preserves each earlier split and produces one finite étale fpqc cover;
the affine-scheme wrapper simultaneously identifies every pullback with a
finite coproduct of that cover.  These isomorphisms now commute with the
structure morphisms to the common fpqc base, so they identify finite covers
over the base rather than merely their abstract source schemes.  The split
projection is finite flat and its rank is its number of sheets; on a
pointwise chart, surjectivity over the chosen base point makes the cover ring
nontrivial, so rank invariance under the compatible isomorphism proves that
this number is exactly the original fiber rank.  Intersecting the finitely
many clopen rank loci first gives the pointwise version over arbitrary
schemes: around every common base point there is one affine neighborhood and
one compatible split cover, with checked sheet counts, for the whole family.
For an ordered lift of a divisor, its finite coordinate family is now
extracted directly and equipped pointwise with these affine étale charts,
retaining repeated coordinates and hence multiplicities.  Each Zariski-main
component remembers its selected point and maps back to the original curve.
The coordinate ring map now retains its exact ground-ring compatibility as a
`CommRingCat` morphism.  Consequently the affine chart inclusion, each
Zariski-main pullback component, and its map back to the curve have checked
morphisms in the slice over the global-section copy of the ground field.
The separate coordinate-line base changes are synchronized by their relative
product over the global-section copy of the ground field.  The chosen point
of this common base is constructed with exact projection equations to every
Zariski-main base point, so each original ordered support point lifts to its
base-changed component and each corresponding fiber rank is positive.  Every
component remains finite étale after pullback, their relative product is
finite étale, and the lifted component points assemble to an actual point of
that product over the specified common-base point.  A separate local-ring
base-change theorem now handles the subtle point-set issue for relative
products: from chosen factor preimages it constructs a preimage of the exact
product point over the spectrum of that point's local ring.  Applying it to
the pulled components gives a product point mapping to the original ordered
support and proves that each of its factor projections is the prescribed
lifted component point.  Thus the residue-field correlation is retained, not
reconstructed from coordinate projections.  This exact lift persists after
restricting every component to any common-base open containing the selected
point.  It also persists after any further common surjective base change: a
second application of the local-ring product-preimage theorem lifts the exact
ordered support through the independent product of all base-changed
components.  The pointwise family theorem now returns one affine
neighborhood and one finite étale fpqc cover splitting all components with
their exact fiber ranks.  The independent product is then mapped
canonically to the relative product obtained by pulling the `i`-th component
along the `i`-th projection from the product of all copies of the splitting
base.  Projection compatibility proves that forgetting this coherent
relative product back to the curve power is exactly the original product
map, so the transported point still maps to the original ordered support.
This gives a genuine one-base family suitable for the split quotient model,
without replacing equality of scheme points by coordinatewise equality.
The coherent components are next assembled into one disjoint family over
that product base.  Coordinatewise coproduct inclusions map their relative
product to the ordered relative power of this single family, and a checked
composition identity shows that its transported exact point still maps to
the original ordered support in `C^d`.  Split finite objects are now defined
intrinsically over an arbitrary scheme as finite coproducts of the base.
Over an affine base this presentation is identified, in the slice, with the
standard spectrum of the product algebra.  Pullback along an arbitrary base
map preserves that split presentation.  Applying this to every affine chart
over the matching projection from the product base proves that all coherent
components remain split there.  A sigma-coproduct flattening and finite-sheet
reindexing then identify their disjoint union with one split finite object
whose sheet count is the cardinality of the dependent sum of the component
sheet sets.  This construction is exposed as
`coherentFpqcFamilyCoproductSplitIso`.  The coherent product base is affine:
it is a finite relative product of copies of the affine splitting cover.
Consequently the intrinsic split family has an exact presentation as the
spectrum of the finite product of the global-section ring, and the
presentation commutes with the family projection to the canonical affine
model of the base.  Finally, applying the topological coproduct equivalence
coordinatewise to the transported exact point extracts a concrete sheet
tuple.  Each reconstructed sheet point has the same coherent base point,
and the tuple selects its actual permutation-orbit component in the split
symmetric power; no multiplicity vector is guessed independently of the
point.  Orbit invariance of fiber cardinalities further proves that the
component's sheet multiplicities are exactly the numbers of coordinates of
that point on the corresponding sheets.  The affine-line coordinate is also
followed through every stage of this construction.  On the original pulled
component it factors through the matching projection of the common base;
the equation persists after restriction, the common fpqc pullback, and the
coherent product-base pullback.  Composing a split-sheet inclusion with the
inverse split chart therefore gives exactly the corresponding coordinate map
from the coherent base.  That sheet is now traced through all four pullback
stages to the original affine curve chart.  Its composite with the chart's
étale coordinate is the coherent-base coordinate, so the general étale graph
theorem identifies it as the first open-and-closed summand of the actual
equal-coordinate fiber product.  The specialization used by pointed
incidence is exposed as
`PointedIncidenceDescent.orderedSupportSplitSheet_exists_graphCoproduct`.
Before choosing the fpqc splitting, the entire selected finite component is
also transported through the two pullback-pasting isomorphisms into the
base-changed curve-coordinate chart.  It is proved open and closed there,
its projections are exactly the original chart map and common-base map, and
it splits off as a single coproduct summand.  The actual ordered-support
specialization is
`orderedSupportPulledComponent_exists_coordinatePullbackCoproduct`; this
packages the finite family prior to any sheetwise quotient comparison.
The restriction, fpqc, and coherent-product pullbacks have now been pasted
into one cartesian square.  Hence the nested coherent component is canonically
the direct base change of that original selected component.  Transporting the
open-and-closed inclusion through the resulting isomorphism proves, with both
projections identified, that the whole coherent component is itself one
coproduct summand of the corresponding base-changed curve-coordinate chart.
The ordered-support consumer is
`orderedSupportCoherentComponent_exists_coordinatePullbackCoproduct`.
The ideal-sheaf localization needed to use these summands is now separate as
well.  Pullback of ideals is not asserted to preserve products for arbitrary
morphisms.  Instead, on an open immersion the affine restriction formula
transports ideals through a ring equivalence, which proves multiplicativity
and then finite-product compatibility.  Applying this to the global ordered
incidence ideal identifies its restriction exactly with the product of the
kernels of the pulled-back coordinate graphs.  The curve-level consumer is
`curveOrderedIncidenceIdeal_comap_eq_prod_pullbackKernels`.  Thus the next
comparison may work factor by factor on the isolated open-and-closed
components without discarding nilpotents or multiplicities.

An audit at this interface exposed an important indexing correction.  The
occurrence-indexed chart construction is valid for lifting the exact ordered
point, but its coproduct cannot itself be the final local curve neighborhood
when coordinates repeat: two copies of one neighborhood would replace the
square of a graph ideal by two artificial reduced summands.  Conversely,
deduplicating only the underlying topological points cannot reconstruct the
ordered point: two morphisms from its residue-field spectrum can have the
same topological image while inducing different residue-field embeddings.

The corrected interface therefore has two layers.  The topological finite
image records which occurrences share an underlying curve point; its
assignment is surjective, its equality criterion is equality of underlying
points, and its fiber cardinalities sum to `d`.  The geometric finite image
enumerates the actual coordinate morphisms from the common residue-field
spectrum.  Selecting one representative of each geometric morphism and
repeating it by the geometric occurrence map is proved to recover the
original residue-field point exactly.  This second layer is the right index
for the split family: conjugate residue-field embeddings over one topological
point become distinct geometric branches after base change, while genuinely
equal coordinate morphisms must share one member and contribute repeated
factors.

`geometricDistinctCharts` and `geometricDistinctNeighborhoods` now feed the
common-base/fpqc splitting construction.  The generic assigned-product API
separates the number of geometric family members from the original degree.
`GeometricSupportAssignedSplitChart.productToAssigned_comp_curvePower`
proves that repeating the coherent product by the occurrence assignment and
then forgetting to the curve is exactly the geometric repeat morphism.  The
checked exact-reconstruction theorem therefore supplies a point of the
degree-`d` assigned product over the original ordered support; insertion into
the degree-`d` power of the single disjoint split family preserves that exact
image.  Its split presentation now extracts the actual length-`d` sheet
tuple and orbit component, and identifies every sheet multiplicity with the
corresponding tuple-fiber cardinality.  The remaining local combinatorial
step is to prove that the owner block of the sheet selected in coordinate
`i` is now proved to be its assigned geometric-support member.  The proof
decomposes the coordinate first in its componentwise split presentation,
traces that local sheet through the coproduct flattening and finite-ordinal
reindexing, and recovers its family owner from the global sheet label.  Thus
the extracted sheet fibers are the intended repeated graph-factor blocks,
not merely equicardinal abstract blocks.  The next geometric step is to
transport the curve-level restricted graph ideals onto those assigned split
sheets and identify their product, with its multiplicities, with the explicit
assigned ordered-root incidence algebra.

A point of the incidence quotient is now lifted through the
surjective ordered-incidence quotient map, embedded in the ordered ambient
product, and fed directly to this packaged split-chart theorem.  The
outstanding step is to transport this exact split-family chart into the
ordered and symmetric incidence quotients, identify the selected orbit
component with the checked free-monic invariant chart, identify the
curve-level incidence restriction of the newly isolated finite-component
summands with the explicit product universal-root algebra, and then descend
that comparison from the fpqc splitting base.

The blockwise invariant calculation and its finite induction are now checked.
Separating a root-variable block from the remaining variables intertwines
permutations of that block with ordinary polynomial-coordinate permutations;
the fundamental theorem of symmetric polynomials therefore replaces that
block by free elementary-symmetric coefficient variables, with an exact
fixed-point membership criterion.  For the subsequent blocks, a general
coefficientwise-action theorem identifies fixed polynomials with polynomial
rings over the fixed coefficient subring.  The joint fiberwise elementary-
symmetric map has also been constructed and shown to land in the invariants
of the full product of fiber permutation groups.  The one-block calculation
has been promoted to the simultaneous coordinate/coefficient product action
and iterated over an arbitrary finite list of blocks.  The recursive
polynomial presentation is proved equivariant with the joint root-variable
renaming action; consequently its fixed ring and affine spectrum are
canonically polynomial coefficient space.  This result is now reindexed by a
sigma type over the actual split sheets.  The reindexing is proved to
conjugate both the variable action and the recursive product group.  The
generator formula for this equivalence is checked: each coefficient variable
maps to the elementary-symmetric polynomial in precisely its own sheet's root
block.  Applying Vieta's signed coefficient reversal independently on every
sheet gives the exact free-monic coordinate convention used by
`SplitComponentUniversalRoot`.  Composition with
`stabilizerEquivFiberPerm` therefore identifies the residual tuple-stabilizer
quotient of each component with that coefficient scheme, not merely with an
abstractly isomorphic polynomial ring.  In these coordinates each sheetwise
universal monic polynomial is proved to pull back to the product of the
ordered linear factors in that sheet.  Tensor product is then proved to
commute with the finite product of sheetwise root algebras, and adjoining a
root is transported through base change on every sheet.  This presents the
explicit multiblock ordered-root incidence algebra as a flat scalar extension
of the product universal-root algebra.  The stabilizer action is transported
through that presentation as algebra automorphisms, and flat invariant base
change identifies its fixed ring with the product universal-root algebra in
arbitrary characteristic.  On spectra this is an isomorphism from the affine
invariant quotient to the product universal-root scheme; its projection is
checked finite flat of constant rank `d`.  The remaining coordinate change is
also explicit: applying the stabilizer-invariant/free-monic coefficient
equivalence to each sheet induces an algebra equivalence between the two
products of root algebras.  Its compatibility with both coefficient
inclusions is proved on every product factor, hence the induced affine-scheme
isomorphism lies over the corresponding coefficient-scheme isomorphism.  What
remained algebraically was to verify that the phrase "ordered-root incidence"
really denotes the scheme-theoretic graph product rather than only a ring of
the expected rank.  This is now checked.  The orbit-adapted finite-fiber
reindexing sends the original `d` positions to their actual sheet/root
indices; it explicitly corrects for the arbitrary representative stored by
the quotient component.  For each distinguished sheet a coordinate graph
contributes its linear root ideal precisely in that sheet's owner block and
contributes the unit ideal on all other sheets.  Their product is proved
equal to the sheetwise ordered-root polynomial ideal, and then to the exact
kernel of the simultaneous map into the product of `AdjoinRoot` algebras.
The geometric specialization at the support point is also explicit: the
ordered-root ring is taken over the ground-field section ring and maps to
global functions on the coherent affine support base by sending each root
variable to its actual étale coordinate function.  Every linear factor maps
to the corresponding concrete graph equation, and the exact universal graph
evaluation commutes with this specialization.  On the geometric side, the
selected split sheet maps back to the correct curve chart with that same
coordinate and is the first open-and-closed summand of the equal-coordinate
pullback.

This calculation deliberately stops at a pointwise specialization.  The
coherent base used there is a product of copies of an already-common fpqc
cover; it is a useful device for correlating sheet labels, but it has too many
base dimensions to be the final symmetric-power chart.  Conversely, using
only one coordinate per distinct support member has too few dimensions when a
point occurs with multiplicity.  The dimension-`d` local chart must instead
keep one independent étale coordinate for every ordered occurrence, while
using the geometric-support assignment only to determine the block subgroup
that permutes equal occurrences.  Concretely, for multiplicities `n_j`, its
ordered base is the product of the `n_j` independent coordinate-line
neighbourhoods.  The checked affine occurrence chart now builds this product
from one reused neighbourhood per distinct geometric support member, equips
it with the exact block action, and maps it equivariantly and étale to ordered
affine-root space.  Its finite block quotient and its stabilizer-fixed central
point are also checked.  After an equivariant fpqc splitting, the selected
sheets form one block-stable open, and quotienting that open by
`∏_j S_{n_j}` must be identified with the already checked blockwise
monic-coefficient chart.  The remaining local theorem must prove that
quotient comparison, identify the graph-product ideal with
`SplitComponentGraphIdeal.orderedGraphIdeal`, and descend the resulting
isomorphism to the actual curve quotient.  Only after that theorem may the
pointwise fpqc interfaces be used to prove the global pointed comparison is
an isomorphism and the universal divisor is finite flat Cartier of degree
`d`.

The affine algebra in that comparison is checked.  For a finite group acting
on an `R`-algebra `A` and a flat `Aᴳ`-algebra `B`, the canonical map
`B → (A ⊗_{Aᴳ} B)ᴳ` is bijective.  On spectra, the base change of
`Spec A → Spec Aᴳ` along `Spec B → Spec Aᴳ` therefore has the full unique
categorical-quotient factorization property.  This affine theorem has also
been globalized over quotient charts and then applied to the smooth (hence
flat) curve factor, completing the ambient comparison above.

For the incidence algebra itself, adjoining the distinguished root commutes
with scalar extension from symmetric coefficients to ordered-root
coordinates.  Transport the coordinate-permutation action through this
base-change equivalence; it permutes the ordered roots and fixes the
distinguished root.  Flat invariant base change then identifies its fixed
subring with the universal monic root algebra.  On spectra, the actual affine
incidence quotient is therefore isomorphic over symmetric coefficient space
to the universal root scheme.  In particular its structure morphism is
finite flat of constant rank `d`, in every characteristic.  The remaining
step is geometric localization: cover the curve-level pointed comparison by
smooth affine charts, pass to their étale one-variable coordinates, and
identify each restricted quotient map with this checked affine model.

Denote the representing object by

```text
J(C) := Pic⁰_{C/k}.
```

Yoneda gives a universal degree-zero line-bundle class on `C × J(C)`.  It is
only defined modulo pullback from `J(C)` in the unrigidified formulation,
which is exactly the correct invariant.

### 2.4 Geometry and dimension of `Pic⁰`

The geometric properties should be proved after base change to an algebraic
closure and descended.

* Finite type follows from the symmetric-power presentation.
* Properness follows from the valuative criterion: a degree-zero line bundle
  on the generic fiber extends across a DVR after twisting by vertical
  components, and the quotient by base line bundles removes the ambiguity.
* Smoothness follows from unobstructed deformation of line bundles on a
  curve.  The obstruction lies in `H²(C, O_C)`, which vanishes by the checked
  dimension-one cohomology theorem.
* The tangent space at the identity is canonically `H¹(C, O_C)`.  Express
  first-order line bundles through the exact sequence

  ```text
  1 → 1 + ε O_C → O^×_{C[ε]} → O_C^× → 1
  ```

  and identify `1 + ε O_C` additively with `O_C`.
* Translation by group elements identifies every tangent space with the
  tangent space at the identity.  Smoothness therefore has constant relative
  dimension `finrank k H¹(C, O_C) = genus(C)`.
* The identity component is geometrically connected by definition; smoothness
  makes it geometrically reduced.  Connected plus reduced for a group scheme
  of finite type over a field gives geometric irreducibility here, or one can
  prove irreducibility directly from the symmetric-power cover.  This step
  must produce Mathlib's exact `GeometricallyIrreducible` morphism property.

Tensor product is symmetric, so the resulting group object is commutative.
The lean-eval target asks only for `GrpObj`; keeping commutativity internally
is nevertheless useful for sums and descent.

### 2.5 Pointed Abel--Jacobi morphism

Let `P : Spec k → C`.  On `C × C`, the diagonal is an effective Cartier
divisor because `C` is smooth of relative dimension one.  The graph of the
constant section `P` is another relative effective Cartier divisor.  The
line bundle

```text
O(Δ - C × P)
```

has degree zero on every fiber.  By the representing property, it determines

```text
a_P : C → Pic⁰_{C/k}.
```

Pulling the family back along `P` yields the trivial class, so
`P ≫ a_P = e`.  This proof should reuse the checked point-difference Picard
class and section base-change lemmas as the pointwise shadow of the family
calculation.

### 2.6 Albanese universal property

Let `A/k` be smooth, proper, geometrically irreducible, and a group object,
and let `f : C → A` satisfy `f(P) = e_A`.

First prove the rigidity lemmas needed by the exact challenge statement.

1. A morphism from a proper geometrically connected scheme to a separated
   group scheme that is constant on one geometric fiber is constant when the
   standard rigidity hypotheses hold.
2. If `h : B → A` is a scheme morphism between abelian varieties and
   `h(e_B) = e_A`, apply rigidity to

   ```text
   (x,y) ↦ h(x+y) - h(x) - h(y)
   ```

   to prove that `h` is a group homomorphism.

This second result matters because the challenge quantifies over ordinary
arrows `J(C) ⟶ A`, not bundled homomorphisms of group objects.

There are two equivalent constructions of the factor map.  The preferred
formal route continues the symmetric-power presentation:

1. On `C^d`, sum the values of `f`.  Commutativity makes this map symmetric,
   so it descends to `s_d : Sym^d(C) → A`.
2. Choose `d ≥ 2g - 1`.  Prove that `s_d` is constant on the complete linear
   systems forming fibers of `Sym^d(C) → Pic^d(C)`.  This is Abel's theorem;
   its proof uses principal divisors and the rigidity lemma.
3. Descend `s_d` through the projective-bundle presentation to
   `Pic^d(C) → A`.
4. Translate degree `d` to degree zero using `dP`, obtaining
   `g : J(C) → A`.
5. Pull back along the degree-one Abel map to prove `f = a_P ≫ g`.
6. If `g₁` and `g₂` have the same pullback along `a_P`, their difference is
   zero on `a_P(C)`.  It is therefore zero on all finite sums, hence on the
   fppf-locally surjective symmetric-power presentation of `J(C)`.  Effective
   epimorphism descent gives `g₁ = g₂`.

The construction commutes with field extension, and all arguments may be
checked fppf locally before descending to `k`.  No rational point is used in
the construction of `J(C)`; `P` is used only to turn the Picard torsor into a
pointed Abel map and to translate `Pic^d` to `Pic⁰`.

## 3. Lean module plan

The proposed files are small dependency layers.  A later file may import
earlier layers, but the cohomology core must not import Picard
representability.

```text
MazurTorsion/AlgebraicGeometry/Jacobian/
  Genus.lean
  RelativePicardFunctor.lean
  RelativePicardDescent.lean
  EulerCharacteristicDegree.lean
  SymmetricPower.lean
  UniversalEffectiveDivisor.lean
  RelativeRiemannRoch.lean
  CohomologyBaseChange.lean
  FiniteMapToProjectiveLine.lean
  FiniteGroupQuotient.lean
  PermutationPower.lean
  ProjectiveFiniteOrbit.lean
  GeometricallyIrreducibleDescent.lean
  PicardRepresentability.lean
  PicardIdentityComponent.lean
  PicardTangentSpace.lean
  PicardGeometry.lean
  AbelJacobi.lean
  AbelianRigidity.lean
  Albanese.lean
  LeanEval.lean
```

`LeanEval.lean` is the named downstream consumer and should expose a narrow
facade whose declarations match the benchmark:

```text
genus
jacobian
jacobianGrpObj
jacobianSmoothOfRelativeDimension
jacobianProper
jacobianGeometricallyIrreducible
abelJacobi
point_comp_abelJacobi
existsUnique_abelJacobi_comp
```

The benchmark submission then imports only Mathlib, so the final checked
facade and every non-Mathlib dependency must be copied into
`Submission/Helpers.lean` with attribution.  The copied code must remain
definitionally compatible with the declarations delegated from
`Submission.lean`.

## 4. Proof obligations by file

Each major definition comes with a concrete consumer and a theorem that
prevents it from becoming inert scaffolding.

* `Genus`: canonical `k`-module on `H¹(O_C)`, finiteness, and the natural
  number `finrank`; consumed by `PicardTangentSpace`.
* `RelativePicardFunctor`: base-change functor and abelian-group structure;
  consumed by descent.
* `RelativePicardDescent`: fppf sheaf condition; consumed by
  representability.
* `EulerCharacteristicDegree`: base-change-stable degree and degree-zero
  subfunctor; consumed by the identity component.
* `SymmetricPower`: quotient, effective divisors, universal family; consumed
  by representability and Albanese descent.
* `PicardRepresentability`: a representing scheme and Yoneda equivalence;
  consumed immediately by `PicardIdentityComponent`.
* `PicardIdentityComponent`: represented `Pic⁰` and group object; consumed by
  geometry and Abel--Jacobi.
* `PicardTangentSpace`: tangent-space equivalence with genuine `H¹`; consumed
  by the relative-dimension proof.
* `PicardGeometry`: smoothness, properness, geometric irreducibility, and
  relative dimension; consumed by the lean-eval facade.
* `AbelianRigidity`: origin-preserving morphisms are homomorphisms; consumed
  by Albanese uniqueness.
* `Albanese`: construction and uniqueness of the factor map; consumed by the
  lean-eval facade.

If an intermediate theorem is not yet proved, it belongs only in a registered
`Challenge/` contract and must not leak as an assumption into the final
facade.  Finishing the benchmark means eliminating every such contract from
the transitive dependency graph of `LeanEval.lean`.

## 5. Verification

For each layer:

1. build the smallest touched module with `LEAN_NUM_THREADS=1`;
2. inspect `#print axioms` for every exported theorem;
3. reject `sorry`, `admit`, custom axioms, `unsafe`, `partial`,
   `native_decide`, and local option changes;
4. run `python3 scripts/quality.py` before handoff;
5. in the generated lean-eval workspace, run its checker and `lake test`;
6. record peak RSS with `/usr/bin/time -v`; keep it below 50 GiB.

The final proof is complete only when both the Mazur facade and the standalone
lean-eval submission compile against their pinned Mathlib versions and the
comparator accepts all nine declarations.
