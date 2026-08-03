/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicReducedBaseChange

/-!
# The canonical dense standard chart of a projective Weierstrass cubic

This file completes the standard-chart comparison for every extension of the
ground field.  The concrete `Z ≠ 0` quotient chart of the mapped cubic is
composed with the unconditional reduction isomorphism into the actual field
pullback.  Its open range agrees with the range of the canonical pullback of
Mathlib's `Proj.awayι` chart.  The open-immersion API therefore supplies the
canonical chart isomorphism.

Since the actual field pullback is isomorphic to the integral mapped cubic,
the nonempty canonical open is dense.  The resulting
`StandardChartComparison` proves geometric integrality and reaches Tau Ceti's
abelian-variety constructor without a reducedness assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The `Z / Y` coordinate does not vanish in the prime quotient defining
the `Y ≠ 0` chart.  Algebraically, the monic cubic chart equation cannot
divide a nonzero constant polynomial in its outer variable. -/
theorem infinityChartPolynomial_not_dvd_innerX (W : WeierstrassCurve K) :
    ¬ infinityChartPolynomial W ∣ Polynomial.C Polynomial.X := by
  intro h
  obtain ⟨g, hg⟩ := h
  have hpoly : infinityChartPolynomial W ≠ 0 :=
    (infinityChartPolynomial_monic W).ne_zero
  have hconstant : (Polynomial.C Polynomial.X :
      Polynomial (Polynomial K)) ≠ 0 :=
    Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero
  have hg0 : g ≠ 0 := by
    intro hzero
    subst g
    simp at hg
  have hdegree := congrArg Polynomial.natDegree hg
  rw [Polynomial.natDegree_C,
    Polynomial.natDegree_mul hpoly hg0,
    infinityChartPolynomial_natDegree] at hdegree
  omega

/-- The `Z / Y` coordinate is not contained in the infinity-chart equation
ideal. -/
theorem coordinateChartRatio_one_two_not_mem_infinityChartIdeal
    (W : WeierstrassCurve K) :
    coordinateChartRatio (K := K) 1 2 ∉ infinityChartIdeal W := by
  rw [infinityChartIdeal_eq_map,
    ← infinityChartRingEquiv_innerX,
    Ideal.apply_mem_of_equiv_iff,
    Ideal.mem_span_singleton]
  exact infinityChartPolynomial_not_dvd_innerX W

/-- The two integral coordinate charts overlap.  The witness is the generic
point of the `Y ≠ 0` quotient chart; the preceding divisibility calculation
shows that its `Z / Y` coordinate is nonzero. -/
theorem coveringChartRanges_inter_nonempty (W : WeierstrassCurve K) :
    (Set.range (coveringChartMap W false) ∩
      Set.range (coveringChartMap W true)).Nonempty := by
  let q : coveringChartScheme W false :=
    (⊥ : PrimeSpectrum (coveringChartCoordinateRing W false))
  let x : scheme W := coveringChartMap W false q
  refine ⟨x, ⟨⟨q, rfl⟩, ?_⟩⟩
  change x ∈ (coveringChartMap W true).opensRange
  rw [coveringChartMap_opensRange]
  change inclusion W x ∈ (coveringChartAway K true).opensRange
  change inclusion W (coveringChartMap W false q) ∈
    (coveringChartAway K true).opensRange
  rw [← Scheme.Hom.comp_apply, coveringChartMap_comp_inclusion]
  have hAway : (coveringChartAway K true).opensRange =
      Proj.basicOpen (homogeneousPieces K)
        (MvPolynomial.X (2 : Fin 3)) := by
    exact Proj.opensRange_awayι (homogeneousPieces K)
      (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X K 2) (by omega)
  rw [hAway]
  change MvPolynomial.X (2 : Fin 3) ∉
    ((coveringChartAway K false)
      (coveringChartQuotientInclusion W false q)).asHomogeneousIdeal
  intro hZ
  have hratio := (polynomial_mem_awayι_iff_awayMk_mem
    (K := K) 1 (coveringChartQuotientInclusion W false q)
      (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X K 2)).mp hZ
  have hmk :
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (MvPolynomial.isHomogeneous_X K 1) 1 (MvPolynomial.X 2)
        (by simpa using MvPolynomial.isHomogeneous_X K 2) :
          HomogeneousLocalization.Away (homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 3))) =
        coordinateChartRatio (K := K) 1 2 := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
      (isLocalizationElem_degree_one_eq_coordinateChartRatio
        (K := K) 1 2)
  rw [hmk] at hratio
  change Ideal.Quotient.mk (infinityChartIdeal W)
      (coordinateChartRatio (K := K) 1 2) ∈
    (⊥ : Ideal (coveringChartCoordinateRing W false)) at hratio
  change Ideal.Quotient.mk (infinityChartIdeal W)
      (coordinateChartRatio (K := K) 1 2) = 0 at hratio
  exact coordinateChartRatio_one_two_not_mem_infinityChartIdeal W
    (Ideal.Quotient.eq_zero_iff_mem.mp hratio)

/-- The two concrete chart ranges cover the cubic. -/
theorem coveringChartRanges_union_eq_univ (W : WeierstrassCurve K) :
    Set.range (coveringChartMap W false) ∪
      Set.range (coveringChartMap W true) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ (⊤ : (scheme W).Opens) := trivial
  rw [← (coveringChartsOpenCover W).iSup_opensRange] at hx
  change x ∈ ⨆ b : Bool, (coveringChartMap W b).opensRange at hx
  rw [iSup_bool_eq] at hx
  exact hx.elim Or.inr Or.inl

private theorem preirreducibleSpace_of_two_open_irreducible_cover
    {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsIrreducible U) (hV : IsIrreducible V)
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hoverlap : (U ∩ V).Nonempty) :
    PreirreducibleSpace X := by
  apply PreirreducibleSpace.of_forall_nonempty_inter
  intro A B hAopen hBopen hA hB
  obtain ⟨a, haA⟩ := hA
  obtain ⟨b, hbB⟩ := hB
  have haCover : a ∈ U ∨ a ∈ V := by
    have : a ∈ U ∪ V := by rw [hcover]; trivial
    exact this
  have hbCover : b ∈ U ∨ b ∈ V := by
    have : b ∈ U ∪ V := by rw [hcover]; trivial
    exact this
  rcases haCover with haU | haV <;> rcases hbCover with hbU | hbV
  · obtain ⟨z, hzU, hzA, hzB⟩ :=
      hU.2 A B hAopen hBopen ⟨a, haU, haA⟩ ⟨b, hbU, hbB⟩
    exact ⟨z, hzA, hzB⟩
  · have hVA : (V ∩ A).Nonempty := by
      obtain ⟨z, hzU, hzA, hzV⟩ :=
        hU.2 A V hAopen hVopen ⟨a, haU, haA⟩ hoverlap
      exact ⟨z, hzV, hzA⟩
    obtain ⟨z, hzV, hzA, hzB⟩ :=
      hV.2 A B hAopen hBopen hVA ⟨b, hbV, hbB⟩
    exact ⟨z, hzA, hzB⟩
  · have hUA : (U ∩ A).Nonempty := by
      obtain ⟨z, hzV, hzA, hzU⟩ :=
        hV.2 A U hAopen hUopen ⟨a, haV, haA⟩
          (by simpa [Set.inter_comm] using hoverlap)
      exact ⟨z, hzU, hzA⟩
    obtain ⟨z, hzU, hzA, hzB⟩ :=
      hU.2 A B hAopen hBopen hUA ⟨b, hbU, hbB⟩
    exact ⟨z, hzA, hzB⟩
  · obtain ⟨z, hzV, hzA, hzB⟩ :=
      hV.2 A B hAopen hBopen ⟨a, haV, haA⟩ ⟨b, hbV, hbB⟩
    exact ⟨z, hzA, hzB⟩

/-- The reduced projective Weierstrass cubic is irreducible.  The proof uses
the two concrete integral charts, their checked cover, and their explicit
nonempty overlap. -/
instance scheme_irreducibleSpace (W : WeierstrassCurve K) :
    IrreducibleSpace (scheme W) where
  toPreirreducibleSpace :=
    preirreducibleSpace_of_two_open_irreducible_cover
      (by
        rw [← Set.image_univ]
        exact (IrreducibleSpace.isIrreducible_univ
          (coveringChartScheme W false)).image
            (coveringChartMap W false)
            (coveringChartMap W false).continuous.continuousOn)
      (by
        rw [← Set.image_univ]
        exact (IrreducibleSpace.isIrreducible_univ
          (coveringChartScheme W true)).image
            (coveringChartMap W true)
            (coveringChartMap W true).continuous.continuousOn)
      (IsOpenImmersion.isOpen_range (coveringChartMap W false))
      (IsOpenImmersion.isOpen_range (coveringChartMap W true))
      (coveringChartRanges_union_eq_univ W)
      (coveringChartRanges_inter_nonempty W)
  toNonempty := Nonempty.map (coveringChartMap W true) inferInstance

/-- The concrete reduced projective Weierstrass cubic is integral. -/
instance scheme_isIntegral (W : WeierstrassCurve K) : IsIntegral (scheme W) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The concrete mapped standard chart, regarded as an open subscheme of the
actual field pullback through the unconditional reduction isomorphism. -/
noncomputable def mappedStandardChartMap
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    standardAffineChartScheme (W.map (algebraMap K L)) ⟶
      fieldBaseChange W L :=
  coveringChartMap (W.map (algebraMap K L)) true ≫
    mappedCubicReductionMap W L

instance mappedStandardChartMap_isOpenImmersion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsOpenImmersion (mappedStandardChartMap W L) := by
  change IsOpenImmersion
    (coveringChartMap (W.map (algebraMap K L)) true ≫
      mappedCubicReductionMap W L)
  infer_instance

/-- The reduction isomorphism respects the maps from the mapped and actual
cubics to the original projective plane. -/
@[reassoc]
theorem mappedCubicReductionMap_comp_fieldBaseChangeAmbientMap
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    mappedCubicReductionMap W L ≫ fieldBaseChangeAmbientMap W L =
      inclusion (W.map (algebraMap K L)) ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) := by
  rw [← fieldBaseChangeInclusion_comp_projectivePlaneBaseChangeProjection]
  simp

/-- Pulling the canonical standard open back through the reduction
isomorphism gives exactly the concrete `Z ≠ 0` chart of the mapped cubic. -/
theorem mappedCubicReductionMap_preimage_canonicalStandardOpen
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    mappedCubicReductionMap W L ⁻¹ᵁ
        (canonicalStandardOpenMap W L).opensRange =
      (coveringChartMap (W.map (algebraMap K L)) true).opensRange := by
  calc
    mappedCubicReductionMap W L ⁻¹ᵁ
          (canonicalStandardOpenMap W L).opensRange =
        mappedCubicReductionMap W L ⁻¹ᵁ
          (fieldBaseChangeAmbientMap W L ⁻¹ᵁ
            Proj.basicOpen (homogeneousPieces K)
              (MvPolynomial.X (2 : Fin 3))) := by
      rw [canonicalStandardOpenMap_opensRange_eq_preimage_basicOpen]
    _ = (mappedCubicReductionMap W L ≫ fieldBaseChangeAmbientMap W L) ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces K)
            (MvPolynomial.X (2 : Fin 3)) := by
      rw [Scheme.Hom.comp_preimage]
    _ = (inclusion (W.map (algebraMap K L)) ≫
          projectivePlaneBaseChangeProjection (K := K) (L := L)) ⁻¹ᵁ
            Proj.basicOpen (homogeneousPieces K)
              (MvPolynomial.X (2 : Fin 3)) := by
      rw [mappedCubicReductionMap_comp_fieldBaseChangeAmbientMap]
    _ = inclusion (W.map (algebraMap K L)) ⁻¹ᵁ
          (projectivePlaneBaseChangeProjection (K := K) (L := L) ⁻¹ᵁ
            Proj.basicOpen (homogeneousPieces K)
              (MvPolynomial.X (2 : Fin 3))) := by
      rw [Scheme.Hom.comp_preimage]
    _ = inclusion (W.map (algebraMap K L)) ⁻¹ᵁ
          Proj.basicOpen (homogeneousPieces L)
            (MvPolynomial.X (2 : Fin 3)) := by
      rw [projectivePlaneBaseChangeProjection_preimage_basicOpen]
    _ = (coveringChartMap (W.map (algebraMap K L)) true).opensRange := by
      rw [coveringChartMap_opensRange]
      have hAway : (coveringChartAway L true).opensRange =
          Proj.basicOpen (homogeneousPieces L)
            (MvPolynomial.X (2 : Fin 3)) := by
        exact Proj.opensRange_awayι (homogeneousPieces L)
          (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X L 2) (by omega)
      rw [hAway]

/-- The concrete and canonical standard charts have the same open range in
the actual field pullback. -/
theorem mappedStandardChartMap_opensRange
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (mappedStandardChartMap W L).opensRange =
      (canonicalStandardOpenMap W L).opensRange := by
  change (coveringChartMap (W.map (algebraMap K L)) true ≫
      mappedCubicReductionMap W L).opensRange = _
  rw [Scheme.Hom.opensRange_comp,
    ← mappedCubicReductionMap_preimage_canonicalStandardOpen]
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_of_isIso]
  simp

/-- The checked standard affine quotient is canonically the `Z ≠ 0` open
of the actual field-base-changed cubic. -/
noncomputable def standardAffineChartIsoCanonicalStandardOpen
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    standardAffineChartScheme (W.map (algebraMap K L)) ≅
      canonicalStandardOpen W L :=
  IsOpenImmersion.isoOfRangeEq
    (mappedStandardChartMap W L) (canonicalStandardOpenMap W L) (by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        mappedStandardChartMap_opensRange])

/-- The chart isomorphism is the unique comparison over the actual field
pullback. -/
@[reassoc (attr := simp)]
theorem standardAffineChartIsoCanonicalStandardOpen_hom_comp
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (standardAffineChartIsoCanonicalStandardOpen W L).hom ≫
        canonicalStandardOpenMap W L =
      mappedStandardChartMap W L := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The canonical `Z ≠ 0` open is dense in every field base change. -/
theorem canonicalStandardOpenMap_denseRange
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    DenseRange (canonicalStandardOpenMap W L) := by
  letI : IsIntegral (fieldBaseChange W L) :=
    IsIntegral.of_isIso (mappedCubicReductionMap W L)
  let e := standardAffineChartIsoCanonicalStandardOpen W L
  letI : Nonempty (canonicalStandardOpen W L) :=
    Nonempty.map e.hom inferInstance
  exact (canonicalStandardOpenMap W L).isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty _)

/-- The unconditional, canonical standard-chart comparison over a field
extension. -/
noncomputable def canonicalStandardChartComparison
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    StandardChartComparison W L :=
  standardChartComparisonOfFieldBaseChange W L
    (standardAffineChartIsoCanonicalStandardOpen W L)
    (canonicalStandardOpenMap_denseRange W L)

/-- The canonical comparison carries the already-checked compatibility with
the ambient projective-plane base-change projection. -/
theorem canonicalStandardChartComparison_isAmbientCompatible
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (canonicalStandardChartComparison W L).IsAmbientCompatible W L :=
  standardChartComparisonOfFieldBaseChange_isAmbientCompatible W L
    (standardAffineChartIsoCanonicalStandardOpen W L)
    (canonicalStandardOpenMap_denseRange W L)

/-- Every concrete reduced projective Weierstrass cubic is geometrically
integral over its ground field. -/
instance structureMap_geometricallyIntegral (W : WeierstrassCurve K) :
    GeometricallyIntegral (structureMap W) :=
  geometricallyIntegral_of_standardChartComparison W fun L ↦
    canonicalStandardChartComparison W L

/-- The canonical chart comparison reaches Tau Ceti's actual
abelian-variety constructor once the independently required group-object
structure is available. -/
noncomputable def toAbelianVarietyOfCanonicalStandardChart
    (W : WeierstrassCurve K) [GrpObj (toOver W)] :
    TauCeti.AlgebraicGeometry.AbelianVariety K :=
  toAbelianVarietyOfStandardChartComparison W fun L ↦
    canonicalStandardChartComparison W L

/-- Real finite-flat consumer of the unconditional chart comparison. Once the independently
required group law on the cubic is supplied, a coordinate point of exact order `N` gives the
checked split `Gamma_0(N)` datum without any chart or geometric-integrality hypothesis at the
call site. -/
noncomputable def canonicalStandardChartSplitGammaZeroPackage
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic] [GrpObj (toOver W)]
    (hgroup : CanonicalPointGroupLawCompatibility W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    StandardChartSplitGammaZeroPackage (N := N) W :=
  standardChartSplitGammaZeroPackage W
    (fun L ↦ (canonicalStandardChartComparison W L).toBaseChangeWitness W L)
    hgroup P hP

/-- The subgroup produced by the canonical chart consumer has the requested constant geometric
order. -/
theorem canonicalStandardChartSplitGammaZeroPackage_hasConstantOrder
    {N : ℕ} [NeZero N] (W : WeierstrassCurve K)
    [DecidableEq K] [W.IsElliptic] [GrpObj (toOver W)]
    (hgroup : CanonicalPointGroupLawCompatibility W)
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (canonicalStandardChartSplitGammaZeroPackage W hgroup P hP).datum.subgroup.carrier
      |>.HasConstantOrder N := by
  simpa [canonicalStandardChartSplitGammaZeroPackage] using
    standardChartSplitGammaZeroPackage_hasConstantOrder W
      (fun L ↦ (canonicalStandardChartComparison W L).toBaseChangeWitness W L)
      hgroup P hP

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
