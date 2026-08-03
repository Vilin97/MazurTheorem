/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePlaneBaseChange

/-!
# The reduced Weierstrass cubic inside the field pullback

For a field extension `K → L`, the ambient comparison identifies the pullback of
`P²_K` with `P²_L`.  This file restricts that comparison to the cubic at the
scheme level.  The resulting closed immersion of the actual field pullback has
the same underlying closed set as the reduced cubic attached to `W.map`.

Consequently, `scheme (W.map ...)` is canonically the reduction of
`fieldBaseChange W L`.  In particular there is a concrete surjective closed
immersion from the mapped reduced cubic to the actual pullback.  If the latter
is reduced, this morphism is an isomorphism, and its inverse has exactly the
ambient compatibility required by `StandardChartComparison`.

The remaining mathematical boundary is therefore precise: proving that the
closed-immersion kernel produced by scalar extension is radical.  No abstract
base-change isomorphism is assumed in this file.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The actual field pullback of the cubic, embedded in the pullback of its
ambient projective plane.  The pullback associator makes this the base change
of `inclusion W`. -/
noncomputable def fieldBaseChangeAmbientPullbackInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChange W L ⟶
      pullback (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (pullbackRightPullbackFstIso
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (inclusion W)).inv ≫
    pullback.snd (inclusion W)
      (pullback.fst (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))

instance fieldBaseChangeAmbientPullbackInclusion_isClosedImmersion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsClosedImmersion (fieldBaseChangeAmbientPullbackInclusion W L) := by
  let e := pullbackRightPullbackFstIso
    (projectivePlaneStructureMap K)
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) (inclusion W)
  let f := pullback.snd (inclusion W)
    (pullback.fst (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  haveI : IsClosedImmersion e.inv := by infer_instance
  haveI : IsClosedImmersion f := by infer_instance
  change IsClosedImmersion (e.inv ≫ f)
  infer_instance

/-- Transport the preceding closed immersion through the checked ambient
projective-plane base-change isomorphism. -/
noncomputable def fieldBaseChangeInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChange W L ⟶ projectivePlane L :=
  fieldBaseChangeAmbientPullbackInclusion W L ≫
    (projectivePlanePullbackIso (K := K) (L := L)).hom

instance fieldBaseChangeInclusion_isClosedImmersion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsClosedImmersion (fieldBaseChangeInclusion W L) := by
  dsimp only [fieldBaseChangeInclusion]
  infer_instance

/-- Before transport to `P²_L`, the field-pullback inclusion projects to the
original cubic inclusion. -/
@[reassoc]
theorem fieldBaseChangeAmbientPullbackInclusion_comp_fst
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChangeAmbientPullbackInclusion W L ≫
        pullback.fst (projectivePlaneStructureMap K)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      fieldBaseChangeProjection W L ≫ inclusion W := by
  dsimp only [fieldBaseChange, fieldBaseChangeAmbientPullbackInclusion,
    fieldBaseChangeProjection, structureMap]
  simpa only [Category.assoc] using
    (pullbackRightPullbackFstIso_inv_snd_fst
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) (inclusion W))

/-- The transported cubic inclusion has the expected projection to the
original ambient plane. -/
@[reassoc]
theorem fieldBaseChangeInclusion_comp_projectivePlaneBaseChangeProjection
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChangeInclusion W L ≫
        projectivePlaneBaseChangeProjection (K := K) (L := L) =
      fieldBaseChangeAmbientMap W L := by
  rw [fieldBaseChangeInclusion, Category.assoc,
    projectivePlanePullbackIso_hom_comp_projection]
  dsimp only [fieldBaseChange, fieldBaseChangeAmbientPullbackInclusion,
    fieldBaseChangeAmbientMap, fieldBaseChangeProjection, structureMap]
  simpa only [Category.assoc] using
    (pullbackRightPullbackFstIso_inv_snd_fst
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) (inclusion W))

/-- The transported cubic inclusion has the expected structure morphism to
`Spec L`. -/
@[reassoc]
theorem fieldBaseChangeInclusion_comp_projectivePlaneStructureMap
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    fieldBaseChangeInclusion W L ≫ projectivePlaneStructureMap L =
      pullback.snd (structureMap W)
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [fieldBaseChangeInclusion, Category.assoc,
    projectivePlanePullbackIso_hom_comp_structureMap]
  dsimp only [fieldBaseChange, fieldBaseChangeAmbientPullbackInclusion, structureMap]
  simpa only [Category.assoc] using
    (pullbackRightPullbackFstIso_inv_snd_snd
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) (inclusion W))

/-- Every point of the scheme-theoretic field pullback lies on the mapped
homogeneous cubic after transport through the ambient isomorphism. -/
theorem fieldBaseChangeInclusion_mem_carrier
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (x : fieldBaseChange W L) :
    fieldBaseChangeInclusion W L x ∈ carrier (W.map (algebraMap K L)) := by
  let q := fieldBaseChangeAmbientPullbackInclusion W L x
  apply (projectivePlanePullbackIso_mem_mappedWeierstrassZeroLocus_iff
    (K := K) (L := L) W q).mpr
  change (fieldBaseChangeAmbientPullbackInclusion W L ≫
    pullback.fst (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) x ∈ carrier W
  rw [fieldBaseChangeAmbientPullbackInclusion_comp_fst]
  change (inclusion W) (fieldBaseChangeProjection W L x) ∈ carrier W
  rw [← range_inclusion W]
  exact ⟨fieldBaseChangeProjection W L x, rfl⟩

/-- The transported field pullback and the reduced mapped cubic have exactly
the same underlying closed subset of `P²_L`. -/
theorem range_fieldBaseChangeInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    Set.range (fieldBaseChangeInclusion W L) =
      carrier (W.map (algebraMap K L)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact fieldBaseChangeInclusion_mem_carrier W L x
  · intro hy
    let q := (projectivePlanePullbackIso (K := K) (L := L)).inv y
    have hyK : pullback.fst (projectivePlaneStructureMap K)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) q ∈ carrier W := by
      apply (projectivePlanePullbackIso_mem_mappedWeierstrassZeroLocus_iff
        (K := K) (L := L) W q).mp
      change y ∈ ProjectiveSpectrum.zeroLocus (homogeneousPieces L)
        {(W.map (algebraMap K L)).toProjective.polynomial} at hy
      have hqy : (projectivePlanePullbackIso (K := K) (L := L)).hom q = y := by
        calc
          (projectivePlanePullbackIso (K := K) (L := L)).hom q =
              ((projectivePlanePullbackIso (K := K) (L := L)).inv ≫
                (projectivePlanePullbackIso (K := K) (L := L)).hom) y := rfl
          _ = y := by
            rw [(projectivePlanePullbackIso (K := K) (L := L)).inv_hom_id]
            rfl
      rw [hqy]
      exact hy
    rw [← range_inclusion W] at hyK
    obtain ⟨w, hw⟩ := hyK
    have hwq : inclusion W w =
        pullback.fst (projectivePlaneStructureMap K)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) q := by
      exact hw
    obtain ⟨p, hpw, hpq⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := inclusion W)
      (g := pullback.fst (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) w q hwq
    let e := pullbackRightPullbackFstIso
      (projectivePlaneStructureMap K)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) (inclusion W)
    refine ⟨e.hom p, ?_⟩
    change (e.inv ≫ pullback.snd (inclusion W)
      (pullback.fst (projectivePlaneStructureMap K)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫
      (projectivePlanePullbackIso (K := K) (L := L)).hom) (e.hom p) = y
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, e.hom_inv_id,
      Category.id_comp, Scheme.Hom.comp_apply, hpq]
    simp [q]

/-- The kernel support of the transported field pullback is the closed mapped
cubic. -/
theorem support_ker_fieldBaseChangeInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (fieldBaseChangeInclusion W L).ker.support =
      closedCarrier (W.map (algebraMap K L)) := by
  ext y
  change y ∈ ((fieldBaseChangeInclusion W L).ker.support :
      Set (projectivePlane L)) ↔ y ∈ carrier (W.map (algebraMap K L))
  rw [Scheme.Hom.support_ker]
  rw [(fieldBaseChangeInclusion W L).isClosedEmbedding.isClosed_range.closure_eq,
    range_fieldBaseChangeInclusion]

/-- The reduced mapped cubic ideal is exactly the radical of the
scheme-theoretic field-pullback ideal in `P²_L`.  This is the precise
scheme-level restriction statement available before proving that scalar
extension preserves radicality. -/
theorem radical_ker_fieldBaseChangeInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (fieldBaseChangeInclusion W L).ker.radical =
      idealSheaf (W.map (algebraMap K L)) := by
  calc
    (fieldBaseChangeInclusion W L).ker.radical =
        Scheme.IdealSheafData.vanishingIdeal
          (fieldBaseChangeInclusion W L).ker.support :=
      (Scheme.IdealSheafData.vanishingIdeal_support).symm
    _ = Scheme.IdealSheafData.vanishingIdeal
          (closedCarrier (W.map (algebraMap K L))) := by
      rw [support_ker_fieldBaseChangeInclusion]
    _ = idealSheaf (W.map (algebraMap K L)) := rfl

/-- The field-pullback ideal is contained in the reduced mapped cubic ideal. -/
theorem ker_fieldBaseChangeInclusion_le_ker_mappedInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    (fieldBaseChangeInclusion W L).ker ≤
      (inclusion (W.map (algebraMap K L))).ker := by
  have hker : (inclusion (W.map (algebraMap K L))).ker =
      idealSheaf (W.map (algebraMap K L)) := by
    simpa only [inclusion] using
      (idealSheaf (W.map (algebraMap K L))).ker_subschemeι
  rw [hker, ← radical_ker_fieldBaseChangeInclusion]
  exact Scheme.IdealSheafData.le_radical _

/-- The canonical reduction morphism from the reduced mapped cubic to the
actual scheme-theoretic field pullback.  It is defined by the universal
property of the latter closed immersion, using the checked radical identity
above. -/
noncomputable def mappedCubicReductionMap
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    scheme (W.map (algebraMap K L)) ⟶ fieldBaseChange W L :=
  IsClosedImmersion.lift (fieldBaseChangeInclusion W L)
    (inclusion (W.map (algebraMap K L)))
    (ker_fieldBaseChangeInclusion_le_ker_mappedInclusion W L)

/-- The reduction morphism is a genuine restriction of the ambient mapped
cubic inclusion. -/
@[reassoc (attr := simp)]
theorem mappedCubicReductionMap_comp_fieldBaseChangeInclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    mappedCubicReductionMap W L ≫ fieldBaseChangeInclusion W L =
      inclusion (W.map (algebraMap K L)) :=
  IsClosedImmersion.lift_fac _ _ _

instance mappedCubicReductionMap_isClosedImmersion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsClosedImmersion (mappedCubicReductionMap W L) := by
  haveI : IsClosedImmersion
      (mappedCubicReductionMap W L ≫ fieldBaseChangeInclusion W L) := by
    rw [mappedCubicReductionMap_comp_fieldBaseChangeInclusion]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (mappedCubicReductionMap W L) (fieldBaseChangeInclusion W L)

/-- The reduction morphism is surjective on underlying points: both closed
immersions have the same checked range. -/
theorem mappedCubicReductionMap_surjective
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    Function.Surjective (mappedCubicReductionMap W L) := by
  intro y
  have hy := fieldBaseChangeInclusion_mem_carrier W L y
  rw [← range_inclusion (W.map (algebraMap K L))] at hy
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (fieldBaseChangeInclusion W L).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply,
    mappedCubicReductionMap_comp_fieldBaseChangeInclusion]
  exact hx

instance mappedCubicReductionMap_surjective_instance
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    Surjective (mappedCubicReductionMap W L) :=
  ⟨mappedCubicReductionMap_surjective W L⟩

/-- The canonical reduction morphism is an isomorphism exactly when the
scheme-theoretic field pullback is reduced.  Thus this is not an extra
comparison hypothesis: reducedness is the sole remaining obstruction. -/
theorem mappedCubicReductionMap_isIso_iff_isReduced
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsIso (mappedCubicReductionMap W L) ↔ IsReduced (fieldBaseChange W L) := by
  constructor
  · intro hIso
    letI : IsIso (mappedCubicReductionMap W L) := hIso
    letI : IsReduced (scheme (W.map (algebraMap K L))) := by infer_instance
    exact isReduced_of_isOpenImmersion (inv (mappedCubicReductionMap W L))
  · intro hReduced
    letI : IsReduced (fieldBaseChange W L) := hReduced
    exact isIso_of_isClosedImmersion_of_surjective (mappedCubicReductionMap W L)

/-- Once the actual field pullback is reduced, the concrete reduction
morphism is an isomorphism. -/
noncomputable def fieldBaseChangeIsoMappedCubic
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    [IsReduced (fieldBaseChange W L)] :
    fieldBaseChange W L ≅ scheme (W.map (algebraMap K L)) := by
  letI : IsIso (mappedCubicReductionMap W L) :=
    isIso_of_isClosedImmersion_of_surjective (mappedCubicReductionMap W L)
  exact (asIso (mappedCubicReductionMap W L)).symm

/-- The inverse reduction isomorphism recovers the transported field-pullback
closed immersion. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeIsoMappedCubic_hom_comp_inclusion
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    [IsReduced (fieldBaseChange W L)] :
    (fieldBaseChangeIsoMappedCubic W L).hom ≫
        inclusion (W.map (algebraMap K L)) =
      fieldBaseChangeInclusion W L := by
  letI : IsIso (mappedCubicReductionMap W L) :=
    isIso_of_isClosedImmersion_of_surjective (mappedCubicReductionMap W L)
  rw [← mappedCubicReductionMap_comp_fieldBaseChangeInclusion]
  change inv (mappedCubicReductionMap W L) ≫
      (mappedCubicReductionMap W L ≫ fieldBaseChangeInclusion W L) = _
  simp

/-- The concrete cubic base-change isomorphism satisfies exactly the ambient
compatibility equation required of `StandardChartComparison.targetBaseChangeIso`. -/
theorem fieldBaseChangeIsoMappedCubic_isAmbientCompatible
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    [IsReduced (fieldBaseChange W L)] :
    ((fieldBaseChangeIsoMappedCubic W L).hom ≫
        inclusion (W.map (algebraMap K L))) ≫
      projectivePlaneBaseChangeProjection (K := K) (L := L) =
        fieldBaseChangeAmbientMap W L := by
  rw [fieldBaseChangeIsoMappedCubic_hom_comp_inclusion,
    fieldBaseChangeInclusion_comp_projectivePlaneBaseChangeProjection]

/-- Install the concrete reduced-target comparison in the full standard-chart
package.  Only the independent chart/open identification and its density are
arguments; the target base-change isomorphism is the one constructed above. -/
noncomputable def standardChartComparisonOfReducedFieldBaseChange
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    [IsReduced (fieldBaseChange W L)]
    (chartIso : standardAffineChartScheme (W.map (algebraMap K L)) ≅
      canonicalStandardOpen W L)
    (canonicalMap_denseRange : DenseRange (canonicalStandardOpenMap W L)) :
    StandardChartComparison W L where
  chartIso := chartIso
  targetBaseChangeIso := fieldBaseChangeIsoMappedCubic W L
  canonicalMap_denseRange := canonicalMap_denseRange

/-- The preceding compiled consumer really satisfies
`StandardChartComparison.IsAmbientCompatible`; callers do not supply this
equation. -/
theorem standardChartComparisonOfReducedFieldBaseChange_isAmbientCompatible
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    [IsReduced (fieldBaseChange W L)]
    (chartIso : standardAffineChartScheme (W.map (algebraMap K L)) ≅
      canonicalStandardOpen W L)
    (canonicalMap_denseRange : DenseRange (canonicalStandardOpenMap W L)) :
    (standardChartComparisonOfReducedFieldBaseChange W L chartIso
      canonicalMap_denseRange).IsAmbientCompatible W L := by
  exact fieldBaseChangeIsoMappedCubic_isAmbientCompatible W L

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
