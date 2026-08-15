/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowTargetCompletionLocalGraph
import MazurTorsion.Upstream.CoherentCohomologyFinite.GraphProjectionTargetOpenCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.TargetOpenRangeCover

/-!
# Completion interiors cover the Chow graph range

If a point of the Chow graph lies over the `i`-th affine chart of the
original scheme, its `i`-th completion coordinate lies in the affine
interior of that completion.  This is proved scheme-theoretically: over
the base chart the original graph factors through the closed equality
locus equating the chart map with the labeled completion coordinate.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    [IsLocallyNoetherian X]
    (c : CommonDenseRelativeAffineCoverData k f)

private abbrev D :
    ChowRationalProjectiveMapData f :=
  c.toRationalProjectiveMapData

private abbrev baseProjection :
    c.D.targetRelativeScheme ⟶ X :=
  pullback.fst f c.D.targetClosureToSpec

private abbrev targetProjection :
    c.D.targetRelativeScheme ⟶ c.D.targetClosure :=
  pullback.snd f c.D.targetClosureToSpec

@[reassoc (attr := simp)]
private theorem graphToTargetRelative_toBase :
    c.D.graphToTargetRelative ≫
        c.baseProjection =
      c.D.toOriginalOpen :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem graphToTargetRelative_toTarget :
    c.D.graphToTargetRelative ≫
        c.targetProjection =
      c.D.toTargetClosure :=
  pullback.lift_snd _ _ _

/-- The open of the target-relative product lying over the `i`-th
affine chart of the original scheme. -/
abbrev baseChartRelativeOpen
    (i : c.toAffineCoverData.ι) :
    c.D.targetRelativeScheme.Opens :=
  c.baseProjection ⁻¹ᵁ
    (c.toAffineCoverData.f i).opensRange

/-- The equality locus between the `i`-th affine chart and the `i`-th
target-closure completion coordinate. -/
abbrev completionEqualityLocus
    (i : c.toAffineCoverData.ι) :
    Scheme.{u} :=
  pullback
    (c.projectiveCompletion i).openMap
    (c.targetClosureToProjectiveCompletion i)

/-- The equality locus maps to the relative product of the affine
chart with the target closure. -/
def completionEqualityLocusToChartProduct
    (i : c.toAffineCoverData.ι) :
    c.completionEqualityLocus i ⟶
      pullback
        (c.toAffineCoverData.f i ≫ f)
        c.D.targetClosureToSpec :=
  pullback.mapDesc
      (c.projectiveCompletion i).openMap
      (c.targetClosureToProjectiveCompletion i)
      (c.projectiveCompletion i).model.toSpec ≫
    (pullback.congrHom
      ((c.projectiveCompletion i).openMap_toSpec.trans
        (c.chart_toBase i).symm)
      (c.targetClosureToProjectiveCompletion_toSpec i)).hom

/-- The equality locus is closed in the relative chart product. -/
theorem isClosedImmersion_completionEqualityLocusToChartProduct
    (i : c.toAffineCoverData.ι) :
    IsClosedImmersion
      (c.completionEqualityLocusToChartProduct i) := by
  letI :
      IsProper (c.projectiveCompletion i).model.toSpec :=
    (c.projectiveCompletion i).model.projective.isProper
  letI :
      IsSeparated (c.projectiveCompletion i).model.toSpec :=
    inferInstance
  letI :
      IsClosedImmersion
        (pullback.mapDesc
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i)
          (c.projectiveCompletion i).model.toSpec) :=
    inferInstance
  dsimp only [completionEqualityLocusToChartProduct]
  infer_instance

/-- Identify the chart-relative product with the pullback of the chart
open immersion along the base projection. -/
def chartProductIsoBasePullback
    (i : c.toAffineCoverData.ι) :
    pullback
        (c.toAffineCoverData.f i ≫ f)
        c.D.targetClosureToSpec ≅
      pullback
        (c.toAffineCoverData.f i)
        c.baseProjection :=
  (pullbackRightPullbackFstIso
    f c.D.targetClosureToSpec
    (c.toAffineCoverData.f i)).symm

/-- The chart itself is canonically isomorphic to its open range. -/
abbrev chartIsoOpensRange
    (i : c.toAffineCoverData.ι) :
    Spec (c.toAffineCoverData.R i) ≅
      (c.toAffineCoverData.f i).opensRange.toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (c.toAffineCoverData.f i)
    (c.toAffineCoverData.f i).opensRange.ι
    Subtype.range_coe.symm

/-- Replace the chart in the base pullback by its canonical open-range
model. -/
def chartPullbackToRangePullback
    (i : c.toAffineCoverData.ι) :
    pullback
        (c.toAffineCoverData.f i)
        c.baseProjection ⟶
      pullback
        (c.toAffineCoverData.f i).opensRange.ι
        c.baseProjection :=
  pullback.map
    (c.toAffineCoverData.f i)
    c.baseProjection
    (c.toAffineCoverData.f i).opensRange.ι
    c.baseProjection
    (c.chartIsoOpensRange i).hom
    (𝟙 _)
    (𝟙 X)
    (by
      rw [Category.comp_id]
      exact
        (IsOpenImmersion.isoOfRangeEq_hom_fac
          (c.toAffineCoverData.f i)
          (c.toAffineCoverData.f i).opensRange.ι
          Subtype.range_coe.symm).symm)
    (by simp)

instance isIso_chartPullbackToRangePullback
    (i : c.toAffineCoverData.ι) :
    IsIso (c.chartPullbackToRangePullback i) := by
  dsimp only [chartPullbackToRangePullback]
  infer_instance

@[reassoc (attr := simp)]
theorem chartPullbackToRangePullback_snd
    (i : c.toAffineCoverData.ι) :
    c.chartPullbackToRangePullback i ≫
        pullback.snd
          (c.toAffineCoverData.f i).opensRange.ι
          c.baseProjection =
      pullback.snd
        (c.toAffineCoverData.f i)
        c.baseProjection := by
  unfold chartPullbackToRangePullback
  rw [pullback.lift_snd]
  simp

/-- The pullback of a chart open immersion is canonically the
corresponding open restriction of the target-relative product. -/
def basePullbackIsoRelativeOpen
    (i : c.toAffineCoverData.ι) :
    pullback
        (c.toAffineCoverData.f i)
        c.baseProjection ≅
      (c.baseChartRelativeOpen i).toScheme :=
  asIso (c.chartPullbackToRangePullback i) ≪≫
    pullbackSymmetry
      (c.toAffineCoverData.f i).opensRange.ι
      c.baseProjection ≪≫
    pullbackRestrictIsoRestrict
      c.baseProjection
      (c.toAffineCoverData.f i).opensRange

/-- The preceding isomorphism followed by the open inclusion is the
second projection of the pullback of the chart immersion. -/
@[reassoc (attr := simp)]
theorem basePullbackIsoRelativeOpen_hom_ι
    (i : c.toAffineCoverData.ι) :
    (c.basePullbackIsoRelativeOpen i).hom ≫
        (c.baseChartRelativeOpen i).ι =
      pullback.snd
        (c.toAffineCoverData.f i)
        c.baseProjection := by
  simp [basePullbackIsoRelativeOpen,
    baseChartRelativeOpen,
    c.chartPullbackToRangePullback_snd]

/-- The equality locus as a closed subscheme of the target-relative
base-chart open. -/
def completionEqualityLocusToBaseChartOpen
    (i : c.toAffineCoverData.ι) :
    c.completionEqualityLocus i ⟶
      (c.baseChartRelativeOpen i).toScheme :=
  c.completionEqualityLocusToChartProduct i ≫
    (c.chartProductIsoBasePullback i).hom ≫
    (c.basePullbackIsoRelativeOpen i).hom

/-- The equality locus remains closed in the target-relative
base-chart open. -/
theorem isClosedImmersion_completionEqualityLocusToBaseChartOpen
    (i : c.toAffineCoverData.ι) :
    IsClosedImmersion
      (c.completionEqualityLocusToBaseChartOpen i) := by
  letI :
      IsClosedImmersion
        (c.completionEqualityLocusToChartProduct i) :=
    c.isClosedImmersion_completionEqualityLocusToChartProduct i
  dsimp only [completionEqualityLocusToBaseChartOpen]
  infer_instance

/-- The equality-locus map to the unrestricted target-relative product. -/
def completionEqualityLocusToTargetRelative
    (i : c.toAffineCoverData.ι) :
    c.completionEqualityLocus i ⟶
      c.D.targetRelativeScheme :=
  pullback.lift
    (pullback.fst
      (c.projectiveCompletion i).openMap
      (c.targetClosureToProjectiveCompletion i) ≫
        c.toAffineCoverData.f i)
    (pullback.snd
      (c.projectiveCompletion i).openMap
      (c.targetClosureToProjectiveCompletion i))
    (by
      rw [Category.assoc, c.chart_toBase i]
      rw [← (c.projectiveCompletion i).openMap_toSpec]
      rw [← Category.assoc, pullback.condition]
      rw [Category.assoc,
        c.targetClosureToProjectiveCompletion_toSpec])

@[reassoc (attr := simp)]
theorem completionEqualityLocusToTargetRelative_toBase
    (i : c.toAffineCoverData.ι) :
    c.completionEqualityLocusToTargetRelative i ≫
        c.baseProjection =
      pullback.fst
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) ≫
        c.toAffineCoverData.f i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem completionEqualityLocusToTargetRelative_toTarget
    (i : c.toAffineCoverData.ι) :
    c.completionEqualityLocusToTargetRelative i ≫
        c.targetProjection =
      pullback.snd
        (c.projectiveCompletion i).openMap
        (c.targetClosureToProjectiveCompletion i) :=
  pullback.lift_snd _ _ _

/-- The closed equality-locus factor followed by the base-chart open
inclusion is its direct map to the target-relative product. -/
@[reassoc]
theorem completionEqualityLocusToBaseChartOpen_ι
    (i : c.toAffineCoverData.ι) :
    c.completionEqualityLocusToBaseChartOpen i ≫
        (c.baseChartRelativeOpen i).ι =
      c.completionEqualityLocusToTargetRelative i := by
  apply pullback.hom_ext
  · simp [completionEqualityLocusToBaseChartOpen,
      completionEqualityLocusToChartProduct,
      chartProductIsoBasePullback,
      basePullbackIsoRelativeOpen,
      baseChartRelativeOpen,
      pullback.mapDesc, pullback.map]
    rw [pullback.lift_fst_assoc,
      pullback.lift_fst_assoc]
  · simp [completionEqualityLocusToBaseChartOpen,
      completionEqualityLocusToChartProduct,
      chartProductIsoBasePullback,
      basePullbackIsoRelativeOpen,
      baseChartRelativeOpen,
      pullback.mapDesc, pullback.map]
    simp only [pullback.lift_snd]

/-- The common-domain map to the `i`-th affine chart, with its source
expressed through the rational-map package. -/
def rationalDomainToChart
    (i : c.toAffineCoverData.ι) :
    c.D.domain ⟶ Spec (c.toAffineCoverData.R i) := by
  change c.domain ⟶ Spec (c.toAffineCoverData.R i)
  exact c.domainToChart i

@[reassoc (attr := simp)]
theorem rationalDomainToChart_chartMap
    (i : c.toAffineCoverData.ι) :
    c.rationalDomainToChart i ≫
        c.toAffineCoverData.f i =
      c.D.toOriginalOpen := by
  change
    c.domainToChart i ≫
        c.toAffineCoverData.f i =
      c.domainInclusion
  exact c.domainToChart_chartMap i

/-- On the common domain, the affine-chart map and the labeled
target-closure coordinate have the same image in the completion. -/
@[reassoc]
theorem rationalDomainToChart_openMap
    (i : c.toAffineCoverData.ι) :
    c.rationalDomainToChart i ≫
        (c.projectiveCompletion i).openMap =
      c.D.toTargetClosure ≫
        c.targetClosureToProjectiveCompletion i := by
  change
    c.domainToProjectiveCompletion i =
      (c.toRationalProjectiveMapData).toTargetClosure ≫
        c.targetClosureToProjectiveCompletion i
  exact
    (c.toTargetClosure_targetClosureToProjectiveCompletion i).symm

/-- The restricted original graph maps to the equality locus. -/
def graphBaseRestrictToCompletionEqualityLocus
    (i : c.toAffineCoverData.ι) :
    (c.D.graphToTargetRelative ⁻¹ᵁ
      c.baseChartRelativeOpen i).toScheme ⟶
      c.completionEqualityLocus i :=
  pullback.lift
    ((c.D.graphToTargetRelative ⁻¹ᵁ
        c.baseChartRelativeOpen i).ι ≫
      c.rationalDomainToChart i)
    ((c.D.graphToTargetRelative ⁻¹ᵁ
        c.baseChartRelativeOpen i).ι ≫
      c.D.toTargetClosure)
    (by
      simp only [Category.assoc]
      rw [c.rationalDomainToChart_openMap])

@[reassoc (attr := simp)]
theorem graphBaseRestrictToCompletionEqualityLocus_fst
    (i : c.toAffineCoverData.ι) :
    c.graphBaseRestrictToCompletionEqualityLocus i ≫
        pullback.fst
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) =
      (c.D.graphToTargetRelative ⁻¹ᵁ
        c.baseChartRelativeOpen i).ι ≫
          c.rationalDomainToChart i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphBaseRestrictToCompletionEqualityLocus_snd
    (i : c.toAffineCoverData.ι) :
    c.graphBaseRestrictToCompletionEqualityLocus i ≫
        pullback.snd
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) =
      (c.D.graphToTargetRelative ⁻¹ᵁ
        c.baseChartRelativeOpen i).ι ≫
          c.D.toTargetClosure :=
  pullback.lift_snd _ _ _

/-- Over the `i`-th base chart, the restricted graph factors through
the closed completion equality locus. -/
theorem graphBaseRestrict_factor_completionEqualityLocus
    (i : c.toAffineCoverData.ι) :
    c.D.graphToTargetRelative ∣_
        c.baseChartRelativeOpen i =
      c.graphBaseRestrictToCompletionEqualityLocus i ≫
        c.completionEqualityLocusToBaseChartOpen i := by
  apply
    (cancel_mono
      (c.baseChartRelativeOpen i).ι).mp
  rw [Category.assoc,
    c.completionEqualityLocusToBaseChartOpen_ι,
    morphismRestrict_ι]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [c.graphToTargetRelative_toBase,
      c.completionEqualityLocusToTargetRelative_toBase,
      c.graphBaseRestrictToCompletionEqualityLocus_fst_assoc,
      c.rationalDomainToChart_chartMap]
  · simp only [Category.assoc]
    rw [c.graphToTargetRelative_toTarget,
      c.completionEqualityLocusToTargetRelative_toTarget,
      c.graphBaseRestrictToCompletionEqualityLocus_snd]

/-- The local scheme-theoretic graph image maps canonically to the
closed completion equality locus. -/
def baseChartImageToCompletionEqualityLocus
    (i : c.toAffineCoverData.ι) :
    targetOpenImage
        c.D.graphToTargetRelative
        c.baseProjection
        (c.toAffineCoverData.f i).opensRange ⟶
      c.completionEqualityLocus i := by
  letI :
      IsClosedImmersion
        (c.completionEqualityLocusToBaseChartOpen i) :=
    c.isClosedImmersion_completionEqualityLocusToBaseChartOpen i
  exact
    SchemeTheoreticImage.toClosedFactor
      (c.D.graphToTargetRelative ∣_
        c.baseChartRelativeOpen i)
      (c.graphBaseRestrictToCompletionEqualityLocus i)
      (c.completionEqualityLocusToBaseChartOpen i)
      (c.graphBaseRestrict_factor_completionEqualityLocus i)

/-- The local image-to-equality-locus map recovers the closed
immersion of the local scheme-theoretic image. -/
@[reassoc]
theorem baseChartImageToCompletionEqualityLocus_factor
    (i : c.toAffineCoverData.ι) :
    c.baseChartImageToCompletionEqualityLocus i ≫
        c.completionEqualityLocusToBaseChartOpen i =
      (c.D.graphToTargetRelative ∣_
        c.baseChartRelativeOpen i).imageι := by
  letI :
      IsClosedImmersion
        (c.completionEqualityLocusToBaseChartOpen i) :=
    c.isClosedImmersion_completionEqualityLocusToBaseChartOpen i
  unfold baseChartImageToCompletionEqualityLocus
  rw [SchemeTheoreticImage.toClosedFactor_comp]

/-- Map the base-chart restriction of the smaller global graph image
to the completion equality locus. -/
def targetGraphImageBaseRestrictionToCompletionEqualityLocus
    (i : c.toAffineCoverData.ι) :
    ((c.D.graphToTargetRelative.imageι ≫
      c.baseProjection) ⁻¹ᵁ
        (c.toAffineCoverData.f i).opensRange).toScheme ⟶
      c.completionEqualityLocus i := by
  letI :
      QuasiCompact c.D.graphToTargetRelative :=
    c.quasiCompact_graphToTargetRelative
  exact
    (targetOpenImageIsoImageRestriction
        c.D.graphToTargetRelative
        c.baseProjection
        (c.toAffineCoverData.f i).opensRange).inv ≫
      c.baseChartImageToCompletionEqualityLocus i

/-- The target coordinate of the equality-locus factor is the target
projection of the smaller graph image. -/
@[reassoc]
theorem targetGraphImageBaseRestrictionToCompletionEqualityLocus_snd
    (i : c.toAffineCoverData.ι) :
    c.targetGraphImageBaseRestrictionToCompletionEqualityLocus i ≫
        pullback.snd
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) =
      ((c.D.graphToTargetRelative.imageι ≫
          c.baseProjection) ⁻¹ᵁ
        (c.toAffineCoverData.f i).opensRange).ι ≫
          c.D.graphToTargetRelative.imageι ≫
            c.targetProjection := by
  letI :
      QuasiCompact c.D.graphToTargetRelative :=
    c.quasiCompact_graphToTargetRelative
  let imageIso :=
    targetOpenImageIsoImageRestriction
      c.D.graphToTargetRelative
      c.baseProjection
      (c.toAffineCoverData.f i).opensRange
  have hinv :
      imageIso.inv ≫
            (c.D.graphToTargetRelative ∣_
              c.baseChartRelativeOpen i).imageι ≫
          (c.baseChartRelativeOpen i).ι =
        ((c.D.graphToTargetRelative.imageι ≫
            c.baseProjection) ⁻¹ᵁ
          (c.toAffineCoverData.f i).opensRange).ι ≫
            c.D.graphToTargetRelative.imageι := by
    calc
      imageIso.inv ≫
            (c.D.graphToTargetRelative ∣_
              c.baseChartRelativeOpen i).imageι ≫
          (c.baseChartRelativeOpen i).ι =
        imageIso.inv ≫
          (imageIso.hom ≫
            ((c.D.graphToTargetRelative.imageι ≫
                c.baseProjection) ⁻¹ᵁ
              (c.toAffineCoverData.f i).opensRange).ι ≫
              c.D.graphToTargetRelative.imageι) := by
                rw [
                  targetOpenImageIsoImageRestriction_hom_toAmbient]
      _ =
        ((c.D.graphToTargetRelative.imageι ≫
            c.baseProjection) ⁻¹ᵁ
          (c.toAffineCoverData.f i).opensRange).ι ≫
            c.D.graphToTargetRelative.imageι := by
              rw [Iso.inv_hom_id_assoc]
  calc
    c.targetGraphImageBaseRestrictionToCompletionEqualityLocus i ≫
          pullback.snd
            (c.projectiveCompletion i).openMap
            (c.targetClosureToProjectiveCompletion i) =
      c.targetGraphImageBaseRestrictionToCompletionEqualityLocus i ≫
        (c.completionEqualityLocusToTargetRelative i ≫
          c.targetProjection) := by
            rw [c.completionEqualityLocusToTargetRelative_toTarget]
    _ =
      c.targetGraphImageBaseRestrictionToCompletionEqualityLocus i ≫
        (c.completionEqualityLocusToBaseChartOpen i ≫
          (c.baseChartRelativeOpen i).ι) ≫
            c.targetProjection := by
              rw [c.completionEqualityLocusToBaseChartOpen_ι]
    _ =
      imageIso.inv ≫
          (c.D.graphToTargetRelative ∣_
            c.baseChartRelativeOpen i).imageι ≫
            (c.baseChartRelativeOpen i).ι ≫
              c.targetProjection := by
                simp only [
                  targetGraphImageBaseRestrictionToCompletionEqualityLocus,
                  Category.assoc]
                rw [c.baseChartImageToCompletionEqualityLocus_factor_assoc]
    _ =
      ((c.D.graphToTargetRelative.imageι ≫
          c.baseProjection) ⁻¹ᵁ
        (c.toAffineCoverData.f i).opensRange).ι ≫
          c.D.graphToTargetRelative.imageι ≫
            c.targetProjection := by
              simpa only [Category.assoc] using
                congrArg
                  (fun q => q ≫ c.targetProjection)
                  hinv

/-- Over the `i`-th base chart, the smaller graph-image target lies in
the `i`-th completion interior. -/
theorem targetGraphImage_baseChart_preimage_le_completionInterior
    (i : c.toAffineCoverData.ι) :
    (c.D.graphToTargetRelative.imageι ≫
        c.baseProjection) ⁻¹ᵁ
        (c.toAffineCoverData.f i).opensRange ≤
      (c.D.graphToTargetRelative.imageι ≫
        c.targetProjection) ⁻¹ᵁ
        c.targetCompletionInterior i := by
  intro z hz
  let z' :
      ((c.D.graphToTargetRelative.imageι ≫
        c.baseProjection) ⁻¹ᵁ
          (c.toAffineCoverData.f i).opensRange).toScheme :=
    ⟨z, hz⟩
  let e : c.completionEqualityLocus i :=
    c.targetGraphImageBaseRestrictionToCompletionEqualityLocus i z'
  change
    c.targetClosureToProjectiveCompletion i
        ((c.D.graphToTargetRelative.imageι ≫
          c.targetProjection) z) ∈
      (c.projectiveCompletion i).openMap.opensRange
  apply (Scheme.Hom.mem_opensRange).2
  refine
    ⟨pullback.fst
        (c.projectiveCompletion i).openMap
        (c.targetClosureToProjectiveCompletion i) e, ?_⟩
  have he :
      pullback.snd
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) e =
        (c.D.graphToTargetRelative.imageι ≫
          c.targetProjection) z := by
    have h :=
      congrArg
        (fun q => q.base z')
        (c.targetGraphImageBaseRestrictionToCompletionEqualityLocus_snd i)
    change
      pullback.snd
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) e =
        (c.D.graphToTargetRelative.imageι ≫
          c.targetProjection) z at h
    exact h
  calc
    (c.projectiveCompletion i).openMap
        (pullback.fst
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) e) =
      c.targetClosureToProjectiveCompletion i
        (pullback.snd
          (c.projectiveCompletion i).openMap
          (c.targetClosureToProjectiveCompletion i) e) := by
            change
              (pullback.fst
                  (c.projectiveCompletion i).openMap
                  (c.targetClosureToProjectiveCompletion i) ≫
                (c.projectiveCompletion i).openMap) e =
              (pullback.snd
                  (c.projectiveCompletion i).openMap
                  (c.targetClosureToProjectiveCompletion i) ≫
                c.targetClosureToProjectiveCompletion i) e
            rw [pullback.condition]
    _ =
      c.targetClosureToProjectiveCompletion i
        ((c.D.graphToTargetRelative.imageι ≫
          c.targetProjection) z) := by rw [he]

/-- The completion interiors cover the range of the target projection
from the smaller graph image. -/
theorem targetGraphImageProjection_range_subset_completionInteriors :
    Set.range
        (c.D.graphToTargetRelative.imageι ≫
          c.targetProjection) ⊆
      (⨆ i, c.targetCompletionInterior i :
        c.D.targetClosure.Opens) := by
  apply
    range_subset_iSup_of_preimage_le
      (c.D.graphToTargetRelative.imageι ≫
        c.baseProjection)
      (c.D.graphToTargetRelative.imageι ≫
        c.targetProjection)
      (fun i => (c.toAffineCoverData.f i).opensRange)
      (fun i => c.targetCompletionInterior i)
  · exact c.toAffineCoverData.toOpenCover.iSup_opensRange
  · exact
      c.targetGraphImage_baseChart_preimage_le_completionInterior

/-- The same completion interiors cover the range of the original Chow
graph-closure projection. -/
theorem graphClosureToTargetClosure_range_subset_completionInteriors :
    Set.range c.D.graphClosureToTargetClosure ⊆
      (⨆ i, c.targetCompletionInterior i :
        c.D.targetClosure.Opens) := by
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  apply c.targetGraphImageProjection_range_subset_completionInteriors
  refine
    ⟨c.D.graphClosureIsoTargetGraphImage.hom z, ?_⟩
  have h :=
    congrArg
      (fun q => q.base z)
      c.D.graphClosureIsoTargetGraphImage_hom_target
  simpa only [Scheme.Hom.comp_apply] using h

/-- The graph-closure projection to the target closure is a
monomorphism. -/
theorem mono_graphClosureToTargetClosure
    [IsSeparated f] :
    Mono c.D.graphClosureToTargetClosure :=
  mono_of_targetOpens_cover_range
    c.D.graphClosureToTargetClosure
    (fun i => c.targetCompletionInterior i)
    c.graphClosureToTargetClosure_range_subset_completionInteriors
    c.mono_graphClosureToTargetClosure_restrict

/-- For a proper original scheme, the second projection of the
canonical Chow graph closure is a monomorphism. -/
theorem mono_graphClosureToProjective
    [IsProper f] :
    Mono
      (projectiveGraphClosureToProjective
        f c.D.dimension c.D.toOriginalOpen
          c.D.toProjective c.D.overBase) := by
  apply
    c.D.mono_graphClosureToProjective_iff_targetClosure.mpr
  exact c.mono_graphClosureToTargetClosure

end CommonDenseRelativeAffineCoverData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
