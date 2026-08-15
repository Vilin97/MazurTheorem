/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowTargetCompletionInteriors
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowTargetGraphImage
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeImageTargetOpenFactor

/-!
# Closed local graphs over completion interiors

On a completion-interior open of the target closure, the labeled
completion coordinate supplies a morphism back to the corresponding
affine chart of the original scheme.  Its graph is closed because the
original structural morphism is separated.  Scheme-theoretic image
restriction then makes the target projection of the Chow graph image a
closed immersion over every such open.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

namespace CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    [IsLocallyNoetherian X]
    (c : CommonDenseRelativeAffineCoverData k f)

private abbrev D :
    ChowRationalProjectiveMapData f :=
  c.toRationalProjectiveMapData

private abbrev targetProjection :
    c.D.targetRelativeScheme ⟶ c.D.targetClosure :=
  pullback.snd f c.D.targetClosureToSpec

@[reassoc (attr := simp)]
private theorem graphToTargetRelative_toOriginal :
    c.D.graphToTargetRelative ≫
        pullback.fst f c.D.targetClosureToSpec =
      c.D.toOriginalOpen :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem graphToTargetRelative_toTarget :
    c.D.graphToTargetRelative ≫
        c.targetProjection =
      c.D.toTargetClosure :=
  pullback.lift_snd _ _ _

/-- The graph into the target-relative product is quasi-compact. -/
theorem quasiCompact_graphToTargetRelative :
    QuasiCompact c.D.graphToTargetRelative := by
  haveI : QuasiCompact c.D.toOriginalOpen :=
    c.D.quasiCompact_toOriginalOpen
  letI : IsProper c.D.targetClosureToSpec :=
    c.D.targetClosure_projective.isProper
  letI :
      IsProper
        (pullback.fst f c.D.targetClosureToSpec) :=
    inferInstance
  haveI :
      QuasiCompact
        (c.D.graphToTargetRelative ≫
          pullback.fst f c.D.targetClosureToSpec) := by
    rw [show
      c.D.graphToTargetRelative ≫
          pullback.fst f c.D.targetClosureToSpec =
        c.D.toOriginalOpen by
          exact pullback.lift_fst _ _ _]
    infer_instance
  exact
    QuasiCompact.of_comp
      c.D.graphToTargetRelative
      (pullback.fst f c.D.targetClosureToSpec)

/-- The graph of the local inverse inside
`X × c.D.targetClosure`. -/
def completionInteriorGraph
    (i : c.toAffineCoverData.ι) :
    (c.targetCompletionInterior i).toScheme ⟶
      c.D.targetRelativeScheme :=
  pullback.lift
    (c.targetCompletionInteriorToOriginal i)
    (c.targetCompletionInterior i).ι
    (c.targetCompletionInteriorToOriginal_toBase i)

@[reassoc (attr := simp)]
theorem completionInteriorGraph_toOriginal
    (i : c.toAffineCoverData.ι) :
    c.completionInteriorGraph i ≫
        pullback.fst f c.D.targetClosureToSpec =
      c.targetCompletionInteriorToOriginal i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem completionInteriorGraph_toTarget
    (i : c.toAffineCoverData.ι) :
    c.completionInteriorGraph i ≫
        c.targetProjection =
      (c.targetCompletionInterior i).ι :=
  pullback.lift_snd _ _ _

/-- The target-relative open over a completion interior, represented as
a pullback of its open immersion. -/
abbrev completionInteriorRelativePullback
    (i : c.toAffineCoverData.ι) :
    Scheme.{u} :=
  pullback
    (c.targetCompletionInterior i).ι
    c.targetProjection

/-- The local graph lifted to the pullback model of the target-relative
open. -/
def completionInteriorPullbackGraph
    (i : c.toAffineCoverData.ι) :
    (c.targetCompletionInterior i).toScheme ⟶
      c.completionInteriorRelativePullback i :=
  pullback.lift
      (𝟙 _)
      (c.completionInteriorGraph i)
      (Category.id_comp _) ≫
    (pullback.congrHom
      (c.completionInteriorGraph_toTarget i)
      rfl).hom

/-- The pullback model of the target-relative open is canonically the
usual open restriction. -/
def completionInteriorRelativePullbackIso
    {i : c.toAffineCoverData.ι} :
    c.completionInteriorRelativePullback i ≅
      (c.targetProjection ⁻¹ᵁ
        c.targetCompletionInterior i).toScheme :=
  pullbackSymmetry
      (c.targetCompletionInterior i).ι
      c.targetProjection ≪≫
    pullbackRestrictIsoRestrict
      c.targetProjection
      (c.targetCompletionInterior i)

/-- The local graph as a morphism to the target-relative open. -/
def completionInteriorGraphToRelativeOpen
    (i : c.toAffineCoverData.ι) :
    (c.targetCompletionInterior i).toScheme ⟶
      (c.targetProjection ⁻¹ᵁ
        c.targetCompletionInterior i).toScheme :=
  c.completionInteriorPullbackGraph i ≫
    c.completionInteriorRelativePullbackIso.hom

/-- The graph-to-open map followed by the open inclusion is the
unrestricted local graph. -/
@[reassoc]
theorem completionInteriorGraphToRelativeOpen_ι
    (i : c.toAffineCoverData.ι) :
    c.completionInteriorGraphToRelativeOpen i ≫
        (c.targetProjection ⁻¹ᵁ
          c.targetCompletionInterior i).ι =
      c.completionInteriorGraph i := by
  simp [completionInteriorGraphToRelativeOpen,
    completionInteriorRelativePullbackIso,
    completionInteriorPullbackGraph]
  simp only [Category.comp_id, pullback.lift_snd]

/-- The local graph is closed inside the target-relative open. -/
theorem isClosedImmersion_completionInteriorGraphToRelativeOpen
    [IsSeparated f]
    (i : c.toAffineCoverData.ι) :
    IsClosedImmersion
      (c.completionInteriorGraphToRelativeOpen i) := by
  letI :
      IsSeparated c.targetProjection :=
    inferInstance
  letI :
      IsClosedImmersion
        (c.completionInteriorPullbackGraph i) := by
    dsimp only [completionInteriorPullbackGraph]
    infer_instance
  dsimp only [completionInteriorGraphToRelativeOpen]
  infer_instance

/-- The restricted source maps to the completion interior through its
target component. -/
def graphRestrictToCompletionInterior
    (i : c.toAffineCoverData.ι) :
    (c.D.graphToTargetRelative ⁻¹ᵁ
      (c.targetProjection ⁻¹ᵁ
        c.targetCompletionInterior i)).toScheme ⟶
      (c.targetCompletionInterior i).toScheme :=
  (c.D.graphToTargetRelative ∣_
      (c.targetProjection ⁻¹ᵁ
        c.targetCompletionInterior i)) ≫
    (c.targetProjection ∣_
      c.targetCompletionInterior i)

/-- The dense-domain lift, with its source expressed through the
rational-map package.  This wrapper avoids exposing the opaque
structure construction during later categorical rewrites. -/
def rationalDomainToTargetCompletionInterior
    (i : c.toAffineCoverData.ι) :
    c.D.domain ⟶ (c.targetCompletionInterior i).toScheme := by
  change c.domain ⟶ (c.targetCompletionInterior i).toScheme
  exact c.domainToTargetCompletionInterior i

@[reassoc (attr := simp)]
theorem rationalDomainToTargetCompletionInterior_ι
    (i : c.toAffineCoverData.ι) :
    c.rationalDomainToTargetCompletionInterior i ≫
        (c.targetCompletionInterior i).ι =
      c.D.toTargetClosure := by
  change
    c.domainToTargetCompletionInterior i ≫
        (c.targetCompletionInterior i).ι =
      (c.toRationalProjectiveMapData).toTargetClosure
  exact c.domainToTargetCompletionInterior_ι i

@[reassoc]
theorem rationalDomainToTargetCompletionInterior_toOriginal
    (i : c.toAffineCoverData.ι) :
    c.rationalDomainToTargetCompletionInterior i ≫
        c.targetCompletionInteriorToOriginal i =
      c.D.toOriginalOpen := by
  change
    c.domainToTargetCompletionInterior i ≫
        c.targetCompletionInteriorToOriginal i =
      c.domainInclusion
  exact c.domainToTargetCompletionInterior_toOriginal i

/-- The target component of the restricted graph agrees with the
canonical lift of the common domain to the completion interior. -/
theorem graphRestrictToCompletionInterior_eq
    (i : c.toAffineCoverData.ι) :
    c.graphRestrictToCompletionInterior i =
      (c.D.graphToTargetRelative ⁻¹ᵁ
        (c.targetProjection ⁻¹ᵁ
          c.targetCompletionInterior i)).ι ≫
        c.rationalDomainToTargetCompletionInterior i := by
  apply
    (cancel_mono
      (c.targetCompletionInterior i).ι).mp
  let sourceOpen :=
    c.D.graphToTargetRelative ⁻¹ᵁ
      (c.targetProjection ⁻¹ᵁ
        c.targetCompletionInterior i)
  let relativeOpen :=
    c.targetProjection ⁻¹ᵁ
      c.targetCompletionInterior i
  change
    ((c.D.graphToTargetRelative ∣_ relativeOpen) ≫
        (c.targetProjection ∣_
          c.targetCompletionInterior i)) ≫
          (c.targetCompletionInterior i).ι =
      (sourceOpen.ι ≫
        c.rationalDomainToTargetCompletionInterior i) ≫
          (c.targetCompletionInterior i).ι
  calc
    ((c.D.graphToTargetRelative ∣_ relativeOpen) ≫
          (c.targetProjection ∣_
            c.targetCompletionInterior i)) ≫
        (c.targetCompletionInterior i).ι =
      (c.D.graphToTargetRelative ∣_ relativeOpen) ≫
        ((c.targetProjection ∣_
            c.targetCompletionInterior i) ≫
          (c.targetCompletionInterior i).ι) := by
            rw [Category.assoc]
    _ =
      (c.D.graphToTargetRelative ∣_ relativeOpen) ≫
        (relativeOpen.ι ≫ c.targetProjection) := by
          rw [morphismRestrict_ι]
    _ =
      ((c.D.graphToTargetRelative ∣_ relativeOpen) ≫
        relativeOpen.ι) ≫ c.targetProjection := by
          rw [Category.assoc]
    _ =
      (sourceOpen.ι ≫
        c.D.graphToTargetRelative) ≫
          c.targetProjection := by
            rw [morphismRestrict_ι]
    _ =
      sourceOpen.ι ≫
        (c.D.graphToTargetRelative ≫
          c.targetProjection) := by
            rw [Category.assoc]
    _ =
      sourceOpen.ι ≫ c.D.toTargetClosure := by
        rw [c.graphToTargetRelative_toTarget]
    _ =
      sourceOpen.ι ≫
        (c.rationalDomainToTargetCompletionInterior i ≫
          (c.targetCompletionInterior i).ι) := by
            rw [c.rationalDomainToTargetCompletionInterior_ι]
    _ =
      (sourceOpen.ι ≫
        c.rationalDomainToTargetCompletionInterior i) ≫
          (c.targetCompletionInterior i).ι := by
            rw [Category.assoc]

/-- The restricted graph factors through the closed local graph. -/
theorem graphRestrict_factor_completionInteriorGraph
    (i : c.toAffineCoverData.ι) :
    c.D.graphToTargetRelative ∣_
        (c.targetProjection ⁻¹ᵁ
          c.targetCompletionInterior i) =
      c.graphRestrictToCompletionInterior i ≫
        c.completionInteriorGraphToRelativeOpen i := by
  apply
    (cancel_mono
      (c.targetProjection ⁻¹ᵁ
        c.targetCompletionInterior i).ι).mp
  rw [Category.assoc,
    c.completionInteriorGraphToRelativeOpen_ι,
    c.graphRestrictToCompletionInterior_eq,
    morphismRestrict_ι]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [c.graphToTargetRelative_toOriginal,
      c.completionInteriorGraph_toOriginal,
      c.rationalDomainToTargetCompletionInterior_toOriginal]
  · simp only [Category.assoc]
    rw [c.graphToTargetRelative_toTarget,
      c.completionInteriorGraph_toTarget,
      c.rationalDomainToTargetCompletionInterior_ι]

/-- The local inverse graph supplies the closed factor required by
scheme-image restriction. -/
def completionInteriorClosedFactor
    [IsSeparated f]
    (i : c.toAffineCoverData.ι) :
    TargetOpenClosedFactor
      c.D.graphToTargetRelative
      c.targetProjection
      (c.targetCompletionInterior i) where
  carrier :=
    (c.targetCompletionInterior i).toScheme
  sourceToFactor :=
    c.graphRestrictToCompletionInterior i
  factorToAmbientOpen :=
    c.completionInteriorGraphToRelativeOpen i
  graphRestrict_factor :=
    c.graphRestrict_factor_completionInteriorGraph i
  isClosedImmersion_factorToAmbientOpen :=
    c.isClosedImmersion_completionInteriorGraphToRelativeOpen i
  factorToTargetOpen := 𝟙 _
  factorToAmbientOpen_toTarget := by
    apply
      (cancel_mono
        (c.targetCompletionInterior i).ι).mp
    calc
      (c.completionInteriorGraphToRelativeOpen i ≫
          (c.targetProjection ∣_
            c.targetCompletionInterior i)) ≫
          (c.targetCompletionInterior i).ι =
        c.completionInteriorGraphToRelativeOpen i ≫
          ((c.targetProjection ∣_
              c.targetCompletionInterior i) ≫
            (c.targetCompletionInterior i).ι) := by
              rw [Category.assoc]
      _ =
        c.completionInteriorGraphToRelativeOpen i ≫
          ((c.targetProjection ⁻¹ᵁ
              c.targetCompletionInterior i).ι ≫
            c.targetProjection) := by
              rw [morphismRestrict_ι]
      _ =
        (c.completionInteriorGraphToRelativeOpen i ≫
          (c.targetProjection ⁻¹ᵁ
            c.targetCompletionInterior i).ι) ≫
              c.targetProjection := by
                rw [Category.assoc]
      _ =
        c.completionInteriorGraph i ≫
          c.targetProjection := by
            rw [c.completionInteriorGraphToRelativeOpen_ι]
      _ = (c.targetCompletionInterior i).ι := by
        rw [c.completionInteriorGraph_toTarget]
      _ =
        (𝟙 (c.targetCompletionInterior i).toScheme) ≫
          (c.targetCompletionInterior i).ι := by
            rw [Category.id_comp]
  isClosedImmersion_factorToTargetOpen := inferInstance

/-- The target projection of the smaller Chow graph image is closed
over each completion-interior open. -/
theorem isClosedImmersion_targetGraphImageProjection_restrict
    [IsSeparated f]
    (i : c.toAffineCoverData.ι) :
    IsClosedImmersion
      ((c.D.graphToTargetRelative.imageι ≫
        c.targetProjection) ∣_
          c.targetCompletionInterior i) := by
  letI :
      QuasiCompact c.D.graphToTargetRelative :=
    c.quasiCompact_graphToTargetRelative
  exact
    (c.completionInteriorClosedFactor i).isClosedImmersion_imageProjection_restrict

/-- Transporting across the canonical graph-image isomorphism, the
original graph-closure projection is also closed over every completion
interior. -/
theorem isClosedImmersion_graphClosureToTargetClosure_restrict
    [IsSeparated f]
    (i : c.toAffineCoverData.ι) :
    IsClosedImmersion
      (c.D.graphClosureToTargetClosure ∣_
        c.targetCompletionInterior i) := by
  let smallerProjection :=
    c.D.graphToTargetRelative.imageι ≫
      c.targetProjection
  letI :
      IsClosedImmersion
        (smallerProjection ∣_
          c.targetCompletionInterior i) :=
    c.isClosedImmersion_targetGraphImageProjection_restrict i
  letI :
      IsClosedImmersion
        c.D.graphClosureIsoTargetGraphImage.hom := by
    infer_instance
  letI :
      IsClosedImmersion
        (c.D.graphClosureIsoTargetGraphImage.hom ∣_
          smallerProjection ⁻¹ᵁ
            c.targetCompletionInterior i) := by
    infer_instance
  rw [← c.D.graphClosureIsoTargetGraphImage_hom_target]
  rw [morphismRestrict_comp]
  change
    IsClosedImmersion
      ((c.D.graphClosureIsoTargetGraphImage.hom ∣_
          smallerProjection ⁻¹ᵁ
            c.targetCompletionInterior i) ≫
        (smallerProjection ∣_
          c.targetCompletionInterior i))
  exact IsClosedImmersion.comp _ _

/-- In particular, every completion-interior restriction of the Chow
graph projection is a monomorphism. -/
theorem mono_graphClosureToTargetClosure_restrict
    [IsSeparated f]
    (i : c.toAffineCoverData.ι) :
    Mono
      (c.D.graphClosureToTargetClosure ∣_
        c.targetCompletionInterior i) := by
  letI :
      IsClosedImmersion
        (c.D.graphClosureToTargetClosure ∣_
          c.targetCompletionInterior i) :=
    c.isClosedImmersion_graphClosureToTargetClosure_restrict i
  infer_instance

end CommonDenseRelativeAffineCoverData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
