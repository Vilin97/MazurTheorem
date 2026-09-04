/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductMixedAdditionCovers
import MazurTorsion.ModularCurve.XZeroWeierstrassStandardPairAdditionCompatibility

/-!
# Compatibility and gluing on the mixed projective-pair charts

On either mixed input chart, the transition-to-standard member and the secant
output-`Z` member meet in the already constructed exact input/output
localization.  This file identifies that localization with the categorical
pullback of the two cover maps and transports the checked equality of
normalized secant formulas to the `Scheme.OpenCover` compatibility condition.

The design boundary is the pair of genuine glued morphisms
`projectivePairStandardInfinityAdditionMorphism` and
`projectivePairInfinityStandardAdditionMorphism`.  Their named restriction
theorems are the downstream interface for compatibility across the four-chart
projective product atlas.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem mixedPullback_morphism_compatible_self
    {U X Y : Scheme.{u}} (i : U ⟶ X) [Mono i] (f : U ⟶ Y) :
    pullback.fst i i ≫ f = pullback.snd i i ≫ f := by
  have hfst : pullback.fst i i = pullback.snd i i := by
    apply (cancel_mono i).mp
    exact pullback.condition
  exact congrArg (fun q => q ≫ f) hfst

private theorem mixedPullback_morphism_compatible_symm
    {U V X Y : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X)
    (f : U ⟶ Y) (g : V ⟶ Y)
    (h : pullback.fst i j ≫ f = pullback.snd i j ≫ g) :
    pullback.fst j i ≫ g = pullback.snd j i ≫ f := by
  apply (cancel_epi (pullbackSymmetry i j).hom).mp
  calc
    _ = ((pullbackSymmetry i j).hom ≫ pullback.fst j i) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = pullback.snd i j ≫ g := congrArg (fun q => q ≫ g)
      (pullbackSymmetry_hom_comp_fst i j)
    _ = pullback.fst i j ≫ f := h.symm
    _ = ((pullbackSymmetry i j).hom ≫ pullback.snd j i) ≫ f :=
      congrArg (fun q => q ≫ f) (pullbackSymmetry_hom_comp_snd i j).symm
    _ = _ := Category.assoc _ _ _

/-! ## Standard-by-infinity compatibility -/

/-- The intrinsic second-input/output localization has the expected principal
open range inside the second-input overlap. -/
theorem projectivePairSecondOverlapAdditionOutputOpen_opensRange
    (W : WeierstrassCurve K) (i out : Bool) :
    (projectivePairSecondOverlapAdditionOutputOpen W i out).opensRange =
      PrimeSpectrum.basicOpen
        (infinityPairToSecondChartOverlapAlgHom W i
          (projectivePairChartAdditionCoordinates W (i, false)
            (coveringCoordinate out))) := by
  dsimp only [projectivePairSecondOverlapAdditionOutputOpen,
    projectivePairSecondOverlapAdditionOutputRing]
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (projectivePairSecondChartOverlapCoordinateRing W i))
    (infinityPairToSecondChartOverlapAlgHom W i
      (projectivePairChartAdditionCoordinates W (i, false)
        (coveringCoordinate out)))

/-- Pulling the mixed secant-`Z` range back to the transition source gives
exactly the intrinsic common input/output localization. -/
theorem projectivePairStandardInfinityTransition_preimage_secantZ
    (W : WeierstrassCurve K) :
    projectivePairSecondOverlapToInfinityPair W true ⁻¹ᵁ
        (projectivePairChartAdditionOutputOpen W
          (true, false) true).opensRange =
      (projectivePairSecondOverlapAdditionOutputOpen W
        true true).opensRange := by
  let e := projectivePairChartIsoSpecTensor W (true, false)
  have hsecant :
      e.hom ⁻¹ᵁ
          (projectivePairStandardInfinitySecantZOpenAffine W).opensRange =
        (projectivePairChartAdditionOutputOpen W
          (true, false) true).opensRange := by
    dsimp [e, projectivePairStandardInfinitySecantZOpenAffine]
    rw [
      Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq]
  have haffine :
      (projectivePairStandardInfinityTransitionOpenAffine W) ⁻¹ᵁ
          (projectivePairStandardInfinitySecantZOpenAffine W).opensRange =
        (projectivePairSecondOverlapAdditionOutputOpen W
          true true).opensRange := by
    rw [projectivePairStandardInfinitySecantZOpenAffine_opensRange]
    simp only [projectivePairStandardInfinityTransitionOpenAffine,
      projectivePairSecondOverlapToInfinityPair, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [projectivePairSecondOverlapAdditionOutputOpen_opensRange]
    rfl
  calc
    projectivePairSecondOverlapToInfinityPair W true ⁻¹ᵁ
          (projectivePairChartAdditionOutputOpen W
            (true, false) true).opensRange =
        projectivePairSecondOverlapToInfinityPair W true ⁻¹ᵁ
          (e.hom ⁻¹ᵁ
            (projectivePairStandardInfinitySecantZOpenAffine W).opensRange) := by
              rw [hsecant]
    _ = (projectivePairStandardInfinityTransitionOpenAffine W) ⁻¹ᵁ
          (projectivePairStandardInfinitySecantZOpenAffine W).opensRange := by
            rfl
    _ = (projectivePairSecondOverlapAdditionOutputOpen W
          true true).opensRange := haffine

/-- The explicit second-input/output localization is a pullback of the two
standard-by-infinity cover members. -/
theorem projectivePairStandardInfinityTransitionSecantZ_isPullback
    (W : WeierstrassCurve K) :
    IsPullback
      (projectivePairSecondOverlapAdditionOutputToInfinity W true true)
      (projectivePairSecondOverlapAdditionOutputOpen W true true)
      (projectivePairChartAdditionOutputOpen W (true, false) true)
      (projectivePairSecondOverlapToInfinityPair W true) := by
  apply IsOpenImmersion.isPullback
  · exact
      (projectivePairSecondOverlapAdditionOutput_infinityOpen_eq
        W true true).symm
  · exact projectivePairStandardInfinityTransition_preimage_secantZ W

/-- On the explicit common localization, the transported standard-pair law
equals the mixed normalized secant law. -/
theorem projectivePairStandardInfinityTransitionSecantZ_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairSecondOverlapAdditionOutputOpen W true true ≫
        projectivePairSecondOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W =
      projectivePairSecondOverlapAdditionOutputToInfinity W true true ≫
        projectivePairChartAdditionOutputMorphism W
          (true, false) true := by
  calc
    _ = (projectivePairSecondOverlapAdditionOutputToStandard W true true ≫
          projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        standardPairAdditionMorphism W := by
          rw [projectivePairSecondOverlapAdditionOutput_standardOpen_eq,
            Category.assoc]
    _ = projectivePairSecondOverlapAdditionOutputToStandard W true true ≫
        (projectivePairChartAdditionOutputOpen W (true, true) true ≫
          standardPairAdditionMorphism W) := Category.assoc _ _ _
    _ = projectivePairSecondOverlapAdditionOutputToStandard W true true ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) true := by
          rw [projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism]
    _ = _ := projectivePairSecondOverlapAdditionOutput_morphisms_eq
      W true true

/-- The two local laws agree on the categorical pullback of the
standard-by-infinity cover members. -/
theorem projectivePairStandardInfinityTransitionSecantZ_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairSecondOverlapToInfinityPair W true)
          (projectivePairChartAdditionOutputOpen W (true, false) true) ≫
        (projectivePairSecondOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) =
      pullback.snd
          (projectivePairSecondOverlapToInfinityPair W true)
          (projectivePairChartAdditionOutputOpen W (true, false) true) ≫
        projectivePairChartAdditionOutputMorphism W
          (true, false) true := by
  apply mixedPullback_morphism_compatible_symm
  let h := projectivePairStandardInfinityTransitionSecantZ_isPullback W
  let hcanonical := IsPullback.of_hasPullback
    (projectivePairChartAdditionOutputOpen W (true, false) true)
    (projectivePairSecondOverlapToInfinityPair W true)
  let e := h.isoIsPullback _ _ hcanonical
  apply (cancel_epi e.hom).mp
  calc
    _ = (projectivePairSecondOverlapAdditionOutputToInfinity W true true) ≫
        projectivePairChartAdditionOutputMorphism W
          (true, false) true := by
          rw [← Category.assoc, h.isoIsPullback_hom_fst _ _ hcanonical]
    _ = projectivePairSecondOverlapAdditionOutputOpen W true true ≫
        (projectivePairSecondOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) := by
          rw [← Category.assoc]
          exact (projectivePairStandardInfinityTransitionSecantZ_morphisms_eq W).symm
    _ = (e.hom ≫
          pullback.snd
            (projectivePairChartAdditionOutputOpen W (true, false) true)
            (projectivePairSecondOverlapToInfinityPair W true)) ≫
        (projectivePairSecondOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) := by
            exact congrArg
              (fun q => q ≫
                (projectivePairSecondOverlapToStandardPair W true ≫
                  standardPairAdditionMorphism W))
              (h.isoIsPullback_hom_snd _ _ hcanonical).symm
    _ = _ := Category.assoc _ _ _

/-- The indexed standard-by-infinity local laws satisfy the open-cover
compatibility condition. -/
theorem projectivePairStandardInfinityAdditionCoverMorphism_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : ProjectiveMixedPairAdditionCoverIndex) :
    pullback.fst
          (projectivePairStandardInfinityAdditionCoverMap W i)
          (projectivePairStandardInfinityAdditionCoverMap W j) ≫
        projectivePairStandardInfinityAdditionCoverMorphism W i =
      pullback.snd
          (projectivePairStandardInfinityAdditionCoverMap W i)
          (projectivePairStandardInfinityAdditionCoverMap W j) ≫
        projectivePairStandardInfinityAdditionCoverMorphism W j := by
  cases i <;> cases j
  · exact mixedPullback_morphism_compatible_self _ _
  · exact projectivePairStandardInfinityTransitionSecantZ_compatible W
  · exact mixedPullback_morphism_compatible_symm _ _ _ _
      (projectivePairStandardInfinityTransitionSecantZ_compatible W)
  · exact mixedPullback_morphism_compatible_self _ _

private theorem projectivePairStandardInfinityAdditionOpenCover_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : (projectivePairStandardInfinityAdditionOpenCover W).I₀) :
    pullback.fst
          ((projectivePairStandardInfinityAdditionOpenCover W).f i)
          ((projectivePairStandardInfinityAdditionOpenCover W).f j) ≫
        projectivePairStandardInfinityAdditionCoverMorphism W i =
      pullback.snd
          ((projectivePairStandardInfinityAdditionOpenCover W).f i)
          ((projectivePairStandardInfinityAdditionOpenCover W).f j) ≫
        projectivePairStandardInfinityAdditionCoverMorphism W j := by
  exact projectivePairStandardInfinityAdditionCoverMorphism_compatible W i j

/-- The actual addition morphism on the entire standard-by-infinity chart. -/
noncomputable def projectivePairStandardInfinityAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartScheme W (true, false) ⟶ scheme W :=
  (projectivePairStandardInfinityAdditionOpenCover W).glueMorphisms
    (projectivePairStandardInfinityAdditionCoverMorphism W)
    (projectivePairStandardInfinityAdditionOpenCover_compatible W)

/-- The glued standard-by-infinity law restricts to the transported
standard-pair law on the transition member. -/
@[reassoc]
theorem projectivePairSecondOverlapToInfinityPair_comp_standardInfinityAddition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairSecondOverlapToInfinityPair W true ≫
        projectivePairStandardInfinityAdditionMorphism W =
      projectivePairSecondOverlapToStandardPair W true ≫
        standardPairAdditionMorphism W := by
  exact (projectivePairStandardInfinityAdditionOpenCover W).ι_glueMorphisms
    (projectivePairStandardInfinityAdditionCoverMorphism W)
    (projectivePairStandardInfinityAdditionOpenCover_compatible W)
    .transition

/-- The glued standard-by-infinity law restricts to the normalized secant law
on the output-`Z` member. -/
@[reassoc]
theorem projectivePairStandardInfinitySecantZOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionOutputOpen W (true, false) true ≫
        projectivePairStandardInfinityAdditionMorphism W =
      projectivePairChartAdditionOutputMorphism W (true, false) true := by
  exact (projectivePairStandardInfinityAdditionOpenCover W).ι_glueMorphisms
    (projectivePairStandardInfinityAdditionCoverMorphism W)
    (projectivePairStandardInfinityAdditionOpenCover_compatible W)
    .secantZ

/-! ## Infinity-by-standard compatibility -/

/-- The intrinsic first-input/output localization has the expected principal
open range inside the first-input overlap. -/
theorem projectivePairFirstOverlapAdditionOutputOpen_opensRange
    (W : WeierstrassCurve K) (j out : Bool) :
    (projectivePairFirstOverlapAdditionOutputOpen W j out).opensRange =
      PrimeSpectrum.basicOpen
        (infinityPairToFirstChartOverlapAlgHom W j
          (projectivePairChartAdditionCoordinates W (false, j)
            (coveringCoordinate out))) := by
  dsimp only [projectivePairFirstOverlapAdditionOutputOpen,
    projectivePairFirstOverlapAdditionOutputRing]
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (projectivePairFirstChartOverlapCoordinateRing W j))
    (infinityPairToFirstChartOverlapAlgHom W j
      (projectivePairChartAdditionCoordinates W (false, j)
        (coveringCoordinate out)))

/-- Pulling the mixed secant-`Z` range back to the transition source gives
exactly the intrinsic common first-input/output localization. -/
theorem projectivePairInfinityStandardTransition_preimage_secantZ
    (W : WeierstrassCurve K) :
    projectivePairFirstOverlapToInfinityPair W true ⁻¹ᵁ
        (projectivePairChartAdditionOutputOpen W
          (false, true) true).opensRange =
      (projectivePairFirstOverlapAdditionOutputOpen W
        true true).opensRange := by
  let e := projectivePairChartIsoSpecTensor W (false, true)
  have hsecant :
      e.hom ⁻¹ᵁ
          (projectivePairInfinityStandardSecantZOpenAffine W).opensRange =
        (projectivePairChartAdditionOutputOpen W
          (false, true) true).opensRange := by
    dsimp [e, projectivePairInfinityStandardSecantZOpenAffine]
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq]
  have haffine :
      (projectivePairInfinityStandardTransitionOpenAffine W) ⁻¹ᵁ
          (projectivePairInfinityStandardSecantZOpenAffine W).opensRange =
        (projectivePairFirstOverlapAdditionOutputOpen W
          true true).opensRange := by
    rw [projectivePairInfinityStandardSecantZOpenAffine_opensRange]
    simp only [projectivePairInfinityStandardTransitionOpenAffine,
      projectivePairFirstOverlapToInfinityPair, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [projectivePairFirstOverlapAdditionOutputOpen_opensRange]
    rfl
  calc
    projectivePairFirstOverlapToInfinityPair W true ⁻¹ᵁ
          (projectivePairChartAdditionOutputOpen W
            (false, true) true).opensRange =
        projectivePairFirstOverlapToInfinityPair W true ⁻¹ᵁ
          (e.hom ⁻¹ᵁ
            (projectivePairInfinityStandardSecantZOpenAffine W).opensRange) := by
              rw [hsecant]
    _ = (projectivePairInfinityStandardTransitionOpenAffine W) ⁻¹ᵁ
          (projectivePairInfinityStandardSecantZOpenAffine W).opensRange := by
            rfl
    _ = (projectivePairFirstOverlapAdditionOutputOpen W
          true true).opensRange := haffine

/-- The explicit first-input/output localization is a pullback of the two
infinity-by-standard cover members. -/
theorem projectivePairInfinityStandardTransitionSecantZ_isPullback
    (W : WeierstrassCurve K) :
    IsPullback
      (projectivePairFirstOverlapAdditionOutputToInfinity W true true)
      (projectivePairFirstOverlapAdditionOutputOpen W true true)
      (projectivePairChartAdditionOutputOpen W (false, true) true)
      (projectivePairFirstOverlapToInfinityPair W true) := by
  apply IsOpenImmersion.isPullback
  · exact
      (projectivePairFirstOverlapAdditionOutput_infinityOpen_eq
        W true true).symm
  · exact projectivePairInfinityStandardTransition_preimage_secantZ W

/-- On the explicit common localization, the transported standard-pair law
equals the mixed normalized secant law. -/
theorem projectivePairInfinityStandardTransitionSecantZ_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairFirstOverlapAdditionOutputOpen W true true ≫
        projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W =
      projectivePairFirstOverlapAdditionOutputToInfinity W true true ≫
        projectivePairChartAdditionOutputMorphism W
          (false, true) true := by
  calc
    _ = (projectivePairFirstOverlapAdditionOutputToStandard W true true ≫
          projectivePairChartAdditionOutputOpen W (true, true) true) ≫
        standardPairAdditionMorphism W := by
          rw [projectivePairFirstOverlapAdditionOutput_standardOpen_eq,
            Category.assoc]
    _ = projectivePairFirstOverlapAdditionOutputToStandard W true true ≫
        (projectivePairChartAdditionOutputOpen W (true, true) true ≫
          standardPairAdditionMorphism W) := Category.assoc _ _ _
    _ = projectivePairFirstOverlapAdditionOutputToStandard W true true ≫
        projectivePairChartAdditionOutputMorphism W
          (true, true) true := by
          rw [projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism]
    _ = _ := projectivePairFirstOverlapAdditionOutput_morphisms_eq
      W true true

/-- The two local laws agree on the categorical pullback of the
infinity-by-standard cover members. -/
theorem projectivePairInfinityStandardTransitionSecantZ_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairFirstOverlapToInfinityPair W true)
          (projectivePairChartAdditionOutputOpen W (false, true) true) ≫
        (projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) =
      pullback.snd
          (projectivePairFirstOverlapToInfinityPair W true)
          (projectivePairChartAdditionOutputOpen W (false, true) true) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, true) true := by
  apply mixedPullback_morphism_compatible_symm
  let h := projectivePairInfinityStandardTransitionSecantZ_isPullback W
  let hcanonical := IsPullback.of_hasPullback
    (projectivePairChartAdditionOutputOpen W (false, true) true)
    (projectivePairFirstOverlapToInfinityPair W true)
  let e := h.isoIsPullback _ _ hcanonical
  apply (cancel_epi e.hom).mp
  calc
    _ = (projectivePairFirstOverlapAdditionOutputToInfinity W true true) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, true) true := by
          rw [← Category.assoc, h.isoIsPullback_hom_fst _ _ hcanonical]
    _ = projectivePairFirstOverlapAdditionOutputOpen W true true ≫
        (projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) := by
          rw [← Category.assoc]
          exact (projectivePairInfinityStandardTransitionSecantZ_morphisms_eq W).symm
    _ = (e.hom ≫
          pullback.snd
            (projectivePairChartAdditionOutputOpen W (false, true) true)
            (projectivePairFirstOverlapToInfinityPair W true)) ≫
        (projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) := by
            exact congrArg
              (fun q => q ≫
                (projectivePairFirstOverlapToStandardPair W true ≫
                  standardPairAdditionMorphism W))
              (h.isoIsPullback_hom_snd _ _ hcanonical).symm
    _ = _ := Category.assoc _ _ _

/-- The indexed infinity-by-standard local laws satisfy the open-cover
compatibility condition. -/
theorem projectivePairInfinityStandardAdditionCoverMorphism_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : ProjectiveMixedPairAdditionCoverIndex) :
    pullback.fst
          (projectivePairInfinityStandardAdditionCoverMap W i)
          (projectivePairInfinityStandardAdditionCoverMap W j) ≫
        projectivePairInfinityStandardAdditionCoverMorphism W i =
      pullback.snd
          (projectivePairInfinityStandardAdditionCoverMap W i)
          (projectivePairInfinityStandardAdditionCoverMap W j) ≫
        projectivePairInfinityStandardAdditionCoverMorphism W j := by
  cases i <;> cases j
  · exact mixedPullback_morphism_compatible_self _ _
  · exact projectivePairInfinityStandardTransitionSecantZ_compatible W
  · exact mixedPullback_morphism_compatible_symm _ _ _ _
      (projectivePairInfinityStandardTransitionSecantZ_compatible W)
  · exact mixedPullback_morphism_compatible_self _ _

private theorem projectivePairInfinityStandardAdditionOpenCover_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : (projectivePairInfinityStandardAdditionOpenCover W).I₀) :
    pullback.fst
          ((projectivePairInfinityStandardAdditionOpenCover W).f i)
          ((projectivePairInfinityStandardAdditionOpenCover W).f j) ≫
        projectivePairInfinityStandardAdditionCoverMorphism W i =
      pullback.snd
          ((projectivePairInfinityStandardAdditionOpenCover W).f i)
          ((projectivePairInfinityStandardAdditionOpenCover W).f j) ≫
        projectivePairInfinityStandardAdditionCoverMorphism W j := by
  exact projectivePairInfinityStandardAdditionCoverMorphism_compatible W i j

/-- The actual addition morphism on the entire infinity-by-standard chart. -/
noncomputable def projectivePairInfinityStandardAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartScheme W (false, true) ⟶ scheme W :=
  (projectivePairInfinityStandardAdditionOpenCover W).glueMorphisms
    (projectivePairInfinityStandardAdditionCoverMorphism W)
    (projectivePairInfinityStandardAdditionOpenCover_compatible W)

/-- The glued infinity-by-standard law restricts to the transported
standard-pair law on the transition member. -/
@[reassoc]
theorem projectivePairFirstOverlapToInfinityPair_comp_infinityStandardAddition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairFirstOverlapToInfinityPair W true ≫
        projectivePairInfinityStandardAdditionMorphism W =
      projectivePairFirstOverlapToStandardPair W true ≫
        standardPairAdditionMorphism W := by
  exact (projectivePairInfinityStandardAdditionOpenCover W).ι_glueMorphisms
    (projectivePairInfinityStandardAdditionCoverMorphism W)
    (projectivePairInfinityStandardAdditionOpenCover_compatible W)
    .transition

/-- The glued infinity-by-standard law restricts to the normalized secant law
on the output-`Z` member. -/
@[reassoc]
theorem projectivePairInfinityStandardSecantZOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionOutputOpen W (false, true) true ≫
        projectivePairInfinityStandardAdditionMorphism W =
      projectivePairChartAdditionOutputMorphism W (false, true) true := by
  exact (projectivePairInfinityStandardAdditionOpenCover W).ι_glueMorphisms
    (projectivePairInfinityStandardAdditionCoverMorphism W)
    (projectivePairInfinityStandardAdditionOpenCover_compatible W)
    .secantZ

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
