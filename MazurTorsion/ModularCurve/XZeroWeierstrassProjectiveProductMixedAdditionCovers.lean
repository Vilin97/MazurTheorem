/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductInfinityAdditionCover

/-!
# Actual addition-source covers of the mixed projective-pair charts

Each mixed input chart is covered by the open where its infinity input enters
the standard chart and by the raw secant output-`Z` open.  The first source
therefore carries the already checked standard-pair law, while the second
carries the normalized secant law.

This file turns both primewise lattice identities into finite
`Scheme.OpenCover`s and indexes the genuine local addition morphisms on their
members.  The design boundary is the pair of named downstream covers
`projectivePairStandardInfinityAdditionOpenCover` and
`projectivePairInfinityStandardAdditionOpenCover`; together with the infinity
cover they leave only pairwise compatibility and gluing inside the four-chart
projective product atlas.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## Standard-by-infinity chart -/

/-- The second-input transition source in the affine presentation of the
standard-by-infinity chart. -/
noncomputable def projectivePairStandardInfinityTransitionOpenAffine
    (W : WeierstrassCurve K) :
    projectivePairSecondChartOverlapScheme W true ⟶
      Spec (.of (projectivePairChartCoordinateRing W (true, false))) :=
  projectivePairSecondOverlapToInfinityPair W true ≫
    (projectivePairChartIsoSpecTensor W (true, false)).hom

/-- The secant output-`Z` source in the affine presentation of the
standard-by-infinity chart. -/
noncomputable def projectivePairStandardInfinitySecantZOpenAffine
    (W : WeierstrassCurve K) :
    Spec (.of
        (projectivePairChartAdditionOutputRing W (true, false) true)) ⟶
      Spec (.of (projectivePairChartCoordinateRing W (true, false))) :=
  projectivePairChartAdditionOutputOpen W (true, false) true ≫
    (projectivePairChartIsoSpecTensor W (true, false)).hom

instance projectivePairStandardInfinityTransitionOpenAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectivePairStandardInfinityTransitionOpenAffine W) := by
  dsimp only [projectivePairStandardInfinityTransitionOpenAffine]
  infer_instance

instance projectivePairStandardInfinitySecantZOpenAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectivePairStandardInfinitySecantZOpenAffine W) := by
  dsimp only [projectivePairStandardInfinitySecantZOpenAffine]
  infer_instance

theorem projectivePairStandardInfinityTransitionOpenAffine_opensRange
    (W : WeierstrassCurve K) :
    (projectivePairStandardInfinityTransitionOpenAffine W).opensRange =
      PrimeSpectrum.basicOpen
        (projectivePairChartSecondUniversalPoint W (true, false)
          (2 : Fin 3)) := by
  letI := (infinityPairToSecondChartOverlapAlgHom W true).toAlgebra
  haveI hLocalization : IsLocalization.Away
      (projectivePairChartSecondUniversalPoint W (true, false)
        (2 : Fin 3))
      (projectivePairSecondChartOverlapCoordinateRing W true) := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := coveringChartCoordinateRing W true)
        (B := coveringChartCoordinateRing W false)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairSecondChartOverlapCoordinateRing W true)
    exact projectivePairSecondOverlap_isLocalization_infinityPair W true
  simp only [projectivePairStandardInfinityTransitionOpenAffine,
    projectivePairSecondOverlapToInfinityPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (projectivePairSecondChartOverlapCoordinateRing W true)
    (projectivePairChartSecondUniversalPoint W (true, false) (2 : Fin 3))

theorem projectivePairStandardInfinitySecantZOpenAffine_opensRange
    (W : WeierstrassCurve K) :
    (projectivePairStandardInfinitySecantZOpenAffine W).opensRange =
      PrimeSpectrum.basicOpen
        (projectivePairChartAdditionCoordinates W (true, false)
          (2 : Fin 3)) := by
  simp only [projectivePairStandardInfinitySecantZOpenAffine,
    projectivePairChartAdditionOutputOpen, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (projectivePairChartCoordinateRing W (true, false)))
    (projectivePairChartAdditionCoordinates W (true, false) (2 : Fin 3))

/-- The two actual addition sources cover the affine presentation of the
standard-by-infinity chart. -/
theorem projectivePairStandardInfinityActualAdditionOpens_cover
    (W : WeierstrassCurve K) :
    (projectivePairStandardInfinityTransitionOpenAffine W).opensRange ⊔
      (projectivePairStandardInfinitySecantZOpenAffine W).opensRange = ⊤ := by
  rw [projectivePairStandardInfinityTransitionOpenAffine_opensRange,
    projectivePairStandardInfinitySecantZOpenAffine_opensRange]
  exact projectivePairStandardInfinityTransitionAndSecantZOpens_cover W

/-! ## Infinity-by-standard chart -/

/-- The first-input transition source in the affine presentation of the
infinity-by-standard chart. -/
noncomputable def projectivePairInfinityStandardTransitionOpenAffine
    (W : WeierstrassCurve K) :
    projectivePairFirstChartOverlapScheme W true ⟶
      Spec (.of (projectivePairChartCoordinateRing W (false, true))) :=
  projectivePairFirstOverlapToInfinityPair W true ≫
    (projectivePairChartIsoSpecTensor W (false, true)).hom

/-- The secant output-`Z` source in the affine presentation of the
infinity-by-standard chart. -/
noncomputable def projectivePairInfinityStandardSecantZOpenAffine
    (W : WeierstrassCurve K) :
    Spec (.of
        (projectivePairChartAdditionOutputRing W (false, true) true)) ⟶
      Spec (.of (projectivePairChartCoordinateRing W (false, true))) :=
  projectivePairChartAdditionOutputOpen W (false, true) true ≫
    (projectivePairChartIsoSpecTensor W (false, true)).hom

instance projectivePairInfinityStandardTransitionOpenAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectivePairInfinityStandardTransitionOpenAffine W) := by
  dsimp only [projectivePairInfinityStandardTransitionOpenAffine]
  infer_instance

instance projectivePairInfinityStandardSecantZOpenAffine_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectivePairInfinityStandardSecantZOpenAffine W) := by
  dsimp only [projectivePairInfinityStandardSecantZOpenAffine]
  infer_instance

theorem projectivePairInfinityStandardTransitionOpenAffine_opensRange
    (W : WeierstrassCurve K) :
    (projectivePairInfinityStandardTransitionOpenAffine W).opensRange =
      PrimeSpectrum.basicOpen
        (projectivePairChartFirstUniversalPoint W (false, true)
          (2 : Fin 3)) := by
  letI := (infinityPairToFirstChartOverlapAlgHom W true).toAlgebra
  haveI hLocalization : IsLocalization.Away
      (projectivePairChartFirstUniversalPoint W (false, true)
        (2 : Fin 3))
      (projectivePairFirstChartOverlapCoordinateRing W true) := by
    change IsLocalization.Away
      (Algebra.TensorProduct.includeLeft
        (R := K)
        (S := K)
        (A := coveringChartCoordinateRing W false)
        (B := coveringChartCoordinateRing W true)
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2)))
      (projectivePairFirstChartOverlapCoordinateRing W true)
    exact projectivePairFirstOverlap_isLocalization_infinityPair W true
  simp only [projectivePairInfinityStandardTransitionOpenAffine,
    projectivePairFirstOverlapToInfinityPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (projectivePairFirstChartOverlapCoordinateRing W true)
    (projectivePairChartFirstUniversalPoint W (false, true) (2 : Fin 3))

theorem projectivePairInfinityStandardSecantZOpenAffine_opensRange
    (W : WeierstrassCurve K) :
    (projectivePairInfinityStandardSecantZOpenAffine W).opensRange =
      PrimeSpectrum.basicOpen
        (projectivePairChartAdditionCoordinates W (false, true)
          (2 : Fin 3)) := by
  simp only [projectivePairInfinityStandardSecantZOpenAffine,
    projectivePairChartAdditionOutputOpen, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (projectivePairChartCoordinateRing W (false, true)))
    (projectivePairChartAdditionCoordinates W (false, true) (2 : Fin 3))

/-- The two actual addition sources cover the affine presentation of the
infinity-by-standard chart. -/
theorem projectivePairInfinityStandardActualAdditionOpens_cover
    (W : WeierstrassCurve K) :
    (projectivePairInfinityStandardTransitionOpenAffine W).opensRange ⊔
      (projectivePairInfinityStandardSecantZOpenAffine W).opensRange = ⊤ := by
  rw [projectivePairInfinityStandardTransitionOpenAffine_opensRange,
    projectivePairInfinityStandardSecantZOpenAffine_opensRange]
  exact projectivePairInfinityStandardTransitionAndSecantZOpens_cover W

/-! ## Scheme open covers and their local laws -/

/-- Labels for either two-member mixed-chart addition cover. -/
inductive ProjectiveMixedPairAdditionCoverIndex
  | transition
  | secantZ
  deriving DecidableEq

/-- Sources of the standard-by-infinity addition cover. -/
abbrev projectivePairStandardInfinityAdditionCoverSource
    (W : WeierstrassCurve K) :
    ProjectiveMixedPairAdditionCoverIndex → Scheme
  | .transition => projectivePairSecondChartOverlapScheme W true
  | .secantZ =>
      Spec (.of
        (projectivePairChartAdditionOutputRing W (true, false) true))

/-- Inclusions of the standard-by-infinity addition cover. -/
noncomputable def projectivePairStandardInfinityAdditionCoverMap
    (W : WeierstrassCurve K) :
    (i : ProjectiveMixedPairAdditionCoverIndex) →
      projectivePairStandardInfinityAdditionCoverSource W i ⟶
        projectivePairChartScheme W (true, false)
  | .transition => projectivePairSecondOverlapToInfinityPair W true
  | .secantZ =>
      projectivePairChartAdditionOutputOpen W (true, false) true

instance projectivePairStandardInfinityAdditionCoverMap_isOpenImmersion
    (W : WeierstrassCurve K) (i : ProjectiveMixedPairAdditionCoverIndex) :
    IsOpenImmersion
      (projectivePairStandardInfinityAdditionCoverMap W i) := by
  cases i <;> dsimp [projectivePairStandardInfinityAdditionCoverMap] <;>
    infer_instance

/-- The transition and secant-`Z` sources form an actual open cover of the
standard-by-infinity pair chart. -/
noncomputable def projectivePairStandardInfinityAdditionOpenCover
    (W : WeierstrassCurve K) :
    (projectivePairChartScheme W (true, false)).OpenCover :=
  Scheme.Cover.mkOfCovers
    ProjectiveMixedPairAdditionCoverIndex
    (projectivePairStandardInfinityAdditionCoverSource W)
    (projectivePairStandardInfinityAdditionCoverMap W) (by
      intro x
      let e : projectivePairChartScheme W (true, false) ≅
          Spec (.of (projectivePairChartCoordinateRing W (true, false))) :=
        projectivePairChartIsoSpecTensor W (true, false)
      have hx : e.hom x ∈ (⊤ :
          (Spec (.of
            (projectivePairChartCoordinateRing W (true, false)))).Opens) :=
        trivial
      rw [← projectivePairStandardInfinityActualAdditionOpens_cover W] at hx
      rcases hx with hx | hx
      · change e.hom x ∈ Set.range
          (projectivePairStandardInfinityTransitionOpenAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveMixedPairAdditionCoverIndex.transition, y, ?_⟩
        change projectivePairSecondOverlapToInfinityPair W true y = x
        apply e.hom.homeomorph.injective
        simpa [projectivePairStandardInfinityTransitionOpenAffine,
          Scheme.Hom.comp_apply] using hy
      · change e.hom x ∈ Set.range
          (projectivePairStandardInfinitySecantZOpenAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveMixedPairAdditionCoverIndex.secantZ, y, ?_⟩
        change projectivePairChartAdditionOutputOpen W
          (true, false) true y = x
        apply e.hom.homeomorph.injective
        simpa [projectivePairStandardInfinitySecantZOpenAffine,
          Scheme.Hom.comp_apply] using hy)

/-- Genuine local addition law on each standard-by-infinity cover member. -/
noncomputable def projectivePairStandardInfinityAdditionCoverMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (i : ProjectiveMixedPairAdditionCoverIndex) →
      projectivePairStandardInfinityAdditionCoverSource W i ⟶ scheme W
  | .transition =>
      projectivePairSecondOverlapToStandardPair W true ≫
        standardPairAdditionMorphism W
  | .secantZ =>
      projectivePairChartAdditionOutputMorphism W (true, false) true

/-- Sources of the infinity-by-standard addition cover. -/
abbrev projectivePairInfinityStandardAdditionCoverSource
    (W : WeierstrassCurve K) :
    ProjectiveMixedPairAdditionCoverIndex → Scheme
  | .transition => projectivePairFirstChartOverlapScheme W true
  | .secantZ =>
      Spec (.of
        (projectivePairChartAdditionOutputRing W (false, true) true))

/-- Inclusions of the infinity-by-standard addition cover. -/
noncomputable def projectivePairInfinityStandardAdditionCoverMap
    (W : WeierstrassCurve K) :
    (i : ProjectiveMixedPairAdditionCoverIndex) →
      projectivePairInfinityStandardAdditionCoverSource W i ⟶
        projectivePairChartScheme W (false, true)
  | .transition => projectivePairFirstOverlapToInfinityPair W true
  | .secantZ =>
      projectivePairChartAdditionOutputOpen W (false, true) true

instance projectivePairInfinityStandardAdditionCoverMap_isOpenImmersion
    (W : WeierstrassCurve K) (i : ProjectiveMixedPairAdditionCoverIndex) :
    IsOpenImmersion
      (projectivePairInfinityStandardAdditionCoverMap W i) := by
  cases i <;> dsimp [projectivePairInfinityStandardAdditionCoverMap] <;>
    infer_instance

/-- The transition and secant-`Z` sources form an actual open cover of the
infinity-by-standard pair chart. -/
noncomputable def projectivePairInfinityStandardAdditionOpenCover
    (W : WeierstrassCurve K) :
    (projectivePairChartScheme W (false, true)).OpenCover :=
  Scheme.Cover.mkOfCovers
    ProjectiveMixedPairAdditionCoverIndex
    (projectivePairInfinityStandardAdditionCoverSource W)
    (projectivePairInfinityStandardAdditionCoverMap W) (by
      intro x
      let e : projectivePairChartScheme W (false, true) ≅
          Spec (.of (projectivePairChartCoordinateRing W (false, true))) :=
        projectivePairChartIsoSpecTensor W (false, true)
      have hx : e.hom x ∈ (⊤ :
          (Spec (.of
            (projectivePairChartCoordinateRing W (false, true)))).Opens) :=
        trivial
      rw [← projectivePairInfinityStandardActualAdditionOpens_cover W] at hx
      rcases hx with hx | hx
      · change e.hom x ∈ Set.range
          (projectivePairInfinityStandardTransitionOpenAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveMixedPairAdditionCoverIndex.transition, y, ?_⟩
        change projectivePairFirstOverlapToInfinityPair W true y = x
        apply e.hom.homeomorph.injective
        simpa [projectivePairInfinityStandardTransitionOpenAffine,
          Scheme.Hom.comp_apply] using hy
      · change e.hom x ∈ Set.range
          (projectivePairInfinityStandardSecantZOpenAffine W) at hx
        rcases hx with ⟨y, hy⟩
        refine ⟨ProjectiveMixedPairAdditionCoverIndex.secantZ, y, ?_⟩
        change projectivePairChartAdditionOutputOpen W
          (false, true) true y = x
        apply e.hom.homeomorph.injective
        simpa [projectivePairInfinityStandardSecantZOpenAffine,
          Scheme.Hom.comp_apply] using hy)

/-- Genuine local addition law on each infinity-by-standard cover member. -/
noncomputable def projectivePairInfinityStandardAdditionCoverMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (i : ProjectiveMixedPairAdditionCoverIndex) →
      projectivePairInfinityStandardAdditionCoverSource W i ⟶ scheme W
  | .transition =>
      projectivePairFirstOverlapToStandardPair W true ≫
        standardPairAdditionMorphism W
  | .secantZ =>
      projectivePairChartAdditionOutputMorphism W (false, true) true

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
