/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAdditionAtlas
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The full projective-product atlas for Weierstrass addition

The concrete projective Weierstrass cubic is covered by its `Y != 0` and
`Z != 0` coordinate charts.  Pulling those covers through both projections
gives four actual open subschemes of the fibre product of the cubic with
itself.  This file constructs that cover and identifies its `Z != 0` by
`Z != 0` member with the four-coordinate affine-pair presentation on which
the checked addition morphism has already been glued.

This is source geometry for the global multiplication construction.  It does
not supply local formulas on the three chart pairs meeting the point at
infinity, and it assumes no group object or pointwise compatibility shadow.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The actual fibre product of the concrete projective cubic with itself. -/
abbrev projectivePair (W : WeierstrassCurve K) : Scheme.{u} :=
  pullback (structureMap W) (structureMap W)

/-- One product of the two concrete coordinate charts of the cubic. -/
abbrev projectivePairChartScheme (W : WeierstrassCurve K)
    (ij : Bool × Bool) : Scheme.{u} :=
  pullback
    (coveringChartMap W ij.1 ≫ structureMap W)
    (coveringChartMap W ij.2 ≫ structureMap W)

/-- The four products of concrete coordinate charts form an actual open cover
of the full projective cubic fibre product. -/
noncomputable def projectivePairOpenCover (W : WeierstrassCurve K) :
    (projectivePair W).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (coveringChartsOpenCover W)
    (coveringChartsOpenCover W) (structureMap W) (structureMap W)

/-- The source and map of the projective-pair cover are definitionally the
expected chart product and its map into the full fibre product. -/
theorem projectivePairOpenCover_X (W : WeierstrassCurve K)
    (ij : Bool × Bool) :
    (projectivePairOpenCover W).X ij = projectivePairChartScheme W ij :=
  rfl

/-- The map from a chart product into the full projective pair. -/
abbrev projectivePairChartMap (W : WeierstrassCurve K)
    (ij : Bool × Bool) :
    projectivePairChartScheme W ij ⟶ projectivePair W :=
  (projectivePairOpenCover W).f ij

instance projectivePairChartMap_isOpenImmersion
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    IsOpenImmersion (projectivePairChartMap W ij) := by
  exact (projectivePairOpenCover W).map_prop ij

/-- The coefficient map equips every concrete coordinate-chart ring with its
canonical algebra structure over the ground field. -/
noncomputable instance coveringChartCoordinateRingAlgebra
    (W : WeierstrassCurve K) (b : Bool) :
    Algebra K (coveringChartCoordinateRing W b) :=
  (coveringChartStructureRingHom W b).toAlgebra

theorem coveringChartCoordinateRing_algebraMap
    (W : WeierstrassCurve K) (b : Bool) :
    algebraMap K (coveringChartCoordinateRing W b) =
      coveringChartStructureRingHom W b :=
  rfl

/-- Tensor-product coordinate ring of one member of the projective-pair
cover. -/
abbrev projectivePairChartTensorRing (W : WeierstrassCurve K)
    (ij : Bool × Bool) :=
  TensorProduct K (coveringChartCoordinateRing W ij.1)
    (coveringChartCoordinateRing W ij.2)

/-- Affine tensor-product presentation of one projective-pair chart. -/
abbrev projectivePairChartTensorScheme (W : WeierstrassCurve K)
    (ij : Bool × Bool) : Scheme.{u} :=
  Spec (.of (projectivePairChartTensorRing W ij))

private noncomputable def projectivePairChartIsoAlgebraPullback
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartScheme W ij ≅
      pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (coveringChartCoordinateRing W ij.1))))
        (Spec.map (CommRingCat.ofHom
          (algebraMap K (coveringChartCoordinateRing W ij.2)))) :=
  pullback.congrHom
    (by rw [coveringChartMap_comp_structureMap])
    (by rw [coveringChartMap_comp_structureMap])

/-- Every member of the concrete projective-product cover is canonically the
spectrum of the tensor product of its two affine chart rings. -/
noncomputable def projectivePairChartTensorIso
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartTensorScheme W ij ≅
      projectivePairChartScheme W ij :=
  (pullbackSpecIso K (coveringChartCoordinateRing W ij.1)
    (coveringChartCoordinateRing W ij.2)).symm ≪≫
      (projectivePairChartIsoAlgebraPullback W ij).symm

/-- The standard-coordinate product, before identifying the source type with
the corresponding member of the concrete product cover. -/
abbrev standardProjectivePairChartScheme
    (W : WeierstrassCurve K) : Scheme.{u} :=
  pullback
    (standardSecantChartMap W ≫ structureMap W)
    (standardSecantChartMap W ≫ structureMap W)

/-- The explicitly typed standard-coordinate product is canonically the
`(true, true)` member of the concrete product cover. -/
noncomputable def standardProjectivePairChartIsoCoverMember
    (W : WeierstrassCurve K) :
    standardProjectivePairChartScheme W ≅
      projectivePairChartScheme W (true, true) :=
  pullback.congrHom (by rfl) (by rfl)

private theorem affineEquationIso_comp_standardChart_comp_structureMap
    (W : WeierstrassCurve K) :
    ((affineEquationSchemeIsoStandardChart W).hom ≫
        standardSecantChartMap W) ≫ structureMap W =
      secantTargetStructureMap W := by
  calc
    ((affineEquationSchemeIsoStandardChart W).hom ≫
        standardSecantChartMap W) ≫ structureMap W =
      (affineEquationSchemeIsoStandardChart W).hom ≫
        (standardSecantChartMap W ≫ structureMap W) :=
      Category.assoc _ _ _
    _ = (affineEquationSchemeIsoStandardChart W).hom ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W true)) := by
      rw [standardSecantChartMap_comp_structureMap]
      rfl
    _ = secantTargetStructureMap W :=
      affineChartIso_comp_coveringStructureMap W

/-- The standard affine product is the standard-by-standard member of the
projective-pair cover. -/
noncomputable def standardAffineProductIsoStandardProjectivePairChart
    (W : WeierstrassCurve K) :
    secantAffineProduct W ≅ standardProjectivePairChartScheme W := by
  have h : secantTargetStructureMap W ≫ 𝟙 (Spec (.of K)) =
      (affineEquationSchemeIsoStandardChart W).hom ≫
        (standardSecantChartMap W ≫ structureMap W) := by
    rw [Category.comp_id]
    exact (affineEquationIso_comp_standardChart_comp_structureMap W).symm
  let hSource := IsPullback.of_hasPullback
    (secantTargetStructureMap W) (secantTargetStructureMap W)
  have hTransport : IsPullback
      (pullback.fst (secantTargetStructureMap W)
          (secantTargetStructureMap W) ≫
        (affineEquationSchemeIsoStandardChart W).hom)
      (pullback.snd (secantTargetStructureMap W)
          (secantTargetStructureMap W) ≫
        (affineEquationSchemeIsoStandardChart W).hom)
      (standardSecantChartMap W ≫ structureMap W)
      (standardSecantChartMap W ≫ structureMap W) :=
    hSource.of_iso (Iso.refl _) (affineEquationSchemeIsoStandardChart W)
      (affineEquationSchemeIsoStandardChart W) (Iso.refl _)
      (by simp) (by simp) h h
  exact hTransport.isoIsPullback _ _
    (IsPullback.of_hasPullback
      (standardSecantChartMap W ≫ structureMap W)
      (standardSecantChartMap W ≫ structureMap W))

/-- The standard affine product is the `(true, true)` member of the actual
full projective-product cover. -/
noncomputable def standardAffineProductIsoProjectivePairChart
    (W : WeierstrassCurve K) :
    secantAffineProduct W ≅ projectivePairChartScheme W (true, true) :=
  standardAffineProductIsoStandardProjectivePairChart W ≪≫
    standardProjectivePairChartIsoCoverMember W

/-- The standard member of the projective-pair cover is the existing explicit
four-coordinate affine-pair scheme. -/
noncomputable def standardPairIsoAffinePair (W : WeierstrassCurve K) :
    projectivePairChartScheme W (true, true) ≅
      Spec (.of (secantPairCoordinateRing W)) :=
  (standardAffineProductIsoProjectivePairChart W).symm ≪≫
    (secantPairSchemeIsoAffineProduct W).symm

/-- The already checked affine-pair addition, transported to the genuine
standard-by-standard member of the full projective-product cover. -/
noncomputable def standardPairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartScheme W (true, true) ⟶ scheme W :=
  (standardPairIsoAffinePair W).hom ≫ affinePairAdditionMorphism W

/-- Transporting back to the explicit affine-pair presentation recovers the
checked glued addition morphism exactly. -/
@[reassoc]
theorem standardPairIsoAffinePair_inv_comp_standardPairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (standardPairIsoAffinePair W).inv ≫ standardPairAdditionMorphism W =
      affinePairAdditionMorphism W := by
  simp [standardPairAdditionMorphism]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
