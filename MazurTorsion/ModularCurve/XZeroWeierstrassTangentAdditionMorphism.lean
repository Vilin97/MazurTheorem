/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicReducedBaseChange
import MazurTorsion.ModularCurve.XZeroWeierstrassTangentAddition
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The scheme morphism on the tangent doubling chart

The denominator-cleared identities in `XZeroWeierstrassTangentAddition`
induce a genuine morphism from the affine Weierstrass chart localized where
`2y + a₁x + a₃` is invertible into the concrete projective Weierstrass
cubic.  The localization is exhibited as the corresponding principal-open
immersion, and the doubling morphism is checked to lie over the base field.

This completes only the tangent/doubling principal-open chart.  It does not
construct overlaps with the secant or infinity charts, glue a global
multiplication, or provide a group object.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The affine principal open -/

/-- The localization map from the tangent chart to the affine Weierstrass
chart. -/
def tangentChartToAffineCurve (W : WeierstrassCurve K) :
    Spec (.of (tangentChartCoordinateRing W)) ⟶
      Spec (.of (affineWeierstrassCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (tangentSourceCoordinateRing W)
      (tangentChartCoordinateRing W)))

instance tangentChartToAffineCurve_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (tangentChartToAffineCurve W) := by
  dsimp only [tangentChartToAffineCurve, tangentChartCoordinateRing]
  infer_instance

/-- The tangent localization has precisely the principal-open range
`D(2y + a₁x + a₃)` in the affine Weierstrass chart. -/
theorem tangentChartToAffineCurve_opensRange (W : WeierstrassCurve K) :
    (tangentChartToAffineCurve W).opensRange =
      PrimeSpectrum.basicOpen (tangentDenominator W) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (tangentSourceCoordinateRing W)
      (Localization.Away (tangentDenominator W))))).opensRange = _
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (tangentSourceCoordinateRing W)) (tangentDenominator W)

/-- Structure morphism of the tangent chart. -/
def tangentChartStructureMap (W : WeierstrassCurve K) :
    Spec (.of (tangentChartCoordinateRing W)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (tangentCoefficientHom W))

/-- Structure morphism of the affine Weierstrass chart. -/
def tangentTargetStructureMap (W : WeierstrassCurve K) :
    Spec (.of (affineWeierstrassCoordinateRing W)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (tangentSourceCoefficientHom W))

/-- The tangent principal-open inclusion lies over the base field. -/
@[reassoc]
theorem tangentChartToAffineCurve_comp_structureMap
    (W : WeierstrassCurve K) :
    tangentChartToAffineCurve W ≫ tangentTargetStructureMap W =
      tangentChartStructureMap W := by
  rw [tangentChartToAffineCurve, tangentTargetStructureMap,
    tangentChartStructureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Spec.map_inj]
  rfl

/-! ## Tangent doubling into the concrete cubic -/

/-- The affine scheme morphism induced by the universal tangent-doubling
formula. -/
def tangentDoublingAffineMorphism (W : WeierstrassCurve K) :
    Spec (.of (tangentChartCoordinateRing W)) ⟶
      Spec (.of (affineWeierstrassCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (tangentDoublingToAffineRing W))

private theorem tangentDoublingAffineMorphism_preimage
    (W : WeierstrassCurve K) :
    Spec.preimage (tangentDoublingAffineMorphism W) =
      CommRingCat.ofHom (tangentDoublingToAffineRing W) := by
  rw [tangentDoublingAffineMorphism, Spec.preimage_map]

/-- The affine tangent-doubling morphism pulls the target abscissa back to
the checked doubled abscissa. -/
theorem tangentDoublingAffineMorphism_preimage_abscissa
    (W : WeierstrassCurve K) :
    (Spec.preimage (tangentDoublingAffineMorphism W)).hom
        (tangentSourceX W) = tangentChartDoubleX W := by
  rw [tangentDoublingAffineMorphism_preimage]
  exact tangentDoublingToAffineRing_abscissa W

/-- The affine tangent-doubling morphism pulls the target ordinate back to
the checked doubled ordinate. -/
theorem tangentDoublingAffineMorphism_preimage_ordinate
    (W : WeierstrassCurve K) :
    (Spec.preimage (tangentDoublingAffineMorphism W)).hom
        (tangentSourceY W) = tangentChartDoubleY W := by
  rw [tangentDoublingAffineMorphism_preimage]
  exact tangentDoublingToAffineRing_ordinate W

/-- The affine tangent-doubling morphism lies over the base field. -/
@[reassoc]
theorem tangentDoublingAffineMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    tangentDoublingAffineMorphism W ≫ tangentTargetStructureMap W =
      tangentChartStructureMap W := by
  rw [tangentDoublingAffineMorphism, tangentTargetStructureMap,
    tangentChartStructureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact tangentDoublingToAffineRing_comp_coefficient W

private theorem affineChartIso_comp_coveringStructureMap_tangent
    (W : WeierstrassCurve K) :
    (affineEquationSchemeIsoStandardChart W).hom ≫
      Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W true)) =
        tangentTargetStructureMap W := by
  rw [show (affineEquationSchemeIsoStandardChart W).hom =
      Spec.map
        (affineEquationToStandardChartRingEquiv W).toCommRingCatIso.symm.hom
    from rfl]
  rw [tangentTargetStructureMap, ← Spec.map_comp, Spec.map_inj]
  ext a
  change (affineEquationToStandardChartRingEquiv W).symm
      (coveringChartStructureRingHom W true a) =
    tangentSourceCoefficientHom W a
  simp only [coveringChartStructureRingHom, coveringCoordinate,
    coveringChartIdeal, coveringChartEquation, tangentSourceCoefficientHom,
    RingHom.coe_comp, Function.comp_apply]
  change (affineEquationToStandardChartRingEquiv W).symm
      (Ideal.Quotient.mk (standardChartIdeal W)
        (coordinateChartConstantHom (K := K) 2 a)) =
    Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
      (Polynomial.C (Polynomial.C a))
  apply (affineEquationToStandardChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartConstantHom (K := K) 2 a) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (affineToStandardChart (K := K)
        (Polynomial.C (Polynomial.C a)))
  rw [affineToStandardChart_C_C]

private def standardTangentChartMap (W : WeierstrassCurve K) :
    standardAffineChartScheme W ⟶ scheme W :=
  coveringChartMap W true

/-- The checked tangent-doubling formula defines an actual morphism from the
principal-open chart into the concrete projective Weierstrass cubic. -/
def tangentDoublingProjectiveMorphism (W : WeierstrassCurve K) :
    Spec (.of (tangentChartCoordinateRing W)) ⟶ scheme W :=
  tangentDoublingAffineMorphism W ≫
    (affineEquationSchemeIsoStandardChart W).hom ≫
    standardTangentChartMap W

/-- The projective tangent-doubling morphism respects the structural
morphisms to the base field. -/
theorem tangentDoublingProjectiveMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    tangentDoublingProjectiveMorphism W ≫ structureMap W =
      tangentChartStructureMap W := by
  let chartStructureMap : standardAffineChartScheme W ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W true))
  have hchart : standardTangentChartMap W ≫ structureMap W =
      chartStructureMap := by
    exact coveringChartMap_comp_structureMap W true
  have htarget : (affineEquationSchemeIsoStandardChart W).hom ≫
      chartStructureMap = tangentTargetStructureMap W := by
    exact affineChartIso_comp_coveringStructureMap_tangent W
  simp only [tangentDoublingProjectiveMorphism, Category.assoc,
    hchart, htarget,
    tangentDoublingAffineMorphism_comp_structureMap]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
