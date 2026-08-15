/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicReducedBaseChange
import MazurTorsion.ModularCurve.XZeroWeierstrassSecantAddition
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The scheme morphism on the secant addition chart

The denominator-cleared identities in `XZeroWeierstrassSecantAddition` induce a genuine morphism
from the explicit four-coordinate presentation localized at `x₁ - x₂` to the concrete projective
Weierstrass cubic.  The quotient/tensor equivalence identifies this presentation with the genuine
principal open in the affine product chart, and the checked secant morphism therefore descends to
that open.  A group object additionally needs the tangent and infinity charts, a cover and overlap
proofs, gluing, and the group axioms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The affine scheme morphism induced by the checked universal secant formula. -/
def secantAdditionAffineMorphism (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ⟶
      Spec (.of (affineWeierstrassCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (secantAdditionToAffineRing W))

/-- The affine morphism has the constructed coordinate-ring map as its comorphism. -/
private theorem secantAdditionAffineMorphism_preimage (W : WeierstrassCurve K) :
    Spec.preimage (secantAdditionAffineMorphism W) =
      CommRingCat.ofHom (secantAdditionToAffineRing W) := by
  rw [secantAdditionAffineMorphism, Spec.preimage_map]

/-- The scheme morphism pulls the affine abscissa back to the checked secant formula. -/
theorem secantAdditionAffineMorphism_preimage_abscissa (W : WeierstrassCurve K) :
    (Spec.preimage (secantAdditionAffineMorphism W)).hom
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
          (Polynomial.C Polynomial.X)) =
      secantChartAddX W := by
  rw [secantAdditionAffineMorphism_preimage]
  exact secantAdditionToAffineRing_abscissa W

/-- The scheme morphism pulls the affine ordinate back to the checked secant formula. -/
theorem secantAdditionAffineMorphism_preimage_ordinate (W : WeierstrassCurve K) :
    (Spec.preimage (secantAdditionAffineMorphism W)).hom
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) Polynomial.X) =
      secantChartAddY W := by
  rw [secantAdditionAffineMorphism_preimage]
  exact secantAdditionToAffineRing_ordinate W

/-- Structure morphism of the secant chart, using its explicit coefficient map. -/
def secantChartStructureMap (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (secantCoefficientHom W))

/-- Structure morphism of the affine Weierstrass target. -/
def secantTargetStructureMap (W : WeierstrassCurve K) :
    Spec (.of (affineWeierstrassCoordinateRing W)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (secantTargetCoefficientHom W))

/-- The affine secant-addition morphism is a morphism over the base field. -/
@[reassoc]
theorem secantAdditionAffineMorphism_comp_structureMap (W : WeierstrassCurve K) :
    secantAdditionAffineMorphism W ≫ secantTargetStructureMap W =
      secantChartStructureMap W := by
  rw [secantAdditionAffineMorphism, secantTargetStructureMap,
    secantChartStructureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact secantAdditionToAffineRing_comp_coefficient W

/-! ## The principal open in the affine product chart -/

/-- The categorical product over `Spec K` of the two affine Weierstrass charts. -/
abbrev secantAffineProduct (W : WeierstrassCurve K) : Scheme.{u} :=
  pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (secantTargetCoordinateRing W))))
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (secantTargetCoordinateRing W))))

/-- The four-coordinate pair presentation is the actual affine fiber product. -/
noncomputable def secantPairSchemeIsoAffineProduct (W : WeierstrassCurve K) :
    Spec (.of (secantPairCoordinateRing W)) ≅ secantAffineProduct W :=
  Scheme.Spec.mapIso (secantPairTensorEquiv W).toCommRingCatIso.symm.op ≪≫
    (pullbackSpecIso K (secantTargetCoordinateRing W)
      (secantTargetCoordinateRing W)).symm

private noncomputable def secantPairFirstProjectionAlgHom
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →ₐ[K] secantPairCoordinateRing W :=
  (secantPairTensorEquiv W).symm.toAlgHom.comp
    (Algebra.TensorProduct.includeLeft (S := K))

private noncomputable def secantPairSecondProjectionAlgHom
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →ₐ[K] secantPairCoordinateRing W :=
  (secantPairTensorEquiv W).symm.toAlgHom.comp
    Algebra.TensorProduct.includeRight

private theorem secantPairSchemeIsoAffineProduct_hom
    (W : WeierstrassCurve K) :
    (secantPairSchemeIsoAffineProduct W).hom =
      Spec.map (CommRingCat.ofHom
        (secantPairTensorEquiv W).symm.toRingHom) ≫
        (pullbackSpecIso K (secantTargetCoordinateRing W)
          (secantTargetCoordinateRing W)).inv := by
  rfl

private theorem secantPairSchemeIsoAffineProduct_hom_fst
    (W : WeierstrassCurve K) :
    (secantPairSchemeIsoAffineProduct W).hom ≫
        pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (secantPairFirstProjectionAlgHom W).toRingHom) := by
  rw [secantPairSchemeIsoAffineProduct_hom, Category.assoc,
    pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem secantPairSchemeIsoAffineProduct_hom_snd
    (W : WeierstrassCurve K) :
    (secantPairSchemeIsoAffineProduct W).hom ≫
        pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (secantPairSecondProjectionAlgHom W).toRingHom) := by
  rw [secantPairSchemeIsoAffineProduct_hom, Category.assoc,
    pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem secantPairSchemeIsoAffineProduct_hom_comp_base
    (W : WeierstrassCurve K) :
    ((secantPairSchemeIsoAffineProduct W).hom ≫ pullback.fst _ _) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (secantTargetCoordinateRing W))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (secantPairCoordinateRing W))) := by
  rw [secantPairSchemeIsoAffineProduct_hom_fst, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, Spec.map_inj]
  ext a
  exact (secantPairFirstProjectionAlgHom W).commutes a

/-- The localization map into the four-coordinate affine-pair presentation. -/
def secantChartToPair (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ⟶
      Spec (.of (secantPairCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)))

instance secantChartToPair_isOpenImmersion (W : WeierstrassCurve K) :
    IsOpenImmersion (secantChartToPair W) := by
  dsimp only [secantChartToPair, secantChartCoordinateRing]
  infer_instance

/-- The localization has precisely the principal-open range `D(x₁ - x₂)`. -/
theorem secantChartToPair_opensRange (W : WeierstrassCurve K) :
    (secantChartToPair W).opensRange =
      PrimeSpectrum.basicOpen (secantDenominator W) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (Localization.Away (secantDenominator W))))).opensRange = _
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (secantPairCoordinateRing W)) (secantDenominator W)

/-- The secant chart as an actual open subscheme of the affine product chart. -/
noncomputable def secantChartToAffineProduct (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ⟶ secantAffineProduct W :=
  secantChartToPair W ≫ (secantPairSchemeIsoAffineProduct W).hom

instance secantChartToAffineProduct_isOpenImmersion (W : WeierstrassCurve K) :
    IsOpenImmersion (secantChartToAffineProduct W) := by
  dsimp only [secantChartToAffineProduct]
  infer_instance

/-- The principal secant open, now living in the genuine affine fiber product. -/
noncomputable def secantProductOpen (W : WeierstrassCurve K) :
    (secantAffineProduct W).Opens :=
  (secantChartToAffineProduct W).opensRange

/-- The explicit localized spectrum is canonically the corresponding product open. -/
noncomputable def secantChartIsoProductOpen (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ≅ (secantProductOpen W).toScheme :=
  IsOpenImmersion.isoOfRangeEq (secantChartToAffineProduct W)
    (secantProductOpen W).ι (by
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
      rfl)

/-- The chart isomorphism followed by the product-open inclusion recovers the constructed open
immersion into the affine product. -/
theorem secantChartIsoProductOpen_hom_comp_ι (W : WeierstrassCurve K) :
    (secantChartIsoProductOpen W).hom ≫ (secantProductOpen W).ι =
      secantChartToAffineProduct W := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The first projection of the product-open presentation is the first affine-point projection
coming from the quotient/tensor equivalence. -/
theorem secantChartIsoProductOpen_hom_comp_ι_fst
    (W : WeierstrassCurve K) :
    ((secantChartIsoProductOpen W).hom ≫ (secantProductOpen W).ι) ≫
        pullback.fst _ _ =
      secantChartToPair W ≫
        Spec.map (CommRingCat.ofHom
          (((secantPairTensorEquiv W).symm.toAlgHom.comp
            (Algebra.TensorProduct.includeLeft (S := K))).toRingHom)) := by
  change _ = secantChartToPair W ≫
    Spec.map (CommRingCat.ofHom
      (secantPairFirstProjectionAlgHom W).toRingHom)
  rw [secantChartIsoProductOpen_hom_comp_ι, secantChartToAffineProduct,
    Category.assoc, secantPairSchemeIsoAffineProduct_hom_fst]

/-- The second projection of the product-open presentation is the second affine-point projection
coming from the quotient/tensor equivalence. -/
theorem secantChartIsoProductOpen_hom_comp_ι_snd
    (W : WeierstrassCurve K) :
    ((secantChartIsoProductOpen W).hom ≫ (secantProductOpen W).ι) ≫
        pullback.snd _ _ =
      secantChartToPair W ≫
        Spec.map (CommRingCat.ofHom
          (((secantPairTensorEquiv W).symm.toAlgHom.comp
            Algebra.TensorProduct.includeRight).toRingHom)) := by
  change _ = secantChartToPair W ≫
    Spec.map (CommRingCat.ofHom
      (secantPairSecondProjectionAlgHom W).toRingHom)
  rw [secantChartIsoProductOpen_hom_comp_ι, secantChartToAffineProduct,
    Category.assoc, secantPairSchemeIsoAffineProduct_hom_snd]

private theorem secantChartToPair_comp_base (W : WeierstrassCurve K) :
    secantChartToPair W ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (secantPairCoordinateRing W))) =
      secantChartStructureMap W := by
  rw [secantChartToPair, secantChartStructureMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, Spec.map_inj]
  rw [secantCoefficientHom_eq_algebraMap]

private theorem secantChartToAffineProduct_comp_base
    (W : WeierstrassCurve K) :
    (secantChartToAffineProduct W ≫ pullback.fst _ _) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (secantTargetCoordinateRing W))) =
      secantChartStructureMap W := by
  rw [secantChartToAffineProduct]
  calc
    ((secantChartToPair W ≫ (secantPairSchemeIsoAffineProduct W).hom) ≫
        pullback.fst _ _) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantTargetCoordinateRing W))) =
      secantChartToPair W ≫
        (((secantPairSchemeIsoAffineProduct W).hom ≫ pullback.fst _ _) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantTargetCoordinateRing W)))) := by
      simp only [Category.assoc]
    _ = secantChartToPair W ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (secantPairCoordinateRing W))) := by
      rw [secantPairSchemeIsoAffineProduct_hom_comp_base]
    _ = secantChartStructureMap W := secantChartToPair_comp_base W

/-- The product-open presentation respects the canonical structure morphism to `Spec K`. -/
theorem secantChartIsoProductOpen_hom_comp_ι_comp_structureMap
    (W : WeierstrassCurve K) :
    (((secantChartIsoProductOpen W).hom ≫ (secantProductOpen W).ι) ≫
        pullback.fst _ _) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantTargetCoordinateRing W))) =
      secantChartStructureMap W := by
  rw [secantChartIsoProductOpen_hom_comp_ι,
    secantChartToAffineProduct_comp_base]

/-- The affine-equation comparison identifies its coefficient map with the
structural morphism of the standard projective chart. -/
theorem affineChartIso_comp_coveringStructureMap
    (W : WeierstrassCurve K) :
    (affineEquationSchemeIsoStandardChart W).hom ≫
      Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W true)) =
        secantTargetStructureMap W := by
  rw [show (affineEquationSchemeIsoStandardChart W).hom =
      Spec.map
        (affineEquationToStandardChartRingEquiv W).toCommRingCatIso.symm.hom
    from rfl]
  rw [secantTargetStructureMap, ← Spec.map_comp, Spec.map_inj]
  ext a
  change (affineEquationToStandardChartRingEquiv W).symm
      (coveringChartStructureRingHom W true a) =
    secantTargetCoefficientHom W a
  simp only [coveringChartStructureRingHom, coveringCoordinate,
    coveringChartIdeal, coveringChartEquation, secantTargetCoefficientHom,
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

/-- The standard affine coordinate chart mapped into the concrete projective
Weierstrass cubic. -/
def standardSecantChartMap (W : WeierstrassCurve K) :
    standardAffineChartScheme W ⟶ scheme W :=
  coveringChartMap W true

/-- The standard affine chart has the restriction of the cubic's structural
morphism. -/
@[reassoc]
theorem standardSecantChartMap_comp_structureMap
    (W : WeierstrassCurve K) :
    standardSecantChartMap W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (coveringChartStructureRingHom W true)) := by
  exact coveringChartMap_comp_structureMap W true

/-- The secant chart maps into the actual reduced projective Weierstrass cubic through its
standard affine open. -/
def secantAdditionProjectiveMorphism (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ⟶ scheme W :=
  secantAdditionAffineMorphism W ≫
    (affineEquationSchemeIsoStandardChart W).hom ≫
    standardSecantChartMap W

/-- After the cubic's closed immersion, the secant formula is the
corresponding morphism into the ambient standard projective chart. -/
@[reassoc]
theorem secantAdditionProjectiveMorphism_comp_inclusion
    (W : WeierstrassCurve K) :
    secantAdditionProjectiveMorphism W ≫ inclusion W =
      secantAdditionAffineMorphism W ≫
        (affineEquationSchemeIsoStandardChart W).hom ≫
          coveringChartAmbientMap W true := by
  unfold secantAdditionProjectiveMorphism
  simp only [Category.assoc]
  congr 1
  congr 1
  exact coveringChartMap_comp_inclusion W true

/-- Secant addition regarded as a morphism from the genuine principal open in the affine
product chart. -/
noncomputable def secantAdditionOnProductOpen (W : WeierstrassCurve K) :
    (secantProductOpen W).toScheme ⟶ scheme W :=
  (secantChartIsoProductOpen W).inv ≫ secantAdditionProjectiveMorphism W

/-- The existing projective secant morphism factors through the genuine product open. -/
theorem secantAdditionProjectiveMorphism_factors_through_productOpen
    (W : WeierstrassCurve K) :
    secantAdditionProjectiveMorphism W =
      (secantChartIsoProductOpen W).hom ≫ secantAdditionOnProductOpen W := by
  simp [secantAdditionOnProductOpen]

/-- The projective secant-chart morphism respects the structural morphisms to the base field. -/
theorem secantAdditionProjectiveMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    secantAdditionProjectiveMorphism W ≫ structureMap W =
      secantChartStructureMap W := by
  let chartStructureMap : standardAffineChartScheme W ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W true))
  have hchart : standardSecantChartMap W ≫ structureMap W =
      chartStructureMap := standardSecantChartMap_comp_structureMap W
  have htarget : (affineEquationSchemeIsoStandardChart W).hom ≫
      chartStructureMap = secantTargetStructureMap W := by
    exact affineChartIso_comp_coveringStructureMap W
  simp only [secantAdditionProjectiveMorphism, Category.assoc,
    hchart, htarget,
    secantAdditionAffineMorphism_comp_structureMap]

/-- Secant addition on the affine product open is a morphism over the ground field. -/
theorem secantAdditionOnProductOpen_comp_structureMap
    (W : WeierstrassCurve K) :
    secantAdditionOnProductOpen W ≫ structureMap W =
      ((secantProductOpen W).ι ≫ pullback.fst _ _) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (secantTargetCoordinateRing W))) := by
  apply (cancel_epi (secantChartIsoProductOpen W).hom).1
  calc
    (secantChartIsoProductOpen W).hom ≫
        (secantAdditionOnProductOpen W ≫ structureMap W) =
      ((secantChartIsoProductOpen W).hom ≫
        secantAdditionOnProductOpen W) ≫ structureMap W :=
      (Category.assoc _ _ _).symm
    _ = secantAdditionProjectiveMorphism W ≫ structureMap W := by
      rw [← secantAdditionProjectiveMorphism_factors_through_productOpen]
    _ = secantChartStructureMap W :=
      secantAdditionProjectiveMorphism_comp_structureMap W
    _ = (((secantChartIsoProductOpen W).hom ≫
        (secantProductOpen W).ι) ≫ pullback.fst _ _) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantTargetCoordinateRing W))) :=
      (secantChartIsoProductOpen_hom_comp_ι_comp_structureMap W).symm
    _ = (secantChartIsoProductOpen W).hom ≫
        (((secantProductOpen W).ι ≫ pullback.fst _ _) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantTargetCoordinateRing W)))) := by
      simp only [Category.assoc]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
