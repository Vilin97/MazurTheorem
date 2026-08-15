/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicReducedBaseChange
import MazurTorsion.ModularCurve.XZeroWeierstrassSecantAddition

/-!
# The scheme morphism on the secant addition chart

The denominator-cleared identities in `XZeroWeierstrassSecantAddition` induce a genuine morphism
from the explicit four-coordinate presentation localized at `x₁ - x₂` to the concrete projective
Weierstrass cubic.  To use it as one chart of multiplication, that presentation must still be
identified with the corresponding open of the scheme product.  A group object additionally needs
the tangent and infinity charts, a cover and overlap proofs, gluing, and the group axioms.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

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

/-- The secant chart maps into the actual reduced projective Weierstrass cubic through its
standard affine open. -/
def secantAdditionProjectiveMorphism (W : WeierstrassCurve K) :
    Spec (.of (secantChartCoordinateRing W)) ⟶ scheme W :=
  secantAdditionAffineMorphism W ≫
    (affineEquationSchemeIsoStandardChart W).hom ≫
    coveringChartMap W true

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
