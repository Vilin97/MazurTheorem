/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointNegation

/-!
# The point at infinity on the projective Weierstrass cubic

This file realizes `[0 : 1 : 0]` as a section of the concrete projective cubic over its base.
The section has the tensor unit of `Over (Spec K)` as its source, so it has exactly the type of
the unit of a future group-object structure.  It is fixed by the already constructed homogeneous
negation involution.

We also compare the section with the canonical Mathlib projective zero after passing through the
canonical isomorphism from the tensor unit to the affine self-test object.  This is scheme-level
pointed geometry: no multiplication morphism or group-object structure is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The tensor unit over `Spec K` is canonically isomorphic to the affine self-test object.
The latter uses `Spec.map (algebraMap K K)` as its structure map rather than the identity. -/
noncomputable def tensorUnitIsoSelfTestObject :
    𝟙_ (Over (Spec (.of K))) ≅
      AffineCommGroupScheme.testObject (R := K) K :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 (Spec (.of K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K))
    rw [Category.id_comp, ← Spec.map_id, Spec.map_injective.eq_iff]
    ext r
    exact Algebra.algebraMap_self_apply r)

/-- The point at infinity `[0 : 1 : 0]` as an actual section of the concrete cubic over
`Spec K`. -/
noncomputable def infinitySectionOver (W : WeierstrassCurve K) :
    𝟙_ (Over (Spec (.of K))) ⟶ toOver W :=
  Over.homMk
    (pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero)
    (by
      change pointOfNonsingularRepresentative W ![0, 1, 0]
          W.toProjective.nonsingular_zero ≫ structureMap W = 𝟙 _
      exact pointOfNonsingularRepresentative_comp_structureMap W _ _)

@[simp]
theorem infinitySectionOver_left (W : WeierstrassCurve K) :
    (infinitySectionOver W).left =
      pointOfNonsingularRepresentative W ![0, 1, 0]
        W.toProjective.nonsingular_zero :=
  rfl

/-- The scheme section at infinity is the canonical coordinate zero, after changing from the
tensor unit to the affine self-test object. -/
@[simp]
theorem tensorUnitIsoSelfTestObject_hom_comp_projectivePointOverMorphism_zero
    (W : WeierstrassCurve K) :
    (tensorUnitIsoSelfTestObject (K := K)).hom ≫
        projectivePointOverMorphism W 0 =
      infinitySectionOver W := by
  ext
  simp only [tensorUnitIsoSelfTestObject, projectivePointOverMorphism,
    WeierstrassCurve.Projective.Point.toAffineLift_zero,
    affinePointOverMorphism, infinitySectionOver, Over.comp_left]
  change 𝟙 (Spec (.of K)) ≫
      pointOfNonsingularRepresentative W ![0, 1, 0]
        W.toProjective.nonsingular_zero =
    pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero
  rw [Category.id_comp]

/-- The actual homogeneous negation morphism fixes the section at infinity. -/
@[simp]
theorem infinitySectionOver_comp_negationOver (W : WeierstrassCurve K) :
    infinitySectionOver W ≫ negationOver W = infinitySectionOver W := by
  ext
  change pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero ≫ negation W =
    pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero
  have hpoint := projectivePointOverMorphism_neg W (0 : W.toProjective.Point)
  rw [neg_zero] at hpoint
  have h := congrArg (fun f ↦ f.left) hpoint
  simp only [projectivePointOverMorphism,
    WeierstrassCurve.Projective.Point.toAffineLift_zero] at h
  change pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero =
    pointOfNonsingularRepresentative W ![0, 1, 0]
      W.toProjective.nonsingular_zero ≫ negation W at h
  exact h.symm

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
