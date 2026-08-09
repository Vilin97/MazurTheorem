/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.FiniteType

/-!
# Properness of the universal projective Tate family

The degree-zero part of the homogeneous Weierstrass coordinate ring is the
base ring.  Evaluation at `[0 : 1 : 0]` gives a left inverse, while the generic
degree-zero surjectivity theorem for homogeneous polynomial quotients gives a
right inverse.  Consequently the projective structure map is Mathlib's proper
`Proj.toSpecZero` followed by an isomorphism.

The proof is adapted from the clean properness prefix of AINTLIB's
`EllipticCurve/WeierstrassModel.lean`; exact provenance is recorded in
`PORTING.md`. No smoothness or group-law assertion is made here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdeal

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section GenericModel

variable {A : Type u} [CommRing A]

private theorem infinity_eval_polynomial_generic (W : WeierstrassCurve A) :
    MvPolynomial.eval ![0, 1, 0] W.toProjective.polynomial = 0 := by
  change W.toProjective.Equation ![0, 1, 0]
  exact W.toProjective.equation_zero

/-- Evaluation at infinity on the homogeneous coordinate quotient. -/
noncomputable def infinityEval (W : WeierstrassCurve A) :
    coordinateRing W →+* A :=
  coordinateEval W ![0, 1, 0] (infinity_eval_polynomial_generic W)

/-- Evaluation at infinity retracts the degree-zero base map. -/
@[simp]
theorem infinityEval_algebraMapGradeZero (W : WeierstrassCurve A) (a : A) :
    infinityEval W
      (algebraMap (↥(quotientGrading (ideal W) 0)) (coordinateRing W)
        (algebraMapGradeZero (ideal W) a)) = a :=
  coordinateEval_algebraMapGradeZero W ![0, 1, 0]
    (infinity_eval_polynomial_generic W) a

/-- The base ring is canonically the degree-zero part of the homogeneous
Weierstrass coordinate quotient. -/
theorem algebraMapGradeZero_bijective (W : WeierstrassCurve A) :
    Function.Bijective (algebraMapGradeZero (ideal W)) := by
  constructor
  · exact Function.LeftInverse.injective
      (g := fun x ↦ infinityEval W
        (algebraMap (↥(quotientGrading (ideal W) 0)) (coordinateRing W) x))
      (infinityEval_algebraMapGradeZero W)
  · exact algebraMapGradeZero_surjective_mvPolynomial (ideal W)

/-- The degree-zero identification as a ring equivalence. -/
noncomputable def gradeZeroRingEquiv (W : WeierstrassCurve A) :
    A ≃+* ↥(quotientGrading (ideal W) 0) :=
  RingEquiv.ofBijective _ (algebraMapGradeZero_bijective W)

noncomputable instance projection_baseMap_isIso (W : WeierstrassCurve A) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (ideal W)))) := by
  have h : CommRingCat.ofHom (algebraMapGradeZero (ideal W)) =
      (gradeZeroRingEquiv W).toCommRingCatIso.hom := rfl
  rw [h]
  infer_instance

instance coordinateRing_finiteType (W : WeierstrassCurve A) :
    Algebra.FiniteType (↥(quotientGrading (ideal W) 0))
      (coordinateRing W) := by
  haveI : Algebra.FiniteType A (coordinateRing W) :=
    Algebra.FiniteType.of_surjective
      (Ideal.Quotient.mkₐ A (ideal W).toIdeal)
      (Ideal.Quotient.mkₐ_surjective A _)
  exact Algebra.FiniteType.of_restrictScalars_finiteType A
    (↥(quotientGrading (ideal W) 0)) (coordinateRing W)

/-- Every scheme-theoretic projective Weierstrass hypersurface is proper over
its coefficient ring. -/
instance projection_isProper (W : WeierstrassCurve A) :
    IsProper (projection W) := by
  unfold projection
  haveI hProj : IsProper (Proj.toSpecZero (quotientGrading (ideal W))) :=
    inferInstance
  haveI hBase : IsProper
      (Spec.map (CommRingCat.ofHom (algebraMapGradeZero (ideal W)))) :=
    inferInstance
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ hProj hBase

end GenericModel

section UniversalTate

variable (R : CommRingCat.{u})

/-- The universal projective Tate family is proper over its affine parameter
base. -/
instance familyProjection_isProper : IsProper (familyProjection R) := by
  unfold familyProjection
  infer_instance

end UniversalTate

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
