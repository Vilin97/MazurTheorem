/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveNegation
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointComparison

/-!
# Negation on projective Weierstrass scheme points

This file proves that the homogeneous involution on the concrete reduced cubic induces Mathlib's
negation on its `K`-valued points.  The proof compares the homogeneous prime at the unique closed
point of `Spec K`; it does not assume a group-object structure on the cubic.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Evaluating the three homogeneous negation coordinates gives Mathlib's projective negation. -/
theorem eval_negationCoordinates (W : WeierstrassCurve K) (P : Fin 3 → K) :
    (fun i ↦ MvPolynomial.eval P (negationCoordinates W i)) =
      W.toProjective.neg P := by
  funext i
  fin_cases i <;>
    simp [negationCoordinates, WeierstrassCurve.Projective.neg,
      WeierstrassCurve.Projective.negY, WeierstrassCurve.map]

/-- Evaluation commutes with the homogeneous coordinate-ring substitution for negation. -/
theorem eval_negationRingHom (W : WeierstrassCurve K) (P : Fin 3 → K)
    (q : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval P (negationRingHom W q) =
      MvPolynomial.eval (W.toProjective.neg P) q := by
  rw [← eval_negationCoordinates W P]
  change MvPolynomial.eval P
      (MvPolynomial.eval₂ MvPolynomial.C (negationCoordinates W) q) = _
  exact (MvPolynomial.eval_assoc (negationCoordinates W) P q).symm

/-- At the closed point, composing a homogeneous-coordinate point with ambient negation
produces the point represented by the negated coordinates. -/
theorem ambientPoint_comp_ambientNegation_closedPoint
    (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) :
    (ambientPoint P (nonsingular_ne_zero W P hP) ≫ ambientNegation W)
        (IsLocalRing.closedPoint K) =
      ambientPoint (W.toProjective.neg P)
        (nonsingular_ne_zero W _ (W.toProjective.nonsingular_neg hP))
        (IsLocalRing.closedPoint K) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n q hq
  cases n with
  | zero =>
      rw [mem_projective_degree_zero_iff_eq_zero _ q hq,
        mem_projective_degree_zero_iff_eq_zero _ q hq]
  | succ n =>
      change negationRingHom W q ∈
          (ambientPoint P (nonsingular_ne_zero W P hP)
            (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔ _
      rw [mem_ambientPoint_closedPoint_iff P (nonsingular_ne_zero W P hP)
          (negationRingHom W q) (Nat.succ_pos n) ((negationGraded W).map_mem hq),
        mem_ambientPoint_closedPoint_iff (W.toProjective.neg P)
          (nonsingular_ne_zero W _ (W.toProjective.nonsingular_neg hP))
          q (Nat.succ_pos n) hq,
        eval_negationRingHom]

/-- The ambient projective-plane morphism underlying a point followed by cubic negation is its
ambient morphism followed by homogeneous negation. -/
theorem ambientMorphismOfOverPoint_comp_negationOver
    (W : WeierstrassCurve K)
    (g : AffineCommGroupScheme.testObject (R := K) K ⟶ toOver W) :
    ambientMorphismOfOverPoint W (g ≫ negationOver W) =
      ambientMorphismOfOverPoint W g ≫ ambientNegation W := by
  let gleft : Spec (.of K) ⟶ scheme W := g.left
  have hcomp := congrArg (fun f ↦ gleft ≫ f) (negation_comp_inclusion W)
  have hleft : (negationOver W).left = negation W := rfl
  dsimp only [ambientMorphismOfOverPoint]
  rw [Over.comp_left, hleft]
  change (gleft ≫ negation W) ≫ inclusion W =
    (gleft ≫ inclusion W) ≫ ambientNegation W
  simpa only [Category.assoc] using hcomp

/-- The ambient morphism of a point constructed from coordinates is the corresponding
homogeneous-coordinate morphism. -/
theorem ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative
    (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) :
    ambientMorphismOfOverPoint W
        (pointOverOfNonsingularRepresentative W P hP) =
      ambientPoint P (nonsingular_ne_zero W P hP) := by
  change pointOfNonsingularRepresentative W P hP ≫ inclusion W = _
  exact pointOfNonsingularRepresentative_comp_inclusion W P hP

/-- Unit-equivalent nonsingular triples define the same point of the concrete cubic. -/
theorem pointOverOfNonsingularRepresentative_eq_of_equiv
    (W : WeierstrassCurve K) (P Q : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P)
    (hQ : W.toProjective.Nonsingular Q) (hPQ : P ≈ Q) :
    pointOverOfNonsingularRepresentative W P hP =
      pointOverOfNonsingularRepresentative W Q hQ := by
  apply overPoint_eq_of_ambientClosedPoint_eq W
  rw [ambientClosedPointOfOverPoint, ambientClosedPointOfOverPoint,
    ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative,
    ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative]
  exact ambientPoint_closedPoint_eq_of_equiv P Q
    (nonsingular_ne_zero W P hP) (nonsingular_ne_zero W Q hQ) hPQ

/-- A nonsingular homogeneous representative followed by scheme negation is represented by the
negated homogeneous triple. -/
theorem pointOverOfNonsingularRepresentative_comp_negationOver
    (W : WeierstrassCurve K) (P : Fin 3 → K)
    (hP : W.toProjective.Nonsingular P) :
    pointOverOfNonsingularRepresentative W P hP ≫ negationOver W =
      pointOverOfNonsingularRepresentative W (W.toProjective.neg P)
        (W.toProjective.nonsingular_neg hP) := by
  apply overPoint_eq_of_ambientClosedPoint_eq W
  rw [ambientClosedPointOfOverPoint, ambientClosedPointOfOverPoint,
    ambientMorphismOfOverPoint_comp_negationOver,
    ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative,
    ambientMorphismOfOverPoint_pointOverOfNonsingularRepresentative]
  exact ambientPoint_comp_ambientNegation_closedPoint W P hP

/-- The coordinate construction sends affine Weierstrass negation to the scheme involution. -/
theorem affinePointOverMorphism_neg (W : WeierstrassCurve K)
    (P : W.toAffine.Point) :
    affinePointOverMorphism W (-P) =
      affinePointOverMorphism W P ≫ negationOver W := by
  cases P with
  | zero =>
      change pointOverOfNonsingularRepresentative W ![0, 1, 0]
          W.toProjective.nonsingular_zero =
        pointOverOfNonsingularRepresentative W ![0, 1, 0]
            W.toProjective.nonsingular_zero ≫ negationOver W
      rw [pointOverOfNonsingularRepresentative_comp_negationOver]
      apply pointOverOfNonsingularRepresentative_eq_of_equiv
      exact Setoid.symm (W.toProjective.equiv_zero_of_Z_eq_zero
        (W.toProjective.nonsingular_neg W.toProjective.nonsingular_zero) rfl)
  | some x y h =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      change pointOverOfNonsingularRepresentative W
          ![x, W.toAffine.negY x y, 1]
            ((W.toProjective.nonsingular_some x (W.toAffine.negY x y)).mpr
              ((W.toAffine.nonsingular_neg x y).mpr h)) =
        pointOverOfNonsingularRepresentative W ![x, y, 1]
            ((W.toProjective.nonsingular_some x y).mpr h) ≫ negationOver W
      rw [pointOverOfNonsingularRepresentative_comp_negationOver]
      apply pointOverOfNonsingularRepresentative_eq_of_equiv
      refine ⟨1, ?_⟩
      funext i
      fin_cases i <;>
        simp [WeierstrassCurve.Projective.neg,
          WeierstrassCurve.Projective.negY,
          WeierstrassCurve.Affine.negY]

/-- The canonical comparison from Mathlib projective points to scheme-valued points intertwines
Mathlib negation with the homogeneous involution on the concrete reduced cubic. -/
@[simp]
theorem projectivePointOverMorphism_neg (W : WeierstrassCurve K)
    (P : W.toProjective.Point) :
    projectivePointOverMorphism W (-P) =
      projectivePointOverMorphism W P ≫ negationOver W := by
  change affinePointOverMorphism W (-P).toAffineLift =
    affinePointOverMorphism W P.toAffineLift ≫ negationOver W
  rw [WeierstrassCurve.Projective.Point.toAffineLift_neg,
    affinePointOverMorphism_neg]

/-- If a future group-object construction identifies its inverse morphism with the checked
homogeneous involution, the canonical point comparison preserves inverses.  This is the exact
consumer expected from a pointed Picard/Jacobian construction; it does not assume or construct
the multiplication morphism. -/
theorem projectivePointOverMorphism_inv_of_inv_eq_negation
    (W : WeierstrassCurve K) [GrpObj (toOver W)]
    (hinv : ι[toOver W] = negationOver W) (P : W.toProjective.Point) :
    projectivePointOverMorphism W (-P) =
      (projectivePointOverMorphism W P)⁻¹ := by
  rw [projectivePointOverMorphism_neg, CategoryTheory.Hom.inv_def, hinv]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
