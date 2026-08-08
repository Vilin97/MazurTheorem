/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.PicardAbelJacobi
import TauCeti.AlgebraicGeometry.RationalPoint.Degree
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth

/-!
# Abel--Jacobi classes of rational sections

`PicardAbelJacobi` constructs Abel--Jacobi classes from codimension-one points
of a curve and a proof that the chosen base point has weight one.  This file
supplies those inputs from an actual rational section of a smooth integral
curve over a field.

The non-genericity field records the geometric fact that the section lands at
a closed point rather than the generic point.  On a proper modular curve this
will come from the represented cusp or modular section.  Smooth relative
dimension one then makes that point codimension one, while the section law
proves that its residue degree is one.  The final definitions feed these
derived facts into the checked scheme-Picard Abel--Jacobi construction.

This is still a group-valued construction.  It neither represents `Pic⁰` nor
asserts that the resulting function on rational sections is induced by a
scheme morphism.
-/

namespace MazurTorsion.AlgebraicGeometry

universe u

open _root_.AlgebraicGeometry
open CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

/-- A rational section of an integral smooth relative curve, together with
the exact non-genericity fact needed to regard its image as a prime divisor.

The section equation is retained explicitly because it also proves that the
resulting prime divisor has residue degree one. -/
structure SmoothCurveRationalSection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 pi] where
  /-- The represented rational point. -/
  hom : Spec (.of K) ⟶ X
  /-- The rational point is a section of the structure morphism. -/
  hom_comp : hom ≫ pi = 𝟙 _
  /-- The represented point is not the generic point of the curve. -/
  ne_generic : hom (IsLocalRing.closedPoint K) ≠ genericPoint X

namespace SmoothCurveRationalSection

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [IsIntegral X]
variable {pi : X ⟶ Spec (.of K)} [SmoothOfRelativeDimension 1 pi]

/-- The codimension-one point underlying a rational section of a smooth
relative curve. -/
noncomputable def toCodimensionOnePoint
    (x : SmoothCurveRationalSection K X pi) :
    CodimensionOnePoint X :=
  ⟨x.hom (IsLocalRing.closedPoint K),
    SchemeWeilDivisor.coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one
      K X pi _ x.ne_generic⟩

@[simp]
theorem coe_toCodimensionOnePoint
    (x : SmoothCurveRationalSection K X pi) :
    (x.toCodimensionOnePoint : X) =
      x.hom (IsLocalRing.closedPoint K) :=
  rfl

/-- The prime divisor defined by a rational section has residue degree one
over the ground field. -/
@[simp]
theorem residueDegree_toCodimensionOnePoint
    (x : SmoothCurveRationalSection K X pi) :
    pi.residueDegree x.toCodimensionOnePoint.1 = 1 := by
  change pi.residueDegree (x.hom (IsLocalRing.closedPoint K)) = 1
  exact residueDegree_eq_one_of_section x.hom_comp
    (IsLocalRing.closedPoint K)

/-- In the integral weight used by the divisor product formula, a rational
section has weight one. -/
@[simp]
theorem residueDegree_int_toCodimensionOnePoint
    (x : SmoothCurveRationalSection K X pi) :
    (pi.residueDegree x.toCodimensionOnePoint.1 : ℤ) = 1 := by
  rw [x.residueDegree_toCodimensionOnePoint]
  norm_num

end SmoothCurveRationalSection

namespace PicardGroup

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
variable (pi : X ⟶ Spec (.of K)) [IsProper pi]
  [SmoothOfRelativeDimension 1 pi]

private noncomputable abbrev curveOrderSystem :=
  SchemeWeilDivisor.orderSystem X

private noncomputable abbrev curveWeight : CodimensionOnePoint X → ℤ :=
  fun x ↦ (pi.residueDegree x.1 : ℤ)

private theorem curveWeight_isWeightedDegreeZero :
    (curveOrderSystem (X := X)).IsWeightedDegreeZero
      (curveWeight pi) :=
  SchemeWeilDivisor.orderSystem_isWeightedDegreeZero K X pi

/-- The scheme-Picard Abel--Jacobi class of an actual rational section,
normalized at another actual rational section.

Both codimension-one facts and the weight-one normalization are derived from
the smooth-curve and section laws. -/
noncomputable def rationalSectionAbelJacobiClass
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 x : SmoothCurveRationalSection K X pi) :
    degreeZero (curveOrderSystem (X := X)) (curveWeight pi)
      (curveWeight_isWeightedDegreeZero pi) e :=
  weightedAbelJacobiClass
    (curveOrderSystem (X := X)) (curveWeight pi)
    (curveWeight_isWeightedDegreeZero pi) e
    x0.residueDegree_int_toCodimensionOnePoint x.toCodimensionOnePoint

/-- The normalizing rational section maps to zero in the actual degree-zero
scheme Picard group. -/
@[simp]
theorem rationalSectionAbelJacobiClass_base
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 : SmoothCurveRationalSection K X pi) :
    rationalSectionAbelJacobiClass pi e x0 x0 = 0 :=
  weightedAbelJacobiClass_base
    (curveOrderSystem (X := X)) (curveWeight pi)
    (curveWeight_isWeightedDegreeZero pi) e
    x0.residueDegree_int_toCodimensionOnePoint

/-- The difference of two rational-section Abel--Jacobi classes is the
scheme-Picard image of the corresponding point-difference divisor.  This is
the section-level downstream consumer of the new adapter. -/
theorem rationalSectionAbelJacobiClass_sub_coe
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 x y : SmoothCurveRationalSection K X pi) :
    (rationalSectionAbelJacobiClass pi e x0 x : PicardGroup X) -
        (rationalSectionAbelJacobiClass pi e x0 y : PicardGroup X) =
      e ((curveOrderSystem (X := X)).divisorClass
        (pointDifference x.toCodimensionOnePoint
          y.toCodimensionOnePoint)) := by
  apply weightedAbelJacobiClass_sub_coe
    (curveOrderSystem (X := X)) (curveWeight pi)
    (curveWeight_isWeightedDegreeZero pi) e
    x0.residueDegree_int_toCodimensionOnePoint
  change (pi.residueDegree x.toCodimensionOnePoint.1 : ℤ) =
    (pi.residueDegree y.toCodimensionOnePoint.1 : ℤ)
  rw [x.residueDegree_int_toCodimensionOnePoint,
    y.residueDegree_int_toCodimensionOnePoint]

/-- Equality of the Abel--Jacobi classes of two represented rational
sections is exactly linear equivalence of their basepoint-corrected prime
divisors. -/
theorem rationalSectionAbelJacobiClass_eq_iff_linearlyEquivalent
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 x y : SmoothCurveRationalSection K X pi) :
    rationalSectionAbelJacobiClass pi e x0 x =
        rationalSectionAbelJacobiClass pi e x0 y ↔
      (curveOrderSystem (X := X)).LinearlyEquivalent
        (weightedPointBaseDifference (curveWeight pi)
          x0.toCodimensionOnePoint x.toCodimensionOnePoint)
        (weightedPointBaseDifference (curveWeight pi)
          x0.toCodimensionOnePoint y.toCodimensionOnePoint) :=
  weightedAbelJacobiClass_eq_iff_linearlyEquivalent
    (curveOrderSystem (X := X)) (curveWeight pi)
    (curveWeight_isWeightedDegreeZero pi) e
    x0.residueDegree_int_toCodimensionOnePoint

end PicardGroup

end MazurTorsion.AlgebraicGeometry
