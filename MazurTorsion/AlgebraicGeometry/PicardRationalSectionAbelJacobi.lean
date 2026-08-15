/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.PicardAbelJacobi
import MazurTorsion.AlgebraicGeometry.RelativePicardFppf
import MazurTorsion.AlgebraicGeometry.SmoothCurveRationalSection
import TauCeti.AlgebraicGeometry.RationalPoint.Degree
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth

/-!
# Abel--Jacobi classes of rational sections

`PicardAbelJacobi` constructs Abel--Jacobi classes from codimension-one points
of a curve and a proof that the chosen base point has weight one.  This file
supplies those inputs from an actual rational section of a smooth integral
curve over a field.

The section law itself makes the represented point a closed immersion.  If
that point were generic, integrality would force the whole curve to be that
one point and the structure map to be an isomorphism.  This contradicts
smooth relative dimension one: a standard-smooth chart would then have
Kähler differentials of both rank one and rank zero.  Thus non-genericity is
derived rather than supplied by callers.  Smooth relative dimension one then
makes the point codimension one, while the section law proves that its residue
degree is one.  The final definitions feed these facts into the checked
scheme-Picard Abel--Jacobi construction.

This is still a group-valued construction.  It neither represents `Pic⁰` nor
asserts that the resulting function on rational sections is induced by a
scheme morphism.
-/

namespace MazurTorsion.AlgebraicGeometry

universe u v

open _root_.AlgebraicGeometry
open CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

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

/-- The Abel--Jacobi class of a rational section in the actual degree-zero
image of a supplied divisor-class-to-Picard homomorphism. -/
noncomputable def rationalSectionAbelJacobiClassImage
    (φ : (curveOrderSystem (X := X)).ClassGroup →+ PicardGroup X)
    (x0 x : SmoothCurveRationalSection K X pi) :
    degreeZeroImage (curveOrderSystem (X := X)) (curveWeight pi)
      (curveWeight_isWeightedDegreeZero pi) φ :=
  weightedAbelJacobiClassImage
    (curveOrderSystem (X := X)) (curveWeight pi)
    (curveWeight_isWeightedDegreeZero pi) φ
    x0.residueDegree_int_toCodimensionOnePoint x.toCodimensionOnePoint

/-- The underlying Picard value of a rational-section Abel--Jacobi image is
the image of the honest point-difference divisor class. -/
@[simp]
theorem coe_rationalSectionAbelJacobiClassImage
    (φ : (curveOrderSystem (X := X)).ClassGroup →+ PicardGroup X)
    (x0 x : SmoothCurveRationalSection K X pi) :
    (rationalSectionAbelJacobiClassImage pi φ x0 x : PicardGroup X) =
      φ ((curveOrderSystem (X := X)).divisorClass
        (pointDifference x.toCodimensionOnePoint
          x0.toCodimensionOnePoint)) := by
  rw [rationalSectionAbelJacobiClassImage,
    coe_weightedAbelJacobiClassImage,
    weightedPointBaseDifference_eq_pointDifference_of_weight_eq_one
      (w := curveWeight pi) (x₀ := x0.toCodimensionOnePoint)
      (x := x.toCodimensionOnePoint)
      x.residueDegree_int_toCodimensionOnePoint]

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

/-! ### Classes in the associated all-degree fppf sheafification -/

/-- Restrict the canonical map from the absolute Picard group to the
associated fppf sheafification at the base object to the existing absolute
degree-zero subgroup determined by the supplied `DivisorPicard.ClassEquivalence`.

This is not a relative degree-zero subfunctor: it neither constructs the supplied
class equivalence nor a relative degree map compatible with base change. -/
private noncomputable def degreeZeroToPicRelFppfAtBase
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 : SmoothCurveRationalSection K X pi) :
    degreeZero (curveOrderSystem (X := X)) (curveWeight pi)
        (curveWeight_isWeightedDegreeZero pi) e →+
      (Scheme.Modules.picRelFppfSheaf pi x0.hom x0.hom_comp).obj.obj
        (Opposite.op (Over.mk (𝟙 (Spec (.of K))))) :=
  (Scheme.Modules.picRelFppfClassAtBaseHom
    pi x0.hom x0.hom_comp).comp
      (degreeZero (curveOrderSystem (X := X)) (curveWeight pi)
        (curveWeight_isWeightedDegreeZero pi) e).subtype

/-- Map the rational-section Abel--Jacobi class into the associated fppf sheafification of
the zero-section-normalized Picard presheaf at the base. This depends on the supplied
`DivisorPicard.ClassEquivalence`; no representing Jacobian or scheme morphism is asserted. -/
noncomputable def rationalSectionAbelJacobiPicRelFppfClass
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 x : SmoothCurveRationalSection K X pi) :
    (Scheme.Modules.picRelFppfSheaf pi x0.hom x0.hom_comp).obj.obj
      (Opposite.op (Over.mk (𝟙 (Spec (.of K))))) :=
  degreeZeroToPicRelFppfAtBase pi e x0
    (rationalSectionAbelJacobiClass pi e x0 x)

/-- The normalizing section maps to zero after passage to the associated fppf
sheafification. -/
@[simp]
theorem rationalSectionAbelJacobiPicRelFppfClass_base
    (e : DivisorPicard.ClassEquivalence (curveOrderSystem (X := X)) X)
    (x0 : SmoothCurveRationalSection K X pi) :
    rationalSectionAbelJacobiPicRelFppfClass pi e x0 x0 = 0 := by
  rw [rationalSectionAbelJacobiPicRelFppfClass,
    rationalSectionAbelJacobiClass_base, map_zero]

/-- The difference of two rational-section Abel--Jacobi classes is the
scheme-Picard image of the corresponding point-difference divisor.  This is a
section-level compatibility theorem for the absolute divisor-class transport. -/
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

namespace CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse

open TopologicalSpace

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
variable (pi : X ⟶ Spec (.of K)) [IsProper pi]
  [SmoothOfRelativeDimension 1 pi]

/-- A rational section valued in the degree-zero Picard image arising from
the actual global-principal-boundary divisor construction.  This is a
compiled section-level consumer of the no-surjectivity image interface. -/
noncomputable def
    rationalSectionAbelJacobiClassImageOfGlobalPrincipalBoundary
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h
      (SchemeWeilDivisor.orderSystem X) C heffective)
    (x0 x : SmoothCurveRationalSection K X pi) :
    degreeZeroImageOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h (SchemeWeilDivisor.orderSystem X)
        C heffective hadd b (fun z ↦ (pi.residueDegree z.1 : ℤ))
        (SchemeWeilDivisor.orderSystem_isWeightedDegreeZero K X pi) :=
  PicardGroup.rationalSectionAbelJacobiClassImage pi
    (classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h (SchemeWeilDivisor.orderSystem X)
        C heffective hadd b) x0 x

/-- The underlying value of the rational-section image class is exactly the
Picard class of the descended point-difference line bundle. -/
@[simp]
theorem
    coe_rationalSectionAbelJacobiClassImageOfGlobalPrincipalBoundary
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h
      (SchemeWeilDivisor.orderSystem X) C heffective)
    (x0 x : SmoothCurveRationalSection K X pi) :
    (rationalSectionAbelJacobiClassImageOfGlobalPrincipalBoundary
        pi U hnonempty hcover hU h C heffective hadd b x0 x :
      PicardGroup X) =
      divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h (SchemeWeilDivisor.orderSystem X)
          C heffective hadd b
          (pointDifference x.toCodimensionOnePoint
            x0.toCodimensionOnePoint) := by
  rw [rationalSectionAbelJacobiClassImageOfGlobalPrincipalBoundary,
    PicardGroup.coe_rationalSectionAbelJacobiClassImage,
    classToPicOfGlobalPrincipalBoundary_divisorClass]

end CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse

end MazurTorsion.AlgebraicGeometry
