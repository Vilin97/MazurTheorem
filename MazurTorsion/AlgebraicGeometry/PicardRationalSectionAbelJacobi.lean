/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.PicardAbelJacobi
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
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

universe u

open _root_.AlgebraicGeometry
open CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

/-- A rational section of an integral smooth relative curve.  Its section
equation will derive both non-genericity and residue degree one. -/
structure SmoothCurveRationalSection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 pi] where
  /-- The represented rational point. -/
  hom : Spec (.of K) ⟶ X
  /-- The rational point is a section of the structure morphism. -/
  hom_comp : hom ≫ pi = 𝟙 _

namespace SmoothCurveRationalSection

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [IsIntegral X]
variable {pi : X ⟶ Spec (.of K)} [SmoothOfRelativeDimension 1 pi]

/-- A section of an integral smooth relative curve cannot land at its generic
point.  The section is a closed immersion.  If its image were generic, that
closed image would be all of the integral curve, making both the section and
the structure map isomorphisms.  A relative-dimension-one standard-smooth
chart would then have Kähler differentials of ranks one and zero. -/
theorem ne_generic (x : SmoothCurveRationalSection K X pi) :
    x.hom (IsLocalRing.closedPoint K) ≠ genericPoint X := by
  letI : IsClosedImmersion x.hom :=
    isClosedImmersion_of_comp_eq_id pi x.hom x.hom_comp
  intro hgeneric
  have hrange : Set.range x.hom = Set.univ := by
    have hclosed : IsClosed (Set.range x.hom) :=
      x.hom.isClosedEmbedding.isClosed_range
    have hrangeSingleton : Set.range x.hom = {genericPoint X} := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        rw [Set.mem_singleton_iff]
        exact (congrArg x.hom (Subsingleton.elim z
          (IsLocalRing.closedPoint K))).trans hgeneric
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨IsLocalRing.closedPoint K, hgeneric.trans hy.symm⟩
    calc
      Set.range x.hom = closure (Set.range x.hom) :=
        hclosed.closure_eq.symm
      _ = closure ({genericPoint X} : Set X) :=
        congrArg closure hrangeSingleton
      _ = Set.univ := genericPoint_closure X
  letI : Surjective x.hom := ⟨Set.range_eq_univ.mp hrange⟩
  letI : Subsingleton X :=
    Function.Surjective.subsingleton x.hom.surjective
  letI : IsIso x.hom :=
    isIso_of_isClosedImmersion_of_surjective x.hom
  haveI : IsIso (x.hom ≫ pi) := by
    rw [x.hom_comp]
    infer_instance
  letI : IsIso pi := IsIso.of_isIso_comp_left x.hom pi
  obtain ⟨U, -, V, -, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := pi) (x.hom (IsLocalRing.closedPoint K))
  have hUtop : U = ⊤ := by
    have hfx : pi (x.hom (IsLocalRing.closedPoint K)) ∈ U := e hx
    apply top_unique
    intro y _
    exact Subsingleton.elim y
      (pi (x.hom (IsLocalRing.closedPoint K))) ▸ hfx
  have hVtop : V = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y
      (x.hom (IsLocalRing.closedPoint K))] using hx
  subst U
  subst V
  have hstdTop :
      RingHom.IsStandardSmoothOfRelativeDimension 1 pi.appTop.hom := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
    exact (pi.appLE_congr e rfl (by simp)
      (fun f ↦ RingHom.IsStandardSmoothOfRelativeDimension 1 f.hom)).mp hstd
  letI : IsIso pi.appTop := by
    apply Scheme.Hom.isIso_app pi ⊤
    rw [Scheme.Hom.opensRange_of_isIso]
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    pi.appTop.hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      Γ(Spec (.of K), ⊤) Γ(X, ⊤) := hstdTop.toAlgebra
  have hbij : Function.Bijective pi.appTop.hom :=
    (ConcreteCategory.isIso_iff_bijective pi.appTop).mp inferInstance
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective hbij
  have hzero :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := Γ(Spec (.of K), ⊤)) (S := Γ(X, ⊤)) 0
  have hone :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := Γ(Spec (.of K), ⊤)) (S := Γ(X, ⊤)) 1
  rw [hzero] at hone
  norm_num at hone

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
