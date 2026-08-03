/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.PicardDegreeZero
import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Sum.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.BasepointChange

/-!
# Abel--Jacobi classes in the scheme Picard group

Tau Ceti constructs the Abel--Jacobi class of a point in the abstract weighted degree-zero
divisor class group.  `PicardDegreeZero` transports that group through a checked
divisor-class/Picard equivalence.  This file composes the two constructions, producing the
point-level and divisor-level Abel--Jacobi maps in the actual Picard group of a scheme.

This is still the group-valued shadow of the geometric Abel--Jacobi morphism.  It does not claim
representability of `Pic⁰`, construct a Jacobian variety, or turn the point function into a scheme
morphism.  Those are the remaining `MT-TC-E1-JACOBIAN-VARIETY` and `MT-TC-F1-ABEL-JACOBI`
obligations.  The formulas here are the normalization and divisor-class consumers those later
constructions must recover.
-/

namespace MazurTorsion.AlgebraicGeometry

universe u v

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

namespace PicardGroup

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]

/-- The weighted Abel--Jacobi class of a point, transported to the degree-zero subgroup of the
scheme Picard group. -/
noncomputable def weightedAbelJacobiClass
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (x : Y) :
    degreeZero S w h e :=
  picZeroEquiv S w h e (S.weightedAbelJacobiClass w h hx₀ x)

/-- The underlying Picard class is the image of the degree-corrected point divisor. -/
@[simp]
lemma coe_weightedAbelJacobiClass
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (x : Y) :
    (weightedAbelJacobiClass S w h e hx₀ x : PicardGroup X) =
      e (S.divisorClass (weightedPointBaseDifference w x₀ x)) :=
  rfl

/-- The base point maps to zero in the absolute degree-zero Picard group. -/
@[simp]
lemma weightedAbelJacobiClass_base
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) :
    weightedAbelJacobiClass S w h e hx₀ x₀ = 0 := by
  rw [weightedAbelJacobiClass, S.weightedAbelJacobiClass_base]
  exact map_zero (picZeroEquiv S w h e)

/-- Collision of two transported Abel--Jacobi point classes is exactly linear equivalence of
their degree-corrected point divisors. -/
lemma weightedAbelJacobiClass_eq_iff_linearlyEquivalent
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) {x y : Y} :
    weightedAbelJacobiClass S w h e hx₀ x =
        weightedAbelJacobiClass S w h e hx₀ y ↔
      S.LinearlyEquivalent (weightedPointBaseDifference w x₀ x)
        (weightedPointBaseDifference w x₀ y) := by
  constructor
  · intro hxy
    apply (S.weightedAbelJacobiClass_eq_iff_linearlyEquivalent w h hx₀).mp
    exact (picZeroEquiv S w h e).injective hxy
  · intro hxy
    apply congrArg (picZeroEquiv S w h e)
    exact (S.weightedAbelJacobiClass_eq_iff_linearlyEquivalent w h hx₀).mpr hxy

/-- For two points of equal weight, the difference of their absolute Abel--Jacobi classes is
the Picard image of the divisor `[x] - [y]`. -/
lemma weightedAbelJacobiClass_sub_coe
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ x y : Y} (hx₀ : w x₀ = 1) (hxy : w x = w y) :
    (weightedAbelJacobiClass S w h e hx₀ x : PicardGroup X) -
        (weightedAbelJacobiClass S w h e hx₀ y : PicardGroup X) =
      e (S.divisorClass (pointDifference x y)) := by
  rw [coe_weightedAbelJacobiClass, coe_weightedAbelJacobiClass, ← map_sub]
  exact congrArg e (S.weightedAbelJacobiClass_sub_coe w h hx₀ hxy)

/-- The additive Abel--Jacobi map on divisors, transported to the scheme Picard group. -/
noncomputable def weightedAbelJacobiDivisorClass
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) :
    WeilDivisor Y →+ degreeZero S w h e :=
  (picZeroEquiv S w h e).toAddMonoidHom.comp
    (S.weightedAbelJacobiDivisorClass w h hx₀)

/-- The underlying Picard class of a divisor is its degree-corrected divisor class. -/
@[simp]
lemma coe_weightedAbelJacobiDivisorClass_apply
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (D : WeilDivisor Y) :
    (weightedAbelJacobiDivisorClass S w h e hx₀ D : PicardGroup X) =
      e (S.divisorClass (D - weightedDegree w D • ofPoint x₀)) := by
  change e ((S.weightedAbelJacobiDivisorClass w h hx₀ D : S.ClassGroup)) = _
  rw [S.coe_weightedAbelJacobiDivisorClass_apply]

/-- On a point divisor, the divisor-level construction is the transported point class.  This
is the downstream normalization consumer for both Abel--Jacobi interfaces. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_ofPoint
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (x : Y) :
    weightedAbelJacobiDivisorClass S w h e hx₀ (ofPoint x) =
      weightedAbelJacobiClass S w h e hx₀ x := by
  change picZeroEquiv S w h e
      (S.weightedAbelJacobiDivisorClass w h hx₀ (ofPoint x)) =
    picZeroEquiv S w h e (S.weightedAbelJacobiClass w h hx₀ x)
  rw [S.weightedAbelJacobiDivisorClass_ofPoint]

/-- Principal divisors map to zero under the absolute Abel--Jacobi divisor map. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_principalDivisor
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (g : G) :
    weightedAbelJacobiDivisorClass S w h e hx₀ (S.principalDivisor g) = 0 := by
  change picZeroEquiv S w h e
      (S.weightedAbelJacobiDivisorClass w h hx₀ (S.principalDivisor g)) = 0
  rw [S.weightedAbelJacobiDivisorClass_principalDivisor, map_zero]

end PicardGroup

namespace DivisorPicard.Dictionary

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]
variable {S : WeilDivisor.OrderSystem Y G}

/-- The divisor dictionary's chosen line-bundle representative of a weighted Abel--Jacobi
point class. -/
noncomputable def weightedAbelJacobiLineBundle
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) {x₀ : Y} (x : Y) : InvertibleSheaf X :=
  d.lineBundle (weightedPointBaseDifference w x₀ x)

/-- The chosen Abel--Jacobi line bundle represents the transported point class in absolute
`Pic⁰`. This is the divisor-line-bundle dictionary consumer of the point-level interface. -/
@[simp]
lemma weightedAbelJacobiLineBundle_toPic
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : Y} (hx₀ : w x₀ = 1) (x : Y) :
    Additive.ofMul
        (d.comparison.toPic (d.weightedAbelJacobiLineBundle w (x₀ := x₀) x)) =
      (PicardGroup.weightedAbelJacobiClass
        S w h d.classEquivalence hx₀ x : PicardGroup X) := by
  rw [weightedAbelJacobiLineBundle, d.lineBundle_toPic,
    PicardGroup.coe_weightedAbelJacobiClass,
    d.classEquivalence_divisorClass]

/-- Two chosen Abel--Jacobi line bundles are isomorphic exactly when the corresponding
degree-corrected point divisors are linearly equivalent. -/
theorem nonempty_weightedAbelJacobiLineBundle_iso_iff_linearlyEquivalent
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) {x₀ x y : Y} :
    Nonempty
        ((d.weightedAbelJacobiLineBundle w (x₀ := x₀) x).obj ≅
          (d.weightedAbelJacobiLineBundle w (x₀ := x₀) y).obj) ↔
      S.LinearlyEquivalent (weightedPointBaseDifference w x₀ x)
        (weightedPointBaseDifference w x₀ y) := by
  exact d.nonempty_lineBundle_iso_iff_linearlyEquivalent
    (weightedPointBaseDifference w x₀ x)
    (weightedPointBaseDifference w x₀ y)

end DivisorPicard.Dictionary

end MazurTorsion.AlgebraicGeometry
