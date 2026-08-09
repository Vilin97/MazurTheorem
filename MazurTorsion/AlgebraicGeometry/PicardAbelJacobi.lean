/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.PicardDegreeZero
import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.LinearSystem
import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Sum.BasepointChange

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
open CategoryTheory
open CategoryTheory.MonoidalCategory

attribute [local instance] schemeModulesMonoidal

namespace PicardGroup

variable {X : Scheme.{u}}
variable {Y : Type*} {G : Type v} [AddCommGroup G]

/-- The weighted Abel--Jacobi class in the actual image of a supplied
divisor-class-to-Picard homomorphism.  No surjectivity onto all Picard classes
is required. -/
noncomputable def weightedAbelJacobiClassImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (x : Y) :
    degreeZeroImage S w h φ :=
  picZeroToDegreeZeroImage S w h φ
    (S.weightedAbelJacobiClass w h hx₀ x)

/-- The underlying Picard value of the image-valued Abel--Jacobi class is
the supplied homomorphism applied to its degree-corrected divisor class. -/
@[simp]
lemma coe_weightedAbelJacobiClassImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X)
    {x₀ : Y} (hx₀ : w x₀ = 1) (x : Y) :
    (weightedAbelJacobiClassImage S w h φ hx₀ x : PicardGroup X) =
      φ (S.divisorClass (weightedPointBaseDifference w x₀ x)) :=
  coe_picZeroToDegreeZeroImage S w h φ
    (S.weightedAbelJacobiClass w h hx₀ x)

/-- The basepoint maps to zero in the degree-zero image. -/
@[simp]
lemma weightedAbelJacobiClassImage_base
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X)
    {x₀ : Y} (hx₀ : w x₀ = 1) :
    weightedAbelJacobiClassImage S w h φ hx₀ x₀ = 0 := by
  rw [weightedAbelJacobiClassImage,
    S.weightedAbelJacobiClass_base, map_zero]

/-- The degree-zero image class `[x₀] - [y₀]` translating between two
weighted Abel--Jacobi normalizations. -/
noncomputable def weightedBasepointChangeClassImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X)
    {x₀ y₀ : Y} (hxy : w x₀ = w y₀) :
    degreeZeroImage S w h φ :=
  picZeroToDegreeZeroImage S w h φ
    (S.weightedBasepointChangeClass w h hxy)

/-- The underlying Picard value of the image-valued basepoint correction is
the image of the corresponding point-difference class. -/
@[simp]
lemma coe_weightedBasepointChangeClassImage
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X)
    {x₀ y₀ : Y} (hxy : w x₀ = w y₀) :
    (weightedBasepointChangeClassImage S w h φ hxy : PicardGroup X) =
      φ (S.divisorClass (pointDifference x₀ y₀)) :=
  coe_picZeroToDegreeZeroImage S w h φ
    (S.weightedBasepointChangeClass w h hxy)

/-- Changing a weight-one basepoint translates the image-valued
Abel--Jacobi class by the point's weight times `[x₀] - [y₀]`.

This is an algebraic basepoint-change law; it makes no claim about geometric
base change of schemes or Picard functors. -/
lemma weightedAbelJacobiClassImage_change_base
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (φ : S.ClassGroup →+ PicardGroup X)
    {x₀ y₀ : Y} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (x : Y) :
    weightedAbelJacobiClassImage S w h φ hy₀ x =
      weightedAbelJacobiClassImage S w h φ hx₀ x +
        w x • weightedBasepointChangeClassImage S w h φ
          (hx₀.trans hy₀.symm) := by
  change picZeroToDegreeZeroImage S w h φ
      (S.weightedAbelJacobiClass w h hy₀ x) =
    picZeroToDegreeZeroImage S w h φ
        (S.weightedAbelJacobiClass w h hx₀ x) +
      w x • picZeroToDegreeZeroImage S w h φ
        (S.weightedBasepointChangeClass w h (hx₀.trans hy₀.symm))
  rw [S.weightedAbelJacobiClass_change_base, map_add, map_zsmul]

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

/-- The degree-zero Picard class `[x₀] - [y₀]` that translates between
two Abel--Jacobi normalizations. -/
noncomputable def weightedBasepointChangeClass
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ y₀ : Y} (hxy : w x₀ = w y₀) :
    degreeZero S w h e :=
  picZeroEquiv S w h e (S.weightedBasepointChangeClass w h hxy)

/-- The underlying scheme-Picard class of a basepoint translation is the
image of the point-difference divisor. -/
@[simp]
lemma coe_weightedBasepointChangeClass
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ y₀ : Y} (hxy : w x₀ = w y₀) :
    (weightedBasepointChangeClass S w h e hxy : PicardGroup X) =
      e (S.divisorClass (pointDifference x₀ y₀)) :=
  rfl

/-- Changing the weight-one basepoint translates the scheme-Picard
Abel--Jacobi class by the point's weight times `[x₀] - [y₀]`. -/
lemma weightedAbelJacobiClass_change_base
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ y₀ : Y} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (x : Y) :
    weightedAbelJacobiClass S w h e hy₀ x =
      weightedAbelJacobiClass S w h e hx₀ x +
        w x • weightedBasepointChangeClass S w h e
          (hx₀.trans hy₀.symm) := by
  change picZeroEquiv S w h e (S.weightedAbelJacobiClass w h hy₀ x) =
    picZeroEquiv S w h e (S.weightedAbelJacobiClass w h hx₀ x) +
      w x • picZeroEquiv S w h e
        (S.weightedBasepointChangeClass w h (hx₀.trans hy₀.symm))
  rw [S.weightedAbelJacobiClass_change_base, map_add, map_zsmul]

/-- The old basepoint, viewed with the new normalization, is exactly the
basepoint-translation class in the scheme Picard group. -/
lemma weightedAbelJacobiClass_oldBase_eq_weightedBasepointChangeClass
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ y₀ : Y} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1) :
    weightedAbelJacobiClass S w h e hy₀ x₀ =
      weightedBasepointChangeClass S w h e
        (hx₀.trans hy₀.symm) := by
  change picZeroEquiv S w h e
      (S.weightedAbelJacobiClass w h hy₀ x₀) =
    picZeroEquiv S w h e
      (S.weightedBasepointChangeClass w h (hx₀.trans hy₀.symm))
  exact congrArg (picZeroEquiv S w h e)
    (S.weightedAbelJacobiClass_oldBase_eq_basepointChangeClass
      w h hx₀ hy₀)

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

/-- Changing the basepoint of the scheme-Picard Abel map on divisors adds
the weighted degree times the same point-difference translation class. -/
lemma weightedAbelJacobiDivisorClass_change_base
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    {x₀ y₀ : Y} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (D : WeilDivisor Y) :
    weightedAbelJacobiDivisorClass S w h e hy₀ D =
      weightedAbelJacobiDivisorClass S w h e hx₀ D +
        weightedDegree w D • weightedBasepointChangeClass S w h e
          (hx₀.trans hy₀.symm) := by
  change picZeroEquiv S w h e
      (S.weightedAbelJacobiDivisorClass w h hy₀ D) =
    picZeroEquiv S w h e
        (S.weightedAbelJacobiDivisorClass w h hx₀ D) +
      weightedDegree w D • picZeroEquiv S w h e
        (S.weightedBasepointChangeClass w h (hx₀.trans hy₀.symm))
  rw [S.weightedAbelJacobiDivisorClass_change_base, map_add, map_zsmul]

/-! ### Fixed-degree fibers in the scheme Picard group -/

/-- After transport to the scheme Picard group, the fixed-degree Abel--Jacobi fiber through an
effective divisor is still its complete linear system.  This is a checked group-valued consumer;
it does not assert that the symmetric power or Picard group is represented by a scheme. -/
lemma weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem
    (S : WeilDivisor.OrderSystem Y G)
    (h : S.IsUnweightedDegreeZero)
    (e : DivisorPicard.ClassEquivalence S X)
    (x₀ : Y) {d : ℕ} (D E : EffectiveDivisorOfDegree Y d) :
    weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
        (E : WeilDivisor Y) =
      weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
        (D : WeilDivisor Y) ↔
      (E : WeilDivisor Y) ∈ S.completeLinearSystem (D : WeilDivisor Y) := by
  change picZeroEquiv S (fun _ : Y => (1 : ℤ)) h e
        (S.weightedAbelJacobiDivisorClass (fun _ : Y => (1 : ℤ)) h (x₀ := x₀) rfl E) =
      picZeroEquiv S (fun _ : Y => (1 : ℤ)) h e
        (S.weightedAbelJacobiDivisorClass (fun _ : Y => (1 : ℤ)) h (x₀ := x₀) rfl D) ↔ _
  rw [(picZeroEquiv S (fun _ : Y => (1 : ℤ)) h e).injective.eq_iff,
    S.weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem]

/-- The scheme-Picard fixed-degree fiber, as a set of effective divisors, is the restriction of
the complete linear system. -/
lemma setOf_weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq
    (S : WeilDivisor.OrderSystem Y G)
    (h : S.IsUnweightedDegreeZero)
    (e : DivisorPicard.ClassEquivalence S X)
    (x₀ : Y) {d : ℕ} (D : EffectiveDivisorOfDegree Y d) :
    {E : EffectiveDivisorOfDegree Y d |
        weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
          (E : WeilDivisor Y) =
        weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
          (D : WeilDivisor Y)} =
      {E : EffectiveDivisorOfDegree Y d |
        (E : WeilDivisor Y) ∈ S.completeLinearSystem (D : WeilDivisor Y)} := by
  ext E
  exact
    weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem
      S h e x₀ D E

/-- The equality fiber of the scheme-Picard class function on a symmetric power is the preimage
of the corresponding complete linear system. -/
lemma weightedAbelJacobiDivisorClass_one_ofSym_eq_iff_mem_completeLinearSystem
    (S : WeilDivisor.OrderSystem Y G)
    (h : S.IsUnweightedDegreeZero)
    (e : DivisorPicard.ClassEquivalence S X)
    (x₀ : Y) {d : ℕ} (s t : Sym Y d) :
    weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
        (EffectiveDivisorOfDegree.ofSym t : WeilDivisor Y) =
      weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
        (EffectiveDivisorOfDegree.ofSym s : WeilDivisor Y) ↔
      (EffectiveDivisorOfDegree.ofSym t : WeilDivisor Y) ∈
        S.completeLinearSystem (EffectiveDivisorOfDegree.ofSym s : WeilDivisor Y) :=
  weightedAbelJacobiDivisorClass_one_effectiveDivisorOfDegree_eq_iff_mem_completeLinearSystem
    S h e x₀ (EffectiveDivisorOfDegree.ofSym s) (EffectiveDivisorOfDegree.ofSym t)

/-- Set-level form of the transported symmetric-power fiber formula. -/
lemma setOf_weightedAbelJacobiDivisorClass_one_ofSym_eq
    (S : WeilDivisor.OrderSystem Y G)
    (h : S.IsUnweightedDegreeZero)
    (e : DivisorPicard.ClassEquivalence S X)
    (x₀ : Y) {d : ℕ} (s : Sym Y d) :
    {t : Sym Y d |
        weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
          (EffectiveDivisorOfDegree.ofSym t : WeilDivisor Y) =
        weightedAbelJacobiDivisorClass S (fun _ : Y => (1 : ℤ)) h e (x₀ := x₀) rfl
          (EffectiveDivisorOfDegree.ofSym s : WeilDivisor Y)} =
      {t : Sym Y d |
        (EffectiveDivisorOfDegree.ofSym t : WeilDivisor Y) ∈
          S.completeLinearSystem (EffectiveDivisorOfDegree.ofSym s : WeilDivisor Y)} := by
  ext t
  exact weightedAbelJacobiDivisorClass_one_ofSym_eq_iff_mem_completeLinearSystem
    S h e x₀ s t

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

/-- Changing the basepoint of the chosen Abel--Jacobi line bundle tensors it
with the chosen bundle of the exact weighted point-difference correction.
This is the line-bundle-level normalization consumed by a future Poincare
bundle construction. -/
theorem nonempty_weightedAbelJacobiLineBundle_change_base
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (x₀ y₀ x : Y) :
    Nonempty
      ((d.weightedAbelJacobiLineBundle w (x₀ := y₀) x).obj ≅
        (d.weightedAbelJacobiLineBundle w (x₀ := x₀) x).obj ⊗
          (d.lineBundle (w x • pointDifference x₀ y₀)).obj) := by
  change Nonempty
    ((d.lineBundle (weightedPointBaseDifference w y₀ x)).obj ≅
      (d.lineBundle (weightedPointBaseDifference w x₀ x)).obj ⊗
        (d.lineBundle (w x • pointDifference x₀ y₀)).obj)
  rw [weightedPointBaseDifference_change_base]
  exact d.lineBundle_add_iso (weightedPointBaseDifference w x₀ x)
    (w x • pointDifference x₀ y₀)

/-- The chosen line-bundle representatives recover the exact scheme-Picard
basepoint-translation law. This is the compiled downstream consumer of the
bundle-level normalization. -/
theorem weightedAbelJacobiLineBundle_toPic_change_base
    (d : DivisorPicard.Dictionary S X)
    (w : Y → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ y₀ : Y} (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (x : Y) :
    Additive.ofMul
        (d.comparison.toPic
          (d.weightedAbelJacobiLineBundle w (x₀ := y₀) x)) =
      Additive.ofMul
          (d.comparison.toPic
            (d.weightedAbelJacobiLineBundle w (x₀ := x₀) x)) +
        w x • (PicardGroup.weightedBasepointChangeClass
          S w h d.classEquivalence (hx₀.trans hy₀.symm) : PicardGroup X) := by
  have hskeleton :
      toSkeleton
          (d.weightedAbelJacobiLineBundle w (x₀ := y₀) x).obj =
        toSkeleton
          ((d.weightedAbelJacobiLineBundle w (x₀ := x₀) x).obj ⊗
            (d.lineBundle (w x • pointDifference x₀ y₀)).obj) :=
    toSkeleton_eq_toSkeleton_iff.mpr
      (d.nonempty_weightedAbelJacobiLineBundle_change_base w x₀ y₀ x)
  have hpic :
      d.comparison.toPic
          (d.weightedAbelJacobiLineBundle w (x₀ := y₀) x) =
        d.comparison.toPic
            (d.weightedAbelJacobiLineBundle w (x₀ := x₀) x) *
          d.comparison.toPic
            (d.lineBundle (w x • pointDifference x₀ y₀)) := by
    apply Units.ext
    change (d.comparison.toPic
        (d.weightedAbelJacobiLineBundle w (x₀ := y₀) x)).val =
      (d.comparison.toPic
          (d.weightedAbelJacobiLineBundle w (x₀ := x₀) x)).val *
        (d.comparison.toPic
          (d.lineBundle (w x • pointDifference x₀ y₀))).val
    rw [d.comparison.toPic_val, d.comparison.toPic_val,
      d.comparison.toPic_val, ← Skeleton.toSkeleton_tensorObj]
    exact hskeleton
  have hadd := congrArg Additive.ofMul hpic
  change Additive.ofMul
      (d.comparison.toPic
        (d.weightedAbelJacobiLineBundle w (x₀ := y₀) x)) =
    Additive.ofMul
        (d.comparison.toPic
          (d.weightedAbelJacobiLineBundle w (x₀ := x₀) x)) +
      Additive.ofMul
        (d.comparison.toPic
          (d.lineBundle (w x • pointDifference x₀ y₀))) at hadd
  have hcorrection :
      Additive.ofMul
          (d.comparison.toPic
            (d.lineBundle (w x • pointDifference x₀ y₀))) =
        w x • (PicardGroup.weightedBasepointChangeClass
          S w h d.classEquivalence
            (hx₀.trans hy₀.symm) : PicardGroup X) := by
    rw [d.lineBundle_toPic, map_zsmul,
      ← d.classEquivalence_divisorClass,
      ← PicardGroup.coe_weightedBasepointChangeClass]
  exact hadd.trans (congrArg _ hcorrection)

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

namespace CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse

open TopologicalSpace
open TauCeti.AlgebraicGeometry.WeilDivisor

/-- The weighted Abel--Jacobi class in the degree-zero Picard image supplied
by a global principal boundary.  This narrower adapter avoids the unrelated
claim that the divisor construction is surjective onto every Picard class. -/
noncomputable def weightedAbelJacobiClassImageOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X} (hx₀ : w x₀ = 1)
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    degreeZeroImageOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b w hdegree :=
  PicardGroup.weightedAbelJacobiClassImage S w hdegree
    (classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b) hx₀ x

/-- The underlying Picard value is the descended line-bundle class of the
degree-corrected point divisor. -/
@[simp]
theorem coe_weightedAbelJacobiClassImageOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X} (hx₀ : w x₀ = 1)
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    (weightedAbelJacobiClassImageOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b
          w hdegree hx₀ x : PicardGroup X) =
      divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b
          (weightedPointBaseDifference w x₀ x) := by
  change classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b
        (S.divisorClass (weightedPointBaseDifference w x₀ x)) = _
  exact classToPicOfGlobalPrincipalBoundary_divisorClass
    X U hnonempty hcover hU h S C heffective hadd b _

/-- The global-principal-boundary image adapter retains the checked
basepoint normalization without a Picard-surjectivity premise. -/
@[simp]
theorem weightedAbelJacobiClassImageOfGlobalPrincipalBoundary_base
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X} (hx₀ : w x₀ = 1) :
    weightedAbelJacobiClassImageOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b
        w hdegree hx₀ x₀ = 0 :=
  PicardGroup.weightedAbelJacobiClassImage_base S w hdegree
    (classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b) hx₀

/-- The image-valued correction class for changing weighted Abel--Jacobi
basepoints under a global principal boundary. -/
noncomputable def weightedBasepointChangeClassImageOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ y₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X}
    (hxy : w x₀ = w y₀) :
    degreeZeroImageOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b w hdegree :=
  PicardGroup.weightedBasepointChangeClassImage S w hdegree
    (classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b) hxy

/-- The underlying correction is the descended Picard class of the honest
point-difference divisor. -/
@[simp]
theorem coe_weightedBasepointChangeClassImageOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ y₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X}
    (hxy : w x₀ = w y₀) :
    (weightedBasepointChangeClassImageOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b
          w hdegree hxy : PicardGroup X) =
      divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b
          (pointDifference x₀ y₀) := by
  change classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b
        (S.divisorClass (pointDifference x₀ y₀)) = _
  exact classToPicOfGlobalPrincipalBoundary_divisorClass
    X U hnonempty hcover hU h S C heffective hadd b _

/-- Changing a weight-one basepoint obeys the same translation law in the
actual degree-zero Picard image, with no ambient surjectivity hypothesis. -/
theorem weightedAbelJacobiClassImageOfGlobalPrincipalBoundary_change_base
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ y₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X}
    (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    weightedAbelJacobiClassImageOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b
          w hdegree hy₀ x =
      weightedAbelJacobiClassImageOfGlobalPrincipalBoundary
          X U hnonempty hcover hU h S C heffective hadd b
            w hdegree hx₀ x +
        w x • weightedBasepointChangeClassImageOfGlobalPrincipalBoundary
          X U hnonempty hcover hU h S C heffective hadd b
            w hdegree (hx₀.trans hy₀.symm) :=
  PicardGroup.weightedAbelJacobiClassImage_change_base S w hdegree
    (classToPicOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b) hx₀ hy₀ x

/-- The pointwise Abel--Jacobi class obtained directly from the exact global principal boundary
for descended divisor bundles. This is a downstream consumer of
`classEquivPicardOfGlobalPrincipalBoundary`: neither arbitrary-object descent separation nor a
separate zero-bundle trivialization occurs in the interface. -/
noncomputable def weightedAbelJacobiClassOfGlobalPrincipalBoundary
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (hsurjective : Function.Surjective
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b))
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X} (hx₀ : w x₀ = 1)
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    PicardGroup.degreeZero S w hdegree
      (classEquivPicardOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b hsurjective) :=
  PicardGroup.weightedAbelJacobiClass S w hdegree
    (classEquivPicardOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b hsurjective) hx₀ x

/-- The global-principal-boundary Abel--Jacobi adapter retains the checked basepoint
normalization. -/
@[simp]
theorem weightedAbelJacobiClassOfGlobalPrincipalBoundary_base
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective)
    (hsurjective : Function.Surjective
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b))
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X} (hx₀ : w x₀ = 1) :
    weightedAbelJacobiClassOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b hsurjective
        w hdegree hx₀ x₀ = 0 :=
  PicardGroup.weightedAbelJacobiClass_base S w hdegree
    (classEquivPicardOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b hsurjective) hx₀

/-- The effective divisor-cocycle construction respects a change of
weight-one Abel--Jacobi basepoint.  This is the concrete descent consumer of
the scheme-Picard normalization law. -/
theorem weightedAbelJacobiClassOfGlobalPrincipalBoundary_change_base
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
        (Additive X.functionFieldˣ))
    (C : CurveDivisorDescent.DivisorCocycleSystem
      X U hnonempty hcover hU h)
    (heffective : CurveDivisorDescent.EffectiveDivisorCocycleSystem
      X U hnonempty hcover hU h C)
    (hadd : CurveDivisorDescent.DescendedTensorAdditive
      X U hnonempty hcover hU h C heffective)
    (b : GlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective)
    (hsurjective : Function.Surjective
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b))
    (w : TauCeti.AlgebraicGeometry.CodimensionOnePoint X → ℤ)
    (hdegree : S.IsWeightedDegreeZero w)
    {x₀ y₀ : TauCeti.AlgebraicGeometry.CodimensionOnePoint X}
    (hx₀ : w x₀ = 1) (hy₀ : w y₀ = 1)
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) :
    weightedAbelJacobiClassOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd b hsurjective
          w hdegree hy₀ x =
      weightedAbelJacobiClassOfGlobalPrincipalBoundary
          X U hnonempty hcover hU h S C heffective hadd b hsurjective
            w hdegree hx₀ x +
        w x • PicardGroup.weightedBasepointChangeClass S w hdegree
          (classEquivPicardOfGlobalPrincipalBoundary
            X U hnonempty hcover hU h S C heffective hadd b hsurjective)
          (hx₀.trans hy₀.symm) :=
  PicardGroup.weightedAbelJacobiClass_change_base S w hdegree
    (classEquivPicardOfGlobalPrincipalBoundary
      X U hnonempty hcover hU h S C heffective hadd b hsurjective)
    hx₀ hy₀ x

end CurveDivisorDescent.DivisorCocycleSystem.ExplicitInverse

end MazurTorsion.AlgebraicGeometry
