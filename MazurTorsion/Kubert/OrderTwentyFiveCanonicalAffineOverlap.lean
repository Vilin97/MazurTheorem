/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalAffineCharts
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The overlap of the two order-25 canonical affine charts

The normalized charts `x + z = 1` and `x + w = 1` overlap where,
respectively, `x + w` and `x + z` are invertible. Their coordinate changes
are projective rescalings by these units. This file constructs both maps on
the localized quotient rings, checks them on all six affine coordinates,
and proves that they are inverse algebra equivalences.

The final algebra equivalence and its induced affine-scheme isomorphism are
the transition datum needed to glue the represented canonical carrier.
-/

noncomputable section

open MvPolynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.Kubert.OrderTwentyFiveCanonicalAffineCharts

universe u

variable (K : Type u) [CommRing K]

def leftX : LeftRing K := Ideal.Quotient.mk (leftIdeal K) (X 0)
def leftY : LeftRing K := Ideal.Quotient.mk (leftIdeal K) (X 1)
def leftW : LeftRing K := Ideal.Quotient.mk (leftIdeal K) (X 2)

def rightX : RightRing K := Ideal.Quotient.mk (rightIdeal K) (X 0)
def rightY : RightRing K := Ideal.Quotient.mk (rightIdeal K) (X 1)
def rightZ : RightRing K := Ideal.Quotient.mk (rightIdeal K) (X 2)

theorem leftCoords :
    OrderTwentyFiveCanonicalOnCurve (leftX K) (leftY K)
      (1 - leftX K) (leftW K) := by
  exact (leftAlgHomToSolution (LeftRing K) (AlgHom.id K (LeftRing K))).2

theorem rightCoords :
    OrderTwentyFiveCanonicalOnCurve (rightX K) (rightY K)
      (rightZ K) (1 - rightX K) := by
  exact (rightAlgHomToSolution (RightRing K) (AlgHom.id K (RightRing K))).2

theorem onCurve_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x y z w : R}
    (h : OrderTwentyFiveCanonicalOnCurve x y z w) :
    OrderTwentyFiveCanonicalOnCurve (f x) (f y) (f z) (f w) := by
  constructor
  · simpa [orderTwentyFiveCanonicalQuadric] using congrArg f h.1
  · simpa [orderTwentyFiveCanonicalCubic] using congrArg f h.2

theorem onCurve_scale {R : Type*} [CommRing R]
    (a : R) {x y z w : R}
    (h : OrderTwentyFiveCanonicalOnCurve x y z w) :
    OrderTwentyFiveCanonicalOnCurve (a * x) (a * y) (a * z) (a * w) := by
  constructor
  · have hq := h.1
    simp only [orderTwentyFiveCanonicalQuadric] at hq ⊢
    linear_combination a ^ 2 * hq
  · have hc := h.2
    simp only [orderTwentyFiveCanonicalCubic] at hc ⊢
    linear_combination a ^ 3 * hc

def leftOverlapElement : LeftRing K := leftX K + leftW K
def rightOverlapElement : RightRing K := rightX K + rightZ K

abbrev LeftOverlapRing := Localization.Away (leftOverlapElement K)
abbrev RightOverlapRing := Localization.Away (rightOverlapElement K)

private def inverseRightOverlapElement : RightOverlapRing K :=
  IsLocalization.Away.invSelf (rightOverlapElement K)

private theorem rightOverlapElement_mul_inverse :
    algebraMap (RightRing K) (RightOverlapRing K) (rightOverlapElement K) *
      inverseRightOverlapElement K = 1 :=
  IsLocalization.Away.mul_invSelf (rightOverlapElement K)

private def leftSolutionInRightOverlap : LeftSolution (RightOverlapRing K) := by
  let φ : RightRing K →+* RightOverlapRing K := algebraMap _ _
  let t := inverseRightOverlapElement K
  let x := φ (rightX K)
  let y := φ (rightY K)
  let z := φ (rightZ K)
  let w := 1 - x
  have hcurve : OrderTwentyFiveCanonicalOnCurve x y z w := by
    simpa [x, y, z, w, φ] using onCurve_map φ (rightCoords K)
  have hsum : (x + z) * t = 1 := by
    simpa [x, z, t, φ, rightOverlapElement, map_add] using
      rightOverlapElement_mul_inverse K
  have hz : 1 - t * x = t * z := by
    calc
      1 - t * x = (x + z) * t - t * x := by rw [hsum]
      _ = t * z := by ring
  refine ⟨![t * x, t * y, t * w], ?_⟩
  change OrderTwentyFiveCanonicalOnCurve
    (t * x) (t * y) (1 - t * x) (t * w)
  rw [hz]
  exact onCurve_scale t hcurve

def leftToRightBase : LeftRing K →ₐ[K] RightOverlapRing K :=
  leftSolutionToAlgHom (RightOverlapRing K) (leftSolutionInRightOverlap K)

@[simp] theorem leftToRightBase_leftX :
    leftToRightBase K (leftX K) =
      inverseRightOverlapElement K *
        algebraMap (RightRing K) (RightOverlapRing K) (rightX K) := by
  exact leftSolutionToAlgHom_X (K := K) (RightOverlapRing K)
    (leftSolutionInRightOverlap K) 0

@[simp] theorem leftToRightBase_leftY :
    leftToRightBase K (leftY K) =
      inverseRightOverlapElement K *
        algebraMap (RightRing K) (RightOverlapRing K) (rightY K) := by
  exact leftSolutionToAlgHom_X (K := K) (RightOverlapRing K)
    (leftSolutionInRightOverlap K) 1

@[simp] theorem leftToRightBase_leftW :
    leftToRightBase K (leftW K) =
      inverseRightOverlapElement K *
        (1 - algebraMap (RightRing K) (RightOverlapRing K) (rightX K)) := by
  exact leftSolutionToAlgHom_X (K := K) (RightOverlapRing K)
    (leftSolutionInRightOverlap K) 2

private theorem inverseRightOverlapElement_isUnit :
    IsUnit (inverseRightOverlapElement K) := by
  let r : RightOverlapRing K :=
    algebraMap (RightRing K) (RightOverlapRing K) (rightOverlapElement K)
  let t := inverseRightOverlapElement K
  have hrt : r * t = 1 := rightOverlapElement_mul_inverse K
  exact ⟨
    { val := t
      inv := r
      val_inv := by simpa [mul_comm] using hrt
      inv_val := hrt }, rfl⟩

private theorem leftToRightBase_overlapElement :
    leftToRightBase K (leftOverlapElement K) =
      inverseRightOverlapElement K := by
  simp [leftOverlapElement]
  ring

def leftToRight : LeftOverlapRing K →ₐ[K] RightOverlapRing K :=
  IsLocalization.Away.liftAlgHom (leftOverlapElement K)
    (f := leftToRightBase K) (by
      rw [leftToRightBase_overlapElement]
      exact inverseRightOverlapElement_isUnit K)

@[simp] theorem leftToRight_algebraMap (a : LeftRing K) :
    leftToRight K
        (algebraMap (LeftRing K) (LeftOverlapRing K) a) =
      leftToRightBase K a := by
  simp [leftToRight, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private def inverseLeftOverlapElement : LeftOverlapRing K :=
  IsLocalization.Away.invSelf (leftOverlapElement K)

private theorem leftOverlapElement_mul_inverse :
    algebraMap (LeftRing K) (LeftOverlapRing K) (leftOverlapElement K) *
      inverseLeftOverlapElement K = 1 :=
  IsLocalization.Away.mul_invSelf (leftOverlapElement K)

private def rightSolutionInLeftOverlap : RightSolution (LeftOverlapRing K) := by
  let φ : LeftRing K →+* LeftOverlapRing K := algebraMap _ _
  let t := inverseLeftOverlapElement K
  let x := φ (leftX K)
  let y := φ (leftY K)
  let z := 1 - x
  let w := φ (leftW K)
  have hcurve : OrderTwentyFiveCanonicalOnCurve x y z w := by
    simpa [x, y, z, w, φ] using onCurve_map φ (leftCoords K)
  have hsum : (x + w) * t = 1 := by
    simpa [x, w, t, φ, leftOverlapElement, map_add] using
      leftOverlapElement_mul_inverse K
  have hw : 1 - t * x = t * w := by
    calc
      1 - t * x = (x + w) * t - t * x := by rw [hsum]
      _ = t * w := by ring
  refine ⟨![t * x, t * y, t * z], ?_⟩
  change OrderTwentyFiveCanonicalOnCurve
    (t * x) (t * y) (t * z) (1 - t * x)
  rw [hw]
  exact onCurve_scale t hcurve

def rightToLeftBase : RightRing K →ₐ[K] LeftOverlapRing K :=
  rightSolutionToAlgHom (LeftOverlapRing K) (rightSolutionInLeftOverlap K)

@[simp] theorem rightToLeftBase_rightX :
    rightToLeftBase K (rightX K) =
      inverseLeftOverlapElement K *
        algebraMap (LeftRing K) (LeftOverlapRing K) (leftX K) := by
  exact rightSolutionToAlgHom_X (K := K) (LeftOverlapRing K)
    (rightSolutionInLeftOverlap K) 0

@[simp] theorem rightToLeftBase_rightY :
    rightToLeftBase K (rightY K) =
      inverseLeftOverlapElement K *
        algebraMap (LeftRing K) (LeftOverlapRing K) (leftY K) := by
  exact rightSolutionToAlgHom_X (K := K) (LeftOverlapRing K)
    (rightSolutionInLeftOverlap K) 1

@[simp] theorem rightToLeftBase_rightZ :
    rightToLeftBase K (rightZ K) =
      inverseLeftOverlapElement K *
        (1 - algebraMap (LeftRing K) (LeftOverlapRing K) (leftX K)) := by
  exact rightSolutionToAlgHom_X (K := K) (LeftOverlapRing K)
    (rightSolutionInLeftOverlap K) 2

private theorem inverseLeftOverlapElement_isUnit :
    IsUnit (inverseLeftOverlapElement K) := by
  let r : LeftOverlapRing K :=
    algebraMap (LeftRing K) (LeftOverlapRing K) (leftOverlapElement K)
  let t := inverseLeftOverlapElement K
  have hrt : r * t = 1 := leftOverlapElement_mul_inverse K
  exact ⟨
    { val := t
      inv := r
      val_inv := by simpa [mul_comm] using hrt
      inv_val := hrt }, rfl⟩

private theorem rightToLeftBase_overlapElement :
    rightToLeftBase K (rightOverlapElement K) =
      inverseLeftOverlapElement K := by
  simp [rightOverlapElement]
  ring

def rightToLeft : RightOverlapRing K →ₐ[K] LeftOverlapRing K :=
  IsLocalization.Away.liftAlgHom (rightOverlapElement K)
    (f := rightToLeftBase K) (by
      rw [rightToLeftBase_overlapElement]
      exact inverseLeftOverlapElement_isUnit K)

@[simp] theorem rightToLeft_algebraMap (a : RightRing K) :
    rightToLeft K
        (algebraMap (RightRing K) (RightOverlapRing K) a) =
      rightToLeftBase K a := by
  simp [rightToLeft, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private theorem rightToLeft_inverseRightOverlapElement :
    rightToLeft K (inverseRightOverlapElement K) =
      algebraMap (LeftRing K) (LeftOverlapRing K) (leftOverlapElement K) := by
  let m : LeftOverlapRing K :=
    algebraMap (LeftRing K) (LeftOverlapRing K) (leftOverlapElement K)
  let s := inverseLeftOverlapElement K
  let u := rightToLeft K (inverseRightOverlapElement K)
  have hms : m * s = 1 := leftOverlapElement_mul_inverse K
  have hsu : s * u = 1 := by
    have h := congrArg (rightToLeft K) (rightOverlapElement_mul_inverse K)
    change rightToLeft K
        (algebraMap (RightRing K) (RightOverlapRing K)
          (rightOverlapElement K) * inverseRightOverlapElement K) =
      rightToLeft K 1 at h
    rw [map_mul, map_one, rightToLeft_algebraMap,
      rightToLeftBase_overlapElement] at h
    exact h
  change u = m
  calc
    u = 1 * u := by rw [one_mul]
    _ = (m * s) * u := by rw [hms]
    _ = m * (s * u) := by rw [mul_assoc]
    _ = m := by rw [hsu, mul_one]

private theorem leftToRight_inverseLeftOverlapElement :
    leftToRight K (inverseLeftOverlapElement K) =
      algebraMap (RightRing K) (RightOverlapRing K) (rightOverlapElement K) := by
  let m : RightOverlapRing K :=
    algebraMap (RightRing K) (RightOverlapRing K) (rightOverlapElement K)
  let s := inverseRightOverlapElement K
  let u := leftToRight K (inverseLeftOverlapElement K)
  have hms : m * s = 1 := rightOverlapElement_mul_inverse K
  have hsu : s * u = 1 := by
    have h := congrArg (leftToRight K) (leftOverlapElement_mul_inverse K)
    change leftToRight K
        (algebraMap (LeftRing K) (LeftOverlapRing K)
          (leftOverlapElement K) * inverseLeftOverlapElement K) =
      leftToRight K 1 at h
    rw [map_mul, map_one, leftToRight_algebraMap,
      leftToRightBase_overlapElement] at h
    exact h
  change u = m
  calc
    u = 1 * u := by rw [one_mul]
    _ = (m * s) * u := by rw [hms]
    _ = m * (s * u) := by rw [mul_assoc]
    _ = m := by rw [hsu, mul_one]

private theorem rightToLeft_leftToRight_leftX :
    rightToLeft K (leftToRight K
      (algebraMap (LeftRing K) (LeftOverlapRing K) (leftX K))) =
        algebraMap (LeftRing K) (LeftOverlapRing K) (leftX K) := by
  rw [leftToRight_algebraMap, leftToRightBase_leftX, map_mul,
    rightToLeft_inverseRightOverlapElement, rightToLeft_algebraMap,
    rightToLeftBase_rightX]
  rw [← mul_assoc, leftOverlapElement_mul_inverse, one_mul]

private theorem rightToLeft_leftToRight_leftY :
    rightToLeft K (leftToRight K
      (algebraMap (LeftRing K) (LeftOverlapRing K) (leftY K))) =
        algebraMap (LeftRing K) (LeftOverlapRing K) (leftY K) := by
  rw [leftToRight_algebraMap, leftToRightBase_leftY, map_mul,
    rightToLeft_inverseRightOverlapElement, rightToLeft_algebraMap,
    rightToLeftBase_rightY]
  rw [← mul_assoc, leftOverlapElement_mul_inverse, one_mul]

private theorem rightToLeft_leftToRight_leftW :
    rightToLeft K (leftToRight K
      (algebraMap (LeftRing K) (LeftOverlapRing K) (leftW K))) =
        algebraMap (LeftRing K) (LeftOverlapRing K) (leftW K) := by
  rw [leftToRight_algebraMap, leftToRightBase_leftW, map_mul, map_sub,
    map_one, rightToLeft_inverseRightOverlapElement,
    rightToLeft_algebraMap, rightToLeftBase_rightX]
  let m : LeftOverlapRing K :=
    algebraMap (LeftRing K) (LeftOverlapRing K) (leftOverlapElement K)
  let s := inverseLeftOverlapElement K
  let x := algebraMap (LeftRing K) (LeftOverlapRing K) (leftX K)
  let w := algebraMap (LeftRing K) (LeftOverlapRing K) (leftW K)
  have hms : m * s = 1 := leftOverlapElement_mul_inverse K
  have hm : m = x + w := by
    simp [m, x, w, leftOverlapElement]
  change m * (1 - s * x) = w
  calc
    m * (1 - s * x) = m - (m * s) * x := by ring
    _ = m - x := by rw [hms, one_mul]
    _ = w := by rw [hm]; ring

theorem rightToLeft_comp_leftToRight :
    (rightToLeft K).comp (leftToRight K) =
      AlgHom.id K (LeftOverlapRing K) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (leftOverlapElement K))
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact rightToLeft_leftToRight_leftX K
  · exact rightToLeft_leftToRight_leftY K
  · exact rightToLeft_leftToRight_leftW K

private theorem leftToRight_rightToLeft_rightX :
    leftToRight K (rightToLeft K
      (algebraMap (RightRing K) (RightOverlapRing K) (rightX K))) =
        algebraMap (RightRing K) (RightOverlapRing K) (rightX K) := by
  rw [rightToLeft_algebraMap, rightToLeftBase_rightX, map_mul,
    leftToRight_inverseLeftOverlapElement, leftToRight_algebraMap,
    leftToRightBase_leftX]
  rw [← mul_assoc, rightOverlapElement_mul_inverse, one_mul]

private theorem leftToRight_rightToLeft_rightY :
    leftToRight K (rightToLeft K
      (algebraMap (RightRing K) (RightOverlapRing K) (rightY K))) =
        algebraMap (RightRing K) (RightOverlapRing K) (rightY K) := by
  rw [rightToLeft_algebraMap, rightToLeftBase_rightY, map_mul,
    leftToRight_inverseLeftOverlapElement, leftToRight_algebraMap,
    leftToRightBase_leftY]
  rw [← mul_assoc, rightOverlapElement_mul_inverse, one_mul]

private theorem leftToRight_rightToLeft_rightZ :
    leftToRight K (rightToLeft K
      (algebraMap (RightRing K) (RightOverlapRing K) (rightZ K))) =
        algebraMap (RightRing K) (RightOverlapRing K) (rightZ K) := by
  rw [rightToLeft_algebraMap, rightToLeftBase_rightZ, map_mul, map_sub,
    map_one, leftToRight_inverseLeftOverlapElement,
    leftToRight_algebraMap, leftToRightBase_leftX]
  let m : RightOverlapRing K :=
    algebraMap (RightRing K) (RightOverlapRing K) (rightOverlapElement K)
  let s := inverseRightOverlapElement K
  let x := algebraMap (RightRing K) (RightOverlapRing K) (rightX K)
  let z := algebraMap (RightRing K) (RightOverlapRing K) (rightZ K)
  have hms : m * s = 1 := rightOverlapElement_mul_inverse K
  have hm : m = x + z := by
    simp [m, x, z, rightOverlapElement]
  change m * (1 - s * x) = z
  calc
    m * (1 - s * x) = m - (m * s) * x := by ring
    _ = m - x := by rw [hms, one_mul]
    _ = z := by rw [hm]; ring

theorem leftToRight_comp_rightToLeft :
    (leftToRight K).comp (rightToLeft K) =
      AlgHom.id K (RightOverlapRing K) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (rightOverlapElement K))
  apply Ideal.Quotient.algHom_ext K
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact leftToRight_rightToLeft_rightX K
  · exact leftToRight_rightToLeft_rightY K
  · exact leftToRight_rightToLeft_rightZ K

def overlapAlgEquiv : LeftOverlapRing K ≃ₐ[K] RightOverlapRing K :=
  AlgEquiv.ofAlgHom (leftToRight K) (rightToLeft K)
    (leftToRight_comp_rightToLeft K)
    (rightToLeft_comp_leftToRight K)

/-- The scheme isomorphism between the two presentations of the affine
overlap. -/
def overlapSchemeIso :
    Spec (.of (LeftOverlapRing K)) ≅ Spec (.of (RightOverlapRing K)) :=
  Scheme.Spec.mapIso
    (overlapAlgEquiv K).toRingEquiv.toCommRingCatIso.symm.op

@[simp]
theorem overlapSchemeIso_hom :
    (overlapSchemeIso K).hom =
      Spec.map (CommRingCat.ofHom (rightToLeft K).toRingHom) := by
  rfl

@[simp]
theorem overlapSchemeIso_inv :
    (overlapSchemeIso K).inv =
      Spec.map (CommRingCat.ofHom (leftToRight K).toRingHom) := by
  rfl

end MazurTorsion.Kubert.OrderTwentyFiveCanonicalAffineCharts
