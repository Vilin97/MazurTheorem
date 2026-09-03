/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalCurve
import Mathlib.Tactic

/-!
# Smoothness certificate for the order-25 canonical carrier

The canonical order-twenty-five carrier is the complete intersection of one
quadric and one cubic in `P³`.  This file records their two explicit gradient
rows and proves that some `2 × 2` Jacobian minor is nonzero at every nonzero
common zero over every characteristic-zero field.  Equivalently, the two
gradient rows are linearly independent there.

The proof is a checked homogeneous ideal calculation on the four standard
projective charts.  It supplies the Jacobian-rank input needed to promote the
affine hyperplane-intersection calculations to local orders on a smooth
curve.  Constructing the represented projective complete intersection and
invoking the scheme-theoretic Jacobian criterion remain the next geometric
boundary.

`orderTwentyFiveCanonical_jacobianRows_independent` is the named downstream
consumer of the nonzero-minor certificate.
-/

namespace MazurTorsion.Kubert

/-- The formal gradient of the canonical quadric, in coordinate order
`(x,y,z,w)`. -/
def orderTwentyFiveCanonicalQuadricGradient
    {R : Type*} [CommRing R] (x y z w : R) : Fin 4 → R :=
  ![-z - w, 2 * y + z, -x + y + w, -x + z]

/-- The formal gradient of the canonical cubic, in coordinate order
`(x,y,z,w)`. -/
def orderTwentyFiveCanonicalCubicGradient
    {R : Type*} [CommRing R] (x y z w : R) : Fin 4 → R :=
  ![y * z + 2 * x * w - y * w - z * w,
    x * z - x * w + z * w,
    x * y - x * w + y * w + 2 * z * w - w ^ 2,
    x ^ 2 - x * y - x * z + y * z + z ^ 2 - 2 * z * w]

@[simp] theorem orderTwentyFiveCanonicalQuadricGradient_zero
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalQuadricGradient x y z w 0 = -z - w := rfl

@[simp] theorem orderTwentyFiveCanonicalQuadricGradient_one
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalQuadricGradient x y z w 1 = 2 * y + z := rfl

@[simp] theorem orderTwentyFiveCanonicalQuadricGradient_two
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalQuadricGradient x y z w 2 = -x + y + w := rfl

@[simp] theorem orderTwentyFiveCanonicalQuadricGradient_three
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalQuadricGradient x y z w 3 = -x + z := rfl

@[simp] theorem orderTwentyFiveCanonicalCubicGradient_zero
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalCubicGradient x y z w 0 =
      y * z + 2 * x * w - y * w - z * w := rfl

@[simp] theorem orderTwentyFiveCanonicalCubicGradient_one
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalCubicGradient x y z w 1 =
      x * z - x * w + z * w := rfl

@[simp] theorem orderTwentyFiveCanonicalCubicGradient_two
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalCubicGradient x y z w 2 =
      x * y - x * w + y * w + 2 * z * w - w ^ 2 := rfl

@[simp] theorem orderTwentyFiveCanonicalCubicGradient_three
    {R : Type*} [CommRing R] (x y z w : R) :
    orderTwentyFiveCanonicalCubicGradient x y z w 3 =
      x ^ 2 - x * y - x * z + y * z + z ^ 2 - 2 * z * w := rfl

/-- A `2 × 2` minor of the two-row Jacobian matrix. -/
def orderTwentyFiveCanonicalJacobianMinor
    {R : Type*} [CommRing R] (x y z w : R) (i j : Fin 4) : R :=
  orderTwentyFiveCanonicalQuadricGradient x y z w i *
      orderTwentyFiveCanonicalCubicGradient x y z w j -
    orderTwentyFiveCanonicalQuadricGradient x y z w j *
      orderTwentyFiveCanonicalCubicGradient x y z w i

/-- At every geometric point of the canonical complete intersection in
characteristic zero, at least one `2 × 2` Jacobian minor is nonzero.  The
six alternatives enumerate the minors in lexicographic coordinate order. -/
theorem orderTwentyFiveCanonical_exists_jacobianMinor_ne_zero
    {K : Type*} [Field K] [CharZero K] (x y z w : K)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w) :
    orderTwentyFiveCanonicalJacobianMinor x y z w 0 1 ≠ 0 ∨
      orderTwentyFiveCanonicalJacobianMinor x y z w 0 2 ≠ 0 ∨
      orderTwentyFiveCanonicalJacobianMinor x y z w 0 3 ≠ 0 ∨
      orderTwentyFiveCanonicalJacobianMinor x y z w 1 2 ≠ 0 ∨
      orderTwentyFiveCanonicalJacobianMinor x y z w 1 3 ≠ 0 ∨
      orderTwentyFiveCanonicalJacobianMinor x y z w 2 3 ≠ 0 := by
  by_contra hminors
  simp only [not_or, not_not] at hminors
  rcases hminors with ⟨h01, h02, h03, h12, h13, h23⟩
  rcases hcurve with ⟨hQ, hC⟩
  rcases hnonzero with hx | hy | hz | hw
  · have hinverse : x * (1 / x) - 1 = 0 := by
      field_simp
      ring
    simp only [orderTwentyFiveCanonicalJacobianMinor,
      orderTwentyFiveCanonicalQuadricGradient_zero,
      orderTwentyFiveCanonicalQuadricGradient_one,
      orderTwentyFiveCanonicalQuadricGradient_two,
      orderTwentyFiveCanonicalQuadricGradient_three,
      orderTwentyFiveCanonicalCubicGradient_zero,
      orderTwentyFiveCanonicalCubicGradient_one,
      orderTwentyFiveCanonicalCubicGradient_two,
      orderTwentyFiveCanonicalCubicGradient_three,
      orderTwentyFiveCanonicalQuadric,
      orderTwentyFiveCanonicalCubic] at hQ hC h01 h02 h03 h12 h13 h23
    grobner
  · have hinverse : y * (1 / y) - 1 = 0 := by
      field_simp
      ring
    simp only [orderTwentyFiveCanonicalJacobianMinor,
      orderTwentyFiveCanonicalQuadricGradient_zero,
      orderTwentyFiveCanonicalQuadricGradient_one,
      orderTwentyFiveCanonicalQuadricGradient_two,
      orderTwentyFiveCanonicalQuadricGradient_three,
      orderTwentyFiveCanonicalCubicGradient_zero,
      orderTwentyFiveCanonicalCubicGradient_one,
      orderTwentyFiveCanonicalCubicGradient_two,
      orderTwentyFiveCanonicalCubicGradient_three,
      orderTwentyFiveCanonicalQuadric,
      orderTwentyFiveCanonicalCubic] at hQ hC h01 h02 h03 h12 h13 h23
    grobner
  · have hinverse : z * (1 / z) - 1 = 0 := by
      field_simp
      ring
    simp only [orderTwentyFiveCanonicalJacobianMinor,
      orderTwentyFiveCanonicalQuadricGradient_zero,
      orderTwentyFiveCanonicalQuadricGradient_one,
      orderTwentyFiveCanonicalQuadricGradient_two,
      orderTwentyFiveCanonicalQuadricGradient_three,
      orderTwentyFiveCanonicalCubicGradient_zero,
      orderTwentyFiveCanonicalCubicGradient_one,
      orderTwentyFiveCanonicalCubicGradient_two,
      orderTwentyFiveCanonicalCubicGradient_three,
      orderTwentyFiveCanonicalQuadric,
      orderTwentyFiveCanonicalCubic] at hQ hC h01 h02 h03 h12 h13 h23
    grobner
  · have hinverse : w * (1 / w) - 1 = 0 := by
      field_simp
      ring
    simp only [orderTwentyFiveCanonicalJacobianMinor,
      orderTwentyFiveCanonicalQuadricGradient_zero,
      orderTwentyFiveCanonicalQuadricGradient_one,
      orderTwentyFiveCanonicalQuadricGradient_two,
      orderTwentyFiveCanonicalQuadricGradient_three,
      orderTwentyFiveCanonicalCubicGradient_zero,
      orderTwentyFiveCanonicalCubicGradient_one,
      orderTwentyFiveCanonicalCubicGradient_two,
      orderTwentyFiveCanonicalCubicGradient_three,
      orderTwentyFiveCanonicalQuadric,
      orderTwentyFiveCanonicalCubic] at hQ hC h01 h02 h03 h12 h13 h23
    grobner

private theorem orderTwentyFiveCanonical_jacobianRows_independent_of_minor
    {K : Type*} [Field K] [CharZero K] (x y z w : K)
    (i j : Fin 4)
    (hminor : orderTwentyFiveCanonicalJacobianMinor x y z w i j ≠ 0)
    (a b : K)
    (hlinear : ∀ i : Fin 4,
      a * orderTwentyFiveCanonicalQuadricGradient x y z w i +
        b * orderTwentyFiveCanonicalCubicGradient x y z w i = 0) :
    a = 0 ∧ b = 0 := by
  have hi := hlinear i
  have hj := hlinear j
  have haProduct :
      a * orderTwentyFiveCanonicalJacobianMinor x y z w i j = 0 := by
    simp only [orderTwentyFiveCanonicalJacobianMinor]
    linear_combination
      (orderTwentyFiveCanonicalCubicGradient x y z w j) * hi -
        (orderTwentyFiveCanonicalCubicGradient x y z w i) * hj
  have hbProduct :
      b * orderTwentyFiveCanonicalJacobianMinor x y z w i j = 0 := by
    simp only [orderTwentyFiveCanonicalJacobianMinor]
    linear_combination
      (orderTwentyFiveCanonicalQuadricGradient x y z w i) * hj -
        (orderTwentyFiveCanonicalQuadricGradient x y z w j) * hi
  exact ⟨(mul_eq_zero.mp haProduct).resolve_right hminor,
    (mul_eq_zero.mp hbProduct).resolve_right hminor⟩

/-- A coordinate-free form of the Jacobian-rank certificate: the two
gradient rows admit no nontrivial linear relation at a nonzero common zero. -/
theorem orderTwentyFiveCanonical_jacobianRows_independent
    {K : Type*} [Field K] [CharZero K] (x y z w : K)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)
    (hcurve : OrderTwentyFiveCanonicalOnCurve x y z w)
    (a b : K)
    (hlinear : ∀ i : Fin 4,
      a * orderTwentyFiveCanonicalQuadricGradient x y z w i +
        b * orderTwentyFiveCanonicalCubicGradient x y z w i = 0) :
    a = 0 ∧ b = 0 := by
  rcases orderTwentyFiveCanonical_exists_jacobianMinor_ne_zero
      x y z w hnonzero hcurve with hminor | hminor | hminor |
        hminor | hminor | hminor
  · exact orderTwentyFiveCanonical_jacobianRows_independent_of_minor
      x y z w 0 1 hminor a b hlinear
  · exact orderTwentyFiveCanonical_jacobianRows_independent_of_minor
      x y z w 0 2 hminor a b hlinear
  · exact orderTwentyFiveCanonical_jacobianRows_independent_of_minor
      x y z w 0 3 hminor a b hlinear
  · exact orderTwentyFiveCanonical_jacobianRows_independent_of_minor
      x y z w 1 2 hminor a b hlinear
  · exact orderTwentyFiveCanonical_jacobianRows_independent_of_minor
      x y z w 1 3 hminor a b hlinear
  · exact orderTwentyFiveCanonical_jacobianRows_independent_of_minor
      x y z w 2 3 hminor a b hlinear

/-- The five displayed cusps have visibly nonzero Jacobian minors.  The
chosen minor is `(x,z)` at cusp zero, `(x,y)` at cusps one and two, `(x,w)`
at cusp three, and `(z,w)` at cusp four. -/
theorem orderTwentyFiveCanonicalCusp_jacobianMinor (i : Fin 5) :
    (i = 0 ∧ orderTwentyFiveCanonicalJacobianMinor
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspY i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) 0 2 = 1) ∨
      (i = 1 ∧ orderTwentyFiveCanonicalJacobianMinor
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspY i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) 0 1 = -1) ∨
      (i = 2 ∧ orderTwentyFiveCanonicalJacobianMinor
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspY i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) 0 1 = -1) ∨
      (i = 3 ∧ orderTwentyFiveCanonicalJacobianMinor
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspY i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) 0 3 = -1) ∨
      (i = 4 ∧ orderTwentyFiveCanonicalJacobianMinor
        (orderTwentyFiveCanonicalCuspX i)
        (orderTwentyFiveCanonicalCuspY i)
        (orderTwentyFiveCanonicalCuspZ i)
        (orderTwentyFiveCanonicalCuspW i) 2 3 = -1) := by
  fin_cases i <;>
    norm_num [orderTwentyFiveCanonicalJacobianMinor,
      orderTwentyFiveCanonicalCuspX,
      orderTwentyFiveCanonicalCuspY,
      orderTwentyFiveCanonicalCuspZ,
      orderTwentyFiveCanonicalCuspW,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Fin.ext_iff, Fin.mk.injEq]

end MazurTorsion.Kubert
