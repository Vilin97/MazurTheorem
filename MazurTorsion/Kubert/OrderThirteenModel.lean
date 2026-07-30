/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirteenReduction

/-!
# A hyperelliptic model for the order-thirteen parameter curve

This file gives a checked rational map from the reduced Tate-parameter equation
in `OrderThirteenReduction` to the standard sextic model

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

The map is obtained by elementary completion of the square after resolving the
singular plane model.  Its only denominators are `s-1` and `r-s`; both were
already proved nonzero from exact order in the preceding reduction.

The two rational affine cusp abscissas on the sextic are `0` and `-1`.  The
forward image of an exact-order certificate has neither abscissa: `x = 0`
would discard `r-1` or `s-1`, while `x = -1` would discard the separately
retained factor `rs-2r+1`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The sextic defining the hyperelliptic model of `X₁(13)`. -/
def orderThirteenHyperellipticPolynomial (x : ℚ) : ℚ :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- The hyperelliptic abscissa attached to a reduced Tate certificate. -/
def orderThirteenHyperellipticX (r s : ℚ) : ℚ :=
  -((r - 1) * (s - 1) / (r - s))

/-- The hyperelliptic ordinate attached to a reduced Tate certificate.

Writing `U = (r-1)(s-1)/(r-s)` and `V = (r-s)/(1-s)`, the intermediate
quadratic model is

`V² + (U³-U²-1)V - U² + U = 0`.

Completing its square and replacing `U` by `-x` gives the displayed formula. -/
def orderThirteenHyperellipticY (r s : ℚ) : ℚ :=
  let U := (r - 1) * (s - 1) / (r - s)
  let V := (r - s) / (1 - s)
  2 * V + (U ^ 3 - U ^ 2 - 1)

/-- Cleared polynomial identity underlying the rational map to the sextic. -/
lemma orderThirteen_hyperelliptic_cleared_identity
    (r s : ℚ) (hsone : s ≠ 1) (hrs : r ≠ s) :
    (r - s) ^ 2 * (s - 1) ^ 2 *
        (orderThirteenHyperellipticY r s ^ 2 -
          orderThirteenHyperellipticPolynomial
            (orderThirteenHyperellipticX r s)) =
      4 * (r - 1) * orderThirteenReducedPolynomial r s := by
  simp only [orderThirteenHyperellipticY,
    orderThirteenHyperellipticX,
    orderThirteenHyperellipticPolynomial,
    orderThirteenReducedPolynomial]
  field_simp [sub_ne_zero.mpr hsone, sub_ne_zero.mpr hrs]
  ring

/-- A noncuspidal point on the reduced Tate model maps to the hyperelliptic
sextic. -/
theorem orderThirteen_reduced_to_hyperelliptic
    (r s : ℚ) (hsone : s ≠ 1) (hrs : r ≠ s)
    (hreduced : orderThirteenReducedPolynomial r s = 0) :
    orderThirteenHyperellipticY r s ^ 2 =
      orderThirteenHyperellipticPolynomial
        (orderThirteenHyperellipticX r s) := by
  have hidentity :=
    orderThirteen_hyperelliptic_cleared_identity r s hsone hrs
  rw [hreduced, mul_zero] at hidentity
  have hprefactor : (r - s) ^ 2 * (s - 1) ^ 2 ≠ 0 :=
    mul_ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr hrs))
      (pow_ne_zero 2 (sub_ne_zero.mpr hsone))
  exact sub_eq_zero.mp <|
    (mul_eq_zero.mp hidentity).resolve_left hprefactor

lemma orderThirteenHyperellipticX_ne_zero
    (r s : ℚ) (hrone : r ≠ 1) (hsone : s ≠ 1) (hrs : r ≠ s) :
    orderThirteenHyperellipticX r s ≠ 0 := by
  simp only [orderThirteenHyperellipticX]
  exact neg_ne_zero.mpr <|
    div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hrone) (sub_ne_zero.mpr hsone))
      (sub_ne_zero.mpr hrs)

lemma orderThirteenHyperellipticX_ne_neg_one
    (r s : ℚ) (hrs : r ≠ s)
    (hfactor : r * s - 2 * r + 1 ≠ 0) :
    orderThirteenHyperellipticX r s ≠ -1 := by
  intro hx
  apply hfactor
  simp only [orderThirteenHyperellipticX] at hx
  field_simp [sub_ne_zero.mpr hrs] at hx
  linear_combination -hx

/-- An exact rational point of order `13` produces an affine rational point on
the standard sextic whose abscissa is neither rational affine cusp abscissa. -/
theorem exists_orderThirteen_hyperelliptic_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 13) :
    ∃ x y : ℚ,
      y ^ 2 = orderThirteenHyperellipticPolynomial x ∧
      x ≠ 0 ∧ x ≠ -1 := by
  obtain ⟨b, c, u, r, s, hu, hb, hc, hbc, hA, hB, hC, hpoly,
      hdisc, hr, hs, hrzero, hrone, hszero, hsone, hrs, hfactor,
      hbsub, hcsub, hreduced⟩ :=
    exists_tateOrderThirteen_certificate E Q hQ
  let x := orderThirteenHyperellipticX r s
  let y := orderThirteenHyperellipticY r s
  have hcurve : y ^ 2 = orderThirteenHyperellipticPolynomial x := by
    exact orderThirteen_reduced_to_hyperelliptic r s hsone hrs hreduced
  have hxzero : x ≠ 0 :=
    orderThirteenHyperellipticX_ne_zero r s hrone hsone hrs
  have hxnegone : x ≠ -1 :=
    orderThirteenHyperellipticX_ne_neg_one r s hrs hfactor
  exact ⟨x, y, hcurve, hxzero, hxnegone⟩

end MazurTorsion.Kubert
