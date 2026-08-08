/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFive
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultFiniteField

/-!
# Brunault modular units for order twenty-five

This file connects exact-order points on the Tate normal curve to the
nonzero modular-unit chart of Brunault's genus-four model.  The first step is
geometric: distinct multiples from `2P` through `12P` have distinct
abscissas.  The proof uses the actual Weierstrass points produced by the
checked Tate recurrence; exact order excludes both equality and equality
after negation.

The modular-unit coordinates and the characteristic-zero polynomial identity
are developed below this separation interface.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

private theorem nsmul_ne_nsmul_of_order_twentyFive
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 25) (m n : ℕ)
    (hm25 : m < 25) (hn25 : n < 25) (hmn : m ≠ n) :
    m • P ≠ n • P := by
  intro heq
  rcases lt_or_gt_of_ne hmn with hmnlt | hmnlt
  · have hzero : (n - m) • P = 0 := by
      have hcancel : m • P + (n - m) • P = m • P + 0 := by
        calc
          m • P + (n - m) • P = n • P := by
            rw [← add_nsmul]
            congr 1
            omega
          _ = m • P := heq.symm
          _ = m • P + 0 := (add_zero _).symm
      exact add_left_cancel hcancel
    have hdvd : 25 ∣ n - m := by
      rw [← horder]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
    obtain ⟨k, hk⟩ := hdvd
    omega
  · have hzero : (m - n) • P = 0 := by
      have hcancel : n • P + (m - n) • P = n • P + 0 := by
        calc
          n • P + (m - n) • P = m • P := by
            rw [← add_nsmul]
            congr 1
            omega
          _ = n • P := heq
          _ = n • P + 0 := (add_zero _).symm
      exact add_left_cancel hcancel
    have hdvd : 25 ∣ m - n := by
      rw [← horder]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
    obtain ⟨k, hk⟩ := hdvd
    omega

private theorem nsmul_ne_neg_nsmul_of_order_twentyFive
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 25) (m n : ℕ)
    (hsum_pos : 0 < m + n) (hsum25 : m + n < 25) :
    m • P ≠ -(n • P) := by
  intro heq
  have hzero : (m + n) • P = 0 := by
    rw [add_nsmul, heq, neg_add_cancel]
  have hdvd : 25 ∣ m + n := by
    rw [← horder]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
  obtain ⟨k, hk⟩ := hdvd
  omega

/-- For an exact-order-25 marked point in Tate normal form, the checked
abscissas of distinct multiples among `2P,…,12P` are distinct.  This is the
separation statement used by every denominator and numerator of Brunault's
six-denominator modular-unit chart. -/
theorem tateSuccessiveX_ne_of_marked_order_twentyFive
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    (m n : ℕ) (hm : m ≤ 10) (hn : n ≤ 10) (hmn : m ≠ n) :
    tateSuccessiveX b c m ≠ tateSuccessiveX b c n := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hx :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive
      b c hb h00 horder
  obtain ⟨hmPoint, hmCoord⟩ :=
    nsmul_origin_eq_successiveCoordinates b c hb h00 m
      (fun k hk => hx k (by omega))
  obtain ⟨hnPoint, hnCoord⟩ :=
    nsmul_origin_eq_successiveCoordinates b c hb h00 n
      (fun k hk => hx k (by omega))
  intro hX
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff
      (W := W.toAffine)
      (y₁ := tateSuccessiveY b c m) (y₂ := tateSuccessiveY b c n)
      (h₁ := hmPoint) (h₂ := hnPoint)).mp hX with heq | hneg
  · rw [← hmCoord, ← hnCoord] at heq
    exact nsmul_ne_nsmul_of_order_twentyFive P horder
      (m + 2) (n + 2) (by omega) (by omega) (by omega) heq
  · rw [← hmCoord, ← hnCoord] at hneg
    exact nsmul_ne_neg_nsmul_of_order_twentyFive P horder
      (m + 2) (n + 2) (by omega) (by omega) hneg

/-- The six distinct abscissa differences occurring as denominators in the
corrected Brunault coordinates are nonzero.  This is the first concrete
consumer of `tateSuccessiveX_ne_of_marked_order_twentyFive`. -/
theorem orderTwentyFiveBrunault_denominators_ne_zero
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    0 - tateSuccessiveX b c 1 ≠ 0 ∧
    tateSuccessiveX b c 5 - tateSuccessiveX b c 2 ≠ 0 ∧
    tateSuccessiveX b c 2 - tateSuccessiveX b c 10 ≠ 0 ∧
    tateSuccessiveX b c 1 - tateSuccessiveX b c 7 ≠ 0 ∧
    tateSuccessiveX b c 7 - tateSuccessiveX b c 0 ≠ 0 ∧
    tateSuccessiveX b c 10 - tateSuccessiveX b c 9 ≠ 0 := by
  have hx0 :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive
      b c hb h00 horder
  have hxy :=
    tateSuccessiveX_ne_of_marked_order_twentyFive
      b c hb h00 horder
  refine ⟨sub_ne_zero.mpr (hx0 1 (by omega)).symm, ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 5 2 (by omega) (by omega) (by omega)), ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 2 10 (by omega) (by omega) (by omega)), ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 1 7 (by omega) (by omega) (by omega)), ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 7 0 (by omega) (by omega) (by omega)), ?_⟩
  exact sub_ne_zero.mpr (hxy 10 9 (by omega) (by omega) (by omega))

/-- Brunault's modular unit `y₄`, written in terms of the checked Tate
abscissas `x(kP)`. -/
def orderTwentyFiveBrunaultYFour (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 2 - tateSuccessiveX b c 0) /
      (tateSuccessiveX b c 2 - tateSuccessiveX b c 10)) *
    ((tateSuccessiveX b c 1 - tateSuccessiveX b c 9) /
      (tateSuccessiveX b c 1 - tateSuccessiveX b c 7))

/-- Brunault's modular unit `y₇`, written in terms of the checked Tate
abscissas `x(kP)`. -/
def orderTwentyFiveBrunaultYSeven (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 5 - tateSuccessiveX b c 7) /
      (tateSuccessiveX b c 5 - tateSuccessiveX b c 2)) *
    ((0 - tateSuccessiveX b c 10) /
      (0 - tateSuccessiveX b c 1))

/-- Brunault's modular unit `y₉`, written in terms of the checked Tate
abscissas `x(kP)`. -/
def orderTwentyFiveBrunaultYNine (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 7 - tateSuccessiveX b c 6) /
      (tateSuccessiveX b c 7 - tateSuccessiveX b c 0)) *
    ((tateSuccessiveX b c 10 - tateSuccessiveX b c 4) /
      (tateSuccessiveX b c 10 - tateSuccessiveX b c 9))

/-- Brunault's modular unit `y₃`, written in terms of the checked Tate
abscissas `x(kP)`. -/
def orderTwentyFiveBrunaultYThree (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 1 - tateSuccessiveX b c 9) /
      (tateSuccessiveX b c 1 - tateSuccessiveX b c 7)) *
    ((tateSuccessiveX b c 2 - tateSuccessiveX b c 0) /
      (tateSuccessiveX b c 2 - tateSuccessiveX b c 10))

/-- Brunault's corrected first coordinate: `u = y₄ y₇`. -/
def orderTwentyFiveBrunaultU (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYFour b c * orderTwentyFiveBrunaultYSeven b c

/-- Brunault's corrected second coordinate: `v = -(y₉ y₃)`. -/
def orderTwentyFiveBrunaultV (b c : ℚ) : ℚ :=
  -(orderTwentyFiveBrunaultYNine b c * orderTwentyFiveBrunaultYThree b c)

private theorem orderTwentyFiveBrunault_numerators_ne_zero
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    tateSuccessiveX b c 2 - tateSuccessiveX b c 0 ≠ 0 ∧
    tateSuccessiveX b c 1 - tateSuccessiveX b c 9 ≠ 0 ∧
    tateSuccessiveX b c 5 - tateSuccessiveX b c 7 ≠ 0 ∧
    0 - tateSuccessiveX b c 10 ≠ 0 ∧
    tateSuccessiveX b c 7 - tateSuccessiveX b c 6 ≠ 0 ∧
    tateSuccessiveX b c 10 - tateSuccessiveX b c 4 ≠ 0 := by
  have hx0 :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive
      b c hb h00 horder
  have hxy :=
    tateSuccessiveX_ne_of_marked_order_twentyFive
      b c hb h00 horder
  refine ⟨sub_ne_zero.mpr (hxy 2 0 (by omega) (by omega) (by omega)), ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 1 9 (by omega) (by omega) (by omega)), ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 5 7 (by omega) (by omega) (by omega)), ?_⟩
  refine ⟨sub_ne_zero.mpr (hx0 10 (by omega)).symm, ?_⟩
  refine ⟨sub_ne_zero.mpr (hxy 7 6 (by omega) (by omega) (by omega)), ?_⟩
  exact sub_ne_zero.mpr (hxy 10 4 (by omega) (by omega) (by omega))

/-- On an exact-order-25 marked Tate curve, both corrected Brunault
coordinates lie in the nonzero modular-unit chart. -/
theorem orderTwentyFiveBrunault_units_ne_zero
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveBrunaultU b c ≠ 0 ∧
      orderTwentyFiveBrunaultV b c ≠ 0 := by
  obtain ⟨hd13, hd74, hd4twelve, hd39, hd92, hd12eleven⟩ :=
    orderTwentyFiveBrunault_denominators_ne_zero b c hb h00 horder
  obtain ⟨hn42, hn3eleven, hn79, hn1twelve, hn98, hn126⟩ :=
    orderTwentyFiveBrunault_numerators_ne_zero b c hb h00 horder
  constructor
  · exact mul_ne_zero
      (mul_ne_zero (div_ne_zero hn42 hd4twelve) (div_ne_zero hn3eleven hd39))
      (mul_ne_zero (div_ne_zero hn79 hd74) (div_ne_zero hn1twelve hd13))
  · exact neg_ne_zero.mpr <| mul_ne_zero
      (mul_ne_zero (div_ne_zero hn98 hd92) (div_ne_zero hn126 hd12eleven))
      (mul_ne_zero (div_ne_zero hn3eleven hd39) (div_ne_zero hn42 hd4twelve))

end MazurTorsion.Kubert
