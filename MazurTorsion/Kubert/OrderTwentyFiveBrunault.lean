/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFive

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

/-- Lécacheux's modular unit `y₁`, written in terms of the checked Tate
abscissas `x(kP)`.  Multiplication by the diamond operator `7` fixes this
unit, which is why the pre-existing coordinate `y₇` agrees with it. -/
def orderTwentyFiveBrunaultYOne (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 5 - tateSuccessiveX b c 7) /
      (tateSuccessiveX b c 5 - tateSuccessiveX b c 2)) *
    ((0 - tateSuccessiveX b c 10) /
      (0 - tateSuccessiveX b c 1))

/-- Lécacheux's modular unit `y₂`, the first diamond translate of
`y₁`, written as two abscissa cross-ratios. -/
def orderTwentyFiveBrunaultYTwo (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 0 - 0) /
      (tateSuccessiveX b c 0 - tateSuccessiveX b c 4)) *
    ((tateSuccessiveX b c 9 - tateSuccessiveX b c 5) /
      (tateSuccessiveX b c 9 - tateSuccessiveX b c 6))

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

/-- Lécacheux's modular unit `y₈`, the third diamond translate of
`y₁`, written as two abscissa cross-ratios. -/
def orderTwentyFiveBrunaultYEight (b c : ℚ) : ℚ :=
  ((tateSuccessiveX b c 6 - tateSuccessiveX b c 2) /
      (tateSuccessiveX b c 6 - 0)) *
    ((tateSuccessiveX b c 4 - tateSuccessiveX b c 1) /
      (tateSuccessiveX b c 4 - tateSuccessiveX b c 5))

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

/-- The quotient diamond action identifies Lécacheux's `y₇` with
`y₁`. -/
theorem orderTwentyFiveBrunaultYSeven_eq_yOne (b c : ℚ) :
    orderTwentyFiveBrunaultYSeven b c =
      orderTwentyFiveBrunaultYOne b c :=
  rfl

/-- The quotient diamond action identifies Lécacheux's `y₃` with
`y₄`. -/
theorem orderTwentyFiveBrunaultYThree_eq_yFour (b c : ℚ) :
    orderTwentyFiveBrunaultYThree b c =
      orderTwentyFiveBrunaultYFour b c := by
  unfold orderTwentyFiveBrunaultYThree orderTwentyFiveBrunaultYFour
  ring

/-- Brunault's corrected first coordinate: `u = y₄ y₇`. -/
def orderTwentyFiveBrunaultU (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYFour b c * orderTwentyFiveBrunaultYSeven b c

/-- Brunault's corrected second coordinate: `v = -(y₉ y₃)`. -/
def orderTwentyFiveBrunaultV (b c : ℚ) : ℚ :=
  -(orderTwentyFiveBrunaultYNine b c * orderTwentyFiveBrunaultYThree b c)

/-- Lécacheux's first orbit unit `x₀ = y₁y₄`. -/
def orderTwentyFiveBrunaultXZero (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYOne b c * orderTwentyFiveBrunaultYFour b c

/-- Lécacheux's second orbit unit `x₁ = y₂y₈`. -/
def orderTwentyFiveBrunaultXOne (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYTwo b c * orderTwentyFiveBrunaultYEight b c

/-- Lécacheux's third orbit unit `x₂ = y₄y₉`. -/
def orderTwentyFiveBrunaultXTwo (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYFour b c * orderTwentyFiveBrunaultYNine b c

/-- Lécacheux's fourth orbit unit `x₃ = y₈y₁`. -/
def orderTwentyFiveBrunaultXThree (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYEight b c * orderTwentyFiveBrunaultYOne b c

/-- Lécacheux's fifth orbit unit `x₄ = y₉y₂`. -/
def orderTwentyFiveBrunaultXFour (b c : ℚ) : ℚ :=
  orderTwentyFiveBrunaultYNine b c * orderTwentyFiveBrunaultYTwo b c

/-- Brunault's first coordinate is Lécacheux's orbit unit `x₀`. -/
theorem orderTwentyFiveBrunaultXZero_eq_U (b c : ℚ) :
    orderTwentyFiveBrunaultXZero b c =
      orderTwentyFiveBrunaultU b c := by
  rw [orderTwentyFiveBrunaultXZero, orderTwentyFiveBrunaultU,
    orderTwentyFiveBrunaultYSeven_eq_yOne]
  ring

/-- The negative of Brunault's second coordinate is Lécacheux's orbit
unit `x₂`. -/
theorem orderTwentyFiveBrunaultXTwo_eq_neg_V (b c : ℚ) :
    orderTwentyFiveBrunaultXTwo b c =
      -orderTwentyFiveBrunaultV b c := by
  rw [orderTwentyFiveBrunaultXTwo, orderTwentyFiveBrunaultV,
    orderTwentyFiveBrunaultYThree_eq_yFour]
  ring

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

/-- On an exact-order-25 marked Tate curve, all five Lécacheux orbit
units lie in the nonzero modular-unit chart.  The two new cross-ratios use
only the same exact-order abscissa separation as the original Brunault
coordinates. -/
theorem orderTwentyFiveBrunault_orbit_units_ne_zero
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveBrunaultXZero b c ≠ 0 ∧
      orderTwentyFiveBrunaultXOne b c ≠ 0 ∧
      orderTwentyFiveBrunaultXTwo b c ≠ 0 ∧
      orderTwentyFiveBrunaultXThree b c ≠ 0 ∧
      orderTwentyFiveBrunaultXFour b c ≠ 0 := by
  have hx0 :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive
      b c hb h00 horder
  have hxy :=
    tateSuccessiveX_ne_of_marked_order_twentyFive
      b c hb h00 horder
  have hyTwo : orderTwentyFiveBrunaultYTwo b c ≠ 0 := by
    unfold orderTwentyFiveBrunaultYTwo
    exact mul_ne_zero
      (div_ne_zero
        (sub_ne_zero.mpr (hx0 0 (by omega)))
        (sub_ne_zero.mpr (hxy 0 4 (by omega) (by omega) (by omega))))
      (div_ne_zero
        (sub_ne_zero.mpr (hxy 9 5 (by omega) (by omega) (by omega)))
        (sub_ne_zero.mpr (hxy 9 6 (by omega) (by omega) (by omega))))
  have hyEight : orderTwentyFiveBrunaultYEight b c ≠ 0 := by
    unfold orderTwentyFiveBrunaultYEight
    exact mul_ne_zero
      (div_ne_zero
        (sub_ne_zero.mpr (hxy 6 2 (by omega) (by omega) (by omega)))
        (sub_ne_zero.mpr (hx0 6 (by omega))))
      (div_ne_zero
        (sub_ne_zero.mpr (hxy 4 1 (by omega) (by omega) (by omega)))
        (sub_ne_zero.mpr (hxy 4 5 (by omega) (by omega) (by omega))))
  obtain ⟨hU, hV⟩ :=
    orderTwentyFiveBrunault_units_ne_zero b c hb h00 horder
  have hyOne : orderTwentyFiveBrunaultYOne b c ≠ 0 := by
    intro hyOne
    apply hU
    simp [orderTwentyFiveBrunaultU,
      orderTwentyFiveBrunaultYSeven_eq_yOne, hyOne]
  have hyFour : orderTwentyFiveBrunaultYFour b c ≠ 0 := by
    intro hyFour
    apply hU
    simp [orderTwentyFiveBrunaultU, hyFour]
  have hyNine : orderTwentyFiveBrunaultYNine b c ≠ 0 := by
    intro hyNine
    apply hV
    simp [orderTwentyFiveBrunaultV, hyNine]
  exact ⟨
    mul_ne_zero hyOne hyFour,
    mul_ne_zero hyTwo hyEight,
    mul_ne_zero hyFour hyNine,
    mul_ne_zero hyEight hyOne,
    mul_ne_zero hyNine hyTwo⟩

end MazurTorsion.Kubert
