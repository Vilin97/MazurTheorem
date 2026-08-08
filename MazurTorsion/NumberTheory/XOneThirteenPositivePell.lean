/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenDescent

/-!
# Integral Pell allocation for the positive `X₁(13)` split system

The normalized cyclic-cubic descent in `XOneThirteenDescent` leaves one
positive system.  This file carries that system back to an integral point on
the homogeneous order-thirteen sextic.  The odd conic parameters give the
canonical positive ordinate `c=(m²+n²)/2`, and the two split coefficient
identities prove the sextic equation without introducing a new hypothesis.

Homogenizing the checked degree-`19` polynomial Pell certificate then gives

`(H+cK)(cK-H)=4b³⁸`.

Both factors are positive.  Moreover, primitivity of `(a,b)` shows that no
odd prime can divide both factors, so every odd prime in the denominator is
allocated to exactly one factor.  This is the arithmetic input needed to
continue from the Pell certificate to a power/divisor-class descent.

The final allocated-factor obstruction below is still a boundary, not a
rational-point classification or a Jacobian rank computation.  It has a
checked exact-order-thirteen consumer.
-/

namespace MazurTorsion.XOneThirteenDescent

open scoped WeierstrassCurve.Affine

/-- The degree-six integral homogenization of the order-thirteen sextic. -/
def integerSexticHomogeneous (a b : ℤ) : ℤ :=
  a ^ 6 + 2 * a ^ 5 * b + a ^ 4 * b ^ 2 +
    2 * a ^ 3 * b ^ 3 + 6 * a ^ 2 * b ^ 4 +
    4 * a * b ^ 5 + b ^ 6

private def rootTrace (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a * b ^ 2 - b ^ 3

private def rootProduct (a b : ℤ) : ℤ :=
  a * b * (a + b)

private lemma integerSexticHomogeneous_eq (a b : ℤ) :
    integerSexticHomogeneous a b =
      4 * rootProduct a b ^ 2 +
        (rootTrace a b + rootProduct a b) ^ 2 := by
  simp only [integerSexticHomogeneous, rootProduct, rootTrace]
  ring

/-- The odd positive split parameters supply the canonical positive
integral ordinate `c=(m²+n²)/2` on the homogeneous sextic. -/
theorem positive_split_homogeneous_curve
    (m n a b : ℤ) (hnpos : 0 < n) (hmOdd : Odd m) (hnOdd : Odd n)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3)) :
    ∃ c : ℤ, 0 < c ∧ 2 * c = m ^ 2 + n ^ 2 ∧
      c ^ 2 = integerSexticHomogeneous a b := by
  obtain ⟨r, hr⟩ := hmOdd
  obtain ⟨s, hs⟩ := hnOdd
  let c : ℤ := 2 * r ^ 2 + 2 * r + 2 * s ^ 2 + 2 * s + 1
  have hc : 2 * c = m ^ 2 + n ^ 2 := by
    rw [hr, hs]
    simp only [c]
    ring
  have hcpos : 0 < c := by
    have hnsq : 0 < n ^ 2 := sq_pos_of_pos hnpos
    nlinarith [sq_nonneg m]
  have hmn : m * n = rootTrace a b + rootProduct a b := by
    simp only [rootTrace, rootProduct]
    linarith
  refine ⟨c, hcpos, hc, ?_⟩
  have hpoly := integerSexticHomogeneous_eq a b
  rw [hpoly, ← hmn]
  have hlead' : n ^ 2 - m ^ 2 = 4 * rootProduct a b := by
    simpa only [rootProduct] using hlead
  nlinarith [sq_nonneg (n ^ 2 - m ^ 2)]

/-- The integral sextic is the degree-six homogenization of the affine
order-thirteen polynomial. -/
theorem integerSexticHomogeneous_eq_den_pow_mul
    (a b : ℤ) (hb : b ≠ 0) :
    (integerSexticHomogeneous a b : ℚ) =
      (b : ℚ) ^ 6 *
        MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial
          ((a : ℚ) / (b : ℚ)) := by
  simp only [integerSexticHomogeneous,
    MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp [Int.cast_ne_zero.mpr hb]

/-- The canonical integral ordinate supplied by a positive split system
dehomogenizes to an actual rational point on the order-thirteen sextic. -/
theorem positive_split_rational_curve_point
    (m n a b : ℤ) (hnpos : 0 < n) (hbpos : 0 < b)
    (hmOdd : Odd m) (hnOdd : Odd n)
    (hlead : n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)))
    (htrace : m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3)) :
    ∃ c : ℤ,
      0 < c ∧
      2 * c = m ^ 2 + n ^ 2 ∧
      c ^ 2 = integerSexticHomogeneous a b ∧
      ((c : ℚ) / (b : ℚ) ^ 3) ^ 2 =
        MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial
          ((a : ℚ) / (b : ℚ)) := by
  obtain ⟨c, hc, htwice, hcurve⟩ :=
    positive_split_homogeneous_curve
      m n a b hnpos hmOdd hnOdd hlead htrace
  refine ⟨c, hc, htwice, hcurve, ?_⟩
  have hb : b ≠ 0 := ne_of_gt hbpos
  have hhom := integerSexticHomogeneous_eq_den_pow_mul a b hb
  have hcurveQ :
      (c : ℚ) ^ 2 = (integerSexticHomogeneous a b : ℚ) := by
    exact_mod_cast hcurve
  calc
    ((c : ℚ) / (b : ℚ) ^ 3) ^ 2 =
        (c : ℚ) ^ 2 / (b : ℚ) ^ 6 := by ring
    _ = (integerSexticHomogeneous a b : ℚ) / (b : ℚ) ^ 6 := by
      rw [hcurveQ]
    _ = MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial
          ((a : ℚ) / (b : ℚ)) := by
      rw [hhom]
      field_simp [Int.cast_ne_zero.mpr hb]

/-- A primitive abscissa and an integral ordinate on the homogeneous
sextic remain coprime at the denominator. -/
theorem positive_split_ordinate_coprime
    (a b c : ℤ) (hab : IsCoprime a b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    IsCoprime c b := by
  have hpoly :
      integerSexticHomogeneous a b = a ^ 6 + b *
        (2 * a ^ 5 + a ^ 4 * b + 2 * a ^ 3 * b ^ 2 +
          6 * a ^ 2 * b ^ 3 + 4 * a * b ^ 4 + b ^ 5) := by
    simp only [integerSexticHomogeneous]
    ring
  have hcopSq : IsCoprime (c ^ 2) b := by
    rw [hcurve, hpoly]
    exact (hab.pow_left (m := 6)).add_mul_left_left _
  have hcopMul : IsCoprime (c * c) b := by
    simpa only [pow_two] using hcopSq
  exact hcopMul.of_mul_left_left

/-- Degree-`19` integral homogenization of the Pell numerator. -/
def pellHHomogeneous (a b : ℤ) : ℤ :=
  a ^ 19 + 3 * a ^ 18 * b + 2 * a ^ 17 * b ^ 2 +
    5 * a ^ 16 * b ^ 3 + 22 * a ^ 15 * b ^ 4 +
    22 * a ^ 14 * b ^ 5 + 10 * a ^ 13 * b ^ 6 +
    54 * a ^ 12 * b ^ 7 + 78 * a ^ 11 * b ^ 8 +
    20 * a ^ 10 * b ^ 9 + 51 * a ^ 9 * b ^ 10 +
    113 * a ^ 8 * b ^ 11 + 36 * a ^ 7 * b ^ 12 +
    13 * a ^ 6 * b ^ 13 + 66 * a ^ 5 * b ^ 14 +
    26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16 +
    12 * a ^ 2 * b ^ 17 + 4 * a * b ^ 18

/-- Degree-`16` integral homogenization of the Pell denominator. -/
def pellKHomogeneous (a b : ℤ) : ℤ :=
  a ^ 16 + 2 * a ^ 15 * b + 4 * a ^ 13 * b ^ 3 +
    14 * a ^ 12 * b ^ 4 + 4 * a ^ 11 * b ^ 5 +
    2 * a ^ 10 * b ^ 6 + 32 * a ^ 9 * b ^ 7 +
    18 * a ^ 8 * b ^ 8 - 8 * a ^ 7 * b ^ 9 +
    29 * a ^ 6 * b ^ 10 + 24 * a ^ 5 * b ^ 11 -
    10 * a ^ 4 * b ^ 12 + 10 * a ^ 3 * b ^ 13 +
    10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 + 2 * b ^ 16

/-- The degree-`19` integral form is the homogenization of `pellH`. -/
theorem pellHHomogeneous_eq_den_pow_mul
    (a b : ℤ) (hb : b ≠ 0) :
    (pellHHomogeneous a b : ℚ) =
      (b : ℚ) ^ 19 * pellH ((a : ℚ) / (b : ℚ)) := by
  simp only [pellHHomogeneous, pellH, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp [Int.cast_ne_zero.mpr hb]

/-- The degree-`16` integral form is the homogenization of `pellK`. -/
theorem pellKHomogeneous_eq_den_pow_mul
    (a b : ℤ) (hb : b ≠ 0) :
    (pellKHomogeneous a b : ℚ) =
      (b : ℚ) ^ 16 * pellK ((a : ℚ) / (b : ℚ)) := by
  simp only [pellKHomogeneous, pellK, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp [Int.cast_ne_zero.mpr hb]

/-- Homogeneous integral form of the degree-`19` polynomial Pell identity. -/
theorem homogeneous_pell_identity (a b : ℤ) :
    pellHHomogeneous a b ^ 2 -
        integerSexticHomogeneous a b * pellKHomogeneous a b ^ 2 =
      -4 * b ^ 38 := by
  simp only [pellHHomogeneous, pellKHomogeneous,
    integerSexticHomogeneous]
  ring

/-- On an integral point of the homogeneous sextic, the two conjugate
homogeneous Pell values have product `-4b³⁸`. -/
theorem homogeneous_pell_factorization
    (a b c : ℤ)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    (pellHHomogeneous a b + c * pellKHomogeneous a b) *
        (pellHHomogeneous a b - c * pellKHomogeneous a b) =
      -4 * b ^ 38 := by
  calc
    _ = pellHHomogeneous a b ^ 2 -
          c ^ 2 * pellKHomogeneous a b ^ 2 := by ring
    _ = pellHHomogeneous a b ^ 2 -
          integerSexticHomogeneous a b * pellKHomogeneous a b ^ 2 := by
      rw [hcurve]
    _ = -4 * b ^ 38 := homogeneous_pell_identity a b

/-- The homogeneous Pell numerator is positive in the positive chamber. -/
theorem pellHHomogeneous_pos
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    0 < pellHHomogeneous a b := by
  by_cases hab : a ≤ b
  · have hsquare : 0 ≤ b ^ 2 - a ^ 2 := by
      have hmul : 0 ≤ (b - a) * (b + a) :=
        mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb.le ha.le)
      nlinarith
    have hcoefficient : 0 < 2 * b ^ 2 - a ^ 2 := by
      nlinarith [sq_pos_of_pos hb]
    have hpair :
        0 < 4 * a * b ^ 18 - 2 * a ^ 3 * b ^ 16 := by
      rw [show 4 * a * b ^ 18 - 2 * a ^ 3 * b ^ 16 =
        2 * a * b ^ 16 * (2 * b ^ 2 - a ^ 2) by ring]
      positivity
    rw [show pellHHomogeneous a b =
      (4 * a * b ^ 18 - 2 * a ^ 3 * b ^ 16) +
        (a ^ 19 + 3 * a ^ 18 * b + 2 * a ^ 17 * b ^ 2 +
          5 * a ^ 16 * b ^ 3 + 22 * a ^ 15 * b ^ 4 +
          22 * a ^ 14 * b ^ 5 + 10 * a ^ 13 * b ^ 6 +
          54 * a ^ 12 * b ^ 7 + 78 * a ^ 11 * b ^ 8 +
          20 * a ^ 10 * b ^ 9 + 51 * a ^ 9 * b ^ 10 +
          113 * a ^ 8 * b ^ 11 + 36 * a ^ 7 * b ^ 12 +
          13 * a ^ 6 * b ^ 13 + 66 * a ^ 5 * b ^ 14 +
          26 * a ^ 4 * b ^ 15 + 12 * a ^ 2 * b ^ 17) by
      simp only [pellHHomogeneous]
      ring]
    positivity
  · have hba : b < a := lt_of_not_ge hab
    have hcoefficient : 0 < 13 * a - b := by linarith
    have hpair :
        0 < 26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16 := by
      rw [show 26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16 =
        2 * a ^ 3 * b ^ 15 * (13 * a - b) by ring]
      positivity
    rw [show pellHHomogeneous a b =
      (26 * a ^ 4 * b ^ 15 - 2 * a ^ 3 * b ^ 16) +
        (a ^ 19 + 3 * a ^ 18 * b + 2 * a ^ 17 * b ^ 2 +
          5 * a ^ 16 * b ^ 3 + 22 * a ^ 15 * b ^ 4 +
          22 * a ^ 14 * b ^ 5 + 10 * a ^ 13 * b ^ 6 +
          54 * a ^ 12 * b ^ 7 + 78 * a ^ 11 * b ^ 8 +
          20 * a ^ 10 * b ^ 9 + 51 * a ^ 9 * b ^ 10 +
          113 * a ^ 8 * b ^ 11 + 36 * a ^ 7 * b ^ 12 +
          13 * a ^ 6 * b ^ 13 + 66 * a ^ 5 * b ^ 14 +
          12 * a ^ 2 * b ^ 17 + 4 * a * b ^ 18) by
      simp only [pellHHomogeneous]
      ring]
    positivity

/-- The homogeneous Pell denominator is positive in the positive chamber. -/
theorem pellKHomogeneous_pos
    (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    0 < pellKHomogeneous a b := by
  have hquadratic : 0 < 5 * a ^ 2 - 2 * a * b + b ^ 2 := by
    rw [show 5 * a ^ 2 - 2 * a * b + b ^ 2 =
      4 * a ^ 2 + (a - b) ^ 2 by ring]
    positivity
  by_cases hab : a ≤ b
  · have hba : 0 ≤ b - a := sub_nonneg.mpr hab
    have hfirstCoefficient : 0 < 29 * b - 8 * a := by
      nlinarith
    have hfirst :
        0 < 29 * a ^ 6 * b ^ 10 - 8 * a ^ 7 * b ^ 9 := by
      rw [show 29 * a ^ 6 * b ^ 10 - 8 * a ^ 7 * b ^ 9 =
        a ^ 6 * b ^ 9 * (29 * b - 8 * a) by ring]
      positivity
    have hsecond :
        0 ≤ 10 * a ^ 3 * b ^ 13 - 10 * a ^ 4 * b ^ 12 := by
      rw [show 10 * a ^ 3 * b ^ 13 - 10 * a ^ 4 * b ^ 12 =
        10 * a ^ 3 * b ^ 12 * (b - a) by ring]
      positivity
    have hthird :
        0 < 10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 +
          2 * b ^ 16 := by
      rw [show 10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 +
          2 * b ^ 16 =
        2 * b ^ 14 * (5 * a ^ 2 - 2 * a * b + b ^ 2) by ring]
      positivity
    rw [show pellKHomogeneous a b =
      (29 * a ^ 6 * b ^ 10 - 8 * a ^ 7 * b ^ 9) +
        (10 * a ^ 3 * b ^ 13 - 10 * a ^ 4 * b ^ 12) +
        (10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 + 2 * b ^ 16) +
        (a ^ 16 + 2 * a ^ 15 * b + 4 * a ^ 13 * b ^ 3 +
          14 * a ^ 12 * b ^ 4 + 4 * a ^ 11 * b ^ 5 +
          2 * a ^ 10 * b ^ 6 + 32 * a ^ 9 * b ^ 7 +
          18 * a ^ 8 * b ^ 8 + 24 * a ^ 5 * b ^ 11) by
      simp only [pellKHomogeneous]
      ring]
    positivity
  · have hba : b < a := lt_of_not_ge hab
    have hfirstCoefficient : 0 < 9 * a - 4 * b := by linarith
    have hsecondCoefficient : 0 < 12 * a - 5 * b := by linarith
    have hfirst :
        0 < 18 * a ^ 8 * b ^ 8 - 8 * a ^ 7 * b ^ 9 := by
      rw [show 18 * a ^ 8 * b ^ 8 - 8 * a ^ 7 * b ^ 9 =
        2 * a ^ 7 * b ^ 8 * (9 * a - 4 * b) by ring]
      positivity
    have hsecond :
        0 < 24 * a ^ 5 * b ^ 11 - 10 * a ^ 4 * b ^ 12 := by
      rw [show 24 * a ^ 5 * b ^ 11 - 10 * a ^ 4 * b ^ 12 =
        2 * a ^ 4 * b ^ 11 * (12 * a - 5 * b) by ring]
      positivity
    have hthird :
        0 < 10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 +
          2 * b ^ 16 := by
      rw [show 10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 +
          2 * b ^ 16 =
        2 * b ^ 14 * (5 * a ^ 2 - 2 * a * b + b ^ 2) by ring]
      positivity
    rw [show pellKHomogeneous a b =
      (18 * a ^ 8 * b ^ 8 - 8 * a ^ 7 * b ^ 9) +
        (24 * a ^ 5 * b ^ 11 - 10 * a ^ 4 * b ^ 12) +
        (10 * a ^ 2 * b ^ 14 - 4 * a * b ^ 15 + 2 * b ^ 16) +
        (a ^ 16 + 2 * a ^ 15 * b + 4 * a ^ 13 * b ^ 3 +
          14 * a ^ 12 * b ^ 4 + 4 * a ^ 11 * b ^ 5 +
          2 * a ^ 10 * b ^ 6 + 32 * a ^ 9 * b ^ 7 +
          29 * a ^ 6 * b ^ 10 + 10 * a ^ 3 * b ^ 13) by
      simp only [pellKHomogeneous]
      ring]
    positivity

/-- At a positive integral sextic point, the `H+cK` Pell factor is
positive and its conjugate `H-cK` is negative. -/
theorem homogeneous_pell_factor_signs
    (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    0 < pellHHomogeneous a b + c * pellKHomogeneous a b ∧
      pellHHomogeneous a b - c * pellKHomogeneous a b < 0 := by
  have hproduct := homogeneous_pell_factorization a b c hcurve
  have hbpow : 0 < b ^ 38 := pow_pos hb 38
  have hH : 0 < pellHHomogeneous a b :=
    pellHHomogeneous_pos a b ha hb
  have hK : 0 < pellKHomogeneous a b :=
    pellKHomogeneous_pos a b ha hb
  have hneg :
      (pellHHomogeneous a b + c * pellKHomogeneous a b) *
          (pellHHomogeneous a b - c * pellKHomogeneous a b) < 0 := by
    rw [hproduct]
    nlinarith
  rcases mul_neg_iff.mp hneg with hcase | hcase
  · exact hcase
  · exfalso
    have hcK : 0 < c * pellKHomogeneous a b := mul_pos hc hK
    linarith

/-- The positive homogeneous Pell factor `H+cK`. -/
def positivePellFactor (a b c : ℤ) : ℤ :=
  pellHHomogeneous a b + c * pellKHomogeneous a b

/-- The positive magnitude `cK-H` of the negative conjugate factor. -/
def negativePellFactorMagnitude (a b c : ℤ) : ℤ :=
  c * pellKHomogeneous a b - pellHHomogeneous a b

/-- Product formula for the two positive Pell-factor magnitudes. -/
theorem positive_pell_factorization
    (a b c : ℤ)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    positivePellFactor a b c * negativePellFactorMagnitude a b c =
      4 * b ^ 38 := by
  have h := homogeneous_pell_factorization a b c hcurve
  simp only [positivePellFactor, negativePellFactorMagnitude]
  nlinarith

private def pellHHomogeneousTail (a b : ℤ) : ℤ :=
  3 * a ^ 18 + 2 * a ^ 17 * b + 5 * a ^ 16 * b ^ 2 +
        22 * a ^ 15 * b ^ 3 + 22 * a ^ 14 * b ^ 4 +
        10 * a ^ 13 * b ^ 5 + 54 * a ^ 12 * b ^ 6 +
        78 * a ^ 11 * b ^ 7 + 20 * a ^ 10 * b ^ 8 +
        51 * a ^ 9 * b ^ 9 + 113 * a ^ 8 * b ^ 10 +
        36 * a ^ 7 * b ^ 11 + 13 * a ^ 6 * b ^ 12 +
        66 * a ^ 5 * b ^ 13 + 26 * a ^ 4 * b ^ 14 -
        2 * a ^ 3 * b ^ 15 + 12 * a ^ 2 * b ^ 16 +
        4 * a * b ^ 17

private lemma pellHHomogeneous_eq_leading_add (a b : ℤ) :
    pellHHomogeneous a b =
      a ^ 19 + b * pellHHomogeneousTail a b := by
  simp only [pellHHomogeneous, pellHHomogeneousTail]
  ring

/-- An odd prime cannot occur in both positive Pell factors of a
primitive homogeneous sextic point. -/
theorem odd_prime_not_common_pell_factor
    (a b c p : ℤ) (hab : IsCoprime a b) (hp : Prime p)
    (hpTwo : ¬p ∣ (2 : ℤ))
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    ¬(p ∣ positivePellFactor a b c ∧
      p ∣ negativePellFactorMagnitude a b c) := by
  rintro ⟨hplus, hminus⟩
  have hproduct : p ∣ 4 * b ^ 38 := by
    rw [← positive_pell_factorization a b c hcurve]
    exact dvd_mul_of_dvd_left hplus _
  have hpFour : ¬p ∣ (4 : ℤ) := by
    intro hfour
    have hpTwo' : p ∣ (2 : ℤ) := by
      have : p ∣ (2 : ℤ) * 2 := by norm_num at hfour ⊢; exact hfour
      exact (hp.dvd_mul.mp this).resolve_right hpTwo
    exact hpTwo hpTwo'
  have hpBpow : p ∣ b ^ 38 :=
    (hp.dvd_mul.mp hproduct).resolve_left hpFour
  have hpB : p ∣ b := hp.dvd_of_dvd_pow hpBpow
  have hpTwoH : p ∣ 2 * pellHHomogeneous a b := by
    have hdiff : p ∣
        positivePellFactor a b c - negativePellFactorMagnitude a b c :=
      dvd_sub hplus hminus
    convert hdiff using 1
    simp only [positivePellFactor, negativePellFactorMagnitude]
    ring
  have hpH : p ∣ pellHHomogeneous a b :=
    (hp.dvd_mul.mp hpTwoH).resolve_left hpTwo
  have hpA19 : p ∣ a ^ 19 := by
    rw [pellHHomogeneous_eq_leading_add] at hpH
    have hpTail : p ∣ b * pellHHomogeneousTail a b :=
      hpB.mul_right _
    have := dvd_sub hpH hpTail
    simpa only [add_sub_cancel_right] using this
  have hpA : p ∣ a := hp.dvd_of_dvd_pow hpA19
  exact hp.not_unit (hab.isUnit_of_dvd' hpA hpB)

/-- Every odd prime in the canonical denominator is allocated to
exactly one of the two positive Pell factors. -/
theorem odd_prime_pell_factor_allocation
    (a b c p : ℤ) (hab : IsCoprime a b) (hp : Prime p)
    (hpTwo : ¬p ∣ (2 : ℤ)) (hpB : p ∣ b)
    (hcurve : c ^ 2 = integerSexticHomogeneous a b) :
    (p ∣ positivePellFactor a b c ∧
        ¬p ∣ negativePellFactorMagnitude a b c) ∨
      (¬p ∣ positivePellFactor a b c ∧
        p ∣ negativePellFactorMagnitude a b c) := by
  have hpProduct :
      p ∣ positivePellFactor a b c *
        negativePellFactorMagnitude a b c := by
    rw [positive_pell_factorization a b c hcurve]
    exact dvd_mul_of_dvd_right (dvd_pow hpB (by norm_num)) 4
  have hnotBoth :=
    odd_prime_not_common_pell_factor a b c p hab hp hpTwo hcurve
  rcases hp.dvd_mul.mp hpProduct with hplus | hminus
  · exact Or.inl ⟨hplus, fun hminus ↦ hnotBoth ⟨hplus, hminus⟩⟩
  · exact Or.inr ⟨(fun hplus ↦ hnotBoth ⟨hplus, hminus⟩), hminus⟩

/-- The residual arithmetic statement after the positive split system has
been normalized to a primitive integral point and the Pell factors have been
made positive and allocated prime by prime. -/
def PositivePellAllocatedFactorObstruction : Prop :=
  ∀ m n a b c : ℤ,
    0 < n →
    0 < a →
    0 < b →
    0 < c →
    IsCoprime m n →
    IsCoprime a b →
    IsCoprime c b →
    Odd m →
    Odd n →
    -n < m ∧ m < n →
    n ^ 2 - m ^ 2 = 4 * (a * b * (a + b)) →
    m ^ 2 + 4 * m * n - n ^ 2 =
      4 * (a ^ 3 - 3 * a * b ^ 2 - b ^ 3) →
    2 * m ^ 2 - 4 * m * n - 2 * n ^ 2 =
      4 * (-a ^ 3 - 3 * a ^ 2 * b + b ^ 3) →
    ¬SixthRootPiConjDivides (a, b) →
    2 * c = m ^ 2 + n ^ 2 →
    c ^ 2 = integerSexticHomogeneous a b →
    0 < positivePellFactor a b c →
    0 < negativePellFactorMagnitude a b c →
    positivePellFactor a b c * negativePellFactorMagnitude a b c =
      4 * b ^ 38 →
    (∀ p : ℤ, Prime p → ¬p ∣ (2 : ℤ) → p ∣ b →
      (p ∣ positivePellFactor a b c ∧
          ¬p ∣ negativePellFactorMagnitude a b c) ∨
        (¬p ∣ positivePellFactor a b c ∧
          p ∣ negativePellFactorMagnitude a b c)) →
    False

/-- The allocated integral Pell boundary implies the existing normalized
positive split-cubic obstruction. -/
theorem positiveSplitCyclicCubicObstruction_of_positivePellAllocatedFactor
    (hpell : PositivePellAllocatedFactorObstruction) :
    PositiveSplitCyclicCubicObstruction := by
  intro m n a b hn ha hb hmn hab hmOdd hnOdd hbetween hlead htrace
    hpair hpi _hnorm
  obtain ⟨c, hc, htwice, hcurve⟩ :=
    positive_split_homogeneous_curve
      m n a b hn hmOdd hnOdd hlead htrace
  have hcb : IsCoprime c b :=
    positive_split_ordinate_coprime a b c hab hcurve
  obtain ⟨hplus, hminus⟩ :=
    homogeneous_pell_factor_signs a b c ha hb hc hcurve
  have hminusMagnitude :
      0 < negativePellFactorMagnitude a b c := by
    simp only [negativePellFactorMagnitude]
    linarith
  have hfactor := positive_pell_factorization a b c hcurve
  exact hpell m n a b c hn ha hb hc hmn hab hcb hmOdd hnOdd
    hbetween hlead htrace hpair hpi htwice hcurve hplus hminusMagnitude
    hfactor
    (fun p hp hpTwo hpB ↦
      odd_prime_pell_factor_allocation
        a b c p hab hp hpTwo hpB hcurve)

/-- The integral Pell allocation boundary is a direct checked input to the
existing exact-order-thirteen exclusion. -/
theorem rationalPoint_addOrderOf_ne_thirteen_of_positivePellAllocatedFactor
    (hpell : PositivePellAllocatedFactorObstruction)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 13 :=
  rationalPoint_addOrderOf_ne_thirteen_of_positiveSplitCyclicCubicObstruction
    (positiveSplitCyclicCubicObstruction_of_positivePellAllocatedFactor hpell)
    E Q

end MazurTorsion.XOneThirteenDescent
