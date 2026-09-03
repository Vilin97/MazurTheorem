/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerExceptionalCongruences

/-!
# The Lehmer deck map on the resolved diagonal chart

In diagonal local coordinates

`N = 1/Z`, `X = N + U`,

the root-zero coordinate of the next Lehmer root is an explicit rational
function of `(U,Z)`.  Its denominator is a three-adic unit and its difference
from `U+1` has positive valuation.  Consequently the valuation of the next
root distinguishes the two diagonal exceptional points: successor slope
`a` comes from `U = -2`, while successor slope `3a` comes from `U = -1`.
-/

namespace MazurTorsion.Kubert

/-- Denominator of the root-zero coordinate of the deck successor, expressed
on the resolved diagonal chart. -/
def orderTwentyFiveLehmerDiagonalDeckDenominator (u z : ℚ) : ℚ :=
  2 * u * z ^ 2 - u * z - z ^ 2 + 2 * z - 1

/-- Numerator of the root-zero coordinate of the deck successor, expressed
on the resolved diagonal chart. -/
def orderTwentyFiveLehmerDiagonalDeckNumerator (u z : ℚ) : ℚ :=
  u ^ 2 * z + u - 2 * z + 1

/-- The root-zero strict-transform coordinate of the deck successor to a
point in the diagonal chart. -/
def orderTwentyFiveLehmerDiagonalDeckCoordinate (u z : ℚ) : ℚ :=
  -orderTwentyFiveLehmerDiagonalDeckNumerator u z /
    orderTwentyFiveLehmerDiagonalDeckDenominator u z

/-- The integral numerator left after subtracting `U+1` from the local deck
coordinate. -/
def orderTwentyFiveLehmerDiagonalDeckError (u z : ℚ) : ℚ :=
  2 * u ^ 2 * z + u * z + u - z

private def diagonalThreeAdicIntegralRationals : Subring ℚ where
  carrier := {q | 0 ≤ padicValRat 3 q}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro q r hq hr
    change 0 ≤ padicValRat 3 q at hq
    change 0 ≤ padicValRat 3 r at hr
    change 0 ≤ padicValRat 3 (q + r)
    by_cases h : q + r = 0
    · simp [h]
    · exact le_trans (le_min hq hr)
        (padicValRat.min_le_padicValRat_add h)
  mul_mem' := by
    intro q r hq hr
    change 0 ≤ padicValRat 3 q at hq
    change 0 ≤ padicValRat 3 r at hr
    change 0 ≤ padicValRat 3 (q * r)
    by_cases hq0 : q = 0
    · simp [hq0]
    by_cases hr0 : r = 0
    · simp [hr0]
    rw [padicValRat.mul hq0 hr0]
    omega
  neg_mem' := by
    intro q hq
    change 0 ≤ padicValRat 3 q at hq
    change 0 ≤ padicValRat 3 (-q)
    simpa only [padicValRat.neg] using hq

private theorem diagonalDeckAuxiliary_nonnegative
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 ≤ padicValRat 3 z) :
    0 ≤ padicValRat 3 (2 * u * z - u - z + 2) := by
  let U : diagonalThreeAdicIntegralRationals := ⟨u, hu⟩
  let Z : diagonalThreeAdicIntegralRationals := ⟨z, hz⟩
  exact (2 * U * Z - U - Z + 2).property

private theorem diagonalDeckError_nonnegative
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 ≤ padicValRat 3 z) :
    0 ≤ padicValRat 3
      (orderTwentyFiveLehmerDiagonalDeckError u z) := by
  let U : diagonalThreeAdicIntegralRationals := ⟨u, hu⟩
  let Z : diagonalThreeAdicIntegralRationals := ⟨z, hz⟩
  exact (2 * U ^ 2 * Z + U * Z + U - Z).property

/-- At a three-integral diagonal coordinate and a positively valued
exceptional parameter, the local deck denominator is a three-adic unit. -/
theorem orderTwentyFiveLehmer_diagonalDeckDenominator_isThreeUnit
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 < padicValRat 3 z) :
    orderTwentyFiveLehmerDiagonalDeckDenominator u z ≠ 0 ∧
      padicValRat 3
        (orderTwentyFiveLehmerDiagonalDeckDenominator u z) = 0 := by
  let d : ℚ := 2 * u * z - u - z + 2
  have hd : 0 ≤ padicValRat 3 d :=
    diagonalDeckAuxiliary_nonnegative u z hu (le_of_lt hz)
  have hdenEq : orderTwentyFiveLehmerDiagonalDeckDenominator u z =
      -1 + z * d := by
    simp only [orderTwentyFiveLehmerDiagonalDeckDenominator, d]
    ring
  by_cases hd0 : d = 0
  · rw [hdenEq, hd0]
    norm_num
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h, padicValRat.zero] at hz
      omega
    have hzd0 : z * d ≠ 0 := mul_ne_zero hz0 hd0
    have hzdv : 0 < padicValRat 3 (z * d) := by
      rw [padicValRat.mul hz0 hd0]
      omega
    have hsum0 : -1 + z * d ≠ 0 := by
      intro h
      have heq : z * d = 1 := by linarith
      rw [heq, padicValRat.one] at hzdv
      omega
    refine ⟨?_, ?_⟩
    · rwa [hdenEq]
    · rw [hdenEq]
      simpa only [padicValRat.neg, padicValRat.one] using
        padicValRat.add_eq_of_lt hsum0 (by norm_num) hzd0 (by
          rw [padicValRat.neg, padicValRat.one]
          exact hzdv)

/-- The deck successor coordinate is congruent to `U+1` along the diagonal
exceptional fiber. -/
theorem orderTwentyFiveLehmer_diagonalDeckCoordinate_cuspCongruence
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 < padicValRat 3 z) :
    orderTwentyFiveLehmerDiagonalDeckCoordinate u z - (u + 1) = 0 ∨
      0 < padicValRat 3
        (orderTwentyFiveLehmerDiagonalDeckCoordinate u z - (u + 1)) := by
  obtain ⟨hden0, hdenv⟩ :=
    orderTwentyFiveLehmer_diagonalDeckDenominator_isThreeUnit u z hu hz
  have hid :
      orderTwentyFiveLehmerDiagonalDeckCoordinate u z - (u + 1) =
        (-z * orderTwentyFiveLehmerDiagonalDeckError u z) /
          orderTwentyFiveLehmerDiagonalDeckDenominator u z := by
    simp only [orderTwentyFiveLehmerDiagonalDeckCoordinate]
    field_simp [hden0]
    simp only [orderTwentyFiveLehmerDiagonalDeckNumerator,
      orderTwentyFiveLehmerDiagonalDeckDenominator,
      orderTwentyFiveLehmerDiagonalDeckError]
    ring
  by_cases he0 : orderTwentyFiveLehmerDiagonalDeckError u z = 0
  · left
    rw [hid, he0]
    simp
  · right
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, padicValRat.zero] at hz
      omega
    have hnum0 :
        -z * orderTwentyFiveLehmerDiagonalDeckError u z ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hz0) he0
    rw [hid, padicValRat.div hnum0 hden0,
      padicValRat.mul (neg_ne_zero.mpr hz0) he0,
      padicValRat.neg, hdenv]
    have herr := diagonalDeckError_nonnegative
      u z hu (le_of_lt hz)
    omega

private theorem add_positive_of_ne_zero_diagonalDeck
    (q r : ℚ) (hq : 0 < padicValRat 3 q)
    (hr : 0 < padicValRat 3 r) (hqr : q + r ≠ 0) :
    0 < padicValRat 3 (q + r) := by
  have hmin := padicValRat.min_le_padicValRat_add (p := 3) hqr
  omega

/-- The valuation of the local successor coordinate separates the two
diagonal exceptional branches. -/
theorem orderTwentyFiveLehmer_diagonalDeckCoordinate_distinguishesBranch
    (u z w : ℚ)
    (hu : 0 ≤ padicValRat 3 u) (hz : 0 < padicValRat 3 z)
    (hstrict : orderTwentyFiveLehmerDiagonalStrictTransform u z = 0)
    (hw : w = orderTwentyFiveLehmerDiagonalDeckCoordinate u z)
    (hw0 : w ≠ 0) :
    (padicValRat 3 w = 0 →
      u = -2 ∨ 0 < padicValRat 3 (u + 2)) ∧
    (0 < padicValRat 3 w →
      u = -1 ∨ 0 < padicValRat 3 (u + 1)) := by
  have hfiber := orderTwentyFiveLehmer_diagonal_exceptionalCongruence
    u z hu hz hstrict
  have hclose :=
    orderTwentyFiveLehmer_diagonalDeckCoordinate_cuspCongruence u z hu hz
  rw [← hw] at hclose
  constructor
  · intro hwv
    rcases hfiber with hminusOne | hminusTwo
    · exfalso
      rcases hminusOne with hu1 | hu1
      · have hdiff : w - (u + 1) = w := by rw [hu1]; norm_num
        rcases hclose with hzero | hpos
        · apply hw0
          linarith
        · rw [hdiff, hwv] at hpos
          omega
      · rcases hclose with hzero | hpos
        · have hwu : w = u + 1 := sub_eq_zero.mp hzero
          rw [hwu] at hwv
          omega
        · have hsum : w = (w - (u + 1)) + (u + 1) := by ring
          have hsum0 : (w - (u + 1)) + (u + 1) ≠ 0 := by
            rwa [← hsum]
          have hpositive := add_positive_of_ne_zero_diagonalDeck
            _ _ hpos hu1 hsum0
          rw [← hsum, hwv] at hpositive
          omega
    · exact hminusTwo
  · intro hwv
    rcases hclose with hzero | hpos
    · right
      have hwu : w = u + 1 := sub_eq_zero.mp hzero
      rwa [← hwu]
    · by_cases hu1 : u + 1 = 0
      · left
        exact eq_neg_of_add_eq_zero_left hu1
      · right
        have heq : u + 1 = w + (-(w - (u + 1))) := by ring
        rw [heq]
        apply add_positive_of_ne_zero_diagonalDeck
          w (-(w - (u + 1))) hwv
        · simpa only [padicValRat.neg] using hpos
        · rwa [← heq]

/-- Substituting `U = X-N` and `Z = 1/N` identifies the local coordinate
with `N` times the actual Lehmer deck successor. -/
theorem orderTwentyFiveLehmer_diagonalDeckCoordinate_eq_deckTransform
    (n x : ℚ) (hn0 : n ≠ 0)
    (hu : 0 ≤ padicValRat 3 (x - n))
    (hz : 0 < padicValRat 3 (1 / n))
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveLehmerDiagonalDeckCoordinate (x - n) (1 / n) =
      orderTwentyFiveLehmerDeckTransform n x * n := by
  have hlocal :=
    (orderTwentyFiveLehmer_diagonalDeckDenominator_isThreeUnit
      (x - n) (1 / n) hu hz).1
  have hdeck :=
    orderTwentyFiveLehmerDeckTransform_denominator_ne_zero n x hroot
  have hnum :
      orderTwentyFiveLehmerDiagonalDeckNumerator (x - n) (1 / n) =
        (x ^ 2 - n * x + n - 2) / n := by
    simp only [orderTwentyFiveLehmerDiagonalDeckNumerator]
    field_simp
    ring
  have hden :
      orderTwentyFiveLehmerDiagonalDeckDenominator (x - n) (1 / n) =
        -(1 + (n - 2) * x) / n ^ 2 := by
    simp only [orderTwentyFiveLehmerDiagonalDeckDenominator]
    field_simp
    ring
  rw [orderTwentyFiveLehmerDiagonalDeckCoordinate, hnum, hden,
    orderTwentyFiveLehmerDeckTransform]
  field_simp [hlocal, hdeck, hn0]

/-- For a root on the `-a` slope, the successor valuation determines the
exact diagonal exceptional branch: successor slope `a` gives `U = -2`, and
successor slope `3a` gives `U = -1`. -/
theorem orderTwentyFiveLehmer_negOneSlope_exceptionalBranch
    (n x y : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hxv : padicValRat 3 x = -a)
    (hyv : padicValRat 3 y = a ∨
      padicValRat 3 y = 3 * a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hxy : orderTwentyFiveLehmerDeckTransform n x = y) :
    (padicValRat 3 y = a ∧
      (x - n = -2 ∨ 0 < padicValRat 3 (x - n + 2))) ∨
    (padicValRat 3 y = 3 * a ∧
      (x - n = -1 ∨ 0 < padicValRat 3 (x - n + 1))) := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hn
    omega
  have hx0 : x ≠ 0 := by
    intro h
    simp [h, orderTwentyFiveLehmerPolynomial] at hroot
  have hyroot : orderTwentyFiveLehmerPolynomial n y = 0 := by
    rw [← hxy]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n x hroot
  have hy0 : y ≠ 0 := by
    intro h
    simp [h, orderTwentyFiveLehmerPolynomial] at hyroot
  have hu := orderTwentyFiveLehmer_negOneSlope_cuspCongruence
    n x y a ha hn hxv hyv hroot hxy
  have hzv : padicValRat 3 (1 / n) = a := by
    rw [padicValRat.div one_ne_zero hn0, padicValRat.one, hn]
    omega
  have hz : 0 < padicValRat 3 (1 / n) := by omega
  have hscaled :
      orderTwentyFiveLehmerHomogeneousPolynomial 1 (x / n) (1 / n) = 0 := by
    have hs := orderTwentyFiveLehmerHomogeneousPolynomial_scale
      (1 / n) n x (1 : ℚ)
    have hsn : (1 / n) * n = 1 := by field_simp
    have hsx : (1 / n) * x = x / n := by ring
    rw [hsn, hsx, mul_one,
      orderTwentyFiveLehmerHomogeneousPolynomial_affine,
      hroot, mul_zero] at hs
    exact hs
  have hstrict :
      orderTwentyFiveLehmerDiagonalStrictTransform (x - n) (1 / n) = 0 := by
    have hcoord : 1 + (1 / n) * (x - n) = x / n := by
      field_simp
      ring
    have hid := orderTwentyFiveLehmer_diagonalStrictTransform_identity
      (x - n) (1 / n)
    rw [hcoord] at hid
    have hprod := hid.symm.trans hscaled
    exact (mul_eq_zero.mp hprod).resolve_left
      (pow_ne_zero 2 (div_ne_zero one_ne_zero hn0))
  have hw :
      y * n = orderTwentyFiveLehmerDiagonalDeckCoordinate
        (x - n) (1 / n) := by
    rw [orderTwentyFiveLehmer_diagonalDeckCoordinate_eq_deckTransform
      n x hn0 hu hz hroot, hxy]
  have hwn0 : y * n ≠ 0 := mul_ne_zero hy0 hn0
  have hdist :=
    orderTwentyFiveLehmer_diagonalDeckCoordinate_distinguishesBranch
      (x - n) (1 / n) (y * n) hu hz hstrict hw hwn0
  rcases hyv with hyv | hyv
  · left
    refine ⟨hyv, hdist.1 ?_⟩
    rw [padicValRat.mul hy0 hn0, hyv, hn]
    omega
  · right
    refine ⟨hyv, hdist.2 ?_⟩
    rw [padicValRat.mul hy0 hn0, hyv, hn]
    omega

end MazurTorsion.Kubert
