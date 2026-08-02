/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.DivisionPolynomialRootCriterion
import MazurTorsion.NumberTheory.XOneElevenDescent
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The dual five-isogeny for `X₁(11)`

This file supplies the rational point map in the direction opposite to
`XOneEleven.veluFiveMap`.  On completed-square coordinates, the two curves are

`z² = 4 x³ - 4 x² + 1`

and

`Z² = 4 X³ - 4 X² - 40 X - 79`.

The dual kernel has abscissa polynomial `5 X² + 5 X - 29`.  It has no rational
root, so the dual map has no exceptional nonidentity rational point.  The
formulas below are the normalized Vélu quotient followed by the change of
variables `(S, T) = (25 x - 8, 125 z)` back to the selected `X₁(11)` model.

The four visible rational torsion points on the quotient are included as a
compiled consumer of the map: they map to the four visible nonidentity points
on `X₁(11)`.  The later five-descent uses this map together with the opposite
Vélu map and their multiplication-by-five composition.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneEleven

open WeierstrassCurve.Affine

/-- The abscissa polynomial of the nonidentity geometric points in the kernel
of the dual five-isogeny. -/
def dualFiveKernelPolynomial (X : ℚ) : ℚ :=
  5 * X ^ 2 + 5 * X - 29

/-- The dual kernel has no nonidentity rational point. -/
theorem dualFiveKernelPolynomial_ne_zero (X : ℚ) :
    dualFiveKernelPolynomial X ≠ 0 := by
  intro hX
  have hfive : ¬ IsSquare (5 : ℚ) := by
    norm_num
  apply hfive
  refine ⟨5 * (2 * X + 1) / 11, ?_⟩
  dsimp only [dualFiveKernelPolynomial] at hX
  field_simp
  nlinarith

/-- The abscissa of the dual five-isogeny. -/
def dualFiveX (X : ℚ) : ℚ :=
  (X - 5) *
      (X ^ 4 + 15 * X ^ 3 + 120 * X ^ 2 + 200 * X + 155) /
    dualFiveKernelPolynomial X ^ 2

/-- The completed-ordinate multiplier for the dual five-isogeny.

It is one fifth of the derivative of `dualFiveX`; the factor of five is the
expected pullback factor for the invariant differential under a dual
degree-five isogeny. -/
def dualFiveDifferential (X : ℚ) : ℚ :=
  (X ^ 6 + 3 * X ^ 5 - 54 * X ^ 4 + 613 * X ^ 3 +
      1752 * X ^ 2 + 8585 * X + 6451) /
    dualFiveKernelPolynomial X ^ 3

/-- The ordinate of the dual five-isogeny. -/
def dualFiveY (X Y : ℚ) : ℚ :=
  ((2 * Y + 1) * dualFiveDifferential X - 1) / 2

/-- The degree-ten factor of the fifth-division polynomial after removing
the four visible kernel points. -/
def fiveDivisionCofactor (x : ℚ) : ℚ :=
  5 * x ^ 10 - 15 * x ^ 9 + x ^ 8 + 96 * x ^ 7 -
    189 * x ^ 6 + 171 * x ^ 5 - 84 * x ^ 4 + 10 * x ^ 3 +
    25 * x ^ 2 - 20 * x + 5

/-- The univariate fifth-division polynomial of the selected `X₁(11)`
model, written in factored form around the four visible kernel points. -/
def fiveDivisionPolynomial (x : ℚ) : ℚ :=
  x * (x - 1) * fiveDivisionCofactor x

/-- Evaluation of Mathlib's fifth-division polynomial agrees with the
explicit factorization used by the five-isogeny formulas. -/
theorem eval_prePsi_five (x : ℚ) :
    Polynomial.eval x (curve.preΨ' 5) = fiveDivisionPolynomial x := by
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
    curve.preΨ'_odd 0]
  norm_num
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, curve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    fiveDivisionPolynomial, fiveDivisionCofactor]
  ring

/-- Outside the visible kernel, the remaining factor of the fifth-division
polynomial cannot vanish over `ℚ`: otherwise the image under the first Vélu
map would give a rational root of the dual kernel polynomial. -/
theorem fiveDivisionCofactor_ne_zero {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    fiveDivisionCofactor x ≠ 0 := by
  intro hcofactor
  apply dualFiveKernelPolynomial_ne_zero (veluFiveX x)
  simp only [dualFiveKernelPolynomial, veluFiveX]
  field_simp [hx0, sub_ne_zero.mpr hx1]
  dsimp only [fiveDivisionCofactor] at hcofactor
  linear_combination hcofactor

/-- Pulling the dual kernel polynomial back along the first Vélu map gives
the non-visible factor of the fifth-division polynomial. -/
theorem dualFiveKernelPolynomial_veluFiveX {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    dualFiveKernelPolynomial (veluFiveX x) =
      fiveDivisionCofactor x / (x ^ 4 * (x - 1) ^ 4) := by
  simp only [dualFiveKernelPolynomial, veluFiveX,
    fiveDivisionCofactor]
  field_simp [hx0, sub_ne_zero.mpr hx1]
  ring

/-- The fifth-division polynomial has no additional rational zero outside
the four visible kernel points. -/
theorem fiveDivisionPolynomial_ne_zero {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    fiveDivisionPolynomial x ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero hx0 (sub_ne_zero.mpr hx1))
    (fiveDivisionCofactor_ne_zero hx0 hx1)

/-- An affine point outside the visible Vélu kernel is not killed by five. -/
theorem five_nsmul_some_ne_zero {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (5 : ℕ) • Point.some x y hP ≠ 0 := by
  intro hfive
  have hroot :=
    DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_five
      curve hP hfive
  rw [eval_prePsi_five] at hroot
  exact (fiveDivisionPolynomial_ne_zero hx0 hx1) hroot

/-- The selected curve has no nonidentity rational two-torsion.  Reduction
modulo three lands in a group of order five, and is injective on torsion of
order prime to three. -/
theorem eq_zero_of_two_nsmul_eq_zero
    (P : curve.toAffine.Point) (hP : (2 : ℕ) • P = 0) :
    P = 0 := by
  let redP := redHom (intPrime 3) map_integralCurve P
  have hredTwo : (2 : ℕ) • redP = 0 := by
    dsimp only [redP]
    rw [← map_nsmul, hP, map_zero]
  have horderTwo : addOrderOf redP ∣ 2 :=
    addOrderOf_dvd_of_nsmul_eq_zero hredTwo
  have horderFive : addOrderOf redP ∣ 5 := by
    rw [← card_reducedCurve]
    exact addOrderOf_dvd_natCard redP
  have horderPos : 0 < addOrderOf redP := addOrderOf_pos redP
  have horderLe : addOrderOf redP ≤ 2 :=
    Nat.le_of_dvd (by norm_num) horderTwo
  have horder : addOrderOf redP = 1 := by
    have hcases : addOrderOf redP = 1 ∨ addOrderOf redP = 2 := by
      omega
    rcases hcases with h | h
    · exact h
    · rw [h] at horderFive
      norm_num at horderFive
  have hred : redP = 0 :=
    AddMonoid.addOrderOf_eq_one_iff.mp horder
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    (intPrime 3) map_integralCurve
    (by norm_num) three_mem_prime
    three_not_mem_prime_pow_two
  · exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, hP⟩
  · exact hred

/-- The third division polynomial has no rational root.  The proof is a
fully explicit rational-root argument: a root has numerator dividing one
and denominator dividing three, and none of the resulting four rational
values is a root. -/
private theorem threeDivisionPolynomial_ne_zero (x : ℚ) :
    3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1 ≠ 0 := by
  intro hx
  let p : Polynomial ℤ :=
    Polynomial.C 3 * Polynomial.X ^ 4 -
      Polynomial.C 4 * Polynomial.X ^ 3 +
        Polynomial.C 3 * Polynomial.X - Polynomial.C 1
  have hroot : Polynomial.aeval x p = 0 := by
    simpa [p, map_ofNat] using hx
  have hn : IsFractionRing.num ℤ x ∣ (1 : ℤ) := by
    have hn := num_dvd_of_is_root hroot
    norm_num [p] at hn
    exact hn
  have hdeg : p.natDegree = 4 := by
    dsimp only [p]
    compute_degree <;> norm_num
  have hlc : p.leadingCoeff = 3 := by
    rw [Polynomial.leadingCoeff, hdeg]
    norm_num [p, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one]
  have hd : ((IsFractionRing.den ℤ x : ℤ)) ∣ 3 := by
    simpa only [hlc] using den_dvd_of_is_root hroot
  have hnabs : (IsFractionRing.num ℤ x).natAbs = 1 := by
    apply Nat.dvd_one.mp
    simpa using (Int.natAbs_dvd_natAbs.mpr hn)
  have hdabs : (IsFractionRing.den ℤ x : ℤ).natAbs = 1 ∨
      (IsFractionRing.den ℤ x : ℤ).natAbs = 3 := by
    apply (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hn_cases : IsFractionRing.num ℤ x = 1 ∨
      IsFractionRing.num ℤ x = -1 := by
    rcases Int.natAbs_eq (IsFractionRing.num ℤ x) with h | h
    · left
      rw [hnabs] at h
      norm_num at h ⊢
      exact h
    · right
      rw [hnabs] at h
      norm_num at h ⊢
      exact h
  have hd_cases : (IsFractionRing.den ℤ x : ℤ) = 1 ∨
      (IsFractionRing.den ℤ x : ℤ) = -1 ∨
      (IsFractionRing.den ℤ x : ℤ) = 3 ∨
      (IsFractionRing.den ℤ x : ℤ) = -3 := by
    rcases hdabs with hdabs | hdabs
    · rcases Int.natAbs_eq (IsFractionRing.den ℤ x : ℤ) with h | h
      · left
        rw [hdabs] at h
        norm_num at h ⊢
        exact h
      · right; left
        rw [hdabs] at h
        norm_num at h ⊢
        exact h
    · rcases Int.natAbs_eq (IsFractionRing.den ℤ x : ℤ) with h | h
      · right; right; left
        rw [hdabs] at h
        norm_num at h ⊢
        exact h
      · right; right; right
        rw [hdabs] at h
        norm_num at h ⊢
        exact h
  have hrepr := IsFractionRing.mk'_num_den' ℤ x
  rcases hn_cases with hn | hn <;>
    rcases hd_cases with hd | hd | hd | hd <;>
    rw [hn, hd] at hrepr <;>
    norm_num at hrepr <;>
    subst x <;>
    norm_num at hx

/-- The selected curve has no nonidentity rational three-torsion. -/
theorem eq_zero_of_three_nsmul_eq_zero
    (P : curve.toAffine.Point) (hP : (3 : ℕ) • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      exfalso
      apply threeDivisionPolynomial_ne_zero x
      have hroot :=
        (ThreeTorsion.three_nsmul_some_eq_zero_iff curve hxy).mp hP
      simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_ofNat, curve,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hroot
      norm_num at hroot ⊢
      simpa only [sub_eq_add_neg] using hroot

private theorem existsCoordinatesOfNeZero
    (P : curve.toAffine.Point) (hP : P ≠ 0) :
    ∃ x y, ∃ hxy : curve.toAffine.Nonsingular x y,
      P = Point.some x y hxy := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hxy => exact ⟨x, y, hxy, rfl⟩

private def completedEquationPolynomial (x : ℚ) : ℚ :=
  4 * x ^ 3 - 4 * x ^ 2 + 1

private def doubleAbscissaNumerator (x : ℚ) : ℚ :=
  (x - 1) * (x ^ 3 + x ^ 2 + x - 1)

private def doubleAbscissa (x : ℚ) : ℚ :=
  doubleAbscissaNumerator x / completedEquationPolynomial x

private def doubleCompletedNumerator (x : ℚ) : ℚ :=
  2 * x ^ 6 - 4 * x ^ 5 + 10 * x ^ 3 - 10 * x ^ 2 + 4 * x - 1

private def doubleCompletedFactor (x : ℚ) : ℚ :=
  doubleCompletedNumerator x / completedEquationPolynomial x ^ 2

private def quadrupleAbscissaNumerator (x : ℚ) : ℚ :=
  x * (x ^ 3 - 4 * x ^ 2 + 4 * x - 2) *
    (x ^ 12 + 4 * x ^ 11 + 12 * x ^ 10 - 102 * x ^ 9 +
      196 * x ^ 8 - 192 * x ^ 7 + 92 * x ^ 6 + 32 * x ^ 5 -
      74 * x ^ 4 + 24 * x ^ 3 + 16 * x ^ 2 - 12 * x + 2)

private def quadrupleAbscissa (x : ℚ) : ℚ :=
  quadrupleAbscissaNumerator x /
    (completedEquationPolynomial x * doubleCompletedNumerator x ^ 2)

private def quadrupleCompletedNumerator (x : ℚ) : ℚ :=
  2 * x ^ 24 - 16 * x ^ 23 + 16 * x ^ 22 + 616 * x ^ 21 -
    4312 * x ^ 20 + 16016 * x ^ 19 - 43736 * x ^ 18 +
    95216 * x ^ 17 - 161942 * x ^ 16 + 208472 * x ^ 15 -
    200376 * x ^ 14 + 144816 * x ^ 13 - 81606 * x ^ 12 +
    36792 * x ^ 11 - 7832 * x ^ 10 - 11484 * x ^ 9 +
    18282 * x ^ 8 - 13112 * x ^ 7 + 4928 * x ^ 6 - 616 * x ^ 5 -
    154 * x ^ 4 + 40 * x ^ 2 - 12 * x + 1

private def quadrupleCompletedFactor (x : ℚ) : ℚ :=
  quadrupleCompletedNumerator x /
    (completedEquationPolynomial x ^ 2 * doubleCompletedNumerator x ^ 3)

private theorem completed_equation {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y) :
    (2 * y + 1) ^ 2 = completedEquationPolynomial x := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [curve, completedEquationPolynomial] at hcurve ⊢
  nlinarith

private theorem tangent_abscissa_eq_doubleAbscissa {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hy : y ≠ curve.toAffine.negY x y) :
    curve.toAffine.addX x x (curve.toAffine.slope x x y y) =
      doubleAbscissa x := by
  have hz : 2 * y + 1 ≠ 0 := by
    intro hz
    apply hy
    simp only [curve, WeierstrassCurve.Affine.negY]
    linarith
  have hden : y - curve.toAffine.negY x y = 2 * y + 1 := by
    simp only [curve, WeierstrassCurve.Affine.negY]
    ring
  have hcompleted := completed_equation hP
  have hD : completedEquationPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  rw [curve.toAffine.slope_of_Y_ne rfl hy]
  rw [hden]
  simp only [WeierstrassCurve.Affine.addX, curve, doubleAbscissa,
    doubleAbscissaNumerator]
  field_simp [hz, hD]
  dsimp only [completedEquationPolynomial] at hcompleted ⊢
  linear_combination -x ^ 2 * (3 * x - 2) ^ 2 * hcompleted

private theorem tangent_completed_eq_doubleCompletedFactor {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hy : y ≠ curve.toAffine.negY x y) :
    2 * curve.toAffine.addY x x y (curve.toAffine.slope x x y y) + 1 =
      (2 * y + 1) * doubleCompletedFactor x := by
  have hz : 2 * y + 1 ≠ 0 := by
    intro hz
    apply hy
    simp only [curve, WeierstrassCurve.Affine.negY]
    linarith
  have hden : y - curve.toAffine.negY x y = 2 * y + 1 := by
    simp only [curve, WeierstrassCurve.Affine.negY]
    ring
  have hcompleted := completed_equation hP
  have hD : completedEquationPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  rw [curve.toAffine.slope_of_Y_ne rfl hy]
  rw [hden]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, curve,
    WeierstrassCurve.Affine.negY, doubleCompletedFactor,
    doubleCompletedNumerator]
  field_simp [hz, hD]
  dsimp only [completedEquationPolynomial] at hcompleted ⊢
  linear_combination
    2 * x * (3 * x - 2) *
      (36 * x ^ 7 - 84 * x ^ 6 + 64 * x ^ 5 -
        12 * x ^ 4 * y ^ 2 - 12 * x ^ 4 * y - 10 * x ^ 4 +
        16 * x ^ 3 * y ^ 2 + 16 * x ^ 3 * y - 8 * x ^ 3 +
        4 * x ^ 2 - 12 * x * y ^ 2 - 12 * x * y - 3 * x +
        4 * y ^ 2 + 4 * y + 1) * hcompleted

private theorem completedEquationPolynomial_doubleAbscissa {x : ℚ}
    (hD : completedEquationPolynomial x ≠ 0) :
    completedEquationPolynomial (doubleAbscissa x) =
      doubleCompletedNumerator x ^ 2 / completedEquationPolynomial x ^ 3 := by
  let D := completedEquationPolynomial x
  let A := doubleAbscissaNumerator x
  let B := doubleCompletedNumerator x
  have hD0 : D ≠ 0 := hD
  have hpoly : 4 * A ^ 3 - 4 * A ^ 2 * D + D ^ 3 = B ^ 2 := by
    dsimp only [A, B, D, doubleAbscissaNumerator,
      doubleCompletedNumerator, completedEquationPolynomial]
    ring
  change 4 * (A / D) ^ 3 - 4 * (A / D) ^ 2 + 1 = B ^ 2 / D ^ 3
  rw [div_pow, div_pow]
  calc
    4 * (A ^ 3 / D ^ 3) - 4 * (A ^ 2 / D ^ 2) + 1 =
        (4 * A ^ 3 - 4 * A ^ 2 * D + D ^ 3) / D ^ 3 := by
      field_simp [hD0]
    _ = B ^ 2 / D ^ 3 := by rw [hpoly]

private theorem doubleAbscissa_iterate {x : ℚ}
    (hD : completedEquationPolynomial x ≠ 0)
    (hB : doubleCompletedNumerator x ≠ 0) :
    doubleAbscissa (doubleAbscissa x) = quadrupleAbscissa x := by
  let D := completedEquationPolynomial x
  let A := doubleAbscissaNumerator x
  let B := doubleCompletedNumerator x
  let N := quadrupleAbscissaNumerator x
  have hD0 : D ≠ 0 := hD
  have hB0 : B ≠ 0 := hB
  have hpoly :
      (A - D) * (A ^ 3 + A ^ 2 * D + A * D ^ 2 - D ^ 3) = N := by
    dsimp only [A, B, D, N, doubleAbscissaNumerator,
      doubleCompletedNumerator, completedEquationPolynomial,
      quadrupleAbscissaNumerator]
    ring
  have hnum : doubleAbscissaNumerator (A / D) = N / D ^ 4 := by
    change (A / D - 1) *
        ((A / D) ^ 3 + (A / D) ^ 2 + A / D - 1) = N / D ^ 4
    rw [div_pow, div_pow]
    calc
      (A / D - 1) * (A ^ 3 / D ^ 3 + A ^ 2 / D ^ 2 + A / D - 1) =
          ((A - D) * (A ^ 3 + A ^ 2 * D + A * D ^ 2 - D ^ 3)) /
            D ^ 4 := by
        field_simp [hD0]
      _ = N / D ^ 4 := by rw [hpoly]
  change doubleAbscissaNumerator (A / D) /
      completedEquationPolynomial (A / D) = N / (D * B ^ 2)
  have hcomp := completedEquationPolynomial_doubleAbscissa hD
  change completedEquationPolynomial (A / D) = B ^ 2 / D ^ 3 at hcomp
  rw [hnum, hcomp]
  field_simp [hD0, hB0]

private theorem doubleCompletedFactor_iterate {x : ℚ}
    (hD : completedEquationPolynomial x ≠ 0)
    (hB : doubleCompletedNumerator x ≠ 0) :
    doubleCompletedFactor x *
        doubleCompletedFactor (doubleAbscissa x) =
      quadrupleCompletedFactor x := by
  let D := completedEquationPolynomial x
  let A := doubleAbscissaNumerator x
  let B := doubleCompletedNumerator x
  let C := quadrupleCompletedNumerator x
  have hD0 : D ≠ 0 := hD
  have hB0 : B ≠ 0 := hB
  have hpoly :
      2 * A ^ 6 - 4 * A ^ 5 * D + 10 * A ^ 3 * D ^ 3 -
          10 * A ^ 2 * D ^ 4 + 4 * A * D ^ 5 - D ^ 6 = C := by
    dsimp only [A, B, C, D, doubleAbscissaNumerator,
      doubleCompletedNumerator, completedEquationPolynomial,
      quadrupleCompletedNumerator]
    ring
  have hnum : doubleCompletedNumerator (A / D) = C / D ^ 6 := by
    change 2 * (A / D) ^ 6 - 4 * (A / D) ^ 5 +
        10 * (A / D) ^ 3 - 10 * (A / D) ^ 2 + 4 * (A / D) - 1 =
      C / D ^ 6
    rw [div_pow, div_pow, div_pow, div_pow]
    calc
      2 * (A ^ 6 / D ^ 6) - 4 * (A ^ 5 / D ^ 5) +
          10 * (A ^ 3 / D ^ 3) - 10 * (A ^ 2 / D ^ 2) +
            4 * (A / D) - 1 =
          (2 * A ^ 6 - 4 * A ^ 5 * D + 10 * A ^ 3 * D ^ 3 -
              10 * A ^ 2 * D ^ 4 + 4 * A * D ^ 5 - D ^ 6) /
            D ^ 6 := by
        field_simp [hD0]
      _ = C / D ^ 6 := by rw [hpoly]
  change (B / D ^ 2) *
      (doubleCompletedNumerator (A / D) /
        completedEquationPolynomial (A / D) ^ 2) =
      C / (D ^ 2 * B ^ 3)
  have hcomp := completedEquationPolynomial_doubleAbscissa hD
  change completedEquationPolynomial (A / D) = B ^ 2 / D ^ 3 at hcomp
  rw [hnum, hcomp]
  field_simp [hD0, hB0]

/-- Mathlib's squared fifth-division polynomial evaluates to the square of
the explicit polynomial above. -/
theorem eval_PsiSq_five (x : ℚ) :
    Polynomial.eval x (curve.ΨSq 5) = fiveDivisionPolynomial x ^ 2 := by
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num,
    WeierstrassCurve.ΨSq_ofNat]
  norm_num [Polynomial.eval_pow, eval_prePsi_five]

/-- The numerator of the multiplication-by-five abscissa, in a factorization
that keeps the checked certificate reasonably small. -/
def fiveDivisionNumerator (x : ℚ) : ℚ :=
  (x ^ 5 - 7 * x ^ 4 + 13 * x ^ 3 - 5 * x ^ 2 - 2 * x + 1) *
    (x ^ 20 + 7 * x ^ 19 + 36 * x ^ 18 - 354 * x ^ 17 +
      1221 * x ^ 16 - 2610 * x ^ 15 + 3697 * x ^ 14 -
      2990 * x ^ 13 - 10 * x ^ 12 + 3139 * x ^ 11 -
      3135 * x ^ 10 - 239 * x ^ 9 + 3552 * x ^ 8 -
      4116 * x ^ 7 + 2678 * x ^ 6 - 1199 * x ^ 5 +
      431 * x ^ 4 - 140 * x ^ 3 + 39 * x ^ 2 - 8 * x + 1)

/-- Evaluation of Mathlib's fifth `Φ` polynomial on the selected curve. -/
theorem eval_Phi_five (x : ℚ) :
    Polynomial.eval x (curve.Φ 5) = fiveDivisionNumerator x := by
  rw [show (5 : ℤ) = ((4 : ℕ) : ℤ) + 1 by norm_num,
    WeierstrassCurve.Φ_ofNat]
  norm_num
  rw [show (6 : ℕ) = 2 * (0 + 3) by norm_num,
    curve.preΨ'_even 0]
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
    curve.preΨ'_odd 0]
  norm_num
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, curve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    fiveDivisionNumerator]
  ring

/-- A single-fraction normal form for the first Vélu abscissa. -/
theorem veluFiveX_eq_fraction {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    veluFiveX x =
      (x ^ 5 - 2 * x ^ 4 + 3 * x ^ 3 - 2 * x + 1) /
        (x ^ 2 * (x - 1) ^ 2) := by
  simp only [veluFiveX]
  field_simp [hx0, sub_ne_zero.mpr hx1]
  ring

/-- The degree-thirty factor in the completed-ordinate formula for
multiplication by five. -/
def fiveDivisionDifferentialCofactor (x : ℚ) : ℚ :=
  x ^ 30 - 9 * x ^ 29 - 12 * x ^ 28 + 1149 * x ^ 27 -
    9477 * x ^ 26 + 48236 * x ^ 25 - 194660 * x ^ 24 +
    629437 * x ^ 23 - 1562985 * x ^ 22 + 2886576 * x ^ 21 -
    3801930 * x ^ 20 + 3139285 * x ^ 19 - 558414 * x ^ 18 -
    2601429 * x ^ 17 + 4291240 * x ^ 16 - 3785543 * x ^ 15 +
    2234480 * x ^ 14 - 1092885 * x ^ 13 + 694521 * x ^ 12 -
    560112 * x ^ 11 + 360701 * x ^ 10 - 147466 * x ^ 9 +
    28125 * x ^ 8 + 4440 * x ^ 7 - 4156 * x ^ 6 + 837 * x ^ 5 +
    177 * x ^ 4 - 178 * x ^ 3 + 63 * x ^ 2 - 12 * x + 1

/-- The numerator of the completed-ordinate multiplier for
multiplication by five. -/
def fiveDivisionDifferentialNumerator (x : ℚ) : ℚ :=
  (x ^ 3 - 4 * x ^ 2 + 4 * x - 2) *
    (x ^ 3 + x ^ 2 + x - 1) *
      fiveDivisionDifferentialCofactor x

/-- The completed-ordinate multiplier in the composite five-isogeny. -/
def fiveDivisionDifferential (x : ℚ) : ℚ :=
  fiveDivisionDifferentialNumerator x / fiveDivisionPolynomial x ^ 3

/-- A single-fraction normal form for the completed ordinate of the first
Vélu map. -/
theorem veluFiveY_completed_fraction {x y : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    2 * veluFiveY x y + 1 =
      (2 * y + 1) * (x ^ 3 - 4 * x ^ 2 + 4 * x - 2) *
          (x ^ 3 + x ^ 2 + x - 1) /
        (x ^ 3 * (x - 1) ^ 3) := by
  simp only [veluFiveY]
  field_simp [hx0, sub_ne_zero.mpr hx1]
  ring

/-- Pulling back the dual completed-ordinate multiplier produces the
degree-thirty factor above. -/
theorem dualFiveDifferential_veluFiveX {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    dualFiveDifferential (veluFiveX x) =
      fiveDivisionDifferentialCofactor x / fiveDivisionCofactor x ^ 3 := by
  have hcofactor := fiveDivisionCofactor_ne_zero hx0 hx1
  have hbase : x ^ 2 * (x - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx0)
      (pow_ne_zero 2 (sub_ne_zero.mpr hx1))
  have hbase' : x ^ 2 - x ^ 3 * 2 + x ^ 4 ≠ 0 := by
    convert hbase using 1
    ring
  simp only [dualFiveDifferential]
  rw [dualFiveKernelPolynomial_veluFiveX hx0 hx1,
    veluFiveX_eq_fraction hx0 hx1]
  simp only [div_pow]
  field_simp [hcofactor, hbase, hbase', hx0, sub_ne_zero.mpr hx1]
  simp only [fiveDivisionDifferentialCofactor]
  ring

/-- The full completed ordinate of the two Vélu maps composes to the
standard multiplication-by-five rational function. -/
theorem dualFiveY_veluFive_completed {x y : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    2 * dualFiveY (veluFiveX x) (veluFiveY x y) + 1 =
      (2 * y + 1) * fiveDivisionDifferential x := by
  calc
    2 * dualFiveY (veluFiveX x) (veluFiveY x y) + 1 =
        (2 * veluFiveY x y + 1) *
          dualFiveDifferential (veluFiveX x) := by
      simp only [dualFiveY]
      ring
    _ = (2 * y + 1) * fiveDivisionDifferential x := by
      rw [veluFiveY_completed_fraction hx0 hx1,
        dualFiveDifferential_veluFiveX hx0 hx1]
      have hcofactor := fiveDivisionCofactor_ne_zero hx0 hx1
      simp only [fiveDivisionDifferential,
        fiveDivisionDifferentialNumerator, fiveDivisionPolynomial]
      field_simp [hcofactor, hx0, sub_ne_zero.mpr hx1]

/-- The numerator left after cancelling the common three-division factor
from the secant joining `P` and `4P`. -/
private def fiveSecantSlopeNumerator (x : ℚ) : ℚ :=
  21 * x ^ 20 - 140 * x ^ 19 + 344 * x ^ 18 - 145 * x ^ 17 -
    1045 * x ^ 16 + 1776 * x ^ 15 + 2665 * x ^ 14 -
    14826 * x ^ 13 + 27706 * x ^ 12 - 30081 * x ^ 11 +
    20449 * x ^ 10 - 8220 * x ^ 9 + 1362 * x ^ 8 + 240 * x ^ 7 -
    105 * x ^ 6 + 15 * x ^ 4 - 35 * x ^ 3 + 28 * x ^ 2 - 9 * x + 1

/-- The remaining degree-twelve factor in the fifth-multiple abscissa
difference. -/
private def fiveAbscissaDifferenceCofactor (x : ℚ) : ℚ :=
  x ^ 12 - 4 * x ^ 11 + 55 * x ^ 9 - 165 * x ^ 8 + 264 * x ^ 7 -
    319 * x ^ 6 + 286 * x ^ 5 - 165 * x ^ 4 + 55 * x ^ 3 -
    11 * x ^ 2 + 3 * x - 1

private theorem quadrupleAbscissa_difference_identity (x : ℚ) :
    x * completedEquationPolynomial x * doubleCompletedNumerator x ^ 2 -
        quadrupleAbscissaNumerator x =
      (3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1) *
        fiveDivisionPolynomial x := by
  unfold completedEquationPolynomial doubleCompletedNumerator
    quadrupleAbscissaNumerator fiveDivisionPolynomial fiveDivisionCofactor
  ring

private theorem quadrupleCompleted_difference_identity (x : ℚ) :
    completedEquationPolynomial x ^ 2 * doubleCompletedNumerator x ^ 3 -
        quadrupleCompletedNumerator x =
      2 * (3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1) *
        fiveSecantSlopeNumerator x := by
  unfold completedEquationPolynomial doubleCompletedNumerator
    quadrupleCompletedNumerator fiveSecantSlopeNumerator
  ring

private theorem fiveAbscissa_difference_identity (x : ℚ) :
    fiveDivisionNumerator x - x * fiveDivisionPolynomial x ^ 2 =
      -completedEquationPolynomial x *
        (3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1) *
        doubleCompletedNumerator x * fiveAbscissaDifferenceCofactor x := by
  unfold fiveDivisionNumerator fiveDivisionPolynomial fiveDivisionCofactor
    completedEquationPolynomial doubleCompletedNumerator
    fiveAbscissaDifferenceCofactor
  ring

private theorem secantFiveAbscissa_identity (x : ℚ) :
    fiveSecantSlopeNumerator x ^ 2 +
        (completedEquationPolynomial x * doubleCompletedNumerator x ^ 2 *
              (1 - 2 * x) - quadrupleAbscissaNumerator x) *
          fiveDivisionPolynomial x ^ 2 +
      completedEquationPolynomial x ^ 2 * doubleCompletedNumerator x ^ 3 *
        (3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1) *
          fiveAbscissaDifferenceCofactor x = 0 := by
  unfold fiveSecantSlopeNumerator completedEquationPolynomial
    doubleCompletedNumerator quadrupleAbscissaNumerator
    fiveDivisionPolynomial fiveDivisionCofactor
    fiveAbscissaDifferenceCofactor
  ring

private theorem secantFiveCompletedOrdinate_identity (x : ℚ) :
    fiveDivisionDifferentialNumerator x =
      2 * fiveSecantSlopeNumerator x *
          (3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1) *
            fiveAbscissaDifferenceCofactor x - fiveDivisionPolynomial x ^ 3 := by
  unfold fiveDivisionDifferentialNumerator fiveDivisionDifferentialCofactor
    fiveSecantSlopeNumerator fiveAbscissaDifferenceCofactor
    fiveDivisionPolynomial fiveDivisionCofactor
  ring

/-- The normalized slope of the secant joining a point to its fourth
multiple. -/
private theorem secantFiveSlope {x z : ℚ}
    (hD : completedEquationPolynomial x ≠ 0)
    (hB : doubleCompletedNumerator x ≠ 0)
    (hψ : fiveDivisionPolynomial x ≠ 0) :
    ((z - z * quadrupleCompletedFactor x) / 2) /
        (x - quadrupleAbscissa x) =
      z * fiveSecantSlopeNumerator x /
        (completedEquationPolynomial x * doubleCompletedNumerator x *
          fiveDivisionPolynomial x) := by
  let D := completedEquationPolynomial x
  let B := doubleCompletedNumerator x
  let N := quadrupleAbscissaNumerator x
  let C := quadrupleCompletedNumerator x
  let T := 3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1
  let ψ := fiveDivisionPolynomial x
  let S := fiveSecantSlopeNumerator x
  have hD0 : D ≠ 0 := hD
  have hB0 : B ≠ 0 := hB
  have hψ0 : ψ ≠ 0 := hψ
  have hT0 : T ≠ 0 := threeDivisionPolynomial_ne_zero x
  have hN : x * D * B ^ 2 - N = T * ψ := by
    exact quadrupleAbscissa_difference_identity x
  have hC : D ^ 2 * B ^ 3 - C = 2 * T * S := by
    exact quadrupleCompleted_difference_identity x
  change ((z - z * (C / (D ^ 2 * B ^ 3))) / 2) /
      (x - N / (D * B ^ 2)) = z * S / (D * B * ψ)
  have hx : x - N / (D * B ^ 2) = T * ψ / (D * B ^ 2) := by
    field_simp [hD0, hB0]
    linear_combination hN
  have hz : (z - z * (C / (D ^ 2 * B ^ 3))) / 2 =
      z * T * S / (D ^ 2 * B ^ 3) := by
    have hC' : C = D ^ 2 * B ^ 3 - 2 * T * S := by
      linear_combination -hC
    rw [hC']
    field_simp [hD0, hB0]
    ring
  rw [hx, hz]
  field_simp [hD0, hB0, hT0, hψ0]

/-- The secant from a point to its fourth multiple has the standard
fifth-division abscissa. -/
private theorem secantFiveAbscissa {x z : ℚ}
    (hz : z ^ 2 = completedEquationPolynomial x)
    (hD : completedEquationPolynomial x ≠ 0)
    (hB : doubleCompletedNumerator x ≠ 0)
    (hψ : fiveDivisionPolynomial x ≠ 0) :
    curve.toAffine.addX x (quadrupleAbscissa x)
        (((z - z * quadrupleCompletedFactor x) / 2) /
          (x - quadrupleAbscissa x)) =
      fiveDivisionNumerator x / fiveDivisionPolynomial x ^ 2 := by
  let D := completedEquationPolynomial x
  let B := doubleCompletedNumerator x
  let N := quadrupleAbscissaNumerator x
  let T := 3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1
  let ψ := fiveDivisionPolynomial x
  let S := fiveSecantSlopeNumerator x
  let F := fiveDivisionNumerator x
  let H := fiveAbscissaDifferenceCofactor x
  have hD0 : D ≠ 0 := hD
  have hB0 : B ≠ 0 := hB
  have hψ0 : ψ ≠ 0 := hψ
  have hdiff : F - x * ψ ^ 2 = -D * T * B * H := by
    exact fiveAbscissa_difference_identity x
  have hadd :
      S ^ 2 + (D * B ^ 2 * (1 - 2 * x) - N) * ψ ^ 2 +
        D ^ 2 * B ^ 3 * T * H = 0 := by
    exact secantFiveAbscissa_identity x
  rw [secantFiveSlope hD hB hψ]
  simp only [curve, WeierstrassCurve.Affine.addX]
  norm_num
  change (z * S / (D * B * ψ)) ^ 2 + 1 - x - N / (D * B ^ 2) =
    F / ψ ^ 2
  field_simp [hD0, hB0, hψ0]
  linear_combination S ^ 2 * hz + D * hadd - D ^ 2 * B ^ 2 * hdiff

/-- The same secant calculation in completed-ordinate coordinates. -/
private theorem secantFiveCompletedOrdinate {x z : ℚ}
    (hD : completedEquationPolynomial x ≠ 0)
    (hB : doubleCompletedNumerator x ≠ 0)
    (hψ : fiveDivisionPolynomial x ≠ 0) :
    -2 * (((z - z * quadrupleCompletedFactor x) / 2) /
          (x - quadrupleAbscissa x)) *
        (fiveDivisionNumerator x / fiveDivisionPolynomial x ^ 2 - x) - z =
      z * fiveDivisionDifferential x := by
  let D := completedEquationPolynomial x
  let B := doubleCompletedNumerator x
  let T := 3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1
  let ψ := fiveDivisionPolynomial x
  let S := fiveSecantSlopeNumerator x
  let F := fiveDivisionNumerator x
  let H := fiveAbscissaDifferenceCofactor x
  let M := fiveDivisionDifferentialNumerator x
  have hD0 : D ≠ 0 := hD
  have hB0 : B ≠ 0 := hB
  have hψ0 : ψ ≠ 0 := hψ
  have hdiff : F - x * ψ ^ 2 = -D * T * B * H := by
    exact fiveAbscissa_difference_identity x
  have hM : M = 2 * S * T * H - ψ ^ 3 := by
    exact secantFiveCompletedOrdinate_identity x
  rw [secantFiveSlope hD hB hψ]
  change -2 * (z * S / (D * B * ψ)) * (F / ψ ^ 2 - x) - z =
    z * (M / ψ ^ 3)
  field_simp [hD0, hB0, hψ0]
  linear_combination (-2 * z * S) * hdiff - z * D * B * hM

/-- The abscissa of the composite of the two explicit Vélu maps is the
standard fifth-division rational function. -/
theorem dualFiveX_veluFiveX_explicit {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    dualFiveX (veluFiveX x) =
      fiveDivisionNumerator x / fiveDivisionPolynomial x ^ 2 := by
  have hcofactor := fiveDivisionCofactor_ne_zero hx0 hx1
  have hbase : x ^ 2 * (x - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx0)
      (pow_ne_zero 2 (sub_ne_zero.mpr hx1))
  have hbase' : x ^ 2 - x ^ 3 * 2 + x ^ 4 ≠ 0 := by
    convert hbase using 1
    ring
  have hdivision := fiveDivisionPolynomial_ne_zero hx0 hx1
  simp only [dualFiveX]
  rw [dualFiveKernelPolynomial_veluFiveX hx0 hx1,
    veluFiveX_eq_fraction hx0 hx1]
  simp only [div_pow]
  field_simp [hcofactor, hdivision, hbase, hbase', hx0,
    sub_ne_zero.mpr hx1]
  simp only [fiveDivisionPolynomial, fiveDivisionCofactor,
    fiveDivisionNumerator]
  ring

/-- The same composition identity in Mathlib's division-polynomial
normalization. -/
theorem dualFiveX_veluFiveX_division {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    dualFiveX (veluFiveX x) =
      Polynomial.eval x (curve.Φ 5) /
        Polynomial.eval x (curve.ΨSq 5) := by
  rw [eval_Phi_five, eval_PsiSq_five]
  exact dualFiveX_veluFiveX_explicit hx0 hx1

/-- The polynomial identity showing that the dual rational functions carry
the completed-square equation of the quotient to the completed-square
equation of `X₁(11)`. -/
theorem dualFive_completedSquare (X : ℚ) :
    dualFiveDifferential X ^ 2 *
        (4 * X ^ 3 - 4 * X ^ 2 - 40 * X - 79) =
      4 * dualFiveX X ^ 3 - 4 * dualFiveX X ^ 2 + 1 := by
  have hkernel : 5 * X ^ 2 + 5 * X - 29 ≠ 0 := by
    simpa only [dualFiveKernelPolynomial] using
      dualFiveKernelPolynomial_ne_zero X
  have hkernel' : X * 5 * (X + 1) - 29 ≠ 0 := by
    convert hkernel using 1
    ring
  simp only [dualFiveDifferential, dualFiveX, dualFiveKernelPolynomial,
    div_pow]
  field_simp [hkernel, hkernel']
  ring

/-- Direct substitution verifies that the dual formulas land on the selected
`X₁(11)` curve. -/
theorem dualFive_equation {X Y : ℚ}
    (hcurve : Y ^ 2 + Y = X ^ 3 - X ^ 2 - 10 * X - 20) :
    curve.toAffine.Equation (dualFiveX X) (dualFiveY X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [curve]
  have hsource :
      (2 * Y + 1) ^ 2 =
        4 * X ^ 3 - 4 * X ^ 2 - 40 * X - 79 := by
    nlinarith
  have htarget :
      (2 * dualFiveY X Y + 1) ^ 2 =
        4 * dualFiveX X ^ 3 - 4 * dualFiveX X ^ 2 + 1 := by
    rw [← dualFive_completedSquare X, ← hsource]
    simp only [dualFiveY]
    ring
  nlinarith

/-- The denominator-safe affine value of the dual five-isogeny. -/
def dualFivePoint {X Y : ℚ}
    (hP : fiveIsogenousCurve.toAffine.Nonsingular X Y) :
    curve.toAffine.Point :=
  .some (dualFiveX X) (dualFiveY X Y)
    (curve.toAffine.equation_iff_nonsingular.mp
      (dualFive_equation (by
        have heq := hP.1
        norm_num
          [WeierstrassCurve.Affine.equation_iff,
            fiveIsogenousCurve] at heq ⊢
        simpa only [sub_eq_add_neg] using heq)))

/-- The total dual five-isogeny on rational points.  Its geometric kernel is
nonconstant over `ℚ`, so no rational affine point is sent to infinity. -/
def dualFiveMap :
    fiveIsogenousCurve.toAffine.Point → curve.toAffine.Point
  | 0 => 0
  | .some _ _ hP => dualFivePoint hP

@[simp]
theorem dualFiveMap_zero : dualFiveMap 0 = 0 :=
  rfl

/-- Away from the visible kernel, the two explicit Vélu maps compose to
multiplication by five on the actual affine point group. -/
theorem dualFiveMap_veluFiveMap_some {x y : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    dualFiveMap (veluFiveMap (Point.some x y hP)) =
      (5 : ℕ) • Point.some x y hP := by
  let P : curve.toAffine.Point := Point.some x y hP
  have hP_ne : P ≠ 0 := Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    exact hP_ne (eq_zero_of_two_nsmul_eq_zero P htwo)
  obtain ⟨x₂, y₂, hP₂, hdouble⟩ :=
    existsCoordinatesOfNeZero ((2 : ℕ) • P) htwo_ne
  have hy : y ≠ curve.toAffine.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact Point.add_self_of_Y_eq hy
  have hdoubleCoords :
      curve.toAffine.addX x x (curve.toAffine.slope x x y y) = x₂ ∧
        curve.toAffine.addY x x y (curve.toAffine.slope x x y y) = y₂ := by
    apply Point.some.inj
    calc
      Point.some _ _ _ = P + P := (Point.add_self_of_Y_ne hy).symm
      _ = (2 : ℕ) • P := (two_nsmul P).symm
      _ = Point.some x₂ y₂ hP₂ := hdouble
  have hx₂ : x₂ = doubleAbscissa x :=
    hdoubleCoords.1.symm.trans (tangent_abscissa_eq_doubleAbscissa hP hy)
  have hz₂ : 2 * y₂ + 1 = (2 * y + 1) * doubleCompletedFactor x := by
    rw [← hdoubleCoords.2]
    exact tangent_completed_eq_doubleCompletedFactor hP hy
  have hz : 2 * y + 1 ≠ 0 := by
    intro hz
    apply hy
    simp only [curve, WeierstrassCurve.Affine.negY]
    linarith
  have hcompleted := completed_equation hP
  have hD : completedEquationPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  have htwo₂_ne : (2 : ℕ) • Point.some x₂ y₂ hP₂ ≠ 0 := by
    intro htwo₂
    have hP₂zero :=
      eq_zero_of_two_nsmul_eq_zero (Point.some x₂ y₂ hP₂) htwo₂
    exact htwo_ne (hdouble.trans hP₂zero)
  obtain ⟨x₄, y₄, hP₄, hdouble₂⟩ :=
    existsCoordinatesOfNeZero
      ((2 : ℕ) • Point.some x₂ y₂ hP₂) htwo₂_ne
  have hy₂ : y₂ ≠ curve.toAffine.negY x₂ y₂ := by
    intro hy₂
    apply htwo₂_ne
    rw [two_nsmul]
    exact Point.add_self_of_Y_eq hy₂
  have hz₂ne : 2 * y₂ + 1 ≠ 0 := by
    intro hz₂zero
    apply hy₂
    simp only [curve, WeierstrassCurve.Affine.negY]
    linarith
  have hB : doubleCompletedNumerator x ≠ 0 := by
    intro hB
    apply hz₂ne
    rw [hz₂, doubleCompletedFactor, hB]
    norm_num
  have hdouble₂Coords :
      curve.toAffine.addX x₂ x₂ (curve.toAffine.slope x₂ x₂ y₂ y₂) = x₄ ∧
        curve.toAffine.addY x₂ x₂ y₂ (curve.toAffine.slope x₂ x₂ y₂ y₂) = y₄ := by
    apply Point.some.inj
    calc
      Point.some _ _ _ = Point.some x₂ y₂ hP₂ + Point.some x₂ y₂ hP₂ :=
        (Point.add_self_of_Y_ne hy₂).symm
      _ = (2 : ℕ) • Point.some x₂ y₂ hP₂ :=
        (two_nsmul (Point.some x₂ y₂ hP₂)).symm
      _ = Point.some x₄ y₄ hP₄ := hdouble₂
  have hx₄ : x₄ = quadrupleAbscissa x := by
    calc
      x₄ = curve.toAffine.addX x₂ x₂
          (curve.toAffine.slope x₂ x₂ y₂ y₂) := hdouble₂Coords.1.symm
      _ = doubleAbscissa x₂ := tangent_abscissa_eq_doubleAbscissa hP₂ hy₂
      _ = doubleAbscissa (doubleAbscissa x) := by rw [hx₂]
      _ = quadrupleAbscissa x := doubleAbscissa_iterate hD hB
  have hz₄ : 2 * y₄ + 1 =
      (2 * y + 1) * quadrupleCompletedFactor x := by
    calc
      2 * y₄ + 1 =
          2 * curve.toAffine.addY x₂ x₂ y₂
              (curve.toAffine.slope x₂ x₂ y₂ y₂) + 1 := by
            rw [hdouble₂Coords.2]
      _ = (2 * y₂ + 1) * doubleCompletedFactor x₂ :=
        tangent_completed_eq_doubleCompletedFactor hP₂ hy₂
      _ = ((2 * y + 1) * doubleCompletedFactor x) *
          doubleCompletedFactor (doubleAbscissa x) := by rw [hz₂, hx₂]
      _ = (2 * y + 1) * quadrupleCompletedFactor x := by
        rw [mul_assoc, doubleCompletedFactor_iterate hD hB]
  have hfour : (4 : ℕ) • P = Point.some x₄ y₄ hP₄ := by
    calc
      (4 : ℕ) • P = (2 : ℕ) • ((2 : ℕ) • P) := by
        norm_num [← mul_nsmul]
      _ = (2 : ℕ) • Point.some x₂ y₂ hP₂ := by rw [hdouble]
      _ = Point.some x₄ y₄ hP₄ := hdouble₂
  have hfive_ne : (5 : ℕ) • P ≠ 0 :=
    five_nsmul_some_ne_zero hP hx0 hx1
  have hsec : x ≠ x₄ := by
    intro hxx₄
    rcases (Point.X_eq_iff).mp hxx₄ with heq | heq
    · have hfour_eq : (4 : ℕ) • P = P := hfour.trans heq.symm
      have hthree : (3 : ℕ) • P = 0 := by
        calc
          (3 : ℕ) • P = (4 : ℕ) • P - P := by abel
          _ = P - P := by rw [hfour_eq]
          _ = 0 := sub_self P
      exact hP_ne (eq_zero_of_three_nsmul_eq_zero P hthree)
    · apply hfive_ne
      calc
        (5 : ℕ) • P = P + (4 : ℕ) • P := by abel
        _ = P + Point.some x₄ y₄ hP₄ := by rw [hfour]
        _ = 0 := (add_eq_zero_iff_eq_neg).2 heq
  have hdy : y - y₄ =
      ((2 * y + 1) - (2 * y + 1) * quadrupleCompletedFactor x) / 2 := by
    linear_combination (-1 / 2 : ℚ) * hz₄
  have hslope : curve.toAffine.slope x x₄ y y₄ =
      (((2 * y + 1) - (2 * y + 1) * quadrupleCompletedFactor x) / 2) /
        (x - quadrupleAbscissa x) := by
    rw [curve.toAffine.slope_of_X_ne hsec, hdy, hx₄]
  have hψ := fiveDivisionPolynomial_ne_zero hx0 hx1
  have hx₅ : curve.toAffine.addX x x₄ (curve.toAffine.slope x x₄ y y₄) =
      fiveDivisionNumerator x / fiveDivisionPolynomial x ^ 2 := by
    rw [hslope, hx₄]
    exact secantFiveAbscissa hcompleted hD hB hψ
  have hz₅ :
      2 * curve.toAffine.addY x x₄ y (curve.toAffine.slope x x₄ y y₄) + 1 =
        (2 * y + 1) * fiveDivisionDifferential x := by
    have hsecant := secantFiveCompletedOrdinate
      (z := 2 * y + 1) hD hB hψ
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    simp_rw [hx₅, hslope]
    norm_num [curve]
    linear_combination hsecant
  have hfiveCoords :
      (5 : ℕ) • P =
        Point.some
          (curve.toAffine.addX x x₄ (curve.toAffine.slope x x₄ y y₄))
          (curve.toAffine.addY x x₄ y (curve.toAffine.slope x x₄ y y₄))
          (nonsingular_add hP hP₄ (fun hxy => hsec hxy.1)) := by
    calc
      (5 : ℕ) • P = P + (4 : ℕ) • P := by abel
      _ = P + Point.some x₄ y₄ hP₄ := by rw [hfour]
      _ = Point.some _ _ _ := Point.add_of_X_ne hsec
  rw [hfiveCoords]
  have hvelu : veluFiveMap P = veluFivePoint hP hx0 hx1 := by
    simp only [P, veluFiveMap]
    rw [dif_neg]
    exact fun h => h.elim hx0 hx1
  rw [hvelu]
  simp only [veluFivePoint, dualFiveMap, dualFivePoint, Point.some.injEq]
  constructor
  · rw [dualFiveX_veluFiveX_explicit hx0 hx1]
    exact hx₅.symm
  · have hdual := dualFiveY_veluFive_completed (y := y) hx0 hx1
    rw [← hz₅] at hdual
    linarith

private theorem five_nsmul_P0n1 : (5 : ℕ) • P0n1 = 0 := by
  rw [← four_P00]
  calc
    (5 : ℕ) • ((4 : ℕ) • P00) = (4 : ℕ) • ((5 : ℕ) • P00) := by
      norm_num [← mul_nsmul]
    _ = 0 := by simpa using congrArg (fun Q => (4 : ℕ) • Q) five_P00

private theorem five_nsmul_P1n1 : (5 : ℕ) • P1n1 = 0 := by
  rw [← double_P00]
  calc
    (5 : ℕ) • ((2 : ℕ) • P00) = (2 : ℕ) • ((5 : ℕ) • P00) := by
      norm_num [← mul_nsmul]
    _ = 0 := by simpa using congrArg (fun Q => (2 : ℕ) • Q) five_P00

private theorem five_nsmul_P10 : (5 : ℕ) • P10 = 0 := by
  rw [← triple_P00]
  calc
    (5 : ℕ) • ((3 : ℕ) • P00) = (3 : ℕ) • ((5 : ℕ) • P00) := by
      norm_num [← mul_nsmul]
    _ = 0 := by simpa using congrArg (fun Q => (3 : ℕ) • Q) five_P00

/-- The two explicit degree-five maps compose to multiplication by five on
every rational point of `X₁(11)`, including the visible kernel. -/
theorem dualFiveMap_veluFiveMap (P : curve.toAffine.Point) :
    dualFiveMap (veluFiveMap P) = (5 : ℕ) • P := by
  cases P with
  | zero => rfl
  | some x y hP =>
      by_cases hx : x = 0 ∨ x = 1
      · have hy : y ^ 2 + y = 0 := by
          have heq := hP.1
          rw [WeierstrassCurve.Affine.equation_iff] at heq
          rcases hx with hx | hx <;> subst x <;>
            norm_num [curve] at heq ⊢ <;> linarith
        have hyprod : y * (y + 1) = 0 := by nlinarith
        have hfive :
            (5 : ℕ) • Point.some x y hP = 0 := by
          rcases hx with hx | hx <;> subst x <;>
            rcases mul_eq_zero.mp hyprod with hy0 | hyn1
          · subst y
            simpa only [P00] using five_P00
          · have : y = -1 := by linarith
            subst y
            simpa only [P0n1] using five_nsmul_P0n1
          · subst y
            simpa only [P10] using five_nsmul_P10
          · have : y = -1 := by linarith
            subst y
            simpa only [P1n1] using five_nsmul_P1n1
        rw [(veluFiveMap_some_eq_zero_iff hP).2 hx,
          dualFiveMap_zero, hfive]
      · exact dualFiveMap_veluFiveMap_some hP
          (fun hx0 => hx (Or.inl hx0))
          (fun hx1 => hx (Or.inr hx1))

/-- The rational quotient point `(5,5)`. -/
def quotientP55 : fiveIsogenousCurve.toAffine.Point :=
  .some 5 5 (fiveIsogenousCurve.toAffine.equation_iff_nonsingular.mp (by
    norm_num [WeierstrassCurve.Affine.equation_iff, fiveIsogenousCurve]))

/-- The rational quotient point `(5,-6)`. -/
def quotientP5n6 : fiveIsogenousCurve.toAffine.Point :=
  .some 5 (-6) (fiveIsogenousCurve.toAffine.equation_iff_nonsingular.mp (by
    norm_num [WeierstrassCurve.Affine.equation_iff, fiveIsogenousCurve]))

/-- The rational quotient point `(16,-61)`. -/
def quotientP16n61 : fiveIsogenousCurve.toAffine.Point :=
  .some 16 (-61) (fiveIsogenousCurve.toAffine.equation_iff_nonsingular.mp (by
    norm_num [WeierstrassCurve.Affine.equation_iff, fiveIsogenousCurve]))

/-- The rational quotient point `(16,60)`. -/
def quotientP1660 : fiveIsogenousCurve.toAffine.Point :=
  .some 16 60 (fiveIsogenousCurve.toAffine.equation_iff_nonsingular.mp (by
    norm_num [WeierstrassCurve.Affine.equation_iff, fiveIsogenousCurve]))

/-- The dual map sends `(5,5)` to the marked point `(0,0)`. -/
@[simp]
theorem dualFiveMap_quotientP55 : dualFiveMap quotientP55 = P00 := by
  simp only [dualFiveMap, quotientP55, dualFivePoint, P00, Point.some.injEq]
  norm_num [dualFiveX, dualFiveY, dualFiveDifferential,
    dualFiveKernelPolynomial]

/-- The dual map sends `(5,-6)` to `(0,-1)`. -/
@[simp]
theorem dualFiveMap_quotientP5n6 : dualFiveMap quotientP5n6 = P0n1 := by
  simp only [dualFiveMap, quotientP5n6, dualFivePoint, P0n1, Point.some.injEq]
  norm_num [dualFiveX, dualFiveY, dualFiveDifferential,
    dualFiveKernelPolynomial]

/-- The dual map sends `(16,-61)` to `(1,-1)`. -/
@[simp]
theorem dualFiveMap_quotientP16n61 : dualFiveMap quotientP16n61 = P1n1 := by
  simp only [dualFiveMap, quotientP16n61, dualFivePoint, P1n1, Point.some.injEq]
  norm_num [dualFiveX, dualFiveY, dualFiveDifferential,
    dualFiveKernelPolynomial]

/-- The dual map sends `(16,60)` to `(1,0)`. -/
@[simp]
theorem dualFiveMap_quotientP1660 : dualFiveMap quotientP1660 = P10 := by
  simp only [dualFiveMap, quotientP1660, dualFivePoint, P10, Point.some.injEq]
  norm_num [dualFiveX, dualFiveY, dualFiveDifferential,
    dualFiveKernelPolynomial]

end MazurTorsion.XOneEleven
