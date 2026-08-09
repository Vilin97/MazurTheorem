/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuotientSevenTorsion
import MazurTorsion.NumberTheory.XOneEighteenQuotientThreeTorsion
import MazurTorsion.NumberTheory.XOneEighteenFinalQuotientFibers

/-!
# Finite-group classification of the `X₁(18)` elliptic quotient

Once good reduction bounds the finite quotient point group by a divisor of
`21`, the visible point of order seven and the absence of three-torsion force
the group to have exactly seven elements.  This file isolates that elementary
consumer from the number-field reduction and two-descent calculations.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientFiniteClassification

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientSevenTorsion
open MazurTorsion.XOneEighteenQuotientThreeTorsion
open MazurTorsion.XOneEighteenFinalQuotientFibers

/-- If the finite quotient point group has cardinality dividing `21`, then
the visible seven-torsion subgroup is the whole group. -/
theorem point_card_eq_seven [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21) :
    Nat.card quotientCurve.toAffine.Point = 7 := by
  have hseven : 7 ∣ Nat.card quotientCurve.toAffine.Point := by
    rw [← addOrderOf_generator]
    exact addOrderOf_dvd_natCard generator
  have hnotThree : ¬3 ∣ Nat.card quotientCurve.toAffine.Point := by
    intro hthree
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ :=
      exists_prime_addOrderOf_dvd_card' (G := quotientCurve.toAffine.Point)
        3 hthree
    have hsmul : (3 : ℕ) • P = 0 := by
      rw [← hP]
      exact addOrderOf_nsmul_eq_zero P
    have hzero := eq_zero_of_three_nsmul_eq_zero P hsmul
    rw [hzero, addOrderOf_zero] at hP
    norm_num at hP
  obtain ⟨k, hk⟩ := hseven
  have hkdiv : k ∣ 3 := by
    rw [hk] at hcard
    apply (mul_dvd_mul_iff_left (by norm_num : (7 : ℕ) ≠ 0)).mp
    simpa using hcard
  rcases (Nat.dvd_prime Nat.prime_three).mp hkdiv with hkone | hkthree
  · simpa [hkone] using hk
  · exfalso
    apply hnotThree
    rw [hk, hkthree]
    norm_num

/-- The seven multiples of the visible generator enumerate every point once
the reduction cardinality divisor is known. -/
theorem generatorMultiples_bijective
    [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21) :
    Function.Bijective
      (fun i : Fin 7 ↦ (i : ℕ) • generator) := by
  have hinj : Function.Injective
      (fun i : Fin 7 ↦ (i : ℕ) • generator) := by
    intro i j hij
    apply Fin.ext
    have hfinite : IsOfFinAddOrder generator := by
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      exact ⟨7, by norm_num, seven_nsmul_generator⟩
    rw [hfinite.nsmul_eq_nsmul_iff_modEq, addOrderOf_generator] at hij
    exact Nat.ModEq.eq_of_lt_of_lt hij i.isLt j.isLt
  apply hinj.bijective_of_nat_card_le
  rw [Nat.card_fin, point_card_eq_seven hcard]

/-- Under the same finite reduction hypothesis, every point is one of the
seven explicitly displayed multiples of the visible generator. -/
theorem point_eq_visible_multiple
    [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21)
    (P : quotientCurve.toAffine.Point) :
    P = 0 ∨ P = generator ∨ P = pointTwo ∨ P = pointThree ∨
      P = pointFour ∨ P = -pointTwo ∨ P = -generator := by
  obtain ⟨i, rfl⟩ := (generatorMultiples_bijective hcard).2 P
  fin_cases i <;>
    simp [two_nsmul_generator_eq_pointTwo,
      three_nsmul_generator_eq_pointThree,
      four_nsmul_generator_eq_pointFour,
      five_nsmul_generator_eq_neg_pointTwo,
      six_nsmul_generator_eq_neg_generator]

/-- The finite-cardinality conclusion supplied by good reduction is already
enough to exclude a noncuspidal rational point on the sextic. -/
theorem no_noncuspidal_point_of_point_card_dvd_twentyOne
    [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21)
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 = MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := by
  have havoid := quotientX_not_mem_torsion_abscissas x hx0 hx1
  have hcases := point_eq_visible_multiple hcard (quotientPoint x y hcurve)
  rcases hcases with hzero | hgen | htwo | hthree | hfour | hfive | hsix
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _ hzero
  · apply havoid.1
    have hcoords : quotientX x = (1 : K) ∧ quotientY x y = 0 := by
      simpa only [quotientPoint, generator,
        WeierstrassCurve.Affine.Point.some.injEq] using hgen
    exact hcoords.1
  · apply havoid.2.1
    have hcoords :
        quotientX x = 3 - tau ^ 2 ∧ quotientY x y = 2 - tau ^ 2 := by
      simpa only [quotientPoint, pointTwo,
        WeierstrassCurve.Affine.Point.some.injEq] using htwo
    exact hcoords.1
  · apply havoid.2.2
    have hcoords :
        quotientX x = 1 - tau ∧ quotientY x y = -tau ^ 2 + tau := by
      simpa only [quotientPoint, pointThree,
        WeierstrassCurve.Affine.Point.some.injEq] using hthree
    exact hcoords.1
  · apply havoid.2.2
    have hcoords : quotientX x = 1 - tau ∧ quotientY x y = -tau := by
      simpa only [quotientPoint, pointFour,
        WeierstrassCurve.Affine.Point.some.injEq] using hfour
    exact hcoords.1
  · apply havoid.2.1
    have hcoords : quotientX x = 3 - tau ^ 2 ∧
        quotientY x y = quotientCurve.toAffine.negY
          (3 - tau ^ 2) (2 - tau ^ 2) := by
      simpa only [quotientPoint, pointTwo,
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] using hfive
    exact hcoords.1
  · apply havoid.1
    have hcoords : quotientX x = (1 : K) ∧
        quotientY x y = quotientCurve.toAffine.negY 1 0 := by
      simpa only [quotientPoint, generator,
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] using hsix
    exact hcoords.1

end

end MazurTorsion.XOneEighteenQuotientFiniteClassification
