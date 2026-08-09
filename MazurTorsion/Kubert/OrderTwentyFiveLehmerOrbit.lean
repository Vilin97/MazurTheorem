/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultIntegrality

/-!
# Finite-field obstructions for the order-twenty-five Lehmer cover

Lécacheux's five cyclic modular units are roots of Emma Lehmer's quintic
`orderTwentyFiveLehmerPolynomial n`.  This file checks that the affine
two-variable Lehmer equation has no points over `F₂`, `F₃`, or `F₁₃`.

The `F₃` computation has a characteristic-zero consumer: a rational root is
impossible when its parameter is integral at three.  The proof first uses the
monic and unit-constant terms to make the root a three-adic unit, then clears
denominators over the integers before reducing.  In particular, this does not
claim that every rational modular parameter is three-integral.  Local Tate
points in the cusp disks need not satisfy that missing global premise.
-/

namespace MazurTorsion.Kubert

/-- The affine Lehmer equation has no point over `F₂`. -/
theorem orderTwentyFiveLehmerPolynomial_f2_ne_zero
    (n x : ZMod 2) :
    orderTwentyFiveLehmerPolynomial n x ≠ 0 := by
  decide +revert

/-- The affine Lehmer equation has no point over `F₃`. -/
theorem orderTwentyFiveLehmerPolynomial_f3_ne_zero
    (n x : ZMod 3) :
    orderTwentyFiveLehmerPolynomial n x ≠ 0 := by
  decide +revert

/-- The affine Lehmer equation has no point over `F₁₃`. -/
theorem orderTwentyFiveLehmerPolynomial_f13_ne_zero
    (n x : ZMod 13) :
    orderTwentyFiveLehmerPolynomial n x ≠ 0 := by
  decide +revert

private theorem orderTwentyFiveLehmerClearedNumerator_rat_identity'
    (nNum nDen xNum xDen : ℤ)
    (hnDen : nDen ≠ 0) (hxDen : xDen ≠ 0) :
    (orderTwentyFiveLehmerClearedNumerator
        nNum nDen xNum xDen : ℚ) =
      (nDen : ℚ) ^ 4 * (xDen : ℚ) ^ 5 *
        orderTwentyFiveLehmerPolynomial
          ((nNum : ℚ) / (nDen : ℚ))
          ((xNum : ℚ) / (xDen : ℚ)) := by
  simp only [orderTwentyFiveLehmerClearedNumerator,
    orderTwentyFiveLehmerPolynomial]
  push_cast
  field_simp [hnDen, hxDen]

private theorem orderTwentyFiveLehmerClearedNumerator_mod_three_identity
    (nNum nDen xNum xDen : ℤ)
    (hnDen : (nDen : ZMod 3) ≠ 0)
    (hxDen : (xDen : ZMod 3) ≠ 0) :
    (orderTwentyFiveLehmerClearedNumerator
        nNum nDen xNum xDen : ZMod 3) =
      (nDen : ZMod 3) ^ 4 * (xDen : ZMod 3) ^ 5 *
        orderTwentyFiveLehmerPolynomial
          ((nNum : ZMod 3) / (nDen : ZMod 3))
          ((xNum : ZMod 3) / (xDen : ZMod 3)) := by
  simp only [orderTwentyFiveLehmerClearedNumerator,
    orderTwentyFiveLehmerPolynomial]
  push_cast
  field_simp [hnDen, hxDen]

private theorem orderTwentyFiveLehmerPolynomial_reduction_eq_zero
    (n x : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n)
    (hxUnit : orderTwentyFiveRatIsThreeUnit x)
    (hpoly : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveLehmerPolynomial
        (orderTwentyFiveRatReduction n)
        (orderTwentyFiveRatReduction x) = 0 := by
  have hnDen : (n.den : ℤ) ≠ 0 := by
    exact_mod_cast n.den_nz
  have hxDen : (x.den : ℤ) ≠ 0 := by
    exact_mod_cast x.den_nz
  have hrat := orderTwentyFiveLehmerClearedNumerator_rat_identity'
    n.num n.den x.num x.den hnDen hxDen
  simp only [Int.cast_natCast] at hrat
  rw [Rat.num_div_den n, Rat.num_div_den x, hpoly, mul_zero] at hrat
  have hint :
      orderTwentyFiveLehmerClearedNumerator
        n.num n.den x.num x.den = 0 := by
    exact_mod_cast hrat
  have hmod :
      (orderTwentyFiveLehmerClearedNumerator
        n.num n.den x.num x.den : ZMod 3) = 0 := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hint
  rw [orderTwentyFiveLehmerClearedNumerator_mod_three_identity
    n.num n.den x.num x.den hn hxUnit.1] at hmod
  have hdenprod :
      (n.den : ZMod 3) ^ 4 * (x.den : ZMod 3) ^ 5 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hn) (pow_ne_zero 5 hxUnit.1)
  have hred := (mul_eq_zero.mp hmod).resolve_left hdenprod
  simpa [orderTwentyFiveRatReduction] using hred

/-- A rational specialization of the Lehmer polynomial has no rational root
when its parameter is integral at three.  The integrality premise is the
global cusp-disk obstruction still required by the order-twenty-five bridge. -/
theorem orderTwentyFiveLehmerPolynomial_ne_zero_of_three_integral
    (n x : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n) :
    orderTwentyFiveLehmerPolynomial n x ≠ 0 := by
  intro hroot
  have hxUnit := orderTwentyFiveLehmer_root_isThreeUnit n x hn hroot
  have hred := orderTwentyFiveLehmerPolynomial_reduction_eq_zero
    n x hn hxUnit hroot
  exact orderTwentyFiveLehmerPolynomial_f3_ne_zero
    (orderTwentyFiveRatReduction n)
    (orderTwentyFiveRatReduction x) hred

/-- A rational Lehmer root forces the parameter into the nonintegral side of
the scalar Fricke dichotomy: `n` is nonzero and nonintegral at three, while
`5 / n` is integral at three.  This is only a statement about the two rational
parameters; it does not assert that Fricke gives a rational self-map of the
same genus-four model or transports the chosen Lehmer root. -/
theorem orderTwentyFiveLehmer_root_fricke_three_integral
    (n x : ℚ)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    n ≠ 0 ∧
      ¬ orderTwentyFiveRatIsThreeIntegral n ∧
      orderTwentyFiveRatIsThreeIntegral (5 / n) := by
  have hnNotIntegral : ¬ orderTwentyFiveRatIsThreeIntegral n := by
    intro hn
    exact orderTwentyFiveLehmerPolynomial_ne_zero_of_three_integral
      n x hn hroot
  have hn0 : n ≠ 0 := by
    intro hn
    apply hnNotIntegral
    subst n
    norm_num [orderTwentyFiveRatIsThreeIntegral]
  have hfricke := orderTwentyFive_frickeParameter_three_integral n hn0
  exact ⟨hn0, hnNotIntegral, hfricke.resolve_left hnNotIntegral⟩

end MazurTorsion.Kubert
