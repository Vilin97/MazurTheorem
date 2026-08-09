/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultFiniteField
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Reduction modulo three for the order-twenty-five Brunault chart

A nonzero rational number need not have a nonzero reduction modulo three.
This file records the exact arithmetic condition needed by the finite-field
Brunault calculation: both the numerator and denominator of each coordinate
must be nonzero modulo three.  It then proves, by clearing denominators over
the integers, that Brunault's characteristic-zero equation reduces to the
same equation over `ZMod 3`.

The final theorem is deliberately stated with explicit three-adic unit
hypotheses.  Producing those hypotheses for a modular point is a separate
geometric or integral-model obligation; rational nonvanishing alone is not
used as a substitute.
-/

namespace MazurTorsion.Kubert

/-- The canonical reduction of a rational number, formed from its normalized
integer numerator and positive denominator.  It represents reduction modulo
three only when `orderTwentyFiveRatIsThreeIntegral` holds. -/
def orderTwentyFiveRatReduction (q : ℚ) : ZMod 3 :=
  (q.num : ZMod 3) / (q.den : ZMod 3)

/-- A rational number is integral at three exactly when its normalized
denominator remains nonzero modulo three. -/
def orderTwentyFiveRatIsThreeIntegral (q : ℚ) : Prop :=
  (q.den : ZMod 3) ≠ 0

/-- A rational number is a three-adic unit when both its normalized numerator
and denominator remain nonzero modulo three. -/
def orderTwentyFiveRatIsThreeUnit (q : ℚ) : Prop :=
  orderTwentyFiveRatIsThreeIntegral q ∧ (q.num : ZMod 3) ≠ 0

/-- A fraction with numerator and denominator nonzero modulo three is a
three-adic unit.  This lets downstream calculations use any convenient
integer fraction, without having to normalize it by hand. -/
theorem orderTwentyFiveRatIsThreeUnit_of_eq_div
    (q : ℚ) (a b : ℤ) (hb : b ≠ 0)
    (hq : q = (a : ℚ) / (b : ℚ))
    (ha3 : (a : ZMod 3) ≠ 0) (hb3 : (b : ZMod 3) ≠ 0) :
    orderTwentyFiveRatIsThreeUnit q := by
  have hq' : q = Rat.divInt a b := by
    simpa [Rat.divInt_eq_div] using hq
  obtain ⟨c, hnum, hden⟩ := Rat.num_den_mk hb hq'
  have hnum3 : (a : ZMod 3) = (c : ZMod 3) * (q.num : ZMod 3) := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hnum
  have hden3 : (b : ZMod 3) = (c : ZMod 3) * (q.den : ZMod 3) := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hden
  constructor
  · intro hqden
    apply hb3
    rw [hden3, hqden, mul_zero]
  · intro hqnum
    apply ha3
    rw [hnum3, hqnum, mul_zero]

/-- Reduction is independent of the chosen three-unit fraction representing
the rational number. -/
theorem orderTwentyFiveRatReduction_eq_div_of_eq_div
    (q : ℚ) (a b : ℤ) (hb : b ≠ 0)
    (hq : q = (a : ℚ) / (b : ℚ))
    (ha3 : (a : ZMod 3) ≠ 0) (hb3 : (b : ZMod 3) ≠ 0) :
    orderTwentyFiveRatReduction q =
      (a : ZMod 3) / (b : ZMod 3) := by
  have hq' : q = Rat.divInt a b := by
    simpa [Rat.divInt_eq_div] using hq
  obtain ⟨c, hnum, hden⟩ := Rat.num_den_mk hb hq'
  have hnum3 : (a : ZMod 3) = (c : ZMod 3) * (q.num : ZMod 3) := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hnum
  have hden3 : (b : ZMod 3) = (c : ZMod 3) * (q.den : ZMod 3) := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hden
  have hc3 : (c : ZMod 3) ≠ 0 := by
    intro hc
    apply ha3
    rw [hnum3, hc, zero_mul]
  have hqden3 : (q.den : ZMod 3) ≠ 0 :=
    (orderTwentyFiveRatIsThreeUnit_of_eq_div q a b hb hq ha3 hb3).1
  simp only [orderTwentyFiveRatReduction, hnum3, hden3]
  field_simp [hc3, hqden3, hb3]

/-- A three-adic unit has a nonzero canonical reduction modulo three. -/
theorem orderTwentyFiveRatReduction_ne_zero
    {q : ℚ} (hq : orderTwentyFiveRatIsThreeUnit q) :
    orderTwentyFiveRatReduction q ≠ 0 := by
  exact div_ne_zero hq.2 hq.1

/-- The integral numerator obtained by multiplying Brunault's equation by
`uDen⁴ vDen⁴`.  It is kept public so a downstream primitive-coordinate
calculation can target the exact certificate checked here. -/
def orderTwentyFiveBrunaultClearedNumerator
    (uNum uDen vNum vDen : ℤ) : ℤ :=
  vNum ^ 2 * uNum ^ 4 * vDen ^ 2 +
    vNum ^ 3 * uNum ^ 3 * uDen * vDen +
    vNum ^ 2 * uNum ^ 3 * uDen * vDen ^ 2 +
    3 * vNum ^ 3 * uNum ^ 2 * uDen ^ 2 * vDen -
    vNum ^ 2 * uNum ^ 2 * uDen ^ 2 * vDen ^ 2 -
    2 * vNum * uNum ^ 2 * uDen ^ 2 * vDen ^ 3 +
    vNum ^ 4 * uNum * uDen ^ 3 -
    4 * vNum ^ 2 * uNum * uDen ^ 3 * vDen ^ 2 +
    vNum * uNum * uDen ^ 3 * vDen ^ 3 -
    uNum * uDen ^ 3 * vDen ^ 4 -
    vNum ^ 3 * uDen ^ 4 * vDen

private theorem orderTwentyFiveBrunaultClearedNumerator_rat_identity
    (uNum uDen vNum vDen : ℤ)
    (huDen : uDen ≠ 0) (hvDen : vDen ≠ 0) :
    (orderTwentyFiveBrunaultClearedNumerator
        uNum uDen vNum vDen : ℚ) =
      (uDen : ℚ) ^ 4 * (vDen : ℚ) ^ 4 *
        orderTwentyFiveBrunaultPolynomial
          ((uNum : ℚ) / (uDen : ℚ))
          ((vNum : ℚ) / (vDen : ℚ)) := by
  simp only [orderTwentyFiveBrunaultClearedNumerator,
    orderTwentyFiveBrunaultPolynomial]
  push_cast
  field_simp [huDen, hvDen]
  ring

private theorem orderTwentyFiveBrunaultClearedNumerator_mod_three_identity
    (uNum uDen vNum vDen : ℤ)
    (huDen : (uDen : ZMod 3) ≠ 0)
    (hvDen : (vDen : ZMod 3) ≠ 0) :
    (orderTwentyFiveBrunaultClearedNumerator
        uNum uDen vNum vDen : ZMod 3) =
      (uDen : ZMod 3) ^ 4 * (vDen : ZMod 3) ^ 4 *
        orderTwentyFiveBrunaultPolynomial
          ((uNum : ZMod 3) / (uDen : ZMod 3))
          ((vNum : ZMod 3) / (vDen : ZMod 3)) := by
  simp only [orderTwentyFiveBrunaultClearedNumerator,
    orderTwentyFiveBrunaultPolynomial]
  push_cast
  field_simp [huDen, hvDen]
  ring

/-- Brunault's characteristic-zero equation is compatible with canonical
reduction modulo three whenever both rational coordinates are three-adic
units.  The proof clears denominators over `ℤ` before casting; there is no
ring homomorphism `ℚ → ZMod 3`. -/
theorem orderTwentyFiveBrunaultPolynomial_reduction_eq_zero
    (u v : ℚ)
    (hu : orderTwentyFiveRatIsThreeUnit u)
    (hv : orderTwentyFiveRatIsThreeUnit v)
    (hpoly : orderTwentyFiveBrunaultPolynomial u v = 0) :
    orderTwentyFiveBrunaultPolynomial
        (orderTwentyFiveRatReduction u)
        (orderTwentyFiveRatReduction v) = 0 := by
  have huDen : (u.den : ℤ) ≠ 0 := by
    exact_mod_cast u.den_nz
  have hvDen : (v.den : ℤ) ≠ 0 := by
    exact_mod_cast v.den_nz
  have hrat := orderTwentyFiveBrunaultClearedNumerator_rat_identity
    u.num u.den v.num v.den huDen hvDen
  simp only [Int.cast_natCast] at hrat
  rw [Rat.num_div_den u, Rat.num_div_den v, hpoly, mul_zero] at hrat
  have hint :
      orderTwentyFiveBrunaultClearedNumerator
        u.num u.den v.num v.den = 0 := by
    exact_mod_cast hrat
  have hmod :
      (orderTwentyFiveBrunaultClearedNumerator
        u.num u.den v.num v.den : ZMod 3) = 0 := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hint
  rw [orderTwentyFiveBrunaultClearedNumerator_mod_three_identity
    u.num u.den v.num v.den hu.1 hv.1] at hmod
  have hdenprod :
      (u.den : ZMod 3) ^ 4 * (v.den : ZMod 3) ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hu.1) (pow_ne_zero 4 hv.1)
  exact (mul_eq_zero.mp hmod).resolve_left hdenprod

/-- There is no rational zero of Brunault's polynomial whose two coordinates
are three-adic units.  This is the checked arithmetic consumer of the full
`F₃` enumeration. -/
theorem orderTwentyFiveBrunaultPolynomial_ne_zero_of_three_units
    (u v : ℚ)
    (hu : orderTwentyFiveRatIsThreeUnit u)
    (hv : orderTwentyFiveRatIsThreeUnit v) :
    orderTwentyFiveBrunaultPolynomial u v ≠ 0 := by
  intro hpoly
  have hred := orderTwentyFiveBrunaultPolynomial_reduction_eq_zero
    u v hu hv hpoly
  exact orderTwentyFiveBrunaultPolynomial_f3_ne_zero_of_open
    (orderTwentyFiveRatReduction u)
    (orderTwentyFiveRatReduction v)
    ⟨orderTwentyFiveRatReduction_ne_zero hu,
      orderTwentyFiveRatReduction_ne_zero hv⟩ hred

end MazurTorsion.Kubert
