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

The auxiliary monic quintic is the one recorded by Odile Lécacheux in
*Unités d'une famille de corps liés à la courbe X₁(25)*.  Its leading and
constant coefficients give a small, kernel-checked integrality criterion for
the two Lécacheux units used as Brunault coordinates.
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

/-- A fraction with denominator nonzero modulo three is integral at three.
No condition on its numerator is needed. -/
theorem orderTwentyFiveRatIsThreeIntegral_of_eq_div
    (q : ℚ) (a b : ℤ) (hb : b ≠ 0)
    (hq : q = (a : ℚ) / (b : ℚ))
    (hb3 : (b : ZMod 3) ≠ 0) :
    orderTwentyFiveRatIsThreeIntegral q := by
  have hq' : q = Rat.divInt a b := by
    simpa [Rat.divInt_eq_div] using hq
  obtain ⟨c, -, hden⟩ := Rat.num_den_mk hb hq'
  have hden3 : (b : ZMod 3) = (c : ZMod 3) * (q.den : ZMod 3) := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hden
  intro hqden
  apply hb3
  rw [hden3, hqden, mul_zero]

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

private theorem orderTwentyFiveRat_num_mod_three_ne_zero_of_den_eq_zero
    (q : ℚ) (hden : (q.den : ZMod 3) = 0) :
    (q.num : ZMod 3) ≠ 0 := by
  intro hnum
  have hcoprime : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using q.reduced
  have hcoprime3 := hcoprime.map (Int.castRingHom (ZMod 3))
  change IsCoprime (q.num : ZMod 3) (q.den : ZMod 3) at hcoprime3
  rw [hnum, hden] at hcoprime3
  exact not_isCoprime_zero_zero hcoprime3

/-- Negation does not change whether a rational number is a three-adic
unit. -/
theorem orderTwentyFiveRatIsThreeUnit_neg_iff (q : ℚ) :
    orderTwentyFiveRatIsThreeUnit (-q) ↔
      orderTwentyFiveRatIsThreeUnit q := by
  simp [orderTwentyFiveRatIsThreeUnit,
    orderTwentyFiveRatIsThreeIntegral]

/-- At least one of the two Fricke-related parameters `n` and `5 / n` is
integral at three.  The geometric statement that Fricke carries the relevant
modular point and its five units to the second parameter is intentionally not
asserted here. -/
theorem orderTwentyFive_frickeParameter_three_integral
    (n : ℚ) (hn : n ≠ 0) :
    orderTwentyFiveRatIsThreeIntegral n ∨
      orderTwentyFiveRatIsThreeIntegral (5 / n) := by
  by_cases hden : (n.den : ZMod 3) = 0
  · right
    have hnum : n.num ≠ 0 := Rat.num_ne_zero.mpr hn
    have hnum3 : (n.num : ZMod 3) ≠ 0 :=
      orderTwentyFiveRat_num_mod_three_ne_zero_of_den_eq_zero n hden
    apply orderTwentyFiveRatIsThreeIntegral_of_eq_div
      (5 / n) (5 * (n.den : ℤ)) n.num hnum
    · calc
        5 / n = 5 / ((n.num : ℚ) / (n.den : ℚ)) := by
          rw [Rat.num_div_den n]
        _ = ((5 * (n.den : ℤ) : ℤ) : ℚ) / (n.num : ℚ) := by
          push_cast
          field_simp [hnum]
    · exact hnum3
  · exact Or.inl hden

/-- Emma Lehmer's monic quintic in Lécacheux's `n`-parameter and
modular-unit convention.  Lécacheux's five cyclically indexed modular units
are its roots. -/
def orderTwentyFiveLehmerPolynomial
    {R : Type*} [CommRing R] (n x : R) : R :=
  x ^ 5 - n ^ 2 * x ^ 4 +
    2 * (n ^ 3 - 3 * n ^ 2 + 5 * n - 5) * x ^ 3 -
    (n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5) * x ^ 2 +
    (-n ^ 3 + 4 * n ^ 2 - 10 * n + 10) * x - 1

/-- The integral numerator obtained from Lehmer's polynomial by multiplying
by `nDen⁴ xDen⁵`. -/
def orderTwentyFiveLehmerClearedNumerator
    (nNum nDen xNum xDen : ℤ) : ℤ :=
  nDen ^ 4 * xNum ^ 5 -
    nNum ^ 2 * nDen ^ 2 * xNum ^ 4 * xDen +
    2 * (nNum ^ 3 * nDen - 3 * nNum ^ 2 * nDen ^ 2 +
      5 * nNum * nDen ^ 3 - 5 * nDen ^ 4) * xNum ^ 3 * xDen ^ 2 -
    (nNum ^ 4 - 5 * nNum ^ 3 * nDen + 11 * nNum ^ 2 * nDen ^ 2 -
      15 * nNum * nDen ^ 3 + 5 * nDen ^ 4) * xNum ^ 2 * xDen ^ 3 +
    (-nNum ^ 3 * nDen + 4 * nNum ^ 2 * nDen ^ 2 -
      10 * nNum * nDen ^ 3 + 10 * nDen ^ 4) * xNum * xDen ^ 4 -
    nDen ^ 4 * xDen ^ 5

private theorem orderTwentyFiveLehmerClearedNumerator_rat_identity
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

/-- A rational root of Lehmer's monic quintic is a three-adic unit whenever
the parameter is integral at three.  The unit constant coefficient `-1` is
essential: after clearing denominators, reduction modulo three separately
rules out a factor of three in the root's denominator and numerator. -/
theorem orderTwentyFiveLehmer_root_isThreeUnit
    (n x : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n)
    (hx : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveRatIsThreeUnit x := by
  have hnDen : (n.den : ℤ) ≠ 0 := by
    exact_mod_cast n.den_nz
  have hxDen : (x.den : ℤ) ≠ 0 := by
    exact_mod_cast x.den_nz
  have hrat := orderTwentyFiveLehmerClearedNumerator_rat_identity
    n.num n.den x.num x.den hnDen hxDen
  simp only [Int.cast_natCast] at hrat
  rw [Rat.num_div_den n, Rat.num_div_den x, hx, mul_zero] at hrat
  have hint :
      orderTwentyFiveLehmerClearedNumerator
        n.num n.den x.num x.den = 0 := by
    exact_mod_cast hrat
  have hmod :
      (orderTwentyFiveLehmerClearedNumerator
        n.num n.den x.num x.den : ZMod 3) = 0 := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 3)) hint
  have hxDen3 : (x.den : ZMod 3) ≠ 0 := by
    intro hxden
    have hxnum : (x.num : ZMod 3) ≠ 0 :=
      orderTwentyFiveRat_num_mod_three_ne_zero_of_den_eq_zero x hxden
    have hlead :
        (n.den : ZMod 3) ^ 4 * (x.num : ZMod 3) ^ 5 = 0 := by
      simpa [orderTwentyFiveLehmerClearedNumerator, hxden] using hmod
    exact (mul_ne_zero (pow_ne_zero 4 hn) (pow_ne_zero 5 hxnum)) hlead
  have hxNum3 : (x.num : ZMod 3) ≠ 0 := by
    intro hxnum
    have hconstant :
        (n.den : ZMod 3) ^ 4 * (x.den : ZMod 3) ^ 5 = 0 := by
      simpa [orderTwentyFiveLehmerClearedNumerator, hxnum] using hmod
    exact (mul_ne_zero (pow_ne_zero 4 hn) (pow_ne_zero 5 hxDen3)) hconstant
  exact ⟨hxDen3, hxNum3⟩

/-- Two selected Lécacheux units are three-adic units as soon as they are
roots of the Lehmer polynomial at a three-integral parameter.  This is the
small interface needed for Brunault's coordinates `u = x₀`, `v = -x₂`. -/
theorem orderTwentyFiveLehmer_two_roots_areThreeUnits
    (n x₀ x₂ : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n)
    (hx₀ : orderTwentyFiveLehmerPolynomial n x₀ = 0)
    (hx₂ : orderTwentyFiveLehmerPolynomial n x₂ = 0) :
    orderTwentyFiveRatIsThreeUnit x₀ ∧
      orderTwentyFiveRatIsThreeUnit (-x₂) := by
  refine ⟨orderTwentyFiveLehmer_root_isThreeUnit n x₀ hn hx₀, ?_⟩
  exact (orderTwentyFiveRatIsThreeUnit_neg_iff x₂).mpr
    (orderTwentyFiveLehmer_root_isThreeUnit n x₂ hn hx₂)

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

/-- The Lehmer-root integrality criterion feeds directly into the checked
finite-field exclusion for Brunault's coordinates `u = x₀`, `v = -x₂`.
The three-integrality and root premises remain explicit for the geometric
bridge to discharge. -/
theorem orderTwentyFiveBrunaultPolynomial_ne_zero_of_lehmer_roots
    (n x₀ x₂ : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n)
    (hx₀ : orderTwentyFiveLehmerPolynomial n x₀ = 0)
    (hx₂ : orderTwentyFiveLehmerPolynomial n x₂ = 0) :
    orderTwentyFiveBrunaultPolynomial x₀ (-x₂) ≠ 0 := by
  obtain ⟨hx₀Unit, hx₂Unit⟩ :=
    orderTwentyFiveLehmer_two_roots_areThreeUnits n x₀ x₂ hn hx₀ hx₂
  exact orderTwentyFiveBrunaultPolynomial_ne_zero_of_three_units
    x₀ (-x₂) hx₀Unit hx₂Unit

end MazurTorsion.Kubert
