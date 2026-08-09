/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultFiniteField
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A checked orbit certificate for Brunault's order-twenty-five equation

This file verifies the small elimination certificate relating Lécacheux's
five cyclic orbit coordinates to Brunault's genus-four polynomial. The
certificate was found by exact Gröbner-basis computation over `ℤ`; Lean's
ring normalizer checks the displayed identity.
-/

namespace MazurTorsion.Kubert

/-- The first of Lécacheux's five cyclic orbit relations. -/
def orderTwentyFiveOrbitRelationZero
    {R : Type*} [CommRing R] (a b c d _e : R) : R :=
  a - c - a * (b - d)

/-- The second of Lécacheux's five cyclic orbit relations. -/
def orderTwentyFiveOrbitRelationOne
    {R : Type*} [CommRing R] (_a b c d e : R) : R :=
  b - d - b * (c - e)

/-- The third of Lécacheux's five cyclic orbit relations. -/
def orderTwentyFiveOrbitRelationTwo
    {R : Type*} [CommRing R] (a _b c d e : R) : R :=
  c - e - c * (d - a)

/-- The fourth of Lécacheux's five cyclic orbit relations. -/
def orderTwentyFiveOrbitRelationThree
    {R : Type*} [CommRing R] (a b _c d e : R) : R :=
  d - a - d * (e - b)

/-- The fifth of Lécacheux's five cyclic orbit relations. -/
def orderTwentyFiveOrbitRelationFour
    {R : Type*} [CommRing R] (a b c _d e : R) : R :=
  e - b - e * (a - c)

/-- The norm-one relation for Lécacheux's five orbit coordinates. -/
def orderTwentyFiveOrbitRelationFive
    {R : Type*} [CommRing R] (a b c d e : R) : R :=
  a * b * c * d * e - 1

private def orderTwentyFiveOrbitMultiplierZero
    {R : Type*} [CommRing R] (a _b c d e : R) : R :=
  4 * a ^ 3 * c ^ 2 - 4 * a ^ 3 * c * e - 4 * a ^ 3 * c -
    2 * a ^ 3 * e - 2 * a ^ 3 - 4 * a ^ 2 * c ^ 3 +
    4 * a ^ 2 * c ^ 2 * e - 4 * a ^ 2 * c ^ 2 + 2 * a ^ 2 * c * d * e +
    10 * a ^ 2 * c * e + 16 * a ^ 2 * c + 2 * a ^ 2 * e ^ 2 +
    5 * a ^ 2 * e + 3 * a ^ 2 + 4 * a * c ^ 3 - 2 * a * c ^ 2 * d * e -
    2 * a * c ^ 2 * e - 4 * a * c ^ 2 - 3 * a * c * d * e -
    2 * a * c * e ^ 2 - 3 * a * c * e - 10 * a * c - 3 * a * e ^ 2 -
    3 * a * e - 2 * a - c ^ 2 * d * e + c ^ 2 * e + 4 * c ^ 2 -
    c * e ^ 2 + c * e + c + e + 2

private def orderTwentyFiveOrbitMultiplierOne
    {R : Type*} [CommRing R] (a _b c _d e : R) : R :=
  -4 * a ^ 4 * c - 2 * a ^ 4 + 4 * a ^ 3 * c ^ 2 + 12 * a ^ 3 * c +
    2 * a ^ 3 * e + a ^ 3 - 4 * a ^ 2 * c ^ 2 - 2 * a ^ 2 * c * e -
    3 * a ^ 2 * e + a ^ 2 - a * c * e + 2 * a + c + 1

private def orderTwentyFiveOrbitMultiplierTwo
    {R : Type*} [CommRing R] (a _b c d e : R) : R :=
  4 * a ^ 4 * c + 2 * a ^ 4 * e - 4 * a ^ 3 * c ^ 2 -
    6 * a ^ 3 * c * e - 8 * a ^ 3 * c + 2 * a ^ 3 * d * e - a ^ 3 * e +
    4 * a ^ 2 * c ^ 2 * e + 4 * a ^ 2 * c ^ 2 - 2 * a ^ 2 * c * d * e +
    3 * a ^ 2 * c * e + 4 * a ^ 2 * c - 3 * a ^ 2 * d * e -
    3 * a ^ 2 * e - a * c * d * e + 2 * a * c + 2 * c ^ 2 * e +
    2 * c * e + c + e + 1

private def orderTwentyFiveOrbitMultiplierThree
    {R : Type*} [CommRing R] (a _b c _d _e : R) : R :=
  -4 * a ^ 3 * c - 2 * a ^ 3 + 4 * a ^ 2 * c ^ 2 + 10 * a ^ 2 * c +
    3 * a ^ 2 - 2 * a * c ^ 2 - a * c + c ^ 2 + 2 * c + 1

private def orderTwentyFiveOrbitMultiplierFour
    {R : Type*} [CommRing R] (a _b c d e : R) : R :=
  2 * a ^ 4 * c - 4 * a ^ 3 * c ^ 2 - 4 * a ^ 3 * c * d -
    5 * a ^ 3 * c - 2 * a ^ 3 * d - 2 * a ^ 3 * e - 2 * a ^ 3 +
    4 * a ^ 2 * c ^ 2 * d + 10 * a ^ 2 * c * d + 4 * a ^ 2 * c * e +
    9 * a ^ 2 * c + 3 * a ^ 2 * d + a ^ 2 * e + 3 * a ^ 2 -
    2 * a * c ^ 2 * d - 4 * a * c ^ 2 - a * c * d - 2 * a * c * e -
    3 * a * c + a * e + c ^ 2 * d - c ^ 2 + 2 * c * d + c * e +
    d + e + 1

private def orderTwentyFiveOrbitMultiplierFive
    {R : Type*} [CommRing R] (a _b c _d _e : R) : R :=
  2 * a ^ 2 - 2 * a * c - 3 * a - c

private theorem orderTwentyFiveOrbit_brunault_certificate
    {R : Type*} [CommRing R] (a b c d e : R) :
    4 * (a - 1) * orderTwentyFiveBrunaultPolynomial a (-c) =
      orderTwentyFiveOrbitMultiplierZero a b c d e *
          orderTwentyFiveOrbitRelationZero a b c d e +
        orderTwentyFiveOrbitMultiplierOne a b c d e *
          orderTwentyFiveOrbitRelationOne a b c d e +
        orderTwentyFiveOrbitMultiplierTwo a b c d e *
          orderTwentyFiveOrbitRelationTwo a b c d e +
        orderTwentyFiveOrbitMultiplierThree a b c d e *
          orderTwentyFiveOrbitRelationThree a b c d e +
        orderTwentyFiveOrbitMultiplierFour a b c d e *
          orderTwentyFiveOrbitRelationFour a b c d e +
        orderTwentyFiveOrbitMultiplierFive a b c d e *
          orderTwentyFiveOrbitRelationFive a b c d e := by
  simp only [orderTwentyFiveBrunaultPolynomial,
    orderTwentyFiveOrbitMultiplierZero, orderTwentyFiveOrbitMultiplierOne,
    orderTwentyFiveOrbitMultiplierTwo, orderTwentyFiveOrbitMultiplierThree,
    orderTwentyFiveOrbitMultiplierFour, orderTwentyFiveOrbitMultiplierFive,
    orderTwentyFiveOrbitRelationZero, orderTwentyFiveOrbitRelationOne,
    orderTwentyFiveOrbitRelationTwo, orderTwentyFiveOrbitRelationThree,
    orderTwentyFiveOrbitRelationFour, orderTwentyFiveOrbitRelationFive]
  ring

/-- Lécacheux's cyclic orbit equations, their norm-one relation, and the
nonexceptional condition `a ≠ 1` force Brunault's genus-four equation. -/
theorem orderTwentyFiveBrunaultPolynomial_eq_zero_of_orbit
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveBrunaultPolynomial a (-c) = 0 := by
  have hcertificate := orderTwentyFiveOrbit_brunault_certificate a b c d e
  rw [h0, h1, h2, h3, h4, h5] at hcertificate
  have hfactor : 4 * (a - 1) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr ha)
  exact (mul_eq_zero.mp (by simpa using hcertificate)).resolve_left hfactor

end MazurTorsion.Kubert
