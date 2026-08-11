/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentModTwoCertificate

/-!
# The finite global/local intersection for the `X₁(13)` two-descent

The four global classes surviving the abstract norm and rational-scalar
relations are represented by `1`, `u₁`, `u₂`, and `u₁u₂`.  At the
prime `2`, rational scalar squareclasses contribute the optional factor
`lambda`, while the two displayed local Kummer generators reduce modulo `2`
to `1` and `a²`.

The latter is already a square.  This leaf performs the resulting bounded
calculation directly: for both choices of `lambda` and both choices of
`a²`, no nonidentity global class becomes a square.  It is the exact finite
intersection needed after the global support theorem and local Kummer-image
theorem are supplied.

This module asserts only the finite quotient-ring calculation.  Passage
from global and `ℚ₂` squareclasses to these residue coordinates remains a
separate arithmetic bridge.
-/

namespace MazurTorsion.XOneThirteenTwoDescentLocalIntersection

open XOneThirteenTwoDescentSquareclasses
open XOneThirteenTwoDescentModTwoCertificate

private instance : NeZero (2 : ℕ) := ⟨by decide⟩
private instance : Fintype (ZMod 2) := ZMod.fintype 2

/-- The reduction of `qB = 1 - 2a²`. -/
def qBReduction : V := one

/-- The reduction of `qC = 2 - a²`; in characteristic two this is `a²`. -/
def qCReduction : V := ![0, 0, 1, 0, 0, 0]

/-- Exponentiation by a binary exponent in the fixed coordinate algebra. -/
def bitPow (x : V) (e : ZMod 2) : V := if e = 0 then one else x

/-- The nontrivial part of a reduced local representative.  The factors `5`
and `qB` reduce to one, so only `lambda` and `qC` remain. -/
def localReducedRepresentative (e d : ZMod 2) : V :=
  quotientMul (bitPow lambda e) (bitPow qCReduction d)

/-- Product of a surviving global class with a reduced local
representative. -/
def globalLocalReducedProduct
    (z : GlobalSquareclassCertificate) (e d : ZMod 2) : V :=
  quotientMul (globalLocalRepresentative z)
    (localReducedRepresentative e d)

/-- The two discarded local factors really reduce to the multiplicative
identity. -/
theorem five_qB_reductions :
    (![1, 0, 0, 0, 0, 0] : V) = one ∧ qBReduction = one :=
  ⟨rfl, rfl⟩

/-- The second local generator has an explicit square root modulo `2`. -/
theorem qCReduction_isSquare :
    XOneThirteenTwoDescentModTwoCertificate.IsSquare qCReduction := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

/-- Exact finite intersection: a displayed global/local product is a square
if and only if the global class and the `lambda` exponent both vanish.  The
`qC` exponent is unrestricted because its reduction is already a square. -/
theorem globalLocalReducedProduct_isSquare_iff
    (z : GlobalSquareclassCertificate) (e d : ZMod 2) :
    XOneThirteenTwoDescentModTwoCertificate.IsSquare
      (globalLocalReducedProduct z e d) ↔
      z = (0, 0) ∧ e = 0 := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  revert z e d
  decide +revert

/-- Consequently, local representability forces the global class to be the
identity. -/
theorem global_eq_zero_of_globalLocalReducedProduct_isSquare
    (z : GlobalSquareclassCertificate) (e d : ZMod 2)
    (hsquare : XOneThirteenTwoDescentModTwoCertificate.IsSquare
      (globalLocalReducedProduct z e d)) :
    z = (0, 0) :=
  (globalLocalReducedProduct_isSquare_iff z e d).mp hsquare |>.1

end MazurTorsion.XOneThirteenTwoDescentLocalIntersection
