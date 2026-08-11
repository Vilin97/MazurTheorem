/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentSquareclasses
import Mathlib.Data.Fin.VecNotation

/-!
# The mod-two certificate for the `X₁(13)` two-descent

This file checks the smallest finite calculation needed to exclude the three
nonidentity global squareclasses isolated in
`XOneThirteenTwoDescentSquareclasses`.

Write `a` for the image of an integral generator modulo `2`.  The residue
algebra is represented in the power basis by

`F₂[a] / (a⁶ + a⁴ + 1)`.

Thus `a⁶ = 1 + a⁴`; multiplying this relation by `a`, ..., `a⁴` gives
the reductions used by `quotientMul` below through degree ten.  All products
and all possible square roots are then checked in the 64-element coordinate
space.  The concrete unit and `lambda` vectors are exact reductions of the
integral formulas used in the two-descent calculation; the declarations in
this file retain only their finite coefficient certificates.

The descent framework is Michael Stoll, *Implementing 2-descent for
Jacobians of hyperelliptic curves*, Acta Arith. 98 (2001), Section 5,
DOI `10.4064/aa98-3-4`.  This file contains no third-party code.
-/

namespace MazurTorsion.XOneThirteenTwoDescentModTwoCertificate

open Polynomial

abbrev F2 := ZMod 2

private instance : NeZero (2 : ℕ) := ⟨by decide⟩
private instance : Fintype F2 := ZMod.fintype 2

/-- Coefficient vectors in the power basis `1, a, ..., a⁵`. -/
abbrev V := Fin 6 → F2

/-- The polynomial defining the mod-two residue algebra. -/
noncomputable def gbar : F2[X] := X ^ 6 + X ^ 4 + 1

/-- The coefficient of degree `n` in the ordinary product of two vectors,
before reduction modulo `gbar`. -/
def convolutionCoefficient (x y : V) (n : ℕ) : F2 :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    if i.val + j.val = n then x i * y j else 0

/-- Multiplication in `F₂[a] / (a⁶ + a⁴ + 1)`, in the power basis.

For raw product coefficients `cₙ`, the formula uses

`a⁶ = 1+a⁴`, `a⁷ = a+a⁵`, `a⁸ = 1+a²+a⁴`,
`a⁹ = a+a³+a⁵`, and `a¹⁰ = 1+a²`.
-/
def quotientMul (x y : V) : V :=
  let c := convolutionCoefficient x y
  ![c 0 + c 6 + c 8 + c 10,
    c 1 + c 7 + c 9,
    c 2 + c 8 + c 10,
    c 3 + c 9,
    c 4 + c 6 + c 8,
    c 5 + c 7 + c 9]

/-- The multiplicative identity in the quotient coordinates. -/
def one : V := ![1, 0, 0, 0, 0, 0]

/-- Frobenius squaring in the quotient coordinates. -/
def squareMap (v : V) : V :=
  ![v 0 + v 3 + v 4 + v 5,
    0,
    v 1 + v 4 + v 5,
    0,
    v 2 + v 3 + v 4,
    0]

/-- The displayed Frobenius formula is the self-product computed by
`quotientMul`. -/
theorem quotientMul_self_eq_squareMap (v : V) :
    quotientMul v v = squareMap v := by
  decide +revert

/-- An element of the 64-element quotient is a square if it is a
self-product in the quotient algebra. -/
def IsSquare (x : V) : Prop := ∃ v : V, quotientMul v v = x

/-- A canonical square root when the odd coefficients vanish. -/
def squareRootCandidate (x : V) : V := ![x 0, x 2, x 4, 0, 0, 0]

/-- Squares in the residue algebra are exactly the vectors whose
coefficients of `a`, `a³`, and `a⁵` vanish. -/
theorem isSquare_iff_odd_coefficients_eq_zero (x : V) :
    IsSquare x ↔ x 1 = 0 ∧ x 3 = 0 ∧ x 5 = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [quotientMul_self_eq_squareMap]
    decide +revert
  · rintro ⟨h₁, h₃, h₅⟩
    refine ⟨squareRootCandidate x, ?_⟩
    rw [quotientMul_self_eq_squareMap]
    funext i
    fin_cases i <;>
      simp [squareMap, squareRootCandidate, h₁, h₃, h₅]

/-- The first nontrivial global unit class, reduced modulo `2`. -/
def u1 : V := ![1, 1, 1, 1, 1, 1]

/-- The second nontrivial global unit class, reduced modulo `2`. -/
def u2 : V := ![1, 1, 1, 0, 0, 1]

/-- The local scalar ambiguity `lambda = 2 / pi²`, reduced modulo `2`. -/
def lambda : V := ![1, 1, 1, 0, 1, 1]

theorem u1_coefficients : u1 = ![1, 1, 1, 1, 1, 1] := rfl

theorem u1_mul_lambda_coefficients :
    quotientMul u1 lambda = ![0, 1, 0, 1, 0, 0] := by
  decide

theorem u2_coefficients : u2 = ![1, 1, 1, 0, 0, 1] := rfl

theorem u2_mul_lambda_coefficients :
    quotientMul u2 lambda = ![1, 1, 0, 1, 1, 0] := by
  decide

theorem u1_mul_u2_coefficients :
    quotientMul u1 u2 = ![0, 1, 1, 0, 1, 1] := by
  decide

theorem u1_mul_u2_mul_lambda_coefficients :
    quotientMul (quotientMul u1 u2) lambda = ![0, 1, 0, 0, 1, 1] := by
  decide

theorem u1_not_square : ¬ IsSquare u1 := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

theorem u1_mul_lambda_not_square : ¬ IsSquare (quotientMul u1 lambda) := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

theorem u2_not_square : ¬ IsSquare u2 := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

theorem u2_mul_lambda_not_square : ¬ IsSquare (quotientMul u2 lambda) := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

theorem u1_mul_u2_not_square : ¬ IsSquare (quotientMul u1 u2) := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

theorem u1_mul_u2_mul_lambda_not_square :
    ¬ IsSquare (quotientMul (quotientMul u1 u2) lambda) := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  decide

/-- The local representative attached to the two global squareclass bits.
The zero pair maps to `1`; the other three pairs map to `u1`, `u2`, and
`u1 * u2`. -/
def globalLocalRepresentative
    (z : XOneThirteenTwoDescentSquareclasses.GlobalSquareclassCertificate) : V :=
  quotientMul (if z.1 = 0 then one else u1)
    (if z.2 = 0 then one else u2)

/-- Optionally multiply a local representative by `lambda`. -/
def multiplyOptionalLambda (twist : Bool) (x : V) : V :=
  if twist then quotientMul x lambda else x

/-- Every nonidentity global squareclass remains nonsquare modulo `2`, for
both possible choices of the local `lambda` ambiguity. -/
theorem nontrivial_global_class_optional_lambda_not_square
    (z : XOneThirteenTwoDescentSquareclasses.GlobalSquareclassCertificate)
    (hz : z ≠ (0, 0)) (twist : Bool) :
    ¬ IsSquare (multiplyOptionalLambda twist (globalLocalRepresentative z)) := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  revert hz
  decide +revert

end MazurTorsion.XOneThirteenTwoDescentModTwoCertificate
