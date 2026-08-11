/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentMagmaBridge

/-!
# Prime-support identities for the `X₁(13)` two-descent field

This file checks explicit factorizations of the rational scalars `2` and
`13` in the monogenic order `ℤ[a]/(g)` used by the independent two-descent
calculation.  The factors at `13` are normalized by a unit so that the
resulting squareclass identity has precisely the coordinate convention

`(0,1,1,1,0,1)`

recorded in `XOneThirteenTwoDescentSquareclasses`: the two prime-supported
generators, `u₁`, and `i` occur, while `u₂` does not.

Only the displayed equalities in the order are asserted here.  In
particular, primality of the factors and exhaustiveness of the supported
squareclasses require separate ideal-theoretic arguments.  The formulas were
obtained by bounded exact polynomial arithmetic; the retained certificate is
the pair of polynomial identities checked below by Lean.
-/

namespace MazurTorsion.XOneThirteenTwoDescentPrimeSupport

open MazurTorsion.XOneThirteenTwoDescentMagmaBridge

noncomputable section

/-! ## Factors above two -/

/-- A degree-four representative of the factor supported above `2`. -/
def primeTwoFactor : MagmaOrder :=
  -1 - integralA + integralA ^ 2 + integralA ^ 4

/-- The remaining explicit square factor in the factorization of `2`. -/
def primeTwoSquareRoot : MagmaOrder :=
  -integralA ^ 5 + 2 * integralA ^ 4 - 2 * integralA ^ 3 +
    2 * integralA ^ 2 - 2 * integralA + 1

/-- An explicit inverse of `primeTwoSquareRoot`. -/
def primeTwoSquareRootInverse : MagmaOrder :=
  -integralA ^ 4 + integralA ^ 3 - integralA ^ 2 + 2 * integralA

/-- A short identity explaining the square factor at `2`. -/
theorem primeTwoFactor_mul_squareRoot :
    primeTwoFactor * primeTwoSquareRoot = integralI - 1 := by
  have h := integralA_spec
  simp only [primeTwoFactor, primeTwoSquareRoot, integralI]
  linear_combination (1 - integralA ^ 3) * h

/-- The displayed square factor at `2` is a unit of the monogenic order. -/
theorem primeTwoSquareRoot_mul_inverse :
    primeTwoSquareRoot * primeTwoSquareRootInverse = 1 := by
  have h := integralA_spec
  simp only [primeTwoSquareRoot, primeTwoSquareRootInverse]
  linear_combination
    (integralA ^ 3 - integralA ^ 2 - 1) * h

/-- The rational scalar `2` represents the class of `i`: all nonunit
contributions in this displayed factorization occur to even order. -/
theorem rationalTwo_squareclass_identity :
    integralI * (primeTwoFactor * primeTwoSquareRoot) ^ 2 = 2 := by
  rw [primeTwoFactor_mul_squareRoot]
  calc
    integralI * (integralI - 1) ^ 2 =
        integralI * integralI ^ 2 - 2 * integralI ^ 2 +
          integralI := by ring
    _ = 2 := by rw [integralI_sq]; ring

/-! ## Factors above thirteen -/

/-- The factor coming from the linear factor of `g` modulo `13`. -/
def primeThirteenLinearFactor : MagmaOrder :=
  -1 - integralA - integralA ^ 2

/-- A raw factor coming from the irreducible cubic factor of `g` modulo
`13`. -/
def primeThirteenCubicFactorRaw : MagmaOrder :=
  -2 - integralA - 2 * integralA ^ 2 + 2 * integralA ^ 3

/-- A unit-normalized associate of `primeThirteenCubicFactorRaw`.  The
normalization moves `u₂ / i` into this supported generator and makes the
rational-scalar relation use `u₁` and `i`, matching the audited parity
coordinates. -/
def primeThirteenCubicFactor : MagmaOrder :=
  (-integralI) * integralUnitTwo * primeThirteenCubicFactorRaw

/-- The explicit square factor in the factorization of `13`. -/
def primeThirteenSquareRoot : MagmaOrder :=
  primeThirteenLinearFactor *
    (-integralA ^ 5 + integralA ^ 4 - integralA ^ 3 +
      2 * integralA ^ 2 - 2 * integralA)

/-- Multiplication by `i` removes the unit used to normalize the cubic
factor. -/
theorem primeThirteenCubicFactor_mul_i :
    primeThirteenCubicFactor * integralI =
      integralUnitTwo * primeThirteenCubicFactorRaw := by
  simp only [primeThirteenCubicFactor]
  calc
    (-integralI) * integralUnitTwo * primeThirteenCubicFactorRaw *
        integralI =
        -(integralI ^ 2) * integralUnitTwo *
          primeThirteenCubicFactorRaw := by ring
    _ = integralUnitTwo * primeThirteenCubicFactorRaw := by
      rw [integralI_sq]
      ring

private theorem rationalThirteen_raw_identity :
    primeThirteenLinearFactor * primeThirteenCubicFactorRaw *
        integralUnitOne * integralUnitTwo *
        primeThirteenSquareRoot ^ 2 = 13 := by
  have h := integralA_spec
  simp only [primeThirteenLinearFactor, primeThirteenCubicFactorRaw,
    primeThirteenSquareRoot, integralUnitOne, integralUnitTwo]
  linear_combination
    (-2 * integralA ^ 23 + 2 * integralA ^ 22 -
      3 * integralA ^ 21 + 18 * integralA ^ 20 -
      16 * integralA ^ 19 + 18 * integralA ^ 18 -
      61 * integralA ^ 17 + 55 * integralA ^ 16 -
      31 * integralA ^ 15 + 111 * integralA ^ 14 -
      95 * integralA ^ 13 + 8 * integralA ^ 12 -
      113 * integralA ^ 11 + 98 * integralA ^ 10 +
      40 * integralA ^ 9 + 60 * integralA ^ 8 -
      75 * integralA ^ 7 - 61 * integralA ^ 6 -
      10 * integralA ^ 5 + 51 * integralA ^ 4 +
      40 * integralA ^ 3 - 8 * integralA ^ 2 -
      26 * integralA - 13) * h

/-- In the normalized supported basis, the rational scalar `13` is the
product of the two supported generators, `u₁`, and `i`, times a square.
This is the exact algebraic identity behind the parity vector
`(0,1,1,1,0,1)`. -/
theorem rationalThirteen_squareclass_identity :
    primeThirteenLinearFactor * primeThirteenCubicFactor *
        integralUnitOne * integralI * primeThirteenSquareRoot ^ 2 = 13 := by
  calc
    primeThirteenLinearFactor * primeThirteenCubicFactor *
        integralUnitOne * integralI * primeThirteenSquareRoot ^ 2 =
        primeThirteenLinearFactor *
          (primeThirteenCubicFactor * integralI) * integralUnitOne *
          primeThirteenSquareRoot ^ 2 := by ring
    _ = primeThirteenLinearFactor *
          (integralUnitTwo * primeThirteenCubicFactorRaw) *
          integralUnitOne * primeThirteenSquareRoot ^ 2 := by
      rw [primeThirteenCubicFactor_mul_i]
    _ = primeThirteenLinearFactor * primeThirteenCubicFactorRaw *
          integralUnitOne * integralUnitTwo *
          primeThirteenSquareRoot ^ 2 := by ring
    _ = 13 := rationalThirteen_raw_identity

/-- The two concrete rational-scalar relations, packaged together for the
global squareclass bridge. -/
theorem rationalScalar_squareclass_identities :
    integralI * (primeTwoFactor * primeTwoSquareRoot) ^ 2 = 2 ∧
      primeThirteenLinearFactor * primeThirteenCubicFactor *
        integralUnitOne * integralI * primeThirteenSquareRoot ^ 2 = 13 :=
  ⟨rationalTwo_squareclass_identity, rationalThirteen_squareclass_identity⟩

end

end MazurTorsion.XOneThirteenTwoDescentPrimeSupport
