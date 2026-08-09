/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPellPowerSplit

/-!
# Fixed Mumford certificates for `X₁(13)`

This file begins a concrete divisor-class calculation for the genus-two curve

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

For a monic quadratic `u = X² + u₁X + u₀` and a linear polynomial
`v = v₁X + v₀`, a Mumford pair must satisfy `u ∣ f - v²`.  Polynomial
division leaves two explicit scalar remainders.  The identity below turns
those two equalities into a small certificate verifier; later finite
divisor-class computations need only provide the scalar equalities.

The first consumer checks the pair supported at the two affine cusps with
abscissae `0` and `-1` and ordinate `1`.
-/

namespace MazurTorsion.XOneThirteenMumford

open Polynomial

noncomputable section

/-- The fixed degree-six polynomial defining the affine `X₁(13)` model. -/
def sexticPolynomial : ℚ[X] :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- A monic quadratic in coefficient coordinates. -/
def monicQuadratic (u₀ u₁ : ℚ) : ℚ[X] :=
  X ^ 2 + C u₁ * X + C u₀

/-- A linear polynomial in coefficient coordinates. -/
def linearPolynomial (v₀ v₁ : ℚ) : ℚ[X] :=
  C v₁ * X + C v₀

/-- The constant coefficient left after division of `f - v²` by `u`. -/
def mumfordRemainderConstant (u₀ u₁ v₀ v₁ : ℚ) : ℚ :=
  -u₀ ^ 3 + 3 * u₀ ^ 2 * u₁ ^ 2 - 4 * u₀ ^ 2 * u₁ + u₀ ^ 2 -
    u₀ * u₁ ^ 4 + 2 * u₀ * u₁ ^ 3 - u₀ * u₁ ^ 2 +
    2 * u₀ * u₁ + u₀ * v₁ ^ 2 - 6 * u₀ - v₀ ^ 2 + 1

/-- The linear coefficient left after division of `f - v²` by `u`. -/
def mumfordRemainderLinear (u₀ u₁ v₀ v₁ : ℚ) : ℚ :=
  -3 * u₀ ^ 2 * u₁ + 2 * u₀ ^ 2 + 4 * u₀ * u₁ ^ 3 -
    6 * u₀ * u₁ ^ 2 + 2 * u₀ * u₁ - 2 * u₀ - u₁ ^ 5 +
    2 * u₁ ^ 4 - u₁ ^ 3 + 2 * u₁ ^ 2 + u₁ * v₁ ^ 2 -
    6 * u₁ - 2 * v₀ * v₁ + 4

/-- The quotient in the fixed monic-quadratic division certificate. -/
def mumfordQuotient (u₀ u₁ v₁ : ℚ) : ℚ[X] :=
  X ^ 4 + C (2 - u₁) * X ^ 3 +
    C (-u₀ + u₁ ^ 2 - 2 * u₁ + 1) * X ^ 2 +
    C (2 * u₀ * u₁ - 2 * u₀ - u₁ ^ 3 + 2 * u₁ ^ 2 - u₁ + 2) * X +
    C (u₀ ^ 2 - 3 * u₀ * u₁ ^ 2 + 4 * u₀ * u₁ - u₀ +
      u₁ ^ 4 - 2 * u₁ ^ 3 + u₁ ^ 2 - 2 * u₁ - v₁ ^ 2 + 6)

/-- Exact polynomial division by a symbolic monic quadratic. -/
theorem mumford_division_certificate (u₀ u₁ v₀ v₁ : ℚ) :
    sexticPolynomial - linearPolynomial v₀ v₁ ^ 2 =
      monicQuadratic u₀ u₁ * mumfordQuotient u₀ u₁ v₁ +
        C (mumfordRemainderConstant u₀ u₁ v₀ v₁) +
        C (mumfordRemainderLinear u₀ u₁ v₀ v₁) * X := by
  apply Polynomial.funext
  intro x
  simp only [sexticPolynomial, linearPolynomial, monicQuadratic,
    mumfordQuotient, mumfordRemainderConstant, mumfordRemainderLinear,
    eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat,
    eval_one]
  ring

/-- Fixed-curve validity condition for a monic quadratic Mumford pair. -/
def IsMumfordPair (u₀ u₁ v₀ v₁ : ℚ) : Prop :=
  monicQuadratic u₀ u₁ ∣
    sexticPolynomial - linearPolynomial v₀ v₁ ^ 2

/-- Two scalar remainder equalities are a sufficient checked certificate for
a fixed-curve Mumford pair. -/
theorem isMumfordPair_of_remainders_eq_zero
    (u₀ u₁ v₀ v₁ : ℚ)
    (h₀ : mumfordRemainderConstant u₀ u₁ v₀ v₁ = 0)
    (h₁ : mumfordRemainderLinear u₀ u₁ v₀ v₁ = 0) :
    IsMumfordPair u₀ u₁ v₀ v₁ := by
  refine ⟨mumfordQuotient u₀ u₁ v₁, ?_⟩
  rw [mumford_division_certificate, h₀, h₁]
  simp

/-- The monic quadratic pair through `(0,1)` and `(-1,1)` is valid on the
fixed sextic.  This is the first concrete cuspidal divisor certificate. -/
theorem cuspPair_isMumfordPair :
    IsMumfordPair 0 1 1 0 := by
  apply isMumfordPair_of_remainders_eq_zero <;>
    norm_num [mumfordRemainderConstant, mumfordRemainderLinear]

end

end MazurTorsion.XOneThirteenMumford
