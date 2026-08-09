/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The explicit level-35 quotient coordinate at infinity

On the hyperelliptic model of `X₀(35)` used by Kubert, put `t = 1 / x`.  The
Atkin--Lehner quotient `X₀(35) / w₅` has affine coordinate

`W = (x² - 6x - 1) / (x² + x - 1)`.

Consequently its parameter at the image of the infinity cusp has the exact
formal expansion

`W - 1 = -7t / (1 + t - t²)`.

This file verifies that identity inside the power-series ring and, in
particular, proves that the tangent coefficient is `-7`.  Thus the quotient
map is unramified at this cusp in every residue characteristic other than
seven, including the auxiliary characteristic eleven.

The model and quotient formula are recorded in J. González Rovira,
"Equations of hyperelliptic modular curves", *Ann. Inst. Fourier* 41 (1991),
779--795, DOI 10.5802/aif.1273, pp. 792--795; the birational Weierstrass
normalization also appears in D. Kubert, "Universal bounds on the torsion of
elliptic curves", *Proc. London Math. Soc.* (3) 33 (1976), 193--237, p. 221.
These references are bibliographic guidance only.  No source text, code, or
data is retained, and the identities below are checked directly by Lean.
-/

noncomputable section

namespace MazurTorsion.OrderThirtyFive.QuotientQExpansion

section AlgebraicMap

variable {R : Type*} [CommRing R]

/-- The infinity-chart denominator obtained from `x² + x - 1` after
putting `t = 1 / x`. -/
def localDenominator (t : R) : R :=
  1 + t - t ^ 2

/-- The infinity-chart numerator obtained from `x² - 6x - 1`. -/
def localNumerator (t : R) : R :=
  1 - 6 * t - t ^ 2

/-- The second factor of the reversed level-35 hyperelliptic polynomial. -/
def localSourceSecondFactor (t : R) : R :=
  1 - 5 * t - 9 * t ^ 3 - 5 * t ^ 5 - t ^ 6

/-- The equation `s² = localSourcePolynomial t` in the infinity chart,
where `s = y / x⁴`. -/
def localSourcePolynomial (t : R) : R :=
  localDenominator t * localSourceSecondFactor t

/-- Expanded form of the reversed hyperelliptic polynomial. -/
theorem localSourcePolynomial_eq (t : R) :
    localSourcePolynomial t =
      1 - 4 * t - 6 * t ^ 2 - 4 * t ^ 3 - 9 * t ^ 4 +
        4 * t ^ 5 - 6 * t ^ 6 + 4 * t ^ 7 + t ^ 8 := by
  simp only [localSourcePolynomial, localDenominator,
    localSourceSecondFactor]
  ring

/-- The denominator-cleared identity proving that the explicit formulas for
`W` and `Z` land on `Z² + Z = W³ + W² + 9W + 1`.  This form is valid over
every commutative ring and is the small algebraic verifier behind the
quotient map. -/
theorem quotientMap_cleared_targetEquation (t s : R)
    (hsource : s ^ 2 = localSourcePolynomial t) :
    49 * s ^ 2 - localDenominator t ^ 4 =
      4 * (localNumerator t ^ 3 * localDenominator t +
        localNumerator t ^ 2 * localDenominator t ^ 2 +
        9 * localNumerator t * localDenominator t ^ 3 +
        localDenominator t ^ 4) := by
  rw [hsource]
  simp only [localSourcePolynomial, localSourceSecondFactor,
    localNumerator, localDenominator]
  ring

/-- The numerator of `dW/dt` is exactly `-7(1+t²)`. -/
theorem quotientCoordinate_derivativeNumerator (t : R) :
    (-6 - 2 * t) * localDenominator t -
        localNumerator t * (1 - 2 * t) =
      -7 * (1 + t ^ 2) := by
  simp only [localDenominator, localNumerator]
  ring

end AlgebraicMap

section FormalExpansion

variable {K : Type*} [Field K]

/-- The denominator `1 + t - t²` in the local expression for the quotient
coordinate.  Its constant coefficient is one, so it is a power-series unit. -/
def denominator : PowerSeries K :=
  1 + PowerSeries.X - PowerSeries.X ^ 2

/-- The numerator `1 - 6t - t²` in the local expression for `W`. -/
def numerator : PowerSeries K :=
  1 - (6 : K) • PowerSeries.X - PowerSeries.X ^ 2

/-- The local expansion of the quotient coordinate `W`. -/
def quotientCoordinateExpansion : PowerSeries K :=
  numerator * denominator⁻¹

/-- The target local parameter `W - 1` pulled back to the infinity cusp. -/
def quotientParameterExpansion : PowerSeries K :=
  quotientCoordinateExpansion - 1

@[simp]
theorem constantCoeff_denominator :
    PowerSeries.constantCoeff (denominator (K := K)) = 1 := by
  simp [denominator]

theorem denominator_ne_zero : denominator (K := K) ≠ 0 := by
  intro h
  have hzero : (1 : K) = 0 := by
    rw [← constantCoeff_denominator (K := K), h]
    exact map_zero PowerSeries.constantCoeff
  exact one_ne_zero hzero

/-- The formal-series version of the exact rational identity
`W - 1 = -7t / (1 + t - t²)`. -/
theorem quotientParameterExpansion_eq :
    quotientParameterExpansion (K := K) =
      (-7 : K) • (PowerSeries.X * denominator⁻¹) := by
  rw [quotientParameterExpansion, quotientCoordinateExpansion]
  have hinv : denominator (K := K) * denominator⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel denominator (by simp)
  have hdifference : numerator (K := K) - denominator =
      (-7 : K) • PowerSeries.X := by
    simp only [numerator, denominator]
    rw [← one_smul K PowerSeries.X]
    module
  calc
    numerator (K := K) * denominator⁻¹ - 1 =
        (numerator - denominator) * denominator⁻¹ := by
      rw [sub_mul, hinv, sub_eq_add_neg]
    _ = (-7 : K) • (PowerSeries.X * denominator⁻¹) := by
      rw [hdifference, smul_mul_assoc]

/-- The quotient parameter has zero constant coefficient. -/
@[simp]
theorem coeff_zero_quotientParameterExpansion :
    PowerSeries.coeff 0 (quotientParameterExpansion (K := K)) = 0 := by
  rw [quotientParameterExpansion_eq]
  simp

/-- The exact tangent coefficient of the level-35 quotient map at infinity. -/
@[simp]
theorem coeff_one_quotientParameterExpansion :
    PowerSeries.coeff 1 (quotientParameterExpansion (K := K)) = -7 := by
  rw [quotientParameterExpansion_eq]
  simp

/-- The local quotient parameter is nonzero whenever seven is nonzero in the
coefficient field. -/
theorem quotientParameterExpansion_ne_zero (hseven : (7 : K) ≠ 0) :
    quotientParameterExpansion (K := K) ≠ 0 := by
  intro h
  have hcoeff := congrArg (PowerSeries.coeff 1) h
  simp only [coeff_one_quotientParameterExpansion, map_zero] at hcoeff
  exact hseven (neg_eq_zero.mp hcoeff)

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- In the auxiliary residue field used by the order-35 argument, the
explicit tangent coefficient is `4`, hence nonzero. -/
theorem zmodEleven_coeff_one_quotientParameterExpansion_ne_zero :
    PowerSeries.coeff 1
        (quotientParameterExpansion (K := ZMod 11)) ≠ 0 := by
  rw [coeff_one_quotientParameterExpansion]
  decide

end FormalExpansion

end MazurTorsion.OrderThirtyFive.QuotientQExpansion
