/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel

/-!
# Pulling the `X₁(18)` two-descent representative back to the sextic

This file computes the `x - T` representative after the explicit
genus-two-to-elliptic quotient map.  The computation is deliberately kept
separate from the global two-descent: it exhibits the pullback as an explicit
quadratic family, without asserting a global squareclass obstruction.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientPullbackDescent

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenQuotientTwoDescentModel

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

/-- The numerator of the descent-model abscissa after pulling it back along
the explicit quotient map. -/
def pullbackAbscissaNumerator (x : ℚ) : K :=
  (3 * tau ^ 2 + 3 * tau + 1) * (x : K) ^ 2 -
    (3 * tau ^ 2 + 7 * tau + 3) * (x : K) +
      tau ^ 2 + 3 * tau + 3

/-- The quotient-to-descent change leaves the abscissa equal to the rational
model abscissa.  Its pullback has the displayed quadratic numerator and the
square denominator `(x + τ)²`. -/
theorem rationalModelX_quotientX_mul_den_sq (x : ℚ) :
    ((x : K) + tau) ^ 2 * rationalModelX (quotientX x) =
      pullbackAbscissaNumerator x := by
  unfold pullbackAbscissaNumerator rationalModelX quotientX quotientD
  field_simp [rational_add_tau_ne_zero x]
  ring_nf
  simp only [tau_pow_six, tau_pow_four, tau_cubic]
  ring

/-- The actual `x - T` representative in the relative two-division algebra.
No squareclass quotient is taken here, so the identity remains valid before
the separate proof that the relative algebra is a field. -/
def pullbackDescentRepresentative (x : ℚ) : M :=
  algebraMap K M (rationalModelX (quotientX x)) - descentRootInM

/-- The rational parameter embedded through the coefficient field. -/
def pullbackParameter (x : ℚ) : M :=
  algebraMap K M (x : K)

/-- The explicit quadratic factor left after removing the square
denominator from the pulled-back descent representative. -/
def pullbackQuadratic (x : ℚ) : M :=
  (s ^ 2 - 2 * s - 4 * t ^ 2 - 4 * t - 3) * pullbackParameter x ^ 2 +
    (2 * s ^ 2 * t - 4 * s * t + 4 * t ^ 2 + 6 * t + 4) *
      pullbackParameter x +
      (s ^ 2 * t ^ 2 - 2 * s * t ^ 2 - 3 * t ^ 2 - 4 * t - 4)

/-- Leading coefficient of the cleared pullback polynomial before
specializing the scaled two-division root. -/
def pullbackCoefficientA (z : M) : M :=
  12 * t ^ 2 + 12 * t - z + 4

/-- Linear coefficient of the cleared pullback polynomial. -/
def pullbackCoefficientB (z : M) : M :=
  -2 * (6 * t ^ 2 + t * z + 14 * t + 6)

/-- Constant coefficient of the cleared pullback polynomial. -/
def pullbackCoefficientC (z : M) : M :=
  -t ^ 2 * z + 4 * t ^ 2 + 12 * t + 12

/-- The cleared factor `-3 * pullbackQuadratic x` has the three explicit
coefficients obtained by specializing `z` to `relativeTwoDivisionZ`. -/
theorem neg_three_mul_pullbackQuadratic_eq_coefficients (x : ℚ) :
    -3 * pullbackQuadratic x =
      pullbackCoefficientA relativeTwoDivisionZ * pullbackParameter x ^ 2 +
        pullbackCoefficientB relativeTwoDivisionZ * pullbackParameter x +
          pullbackCoefficientC relativeTwoDivisionZ := by
  simp only [pullbackQuadratic, pullbackCoefficientA,
    pullbackCoefficientB, pullbackCoefficientC, relativeTwoDivisionZ]
  ring

/-- Discriminant certificate for the quadratic pullback family.  The only
reduction is the checked coefficient-field relation `t³ = 3t + 1`. -/
theorem pullback_coefficients_discriminant (z : M) :
    pullbackCoefficientB z ^ 2 -
        4 * pullbackCoefficientA z * pullbackCoefficientC z =
      144 * (t + 1) * (2 * t + 1) * (z - 1) := by
  simp only [pullbackCoefficientA, pullbackCoefficientB,
    pullbackCoefficientC]
  linear_combination 48 * (t + 2) * (z - 1) * t_cubic

/-- Exact pullback identity.  The factor `4 (x + t)²` is a square; what
remains is `-3` times the explicit quadratic family `pullbackQuadratic x`.
This is a rational-factor formula, not by itself a classification or a
squareclass obstruction. -/
theorem pullbackDescentRepresentative_cleared (x : ℚ) :
    4 * (pullbackParameter x + t) ^ 2 * pullbackDescentRepresentative x =
      -3 * pullbackQuadratic x := by
  have habs := congrArg (algebraMap K M)
    (rationalModelX_quotientX_mul_den_sq x)
  simp only [map_mul, map_pow, map_add] at habs
  change
    (pullbackParameter x + t) ^ 2 *
        algebraMap K M (rationalModelX (quotientX x)) =
      algebraMap K M (pullbackAbscissaNumerator x) at habs
  rw [pullbackDescentRepresentative, descentRootInM]
  simp only [relativeTwoDivisionZ, pullbackQuadratic]
  change
    4 * (pullbackParameter x + t) ^ 2 *
        (algebraMap K M (rationalModelX (quotientX x)) -
          algebraMap K M (1 / 4 : K) * (3 * s ^ 2 - 6 * s - 5)) = _
  have hquarter : (4 : M) * algebraMap K M (1 / 4 : K) = 1 := by
    rw [← map_ofNat (algebraMap K M) 4, ← map_mul]
    norm_num
  have ht : algebraMap K M tau = t := by
    rfl
  have hnum : algebraMap K M (pullbackAbscissaNumerator x) =
      (3 * t ^ 2 + 3 * t + 1) * pullbackParameter x ^ 2 -
        (3 * t ^ 2 + 7 * t + 3) * pullbackParameter x +
          t ^ 2 + 3 * t + 3 := by
    simp only [pullbackAbscissaNumerator, pullbackParameter,
      map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, ht]
  rw [hnum] at habs
  linear_combination 4 * habs +
    -(pullbackParameter x + t) ^ 2 *
      (3 * s ^ 2 - 6 * s - 5) * hquarter

end

end MazurTorsion.XOneEighteenQuotientPullbackDescent
