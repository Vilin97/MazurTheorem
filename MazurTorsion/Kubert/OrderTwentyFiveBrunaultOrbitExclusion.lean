/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultIntegrality
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Arithmetic exclusion for a Lécacheux order-twenty-five orbit

This file composes the characteristic-zero orbit certificate with the
three-adic Lehmer-root exclusion.  The cyclic-orbit and three-integrality
hypotheses remain explicit: deriving them from an actual marked elliptic curve
is the remaining geometric and integral-model bridge.

It also recovers Lécacheux's `n`-parameter from the five orbit coordinates.
The orbit equations then force the two selected coordinates to be roots of
Lehmer's quintic, so downstream exclusion no longer needs those root
conditions as separate hypotheses.
-/

namespace MazurTorsion.Kubert

/-- Lécacheux's invariant parameter recovered from a cyclic five-term
orbit.  The formula is `n = 1 - (R + Q - S) / 5`, where `S` is the sum of
the orbit, `R` is the cyclic adjacent-pair sum, and `Q` is the sum of the
fourfold products (the reciprocal sum when the orbit has norm one). -/
def orderTwentyFiveOrbitParameter (a b c d e : ℚ) : ℚ :=
  1 - ((a * b + b * c + c * d + d * e + e * a) +
      (a * b * c * d + a * b * c * e + a * b * d * e +
        a * c * d * e + b * c * d * e) -
      (a + b + c + d + e)) / 5

/-- The denominator in Lécacheux's two-consecutive-root recovery formula
for the invariant parameter. -/
def orderTwentyFiveOrbitPairDenominator (a b : ℚ) : ℚ :=
  1 - a - a * b

/-- Lécacheux's invariant parameter recovered from the first two
consecutive roots of the cyclic orbit. -/
def orderTwentyFiveOrbitPairParameter (a b : ℚ) : ℚ :=
  (2 - 2 * a * b - a ^ 2 + b) /
    orderTwentyFiveOrbitPairDenominator a b

private noncomputable def orderTwentyFiveOrbitPairExceptionalPolynomial :
    Polynomial ℤ :=
  Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 + Polynomial.X - 1

private theorem orderTwentyFiveOrbitPairExceptionalPolynomial_monic :
    orderTwentyFiveOrbitPairExceptionalPolynomial.Monic := by
  unfold orderTwentyFiveOrbitPairExceptionalPolynomial
  monicity!

private theorem orderTwentyFiveOrbitPairExceptionalPolynomial_ne_zero
    (a : ℚ) :
    a ^ 3 - 2 * a ^ 2 + a - 1 ≠ 0 := by
  intro ha
  have hroot :
      Polynomial.aeval a orderTwentyFiveOrbitPairExceptionalPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderTwentyFiveOrbitPairExceptionalPolynomial]
    linear_combination ha
  obtain ⟨z, haz, hdiv⟩ :=
    exists_integer_of_is_root_of_monic
      orderTwentyFiveOrbitPairExceptionalPolynomial_monic hroot
  have hunit : IsUnit z := by
    rw [isUnit_iff_dvd_one]
    simpa [orderTwentyFiveOrbitPairExceptionalPolynomial] using hdiv
  rcases Int.isUnit_iff.mp hunit with rfl | rfl
  · norm_num [haz] at ha
  · norm_num [haz] at ha

/-- The two-root recovery formula has no rational pole on a complete
Lécacheux orbit. At a putative pole, the cyclic equations force the first
root to satisfy a monic cubic with constant coefficient `-1`; the rational
root theorem excludes both possible integral roots. -/
theorem orderTwentyFiveOrbitPairDenominator_ne_zero
    (a b c d e : ℚ)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveOrbitPairDenominator a b ≠ 0 := by
  intro hden
  have hcubic : a ^ 3 - 2 * a ^ 2 + a - 1 = 0 := by
    simp only [orderTwentyFiveOrbitPairDenominator,
      orderTwentyFiveOrbitRelationZero,
      orderTwentyFiveOrbitRelationOne,
      orderTwentyFiveOrbitRelationTwo,
      orderTwentyFiveOrbitRelationThree,
      orderTwentyFiveOrbitRelationFour,
      orderTwentyFiveOrbitRelationFive] at hden h0 h1 h2 h3 h4 h5
    grobner
  exact orderTwentyFiveOrbitPairExceptionalPolynomial_ne_zero a hcubic

/-- On a complete Lécacheux orbit, the symmetric five-root definition of
the invariant agrees with its substantially smaller two-consecutive-root
formula. -/
theorem orderTwentyFiveOrbitParameter_eq_pairParameter
    (a b c d e : ℚ)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveOrbitParameter a b c d e =
      orderTwentyFiveOrbitPairParameter a b := by
  have hden := orderTwentyFiveOrbitPairDenominator_ne_zero
    a b c d e h0 h1 h2 h3 h4 h5
  rw [orderTwentyFiveOrbitPairParameter, eq_div_iff hden]
  simp only [orderTwentyFiveOrbitParameter,
    orderTwentyFiveOrbitPairDenominator,
    orderTwentyFiveOrbitRelationZero,
    orderTwentyFiveOrbitRelationOne,
    orderTwentyFiveOrbitRelationTwo,
    orderTwentyFiveOrbitRelationThree,
    orderTwentyFiveOrbitRelationFour,
    orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5 ⊢
  grobner

private def orderTwentyFiveOrbitInvariantRelation
    (n a b c d e : ℚ) : ℚ :=
  5 * (n - 1) + (a * b + b * c + c * d + d * e + e * a) +
    (a * b * c * d + a * b * c * e + a * b * d * e +
      a * c * d * e + b * c * d * e) -
    (a + b + c + d + e)

private theorem orderTwentyFiveLehmer_selectedRoots_of_invariantRelation
    (n a b c d e : ℚ) (ha : a ≠ 1)
    (hn : orderTwentyFiveOrbitInvariantRelation n a b c d e = 0)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveLehmerPolynomial n a = 0 ∧
      orderTwentyFiveLehmerPolynomial n c = 0 := by
  simp only [orderTwentyFiveOrbitInvariantRelation] at hn
  simp only [orderTwentyFiveOrbitRelationZero,
    orderTwentyFiveOrbitRelationOne, orderTwentyFiveOrbitRelationTwo,
    orderTwentyFiveOrbitRelationThree, orderTwentyFiveOrbitRelationFour,
    orderTwentyFiveOrbitRelationFive] at h0 h1 h2 h3 h4 h5
  have hsumProduct :
      (a - 1) * (a + b + c + d + e - n ^ 2) = 0 := by
    clear ha
    grobner
  have hsum : a + b + c + d + e = n ^ 2 := by
    exact sub_eq_zero.mp <|
      (mul_eq_zero.mp hsumProduct).resolve_left (sub_ne_zero.mpr ha)
  have hpairs :
      a * b + a * c + a * d + a * e + b * c + b * d + b * e +
          c * d + c * e + d * e =
        2 * (n ^ 3 - 3 * n ^ 2 + 5 * n - 5) := by
    clear ha
    grobner
  have htriples :
      a * b * c + a * b * d + a * b * e + a * c * d + a * c * e +
          a * d * e + b * c * d + b * c * e + b * d * e + c * d * e =
        n ^ 4 - 5 * n ^ 3 + 11 * n ^ 2 - 15 * n + 5 := by
    clear ha
    grobner
  have hquadruples :
      a * b * c * d + a * b * c * e + a * b * d * e +
          a * c * d * e + b * c * d * e =
        -n ^ 3 + 4 * n ^ 2 - 10 * n + 10 := by
    clear ha
    grobner
  have hproduct : a * b * c * d * e = 1 :=
    sub_eq_zero.mp h5
  constructor
  · simp only [orderTwentyFiveLehmerPolynomial]
    rw [← hpairs, ← htriples, ← hquadruples, ← hsum,
      ← hproduct]
    ring
  · simp only [orderTwentyFiveLehmerPolynomial]
    rw [← hpairs, ← htriples, ← hquadruples, ← hsum,
      ← hproduct]
    ring

/-- The six cyclic orbit equations and the nonexceptional condition recover
the two Lehmer-root facts needed by the three-adic Brunault exclusion. -/
theorem orderTwentyFiveLehmer_selectedRoots_of_orbit
    (a b c d e : ℚ) (ha : a ≠ 1)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveLehmerPolynomial
          (orderTwentyFiveOrbitParameter a b c d e) a = 0 ∧
      orderTwentyFiveLehmerPolynomial
          (orderTwentyFiveOrbitParameter a b c d e) c = 0 := by
  apply orderTwentyFiveLehmer_selectedRoots_of_invariantRelation
    (orderTwentyFiveOrbitParameter a b c d e) a b c d e ha
  · simp [orderTwentyFiveOrbitInvariantRelation,
      orderTwentyFiveOrbitParameter]
    ring
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- A five-term Lécacheux orbit cannot simultaneously satisfy its six cyclic
relations and arise from two Lehmer roots at a three-integral parameter.

The orbit relations force Brunault's polynomial to vanish at `(a, -c)`,
whereas the Lehmer-root integrality theorem and the checked `F₃` enumeration
force the same value to be nonzero. -/
theorem no_orderTwentyFiveBrunaultOrbit_of_threeIntegral_lehmerRoots
    (n a b c d e : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n)
    (ha : a ≠ 1)
    (haRoot : orderTwentyFiveLehmerPolynomial n a = 0)
    (hcRoot : orderTwentyFiveLehmerPolynomial n c = 0)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    False := by
  exact
    orderTwentyFiveBrunaultPolynomial_ne_zero_of_lehmer_roots
      n a c hn haRoot hcRoot
      (orderTwentyFiveBrunaultPolynomial_eq_zero_of_orbit
        a b c d e ha h0 h1 h2 h3 h4 h5)

/-- A nonexceptional Lécacheux orbit whose recovered invariant is integral
at three cannot satisfy the six cyclic orbit equations.  Compared with
`no_orderTwentyFiveBrunaultOrbit_of_threeIntegral_lehmerRoots`, the two
Lehmer-root hypotheses are now consequences rather than inputs. -/
theorem no_orderTwentyFiveBrunaultOrbit_of_threeIntegral
    (a b c d e : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveOrbitParameter a b c d e))
    (ha : a ≠ 1)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    False := by
  obtain ⟨haRoot, hcRoot⟩ :=
    orderTwentyFiveLehmer_selectedRoots_of_orbit
      a b c d e ha h0 h1 h2 h3 h4 h5
  exact no_orderTwentyFiveBrunaultOrbit_of_threeIntegral_lehmerRoots
    (orderTwentyFiveOrbitParameter a b c d e) a b c d e hn ha
    haRoot hcRoot h0 h1 h2 h3 h4 h5

/-- For a hypothetical nonexceptional rational Lécacheux orbit, the original
parameter is nonzero and cannot be integral at three, while its reciprocal
Fricke parameter `5 / n` must be integral at three.

This is only an arithmetic reduction.  It does not assert that the Fricke
parameter comes with a second rational orbit. -/
theorem orderTwentyFiveOrbitParameter_residual_integrality_of_orbit
    (a b c d e : ℚ)
    (ha : a ≠ 1)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveOrbitParameter a b c d e ≠ 0 ∧
      ¬orderTwentyFiveRatIsThreeIntegral
        (orderTwentyFiveOrbitParameter a b c d e) ∧
      orderTwentyFiveRatIsThreeIntegral
        (5 / orderTwentyFiveOrbitParameter a b c d e) := by
  let n := orderTwentyFiveOrbitParameter a b c d e
  have hnNotIntegral : ¬orderTwentyFiveRatIsThreeIntegral n := by
    intro hn
    exact no_orderTwentyFiveBrunaultOrbit_of_threeIntegral
      a b c d e hn ha h0 h1 h2 h3 h4 h5
  have hnZeroIntegral : orderTwentyFiveRatIsThreeIntegral (0 : ℚ) := by
    norm_num [orderTwentyFiveRatIsThreeIntegral]
  have hnZero : n ≠ 0 := by
    intro hn
    apply hnNotIntegral
    simpa only [hn] using hnZeroIntegral
  have hreciprocal : orderTwentyFiveRatIsThreeIntegral (5 / n) := by
    rcases orderTwentyFive_frickeParameter_three_integral n hnZero with hn | hn
    · exact (hnNotIntegral hn).elim
    · exact hn
  simpa only [n] using ⟨hnZero, hnNotIntegral, hreciprocal⟩

end MazurTorsion.Kubert
