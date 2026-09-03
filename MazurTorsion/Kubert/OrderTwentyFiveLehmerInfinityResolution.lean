/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerInfinity

/-!
# Resolving the infinity points of Lehmer's order-twenty-five curve

The sextic Lehmer plane model has three points at infinity.  This file gives
explicit local strict transforms at all three:

* above `[0 : 1 : 0]`, two successive blowups have exceptional coordinates
  `0` and `-1`;
* above `[1 : 1 : 0]`, one blowup has exceptional coordinates `-1` and `-2`;
* at `[1 : 0 : 0]`, the transverse linear coefficient is a unit.

Thus the three singular directions separate into two, two, and one smooth
branches, accounting algebraically for the five points above infinity on the
normalization.
-/

namespace MazurTorsion.Kubert

/-- The strict-transform equation after the substitutions `N = 1` and
`X = Z²U`, which encode two successive blowups above `[0 : 1 : 0]`. -/
def orderTwentyFiveLehmerRootZeroSecondStrictTransform
    {R : Type*} [CommRing R] (u z : R) : R :=
  u ^ 5 * z ^ 7 - u ^ 4 * z ^ 4 - 10 * u ^ 3 * z ^ 5 +
    10 * u ^ 3 * z ^ 4 - 6 * u ^ 3 * z ^ 3 + 2 * u ^ 3 * z ^ 2 -
    5 * u ^ 2 * z ^ 4 + 15 * u ^ 2 * z ^ 3 - 11 * u ^ 2 * z ^ 2 +
    5 * u ^ 2 * z - u ^ 2 + 10 * u * z ^ 3 - 10 * u * z ^ 2 +
    4 * u * z - u - z ^ 2

/-- Substituting `X = Z²U` into the root-zero chart extracts exactly the
fourth power of the exceptional parameter. -/
theorem orderTwentyFiveLehmer_rootZeroSecondStrictTransform_identity
    {R : Type*} [CommRing R] (u z : R) :
    orderTwentyFiveLehmerHomogeneousPolynomial 1 (z ^ 2 * u) z =
      z ^ 4 * orderTwentyFiveLehmerRootZeroSecondStrictTransform u z := by
  simp only [orderTwentyFiveLehmerHomogeneousPolynomial,
    orderTwentyFiveLehmerRootZeroSecondStrictTransform]
  ring

/-- The second exceptional fiber above `[0 : 1 : 0]` consists exactly of
the two points `U = 0` and `U = -1`. -/
theorem orderTwentyFiveLehmer_rootZero_exceptionalFiber
    {K : Type*} [Field K] (u : K) :
    orderTwentyFiveLehmerRootZeroSecondStrictTransform u 0 = 0 ↔
      u = 0 ∨ u = -1 := by
  have hfac :
      orderTwentyFiveLehmerRootZeroSecondStrictTransform u 0 =
        -(u * (u + 1)) := by
    simp only [orderTwentyFiveLehmerRootZeroSecondStrictTransform]
    ring
  rw [hfac, neg_eq_zero, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · rintro (h | h)
    · exact Or.inl h
    · right
      rw [h]
      simp

/-- The strict-transform equation after the substitutions `N = 1` and
`X = 1 + ZU`, the first blowup above `[1 : 1 : 0]`. -/
def orderTwentyFiveLehmerDiagonalStrictTransform
    {R : Type*} [CommRing R] (u z : R) : R :=
  u ^ 5 * z ^ 4 + 5 * u ^ 4 * z ^ 3 - u ^ 4 * z ^ 2 -
    10 * u ^ 3 * z ^ 4 + 10 * u ^ 3 * z ^ 3 + 4 * u ^ 3 * z ^ 2 -
    2 * u ^ 3 * z - 5 * u ^ 2 * z ^ 4 - 15 * u ^ 2 * z ^ 3 +
    19 * u ^ 2 * z ^ 2 - 3 * u ^ 2 * z - u ^ 2 +
    10 * u * z ^ 4 - 20 * u * z ^ 3 + 4 * u * z ^ 2 + 7 * u * z -
    3 * u - z ^ 4 + 10 * z ^ 3 - 15 * z ^ 2 + 9 * z - 2

/-- Substituting `X = 1 + ZU` into the diagonal chart extracts exactly the
square of the exceptional parameter. -/
theorem orderTwentyFiveLehmer_diagonalStrictTransform_identity
    {R : Type*} [CommRing R] (u z : R) :
    orderTwentyFiveLehmerHomogeneousPolynomial 1 (1 + z * u) z =
      z ^ 2 * orderTwentyFiveLehmerDiagonalStrictTransform u z := by
  simp only [orderTwentyFiveLehmerHomogeneousPolynomial,
    orderTwentyFiveLehmerDiagonalStrictTransform]
  ring

/-- The exceptional fiber above `[1 : 1 : 0]` consists exactly of the two
points `U = -1` and `U = -2`. -/
theorem orderTwentyFiveLehmer_diagonal_exceptionalFiber
    {K : Type*} [Field K] (u : K) :
    orderTwentyFiveLehmerDiagonalStrictTransform u 0 = 0 ↔
      u = -1 ∨ u = -2 := by
  have hvalue : orderTwentyFiveLehmerDiagonalStrictTransform u 0 =
      -u ^ 2 - 3 * u - 2 := by
    simp [orderTwentyFiveLehmerDiagonalStrictTransform]
  rw [hvalue]
  constructor
  · intro h
    have hfac : -(u + 1) * (u + 2) = 0 := by
      calc
        -(u + 1) * (u + 2) = -u ^ 2 - 3 * u - 2 := by ring
        _ = 0 := h
    rcases mul_eq_zero.mp hfac with hleft | hright
    · left
      have : u + 1 = 0 := by
        simpa only [neg_mul, neg_eq_zero] using hleft
      exact eq_neg_of_add_eq_zero_left this
    · right
      exact eq_neg_of_add_eq_zero_left hright
  · rintro (rfl | rfl) <;> ring

/-- The factor multiplying the transverse coordinate on the line `N = 0`
through `[1 : 0 : 0]`. -/
def orderTwentyFiveLehmerParameterZeroTransverseFactor
    {R : Type*} [CommRing R] (z : R) : R :=
  1 - 10 * z ^ 2 - 5 * z ^ 3 + 10 * z ^ 4 - z ^ 5

/-- On `N = 0`, the parameter-zero chart equation is `Z` times a factor
whose value at the infinity point is one. -/
theorem orderTwentyFiveLehmer_parameterZero_transverse_identity
    {R : Type*} [CommRing R] (z : R) :
    orderTwentyFiveLehmerHomogeneousPolynomial 0 1 z =
      z * orderTwentyFiveLehmerParameterZeroTransverseFactor z := by
  simp only [orderTwentyFiveLehmerHomogeneousPolynomial,
    orderTwentyFiveLehmerParameterZeroTransverseFactor]
  ring

/-- The transverse factor at `[1 : 0 : 0]` is a unit, certifying that this
infinity point contributes one smooth branch. -/
theorem orderTwentyFiveLehmer_parameterZero_transverse_at_origin
    {R : Type*} [CommRing R] :
    orderTwentyFiveLehmerParameterZeroTransverseFactor (0 : R) = 1 := by
  simp [orderTwentyFiveLehmerParameterZeroTransverseFactor]

/-- The explicit exceptional fibers separate the three plane directions at
infinity into two root-zero branches, two diagonal branches, and one smooth
parameter-zero branch. -/
theorem orderTwentyFiveLehmer_resolvedInfinityFibers
    {K : Type*} [Field K] :
    (∀ u : K,
        orderTwentyFiveLehmerRootZeroSecondStrictTransform u 0 = 0 ↔
          u = 0 ∨ u = -1) ∧
      (∀ u : K,
        orderTwentyFiveLehmerDiagonalStrictTransform u 0 = 0 ↔
          u = -1 ∨ u = -2) ∧
      orderTwentyFiveLehmerParameterZeroTransverseFactor (0 : K) = 1 := by
  exact ⟨orderTwentyFiveLehmer_rootZero_exceptionalFiber,
    orderTwentyFiveLehmer_diagonal_exceptionalFiber,
    orderTwentyFiveLehmer_parameterZero_transverse_at_origin⟩

end MazurTorsion.Kubert
