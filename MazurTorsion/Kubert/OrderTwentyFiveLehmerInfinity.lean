/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerThreeAdicCycle

/-!
# The projective infinity locus of Lehmer's order-twenty-five curve

This file homogenizes Lehmer's two-variable quintic to total degree six in
coordinates `[X : N : Z]`.  On the line `Z = 0`, its equation factors as

`-N² X² (X - N)²`.

Consequently its nonzero geometric points at infinity have exactly the three
directions `[0 : 1 : 0]`, `[1 : 1 : 0]`, and `[1 : 0 : 0]`.  The final
theorem consumes the checked three-adic root certificate for an actual marked
point of order twenty-five and assigns each of its five cyclic branches to
one of these directions.
-/

namespace MazurTorsion.Kubert

/-- The total-degree-six homogenization of Lehmer's polynomial, with
coordinate order `(N, X, Z)` corresponding to projective coordinates
`[X : N : Z]`. -/
def orderTwentyFiveLehmerHomogeneousPolynomial
    {R : Type*} [CommRing R] (n x z : R) : R :=
  x ^ 5 * z - n ^ 2 * x ^ 4 +
    2 * (n ^ 3 - 3 * n ^ 2 * z + 5 * n * z ^ 2 - 5 * z ^ 3) * x ^ 3 -
    (n ^ 4 - 5 * n ^ 3 * z + 11 * n ^ 2 * z ^ 2 -
      15 * n * z ^ 3 + 5 * z ^ 4) * x ^ 2 +
    (-n ^ 3 * z ^ 2 + 4 * n ^ 2 * z ^ 3 -
      10 * n * z ^ 4 + 10 * z ^ 5) * x - z ^ 6

/-- The affine chart `Z = 1` of the homogenization is Lehmer's original
polynomial. -/
theorem orderTwentyFiveLehmerHomogeneousPolynomial_affine
    {R : Type*} [CommRing R] (n x : R) :
    orderTwentyFiveLehmerHomogeneousPolynomial n x 1 =
      orderTwentyFiveLehmerPolynomial n x := by
  simp only [orderTwentyFiveLehmerHomogeneousPolynomial,
    orderTwentyFiveLehmerPolynomial]
  ring

/-- On the line at infinity, Lehmer's plane equation is the product of three
square linear factors. -/
theorem orderTwentyFiveLehmerHomogeneousPolynomial_at_infinity
    {R : Type*} [CommRing R] (n x : R) :
    orderTwentyFiveLehmerHomogeneousPolynomial n x 0 =
      -(n ^ 2 * x ^ 2 * (x - n) ^ 2) := by
  simp only [orderTwentyFiveLehmerHomogeneousPolynomial]
  ring

/-- Over a field, the affine cone over the line-at-infinity locus is exactly
the union `X = 0`, `N = 0`, and `X = N`. -/
theorem orderTwentyFiveLehmer_projectiveInfinity_locus
    {K : Type*} [Field K] (n x : K) :
    orderTwentyFiveLehmerHomogeneousPolynomial n x 0 = 0 ↔
      x = 0 ∨ n = 0 ∨ x = n := by
  rw [orderTwentyFiveLehmerHomogeneousPolynomial_at_infinity]
  constructor
  · intro h
    have hprod : n ^ 2 * x ^ 2 * (x - n) ^ 2 = 0 := neg_eq_zero.mp h
    rcases mul_eq_zero.mp hprod with hnx | hsub
    · rcases mul_eq_zero.mp hnx with hn | hx
      · exact Or.inr (Or.inl (sq_eq_zero_iff.mp hn))
      · exact Or.inl (sq_eq_zero_iff.mp hx)
    · exact Or.inr (Or.inr (sub_eq_zero.mp (sq_eq_zero_iff.mp hsub)))
  · rintro (hx | hn | hxn)
    · simp [hx]
    · simp [hn]
    · simp [hxn]

/-- Removing the cone origin turns the infinity locus into precisely the
three projective directions `[0 : 1 : 0]`, `[1 : 0 : 0]`, and
`[1 : 1 : 0]`. -/
theorem orderTwentyFiveLehmer_projectiveInfinity_directions
    {K : Type*} [Field K] (n x : K)
    (hnx : n ≠ 0 ∨ x ≠ 0)
    (h : orderTwentyFiveLehmerHomogeneousPolynomial n x 0 = 0) :
    (x = 0 ∧ n ≠ 0) ∨ (n = 0 ∧ x ≠ 0) ∨
      (x = n ∧ n ≠ 0) := by
  rcases (orderTwentyFiveLehmer_projectiveInfinity_locus n x).mp h with
    hx | hn | hxn
  · left
    refine ⟨hx, ?_⟩
    rcases hnx with hn0 | hx0
    · exact hn0
    · exact False.elim (hx0 hx)
  · right; left
    refine ⟨hn, ?_⟩
    rcases hnx with hn0 | hx0
    · exact False.elim (hn0 hn)
    · exact hx0
  · right; right
    refine ⟨hxn, ?_⟩
    rcases hnx with hn0 | hx0
    · exact hn0
    · intro hn
      apply hx0
      exact hxn.trans hn

/-- A three-adic Lehmer branch together with its corresponding point on the
projective line-at-infinity locus.  The positive slopes target
`[0 : 1 : 0]`, slope `-a` targets `[1 : 1 : 0]`, and slope `-2a` targets
`[1 : 0 : 0]`. -/
def orderTwentyFiveLehmerThreeAdicInfinityBranch
    (n x : ℚ) (a : ℤ) : Prop :=
  ((((padicValRat 3 x = 3 * a ∧
          padicValRat 3 (x / n) = 4 * a) ∨
        (padicValRat 3 x = a ∧
          padicValRat 3 (x / n) = 2 * a)) ∧
      orderTwentyFiveLehmerHomogeneousPolynomial (1 : ℚ) 0 0 = 0) ∨
    ((padicValRat 3 x = -a ∧
          (x = n ∨ 0 < padicValRat 3 (x / n - 1))) ∧
      orderTwentyFiveLehmerHomogeneousPolynomial (1 : ℚ) 1 0 = 0) ∨
    ((padicValRat 3 x = -2 * a ∧
          padicValRat 3 (n / x) = a) ∧
      orderTwentyFiveLehmerHomogeneousPolynomial (0 : ℚ) 1 0 = 0))

/-- Each alternative in the exact three-adic chart certificate lands at its
claimed point of the projective infinity locus. -/
theorem orderTwentyFiveLehmer_threeAdicChart_isInfinityBranch
    (n x : ℚ) (a : ℤ)
    (hchart :
      (padicValRat 3 x = 3 * a ∧
          padicValRat 3 (x / n) = 4 * a) ∨
        (padicValRat 3 x = a ∧
          padicValRat 3 (x / n) = 2 * a) ∨
        (padicValRat 3 x = -a ∧
          (x = n ∨ 0 < padicValRat 3 (x / n - 1))) ∨
        (padicValRat 3 x = -2 * a ∧
          padicValRat 3 (n / x) = a)) :
    orderTwentyFiveLehmerThreeAdicInfinityBranch n x a := by
  rcases hchart with h | h | h | h
  · left
    exact ⟨Or.inl h,
      (orderTwentyFiveLehmer_projectiveInfinity_locus
        (1 : ℚ) 0).2 (Or.inl rfl)⟩
  · left
    exact ⟨Or.inr h,
      (orderTwentyFiveLehmer_projectiveInfinity_locus
        (1 : ℚ) 0).2 (Or.inl rfl)⟩
  · right; left
    exact ⟨h, (orderTwentyFiveLehmer_projectiveInfinity_locus
      (1 : ℚ) 1).2 (Or.inr (Or.inr rfl))⟩
  · right; right
    exact ⟨h, (orderTwentyFiveLehmer_projectiveInfinity_locus
      (0 : ℚ) 1).2 (Or.inr (Or.inl rfl))⟩

/-- Every one of the five actual cyclic Brunault branches attached to a
hypothetical marked point of order twenty-five lands at one of the three
projective infinity points of Lehmer's plane curve. -/
theorem orderTwentyFive_threeAdicInfinityBranches_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ IsCoprime m n ∧
      (m : ZMod 3) = 0 ∧ (n : ZMod 3) ≠ 0 ∧
      -(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c)) =
        orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ)) ∧
      orderTwentyFiveRatIsThreeIntegral
        (-5 / orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ))) ∧
      ∃ a : ℤ, 0 < a ∧
        padicValRat 3 ((m : ℚ) / (n : ℚ)) = a ∧
        let N := -orderTwentyFiveFifthPowerHauptmodul
          ((m : ℚ) / (n : ℚ))
        ∀ x ∈ [orderTwentyFiveBrunaultXZero b c,
            orderTwentyFiveBrunaultXOne b c,
            orderTwentyFiveBrunaultXTwo b c,
            orderTwentyFiveBrunaultXThree b c,
            orderTwentyFiveBrunaultXFour b c],
          orderTwentyFiveLehmerThreeAdicInfinityBranch N x a := by
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
      hreciprocal, a, ha, hval, -, hcharts⟩ :=
    orderTwentyFive_threeAdicCuspCongruences_of_marked_order
      b c hb h00 horder
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
    hreciprocal, a, ha, hval, ?_⟩
  dsimp only
  intro x hx
  exact orderTwentyFiveLehmer_threeAdicChart_isInfinityBranch
    _ _ _ (hcharts x hx)

end MazurTorsion.Kubert
