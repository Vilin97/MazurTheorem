/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerDiagonalDeck

/-!
# The cyclic order of the five Lehmer cusps

The resolved infinity calculation supplies five cusp labels.  Three are
already distinguished by their unique Newton slopes; the two diagonal cusps
are distinguished by the successor calculation in the resolved deck chart.
This gives the cyclic cusp order

`root(0) → diagonal(-2) → root(-1) → parameter → diagonal(-1)`

up to rotation.  The final theorem proves this pattern for the five actual
Brunault roots of a hypothetical marked point of exact order twenty-five.
-/

namespace MazurTorsion.Kubert

/-- The five resolved points above infinity on Lehmer's plane model.  The
suffixes record the exceptional-fiber coordinate. -/
inductive OrderTwentyFiveLehmerInfinityCusp
  | rootZeroAtZero
  | diagonalAtNegTwo
  | rootZeroAtNegOne
  | parameterZero
  | diagonalAtNegOne

/-- The three-adic condition identifying a Lehmer root with one of the five
resolved infinity cusps.  The three unique slopes have already been tied to
their strict-transform charts; the repeated `-a` slope also records its
diagonal exceptional congruence. -/
def orderTwentyFiveLehmerAtInfinityCusp
    (cusp : OrderTwentyFiveLehmerInfinityCusp)
    (n x : ℚ) (a : ℤ) : Prop :=
  match cusp with
  | .rootZeroAtZero => padicValRat 3 x = 3 * a
  | .diagonalAtNegTwo =>
      padicValRat 3 x = -a ∧
        (x - n = -2 ∨ 0 < padicValRat 3 (x - n + 2))
  | .rootZeroAtNegOne => padicValRat 3 x = a
  | .parameterZero => padicValRat 3 x = -2 * a
  | .diagonalAtNegOne =>
      padicValRat 3 x = -a ∧
        (x - n = -1 ∨ 0 < padicValRat 3 (x - n + 1))

/-- Five cyclic roots occupy the five resolved infinity cusps in the standard
order, with an arbitrary choice of starting root. -/
def orderTwentyFiveLehmerInfinityCuspCycle
    (n x0 x1 x2 x3 x4 : ℚ) (a : ℤ) : Prop :=
  (orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtZero n x0 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegTwo n x1 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtNegOne n x2 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .parameterZero n x3 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegOne n x4 a) ∨
    (orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegOne n x0 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtZero n x1 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegTwo n x2 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtNegOne n x3 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .parameterZero n x4 a) ∨
    (orderTwentyFiveLehmerAtInfinityCusp .parameterZero n x0 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegOne n x1 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtZero n x2 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegTwo n x3 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtNegOne n x4 a) ∨
    (orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtNegOne n x0 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .parameterZero n x1 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegOne n x2 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtZero n x3 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegTwo n x4 a) ∨
    (orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegTwo n x0 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtNegOne n x1 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .parameterZero n x2 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .diagonalAtNegOne n x3 a ∧
      orderTwentyFiveLehmerAtInfinityCusp .rootZeroAtZero n x4 a)

private theorem diagonalAtNegTwo_of_successor_slope_one
    (n x y : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hx : padicValRat 3 x = -a) (hy : padicValRat 3 y = a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hxy : orderTwentyFiveLehmerDeckTransform n x = y) :
    x - n = -2 ∨ 0 < padicValRat 3 (x - n + 2) := by
  rcases orderTwentyFiveLehmer_negOneSlope_exceptionalBranch
    n x y a ha hn hx (Or.inl hy) hroot hxy with h | h
  · exact h.2
  · omega

private theorem diagonalAtNegOne_of_successor_slope_three
    (n x y : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hx : padicValRat 3 x = -a)
    (hy : padicValRat 3 y = 3 * a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hxy : orderTwentyFiveLehmerDeckTransform n x = y) :
    x - n = -1 ∨ 0 < padicValRat 3 (x - n + 1) := by
  rcases orderTwentyFiveLehmer_negOneSlope_exceptionalBranch
    n x y a ha hn hx (Or.inr hy) hroot hxy with h | h
  · omega
  · exact h.2

/-- The exact valuation cycle and the resolved local deck calculation refine
to the full five-cusp cycle. -/
theorem orderTwentyFiveLehmer_fiveCycle_threeAdicCuspPattern
    (n x0 x1 x2 x3 x4 : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hroot0 : orderTwentyFiveLehmerPolynomial n x0 = 0)
    (hroot1 : orderTwentyFiveLehmerPolynomial n x1 = 0)
    (hroot2 : orderTwentyFiveLehmerPolynomial n x2 = 0)
    (hroot3 : orderTwentyFiveLehmerPolynomial n x3 = 0)
    (hroot4 : orderTwentyFiveLehmerPolynomial n x4 = 0)
    (h01 : orderTwentyFiveLehmerDeckTransform n x0 = x1)
    (h12 : orderTwentyFiveLehmerDeckTransform n x1 = x2)
    (h23 : orderTwentyFiveLehmerDeckTransform n x2 = x3)
    (h34 : orderTwentyFiveLehmerDeckTransform n x3 = x4)
    (h40 : orderTwentyFiveLehmerDeckTransform n x4 = x0)
    (hpattern :
      (padicValRat 3 x0 = 3 * a ∧ padicValRat 3 x1 = -a ∧
          padicValRat 3 x2 = a ∧ padicValRat 3 x3 = -2 * a ∧
          padicValRat 3 x4 = -a) ∨
        (padicValRat 3 x0 = -a ∧ padicValRat 3 x1 = 3 * a ∧
          padicValRat 3 x2 = -a ∧ padicValRat 3 x3 = a ∧
          padicValRat 3 x4 = -2 * a) ∨
        (padicValRat 3 x0 = -2 * a ∧ padicValRat 3 x1 = -a ∧
          padicValRat 3 x2 = 3 * a ∧ padicValRat 3 x3 = -a ∧
          padicValRat 3 x4 = a) ∨
        (padicValRat 3 x0 = a ∧ padicValRat 3 x1 = -2 * a ∧
          padicValRat 3 x2 = -a ∧ padicValRat 3 x3 = 3 * a ∧
          padicValRat 3 x4 = -a) ∨
        (padicValRat 3 x0 = -a ∧ padicValRat 3 x1 = a ∧
          padicValRat 3 x2 = -2 * a ∧ padicValRat 3 x3 = -a ∧
          padicValRat 3 x4 = 3 * a)) :
    orderTwentyFiveLehmerInfinityCuspCycle n x0 x1 x2 x3 x4 a := by
  rcases hpattern with h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2, h3, h4⟩
  · left
    simp only [orderTwentyFiveLehmerAtInfinityCusp]
    exact ⟨h0,
      ⟨h1, diagonalAtNegTwo_of_successor_slope_one
        n x1 x2 a ha hn h1 h2 hroot1 h12⟩,
      h2, h3,
      ⟨h4, diagonalAtNegOne_of_successor_slope_three
        n x4 x0 a ha hn h4 h0 hroot4 h40⟩⟩
  · right; left
    simp only [orderTwentyFiveLehmerAtInfinityCusp]
    exact ⟨⟨h0, diagonalAtNegOne_of_successor_slope_three
        n x0 x1 a ha hn h0 h1 hroot0 h01⟩,
      h1,
      ⟨h2, diagonalAtNegTwo_of_successor_slope_one
        n x2 x3 a ha hn h2 h3 hroot2 h23⟩,
      h3, h4⟩
  · right; right; left
    simp only [orderTwentyFiveLehmerAtInfinityCusp]
    exact ⟨h0,
      ⟨h1, diagonalAtNegOne_of_successor_slope_three
        n x1 x2 a ha hn h1 h2 hroot1 h12⟩,
      h2,
      ⟨h3, diagonalAtNegTwo_of_successor_slope_one
        n x3 x4 a ha hn h3 h4 hroot3 h34⟩,
      h4⟩
  · right; right; right; left
    simp only [orderTwentyFiveLehmerAtInfinityCusp]
    exact ⟨h0, h1,
      ⟨h2, diagonalAtNegOne_of_successor_slope_three
        n x2 x3 a ha hn h2 h3 hroot2 h23⟩,
      h3,
      ⟨h4, diagonalAtNegTwo_of_successor_slope_one
        n x4 x0 a ha hn h4 h0 hroot4 h40⟩⟩
  · right; right; right; right
    simp only [orderTwentyFiveLehmerAtInfinityCusp]
    exact ⟨⟨h0, diagonalAtNegTwo_of_successor_slope_one
        n x0 x1 a ha hn h0 h1 hroot0 h01⟩,
      h1, h2,
      ⟨h3, diagonalAtNegOne_of_successor_slope_three
        n x3 x4 a ha hn h3 h4 hroot3 h34⟩,
      h4⟩

/-- A hypothetical marked point of exact order twenty-five specializes its
five actual Brunault roots to the five resolved infinity cusps in the exact
cyclic order, up to rotation. -/
theorem orderTwentyFive_threeAdicInfinityCuspCycle_of_marked_order
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
        orderTwentyFiveLehmerInfinityCuspCycle N
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c) a := by
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
      hreciprocal, a, ha, hval, hpattern⟩ :=
    orderTwentyFive_exactThreeAdicRootValuationCycle_of_marked_order
      b c hb h00 horder
  let N : ℚ := -orderTwentyFiveFifthPowerHauptmodul
    ((m : ℚ) / (n : ℚ))
  let r0 := orderTwentyFiveBrunaultXZero b c
  let r1 := orderTwentyFiveBrunaultXOne b c
  let r2 := orderTwentyFiveBrunaultXTwo b c
  let r3 := orderTwentyFiveBrunaultXThree b c
  let r4 := orderTwentyFiveBrunaultXFour b c
  have hN : N = orderTwentyFiveOrbitParameter r0 r1 r2 r3 r4 := by
    dsimp only [N, r0, r1, r2, r3, r4]
    linarith
  have hNv : padicValRat 3 N = -a := by
    dsimp only [N]
    exact orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation
      ((m : ℚ) / (n : ℚ)) a ha hval
  have hor0 := orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
    b c hb h00 horder
  have hor1 := orderTwentyFiveOrbitRelationOne_eq_zero_of_marked_order
    b c hb h00 horder
  have hor2 := orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
    b c hb h00 horder
  have hor3 := orderTwentyFiveOrbitRelationThree_eq_zero_of_marked_order
    b c hb h00 horder
  have hor4 := orderTwentyFiveOrbitRelationFour_eq_zero_of_marked_order
    b c hb h00 horder
  have hor5 := orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
    b c hb h00 horder
  have hxOne : r0 ≠ 1 := by
    dsimp only [r0]
    rw [orderTwentyFiveBrunaultXZero_eq_U]
    exact orderTwentyFiveBrunaultU_ne_one_of_marked_order
      b c hb h00 horder
  have hroot0 : orderTwentyFiveLehmerPolynomial N r0 = 0 := by
    rw [hN]
    exact (orderTwentyFiveLehmer_selectedRoots_of_orbit
      r0 r1 r2 r3 r4 hxOne hor0 hor1 hor2 hor3 hor4 hor5).1
  have hcycle := orderTwentyFiveLehmerDeckTransform_cycle_of_orbit
    r0 r1 r2 r3 r4 hxOne hor0 hor1 hor2 hor3 hor4 hor5
  dsimp only at hcycle
  rw [← hN] at hcycle
  obtain ⟨h01, h12, h23, h34, h40⟩ := hcycle
  have hroot1 : orderTwentyFiveLehmerPolynomial N r1 = 0 := by
    rw [← h01]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r0 hroot0
  have hroot2 : orderTwentyFiveLehmerPolynomial N r2 = 0 := by
    rw [← h12]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r1 hroot1
  have hroot3 : orderTwentyFiveLehmerPolynomial N r3 = 0 := by
    rw [← h23]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r2 hroot2
  have hroot4 : orderTwentyFiveLehmerPolynomial N r4 = 0 := by
    rw [← h34]
    exact orderTwentyFiveLehmerDeckTransform_isRoot N r3 hroot3
  have hcuspCycle :=
    orderTwentyFiveLehmer_fiveCycle_threeAdicCuspPattern
      N r0 r1 r2 r3 r4 a ha hNv
      hroot0 hroot1 hroot2 hroot3 hroot4 h01 h12 h23 h34 h40 (by
        simpa only [r0, r1, r2, r3, r4] using hpattern)
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
    hreciprocal, a, ha, hval, ?_⟩
  simpa only [N, r0, r1, r2, r3, r4] using hcuspCycle

end MazurTorsion.Kubert
