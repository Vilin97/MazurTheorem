/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerThreeAdicResolution

/-!
# Exceptional-fiber congruences for the Lehmer curve

The two strict transforms from the infinity resolution have the forms

* `-U(U+1) + Z R₀(U,Z)`, and
* `-(U+1)(U+2) + Z R₁(U,Z)`.

When `U` is three-integral and `Z` has positive three-adic valuation, both
remainders are three-integral.  The strict-transform equation therefore
forces `U` to reduce to one of the corresponding exceptional-fiber roots.
The final theorem applies this directly to every cyclic root attached to a
hypothetical marked point of order twenty-five.
-/

namespace MazurTorsion.Kubert

/-- The integral remainder after removing the exceptional factor `-U(U+1)`
from the second root-zero strict transform. -/
def orderTwentyFiveLehmerRootZeroExceptionalRemainder
    {R : Type*} [CommRing R] (u z : R) : R :=
  u ^ 5 * z ^ 6 - u ^ 4 * z ^ 3 - 10 * u ^ 3 * z ^ 4 +
    10 * u ^ 3 * z ^ 3 - 6 * u ^ 3 * z ^ 2 + 2 * u ^ 3 * z -
    5 * u ^ 2 * z ^ 3 + 15 * u ^ 2 * z ^ 2 - 11 * u ^ 2 * z +
    5 * u ^ 2 + 10 * u * z ^ 2 - 10 * u * z + 4 * u - z

/-- The root-zero strict transform is its exceptional factor plus `Z` times
an integral polynomial. -/
theorem orderTwentyFiveLehmer_rootZeroExceptionalRemainder_identity
    {R : Type*} [CommRing R] (u z : R) :
    orderTwentyFiveLehmerRootZeroSecondStrictTransform u z =
      -(u * (u + 1)) +
        z * orderTwentyFiveLehmerRootZeroExceptionalRemainder u z := by
  simp only [orderTwentyFiveLehmerRootZeroSecondStrictTransform,
    orderTwentyFiveLehmerRootZeroExceptionalRemainder]
  ring

/-- The integral remainder after removing the exceptional factor
`-(U+1)(U+2)` from the diagonal strict transform. -/
def orderTwentyFiveLehmerDiagonalExceptionalRemainder
    {R : Type*} [CommRing R] (u z : R) : R :=
  u ^ 5 * z ^ 3 + 5 * u ^ 4 * z ^ 2 - u ^ 4 * z -
    10 * u ^ 3 * z ^ 3 + 10 * u ^ 3 * z ^ 2 + 4 * u ^ 3 * z -
    2 * u ^ 3 - 5 * u ^ 2 * z ^ 3 - 15 * u ^ 2 * z ^ 2 +
    19 * u ^ 2 * z - 3 * u ^ 2 + 10 * u * z ^ 3 -
    20 * u * z ^ 2 + 4 * u * z + 7 * u - z ^ 3 + 10 * z ^ 2 -
    15 * z + 9

/-- The diagonal strict transform is its exceptional factor plus `Z` times
an integral polynomial. -/
theorem orderTwentyFiveLehmer_diagonalExceptionalRemainder_identity
    {R : Type*} [CommRing R] (u z : R) :
    orderTwentyFiveLehmerDiagonalStrictTransform u z =
      -((u + 1) * (u + 2)) +
        z * orderTwentyFiveLehmerDiagonalExceptionalRemainder u z := by
  simp only [orderTwentyFiveLehmerDiagonalStrictTransform,
    orderTwentyFiveLehmerDiagonalExceptionalRemainder]
  ring

private def threeAdicIntegralRationals : Subring ℚ where
  carrier := {q | 0 ≤ padicValRat 3 q}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro q r hq hr
    change 0 ≤ padicValRat 3 q at hq
    change 0 ≤ padicValRat 3 r at hr
    change 0 ≤ padicValRat 3 (q + r)
    by_cases h : q + r = 0
    · simp [h]
    · exact le_trans (le_min hq hr)
        (padicValRat.min_le_padicValRat_add h)
  mul_mem' := by
    intro q r hq hr
    change 0 ≤ padicValRat 3 q at hq
    change 0 ≤ padicValRat 3 r at hr
    change 0 ≤ padicValRat 3 (q * r)
    by_cases hq0 : q = 0
    · simp [hq0]
    by_cases hr0 : r = 0
    · simp [hr0]
    rw [padicValRat.mul hq0 hr0]
    omega
  neg_mem' := by
    intro q hq
    change 0 ≤ padicValRat 3 q at hq
    change 0 ≤ padicValRat 3 (-q)
    simpa only [padicValRat.neg] using hq

private theorem rootZeroExceptionalRemainder_nonnegative
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 ≤ padicValRat 3 z) :
    0 ≤ padicValRat 3
      (orderTwentyFiveLehmerRootZeroExceptionalRemainder u z) := by
  let U : threeAdicIntegralRationals := ⟨u, hu⟩
  let Z : threeAdicIntegralRationals := ⟨z, hz⟩
  exact (orderTwentyFiveLehmerRootZeroExceptionalRemainder U Z).property

private theorem diagonalExceptionalRemainder_nonnegative
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 ≤ padicValRat 3 z) :
    0 ≤ padicValRat 3
      (orderTwentyFiveLehmerDiagonalExceptionalRemainder u z) := by
  let U : threeAdicIntegralRationals := ⟨u, hu⟩
  let Z : threeAdicIntegralRationals := ⟨z, hz⟩
  exact (orderTwentyFiveLehmerDiagonalExceptionalRemainder U Z).property

private theorem factor_congruence_of_eq_parameter_mul
    (f g z r : ℚ)
    (hf : 0 ≤ padicValRat 3 f) (hg : 0 ≤ padicValRat 3 g)
    (hz : 0 < padicValRat 3 z) (hr : 0 ≤ padicValRat 3 r)
    (heq : f * g = z * r) :
    (f = 0 ∨ 0 < padicValRat 3 f) ∨
      (g = 0 ∨ 0 < padicValRat 3 g) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hz
    omega
  by_cases hr0 : r = 0
  · rw [hr0, mul_zero] at heq
    rcases mul_eq_zero.mp heq with hf0 | hg0
    · exact Or.inl (Or.inl hf0)
    · exact Or.inr (Or.inl hg0)
  · have hfg0 : f * g ≠ 0 := by
      rw [heq]
      exact mul_ne_zero hz0 hr0
    have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg0
    have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg0
    have hval :
        padicValRat 3 f + padicValRat 3 g =
          padicValRat 3 z + padicValRat 3 r := by
      rw [← padicValRat.mul hf0 hg0, heq,
        padicValRat.mul hz0 hr0]
    by_cases hfp : 0 < padicValRat 3 f
    · exact Or.inl (Or.inr hfp)
    · right; right
      omega

/-- A three-integral point of the root-zero strict transform with positively
valued exceptional parameter reduces to `U = 0` or `U = -1`. -/
theorem orderTwentyFiveLehmer_rootZero_exceptionalCongruence
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 < padicValRat 3 z)
    (hstrict :
      orderTwentyFiveLehmerRootZeroSecondStrictTransform u z = 0) :
    (u = 0 ∨ 0 < padicValRat 3 u) ∨
      (u = -1 ∨ 0 < padicValRat 3 (u + 1)) := by
  have hz' : 0 ≤ padicValRat 3 z := le_of_lt hz
  have hu1 : 0 ≤ padicValRat 3 (u + 1) :=
    threeAdicIntegralRationals.add_mem hu (by simp)
  have heq :
      u * (u + 1) =
        z * orderTwentyFiveLehmerRootZeroExceptionalRemainder u z := by
    rw [orderTwentyFiveLehmer_rootZeroExceptionalRemainder_identity]
      at hstrict
    linarith
  have h := factor_congruence_of_eq_parameter_mul
    u (u + 1) z
    (orderTwentyFiveLehmerRootZeroExceptionalRemainder u z)
    hu hu1 hz (rootZeroExceptionalRemainder_nonnegative u z hu hz') heq
  rcases h with h | h
  · exact Or.inl h
  · right
    rcases h with h | h
    · exact Or.inl (eq_neg_of_add_eq_zero_left h)
    · exact Or.inr h

/-- A three-integral point of the diagonal strict transform with positively
valued exceptional parameter reduces to `U = -1` or `U = -2`. -/
theorem orderTwentyFiveLehmer_diagonal_exceptionalCongruence
    (u z : ℚ) (hu : 0 ≤ padicValRat 3 u)
    (hz : 0 < padicValRat 3 z)
    (hstrict : orderTwentyFiveLehmerDiagonalStrictTransform u z = 0) :
    (u = -1 ∨ 0 < padicValRat 3 (u + 1)) ∨
      (u = -2 ∨ 0 < padicValRat 3 (u + 2)) := by
  have hz' : 0 ≤ padicValRat 3 z := le_of_lt hz
  have hu1 : 0 ≤ padicValRat 3 (u + 1) :=
    threeAdicIntegralRationals.add_mem hu (by simp)
  have hu2 : 0 ≤ padicValRat 3 (u + 2) :=
    threeAdicIntegralRationals.add_mem hu (by norm_num)
  have heq :
      (u + 1) * (u + 2) =
        z * orderTwentyFiveLehmerDiagonalExceptionalRemainder u z := by
    rw [orderTwentyFiveLehmer_diagonalExceptionalRemainder_identity]
      at hstrict
    linarith
  have h := factor_congruence_of_eq_parameter_mul
    (u + 1) (u + 2) z
    (orderTwentyFiveLehmerDiagonalExceptionalRemainder u z)
    hu1 hu2 hz (diagonalExceptionalRemainder_nonnegative u z hu hz') heq
  rcases h with h | h
  · left
    rcases h with h | h
    · exact Or.inl (eq_neg_of_add_eq_zero_left h)
    · exact Or.inr h
  · right
    rcases h with h | h
    · exact Or.inl (eq_neg_of_add_eq_zero_left h)
    · exact Or.inr h

/-- A resolved Lehmer chart together with its exact exceptional-fiber
congruence. -/
def orderTwentyFiveLehmerResolvedThreeAdicBranch
    (n x : ℚ) (a : ℤ) : Prop :=
  (∃ u z : ℚ,
      u = x * n ∧ z = 1 / n ∧
      padicValRat 3 u = 2 * a ∧ padicValRat 3 z = a ∧
      orderTwentyFiveLehmerRootZeroSecondStrictTransform u z = 0 ∧
      (u = 0 ∨ 0 < padicValRat 3 u)) ∨
    (∃ u z : ℚ,
      u = x * n ∧ z = 1 / n ∧
      padicValRat 3 u = 0 ∧ padicValRat 3 z = a ∧
      orderTwentyFiveLehmerRootZeroSecondStrictTransform u z = 0 ∧
      (u = -1 ∨ 0 < padicValRat 3 (u + 1))) ∨
    (∃ u z : ℚ,
      u = x - n ∧ z = 1 / n ∧
      0 ≤ padicValRat 3 u ∧ padicValRat 3 z = a ∧
      orderTwentyFiveLehmerDiagonalStrictTransform u z = 0 ∧
      ((u = -1 ∨ 0 < padicValRat 3 (u + 1)) ∨
        (u = -2 ∨ 0 < padicValRat 3 (u + 2)))) ∨
    (∃ u z : ℚ,
      u = n / x ∧ z = 1 / x ∧
      padicValRat 3 u = a ∧ padicValRat 3 z = 2 * a ∧
      orderTwentyFiveLehmerHomogeneousPolynomial u 1 z = 0)

/-- The valuation data on a resolved chart determines its exceptional-fiber
branch. -/
theorem orderTwentyFiveLehmer_resolvedChart_isThreeAdicBranch
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn0 : n ≠ 0) (hx0 : x ≠ 0)
    (h : orderTwentyFiveLehmerResolvedThreeAdicChart n x a) :
    orderTwentyFiveLehmerResolvedThreeAdicBranch n x a := by
  rcases h with h | h | h | h
  · obtain ⟨u, z, hu, hz, huv, hzv, hstrict⟩ := h
    left
    refine ⟨u, z, hu, hz, huv, hzv, hstrict, Or.inr ?_⟩
    omega
  · obtain ⟨u, z, hu, hz, huv, hzv, hstrict⟩ := h
    right; left
    refine ⟨u, z, hu, hz, huv, hzv, hstrict, ?_⟩
    have hu0 : u ≠ 0 := by
      rw [hu]
      exact mul_ne_zero hx0 hn0
    have hres := orderTwentyFiveLehmer_rootZero_exceptionalCongruence
      u z (by omega) (by omega) hstrict
    rcases hres with hbad | hgood
    · rcases hbad with hzero | hpos
      · exact False.elim (hu0 hzero)
      · omega
    · exact hgood
  · obtain ⟨u, z, hu, hz, huv, hzv, hstrict⟩ := h
    right; right; left
    exact ⟨u, z, hu, hz, huv, hzv, hstrict,
      orderTwentyFiveLehmer_diagonal_exceptionalCongruence
        u z huv (by omega) hstrict⟩
  · exact Or.inr (Or.inr (Or.inr h))

/-- All five actual cyclic roots have resolved three-adic branch data: the
two root-zero slopes specialize separately to `U = 0` and `U = -1`, the two
diagonal roots specialize to `U = -1` or `U = -2`, and the final root lies
on the unique smooth parameter-zero branch. -/
theorem orderTwentyFive_threeAdicResolvedInfinityBranches_of_marked_order
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
          orderTwentyFiveLehmerResolvedThreeAdicBranch N x a := by
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
      hreciprocal, a, ha, hval, hresolved⟩ :=
    orderTwentyFive_threeAdicResolvedInfinityCharts_of_marked_order
      b c hb h00 horder
  let N : ℚ := -orderTwentyFiveFifthPowerHauptmodul
    ((m : ℚ) / (n : ℚ))
  have hNv : padicValRat 3 N = -a := by
    dsimp only [N]
    exact orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation
      ((m : ℚ) / (n : ℚ)) a ha hval
  have hN0 : N ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hNv
    omega
  have hnonzero := orderTwentyFiveBrunault_orbit_units_ne_zero
    b c hb h00 horder
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
    hreciprocal, a, ha, hval, ?_⟩
  dsimp only
  intro x hx
  have hx0 : x ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hnonzero.1
    · exact hnonzero.2.1
    · exact hnonzero.2.2.1
    · exact hnonzero.2.2.2.1
    · exact hnonzero.2.2.2.2
  exact orderTwentyFiveLehmer_resolvedChart_isThreeAdicBranch
    N x a ha hN0 hx0 (hresolved x hx)

end MazurTorsion.Kubert
