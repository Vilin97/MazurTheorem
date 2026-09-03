/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveLehmerInfinityResolution

/-!
# Three-adic points on the resolved Lehmer infinity charts

This file lifts the coarse infinity-chart certificate to the explicit strict
transforms.  Homogeneity moves an affine Lehmer root `(N, X, 1)` into the
appropriate projective chart.  The four Newton slopes then give:

* root-zero coordinates `Z = 1/N`, `U = XN`, with `v₃(U) = 2a` or `0`;
* diagonal coordinates `Z = 1/N`, `U = X-N`, with `U` three-integral;
* parameter-zero coordinates `U = N/X`, `Z = 1/X`, both positively valued.

The final theorem supplies this resolved-chart data simultaneously for all
five cyclic Brunault roots of a hypothetical marked point of order
twenty-five.
-/

namespace MazurTorsion.Kubert

/-- Lehmer's degree-six homogenization has the expected scaling law. -/
theorem orderTwentyFiveLehmerHomogeneousPolynomial_scale
    {R : Type*} [CommRing R] (s n x z : R) :
    orderTwentyFiveLehmerHomogeneousPolynomial (s * n) (s * x) (s * z) =
      s ^ 6 * orderTwentyFiveLehmerHomogeneousPolynomial n x z := by
  simp only [orderTwentyFiveLehmerHomogeneousPolynomial]
  ring

private theorem homogeneous_root_scaled_at_parameter
    (n x : ℚ) (hn : n ≠ 0)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveLehmerHomogeneousPolynomial 1 (x / n) (1 / n) = 0 := by
  have hscale := orderTwentyFiveLehmerHomogeneousPolynomial_scale
    (1 / n) n x (1 : ℚ)
  have hsn : (1 / n) * n = 1 := by field_simp
  have hsx : (1 / n) * x = x / n := by ring
  rw [hsn, hsx, mul_one,
    orderTwentyFiveLehmerHomogeneousPolynomial_affine,
    hroot, mul_zero] at hscale
  exact hscale

private theorem homogeneous_root_scaled_at_root
    (n x : ℚ) (hx : x ≠ 0)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0) :
    orderTwentyFiveLehmerHomogeneousPolynomial (n / x) 1 (1 / x) = 0 := by
  have hscale := orderTwentyFiveLehmerHomogeneousPolynomial_scale
    (1 / x) n x (1 : ℚ)
  have hsn : (1 / x) * n = n / x := by ring
  have hsx : (1 / x) * x = 1 := by field_simp
  rw [hsn, hsx, mul_one,
    orderTwentyFiveLehmerHomogeneousPolynomial_affine,
    hroot, mul_zero] at hscale
  exact hscale

/-- The resolved three-adic chart occupied by a Lehmer root.  The first two
alternatives are the two slopes above `[0 : 1 : 0]`; the third is the
integral strict-transform coordinate above `[1 : 1 : 0]`; the fourth is the
smooth chart at `[1 : 0 : 0]`. -/
def orderTwentyFiveLehmerResolvedThreeAdicChart
    (n x : ℚ) (a : ℤ) : Prop :=
  (∃ u z : ℚ,
      u = x * n ∧ z = 1 / n ∧
      padicValRat 3 u = 2 * a ∧ padicValRat 3 z = a ∧
      orderTwentyFiveLehmerRootZeroSecondStrictTransform u z = 0) ∨
    (∃ u z : ℚ,
      u = x * n ∧ z = 1 / n ∧
      padicValRat 3 u = 0 ∧ padicValRat 3 z = a ∧
      orderTwentyFiveLehmerRootZeroSecondStrictTransform u z = 0) ∨
    (∃ u z : ℚ,
      u = x - n ∧ z = 1 / n ∧
      0 ≤ padicValRat 3 u ∧ padicValRat 3 z = a ∧
      orderTwentyFiveLehmerDiagonalStrictTransform u z = 0) ∨
    (∃ u z : ℚ,
      u = n / x ∧ z = 1 / x ∧
      padicValRat 3 u = a ∧ padicValRat 3 z = 2 * a ∧
      orderTwentyFiveLehmerHomogeneousPolynomial u 1 z = 0)

/-- A Lehmer root satisfying one alternative of the exact three-adic chart
certificate satisfies the corresponding strict-transform equation with the
claimed local-coordinate valuations. -/
theorem orderTwentyFiveLehmer_root_resolvedThreeAdicChart
    (n x : ℚ) (a : ℤ) (ha : 0 < a)
    (hn : padicValRat 3 n = -a)
    (hroot : orderTwentyFiveLehmerPolynomial n x = 0)
    (hcusp : padicValRat 3 x = -a →
      0 ≤ padicValRat 3 (x - n))
    (hchart :
      (padicValRat 3 x = 3 * a ∧
          padicValRat 3 (x / n) = 4 * a) ∨
        (padicValRat 3 x = a ∧
          padicValRat 3 (x / n) = 2 * a) ∨
        (padicValRat 3 x = -a ∧
          (x = n ∨ 0 < padicValRat 3 (x / n - 1))) ∨
        (padicValRat 3 x = -2 * a ∧
          padicValRat 3 (n / x) = a)) :
    orderTwentyFiveLehmerResolvedThreeAdicChart n x a := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, padicValRat.zero] at hn
    omega
  have hx0 : x ≠ 0 := by
    intro h
    simp [h, orderTwentyFiveLehmerPolynomial] at hroot
  have hzN0 : (1 / n : ℚ) ≠ 0 := div_ne_zero one_ne_zero hn0
  have hzNv : padicValRat 3 (1 / n) = a := by
    rw [padicValRat.div one_ne_zero hn0, padicValRat.one, hn]
    omega
  have hscaledN := homogeneous_root_scaled_at_parameter n x hn0 hroot
  have hrootStrict :
      orderTwentyFiveLehmerRootZeroSecondStrictTransform
        (x * n) (1 / n) = 0 := by
    have hcoord : (1 / n : ℚ) ^ 2 * (x * n) = x / n := by
      field_simp
    have hid :=
      orderTwentyFiveLehmer_rootZeroSecondStrictTransform_identity
        (x * n) (1 / n)
    rw [hcoord] at hid
    have hprod := hid.symm.trans hscaledN
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 4 hzN0)
  have hdiagStrict :
      orderTwentyFiveLehmerDiagonalStrictTransform
        (x - n) (1 / n) = 0 := by
    have hcoord : 1 + (1 / n) * (x - n) = x / n := by
      field_simp
      ring
    have hid := orderTwentyFiveLehmer_diagonalStrictTransform_identity
      (x - n) (1 / n)
    rw [hcoord] at hid
    have hprod := hid.symm.trans hscaledN
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hzN0)
  rcases hchart with h | h | h | h
  · left
    refine ⟨x * n, 1 / n, rfl, rfl, ?_, hzNv, hrootStrict⟩
    rw [padicValRat.mul hx0 hn0, h.1, hn]
    omega
  · right; left
    refine ⟨x * n, 1 / n, rfl, rfl, ?_, hzNv, hrootStrict⟩
    rw [padicValRat.mul hx0 hn0, h.1, hn]
    omega
  · right; right; left
    exact ⟨x - n, 1 / n, rfl, rfl,
      hcusp h.1, hzNv, hdiagStrict⟩
  · right; right; right
    refine ⟨n / x, 1 / x, rfl, rfl, h.2, ?_,
      homogeneous_root_scaled_at_root n x hx0 hroot⟩
    rw [padicValRat.div one_ne_zero hx0, padicValRat.one, h.1]
    omega

private theorem brunault_roots_of_marked_order
    (b c n : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    (hn : n = orderTwentyFiveOrbitParameter
      (orderTwentyFiveBrunaultXZero b c)
      (orderTwentyFiveBrunaultXOne b c)
      (orderTwentyFiveBrunaultXTwo b c)
      (orderTwentyFiveBrunaultXThree b c)
      (orderTwentyFiveBrunaultXFour b c)) :
    ∀ x ∈ [orderTwentyFiveBrunaultXZero b c,
        orderTwentyFiveBrunaultXOne b c,
        orderTwentyFiveBrunaultXTwo b c,
        orderTwentyFiveBrunaultXThree b c,
        orderTwentyFiveBrunaultXFour b c],
      orderTwentyFiveLehmerPolynomial n x = 0 := by
  let r0 := orderTwentyFiveBrunaultXZero b c
  let r1 := orderTwentyFiveBrunaultXOne b c
  let r2 := orderTwentyFiveBrunaultXTwo b c
  let r3 := orderTwentyFiveBrunaultXThree b c
  let r4 := orderTwentyFiveBrunaultXFour b c
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
  have hroot0 : orderTwentyFiveLehmerPolynomial n r0 = 0 := by
    rw [hn]
    exact (orderTwentyFiveLehmer_selectedRoots_of_orbit
      r0 r1 r2 r3 r4 hxOne hor0 hor1 hor2 hor3 hor4 hor5).1
  have hcycle := orderTwentyFiveLehmerDeckTransform_cycle_of_orbit
    r0 r1 r2 r3 r4 hxOne hor0 hor1 hor2 hor3 hor4 hor5
  dsimp only at hcycle
  rw [← hn] at hcycle
  obtain ⟨h01, h12, h23, h34, -⟩ := hcycle
  have hroot1 : orderTwentyFiveLehmerPolynomial n r1 = 0 := by
    rw [← h01]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n r0 hroot0
  have hroot2 : orderTwentyFiveLehmerPolynomial n r2 = 0 := by
    rw [← h12]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n r1 hroot1
  have hroot3 : orderTwentyFiveLehmerPolynomial n r3 = 0 := by
    rw [← h23]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n r2 hroot2
  have hroot4 : orderTwentyFiveLehmerPolynomial n r4 = 0 := by
    rw [← h34]
    exact orderTwentyFiveLehmerDeckTransform_isRoot n r3 hroot3
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hroot0
  · exact hroot1
  · exact hroot2
  · exact hroot3
  · exact hroot4

/-- Every cyclic root arising from a hypothetical marked point of exact order
twenty-five satisfies one of the explicit resolved infinity-chart equations,
with its local coordinates carrying the exact required three-adic bounds. -/
theorem orderTwentyFive_threeAdicResolvedInfinityCharts_of_marked_order
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
          orderTwentyFiveLehmerResolvedThreeAdicChart N x a := by
  obtain ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
      hreciprocal, a, ha, hval, hcusp, hcharts⟩ :=
    orderTwentyFive_threeAdicCuspCongruences_of_marked_order
      b c hb h00 horder
  let N : ℚ := -orderTwentyFiveFifthPowerHauptmodul
    ((m : ℚ) / (n : ℚ))
  have hN : N = orderTwentyFiveOrbitParameter
      (orderTwentyFiveBrunaultXZero b c)
      (orderTwentyFiveBrunaultXOne b c)
      (orderTwentyFiveBrunaultXTwo b c)
      (orderTwentyFiveBrunaultXThree b c)
      (orderTwentyFiveBrunaultXFour b c) := by
    dsimp only [N]
    linarith
  have hNv : padicValRat 3 N = -a := by
    dsimp only [N]
    exact orderTwentyFiveFifthPowerHauptmodul_threeAdicValuation
      ((m : ℚ) / (n : ℚ)) a ha hval
  have hroots := brunault_roots_of_marked_order
    b c N hb h00 horder hN
  refine ⟨m, n, hm0, hn0, hmn, hm3, hn3, hparameter,
    hreciprocal, a, ha, hval, ?_⟩
  dsimp only
  intro x hx
  exact orderTwentyFiveLehmer_root_resolvedThreeAdicChart
    N x a ha hNv (hroots x hx) (hcusp x hx) (hcharts x hx)

end MazurTorsion.Kubert
