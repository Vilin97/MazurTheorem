/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCuspDivisorPicard

/-!
# Pointwise order certificates for the order-twenty-five cusp divisors

The Picard interface asks for equality between five explicit cusp divisors
and principal divisors.  Local calculations naturally provide pointwise
orders of five rational functions instead.  This file gives the exact bridge:
the order vector `(3, -1, 1, -2, -1)` on five pairwise-distinct cusps, with
order zero everywhere else, determines those principal divisors.

`orderTwentyFiveCuspOrderRelations` is the local-order interface and
`orderTwentyFive_picardCuspidalSubgroupZModEquiv_of_orderRelations` is its
named Picard-level consumer.
-/

namespace MazurTorsion.Kubert

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open MazurTorsion.AlgebraicGeometry

/-- Explicit pairwise distinctness of the five cyclic cusp labels. -/
def OrderTwentyFiveCuspsPairwiseDistinct
    {Y : Type*} (c0 c1 c2 c3 c4 : Y) : Prop :=
  c0 ≠ c1 ∧ c0 ≠ c2 ∧ c0 ≠ c3 ∧ c0 ≠ c4 ∧
    c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c4 ∧
    c2 ≠ c3 ∧ c2 ≠ c4 ∧ c3 ≠ c4

/-- Cyclic rotation preserves pairwise distinctness. -/
theorem OrderTwentyFiveCuspsPairwiseDistinct.rotate
    {Y : Type*} {c0 c1 c2 c3 c4 : Y}
    (h : OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4) :
    OrderTwentyFiveCuspsPairwiseDistinct c1 c2 c3 c4 c0 := by
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  exact ⟨h12, h13, h14, h01.symm, h23, h24, h02.symm,
    h34, h03.symm, h04.symm⟩

/-- The pointwise order function supported on five cyclic cusp labels. -/
noncomputable def orderTwentyFiveCuspOrder
    {Y : Type*} (c0 c1 c2 c3 c4 x : Y) : ℤ := by
  classical
  exact if x = c0 then 3 else if x = c1 then -1 else
    if x = c2 then 1 else if x = c3 then -2 else
    if x = c4 then -1 else 0

/-- Coefficients of the first explicit cusp divisor are exactly the declared
pointwise cusp-order function. -/
theorem coeff_orderTwentyFiveCuspDivisorZero
    {Y : Type*} {c0 c1 c2 c3 c4 : Y}
    (h : OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4) (x : Y) :
    coeff (orderTwentyFiveCuspDivisorZero c0 c1 c2 c3 c4) x =
      orderTwentyFiveCuspOrder c0 c1 c2 c3 c4 x := by
  classical
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  by_cases hx0 : x = c0
  · subst x
    simp [orderTwentyFiveCuspDivisorZero, orderTwentyFiveCuspOrder, coeff,
      ofPoint, *]
  by_cases hx1 : x = c1
  · subst x
    simp [orderTwentyFiveCuspDivisorZero, orderTwentyFiveCuspOrder, coeff,
      ofPoint, *]
  by_cases hx2 : x = c2
  · subst x
    simp [orderTwentyFiveCuspDivisorZero, orderTwentyFiveCuspOrder, coeff,
      ofPoint, *]
  by_cases hx3 : x = c3
  · subst x
    simp [orderTwentyFiveCuspDivisorZero, orderTwentyFiveCuspOrder, coeff,
      ofPoint, *]
  by_cases hx4 : x = c4
  · subst x
    simp [orderTwentyFiveCuspDivisorZero, orderTwentyFiveCuspOrder, coeff,
      ofPoint, *]
  · simp [orderTwentyFiveCuspDivisorZero, orderTwentyFiveCuspOrder, coeff,
      ofPoint, hx0, hx1, hx2, hx3, hx4]

/-- Coefficients of the first rotated cusp divisor. -/
theorem coeff_orderTwentyFiveCuspDivisorOne
    {Y : Type*} {c0 c1 c2 c3 c4 : Y}
    (h : OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4) (x : Y) :
    coeff (orderTwentyFiveCuspDivisorOne c0 c1 c2 c3 c4) x =
      orderTwentyFiveCuspOrder c1 c2 c3 c4 c0 x := by
  simpa [orderTwentyFiveCuspDivisorOne, orderTwentyFiveCuspDivisorZero] using
    coeff_orderTwentyFiveCuspDivisorZero h.rotate x

/-- Coefficients of the second rotated cusp divisor. -/
theorem coeff_orderTwentyFiveCuspDivisorTwo
    {Y : Type*} {c0 c1 c2 c3 c4 : Y}
    (h : OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4) (x : Y) :
    coeff (orderTwentyFiveCuspDivisorTwo c0 c1 c2 c3 c4) x =
      orderTwentyFiveCuspOrder c2 c3 c4 c0 c1 x := by
  simpa [orderTwentyFiveCuspDivisorTwo, orderTwentyFiveCuspDivisorZero] using
    coeff_orderTwentyFiveCuspDivisorZero h.rotate.rotate x

/-- Coefficients of the third rotated cusp divisor. -/
theorem coeff_orderTwentyFiveCuspDivisorThree
    {Y : Type*} {c0 c1 c2 c3 c4 : Y}
    (h : OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4) (x : Y) :
    coeff (orderTwentyFiveCuspDivisorThree c0 c1 c2 c3 c4) x =
      orderTwentyFiveCuspOrder c3 c4 c0 c1 c2 x := by
  simpa [orderTwentyFiveCuspDivisorThree, orderTwentyFiveCuspDivisorZero] using
    coeff_orderTwentyFiveCuspDivisorZero h.rotate.rotate.rotate x

/-- Coefficients of the fourth rotated cusp divisor. -/
theorem coeff_orderTwentyFiveCuspDivisorFour
    {Y : Type*} {c0 c1 c2 c3 c4 : Y}
    (h : OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4) (x : Y) :
    coeff (orderTwentyFiveCuspDivisorFour c0 c1 c2 c3 c4) x =
      orderTwentyFiveCuspOrder c4 c0 c1 c2 c3 x := by
  simpa [orderTwentyFiveCuspDivisorFour, orderTwentyFiveCuspDivisorZero] using
    coeff_orderTwentyFiveCuspDivisorZero h.rotate.rotate.rotate.rotate x

/-- Pointwise order data for five rational functions.  The piecewise order
functions include both the five cusp orders and vanishing order zero at every
other point. -/
def orderTwentyFiveCuspOrderRelations
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y) : Prop :=
  OrderTwentyFiveCuspsPairwiseDistinct c0 c1 c2 c3 c4 ∧
    ∃ g0 g1 g2 g3 g4 : G,
      (∀ x, S.ord x g0 = orderTwentyFiveCuspOrder c0 c1 c2 c3 c4 x) ∧
      (∀ x, S.ord x g1 = orderTwentyFiveCuspOrder c1 c2 c3 c4 c0 x) ∧
      (∀ x, S.ord x g2 = orderTwentyFiveCuspOrder c2 c3 c4 c0 c1 x) ∧
      (∀ x, S.ord x g3 = orderTwentyFiveCuspOrder c3 c4 c0 c1 c2 x) ∧
      ∀ x, S.ord x g4 = orderTwentyFiveCuspOrder c4 c0 c1 c2 c3 x

/-- The pointwise order certificate determines the five required principal
divisors. -/
theorem orderTwentyFiveCuspPrincipalDivisorRelations_of_orderRelations
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y)
    (h : orderTwentyFiveCuspOrderRelations S c0 c1 c2 c3 c4) :
    orderTwentyFiveCuspPrincipalDivisorRelations S c0 c1 c2 c3 c4 := by
  rcases h with ⟨hdist, g0, g1, g2, g3, g4, h0, h1, h2, h3, h4⟩
  refine ⟨g0, g1, g2, g3, g4, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [S.coeff_principalDivisor]
    exact (coeff_orderTwentyFiveCuspDivisorZero hdist x).trans (h0 x).symm
  · ext x
    rw [S.coeff_principalDivisor]
    exact (coeff_orderTwentyFiveCuspDivisorOne hdist x).trans (h1 x).symm
  · ext x
    rw [S.coeff_principalDivisor]
    exact (coeff_orderTwentyFiveCuspDivisorTwo hdist x).trans (h2 x).symm
  · ext x
    rw [S.coeff_principalDivisor]
    exact (coeff_orderTwentyFiveCuspDivisorThree hdist x).trans (h3 x).symm
  · ext x
    rw [S.coeff_principalDivisor]
    exact (coeff_orderTwentyFiveCuspDivisorFour hdist x).trans (h4 x).symm

/-- Named downstream consumer of pointwise cusp orders: exact local order
data and Picard distinctness produce the cyclic order-`71` cusp subgroup. -/
noncomputable def
    orderTwentyFive_picardCuspidalSubgroupZModEquiv_of_orderRelations
    {X : Scheme} {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (hw : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (c0 c1 c2 c3 c4 : Y) (hc0 : w c0 = 1)
    (horders : orderTwentyFiveCuspOrderRelations S c0 c1 c2 c3 c4)
    (hne :
      PicardGroup.weightedAbelJacobiClass S w hw e hc0 c0 ≠
        PicardGroup.weightedAbelJacobiClass S w hw e hc0 c1) :
    ZMod 71 ≃+
      orderTwentyFiveBasedCuspSubgroup
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c0)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c1)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c2)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c3)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c4) :=
  orderTwentyFive_picardCuspidalSubgroupZModEquiv S w hw e
    c0 c1 c2 c3 c4 hc0
    (orderTwentyFiveCuspPrincipalDivisorRelations_of_orderRelations
      S c0 c1 c2 c3 c4 horders)
    hne

end MazurTorsion.Kubert
