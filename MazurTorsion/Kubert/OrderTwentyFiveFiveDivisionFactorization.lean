/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveFiveDivision
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Components of the order-twenty-five five-division relation

The invariant relation between the source order-five parameter and the
residual parameter on its quotient has three components over an algebraic
closure: one quadratic component and two quintic components.  The quadratic
component has discriminant `125 * (c² + 1)²`, so it has no rational points.
The two quintic components are exchanged by the order-five diamond involution
`d ↦ -1/d`.  Consequently every rational five-division point can be oriented
onto one fixed quintic component.
-/

namespace MazurTorsion.Kubert

/-- The quadratic component of the invariant relation. -/
def orderTwentyFiveFiveDivisionQuadratic (c d : ℚ) : ℚ :=
  (c ^ 2 - 11 * c - 1) * d ^ 2 +
    (-11 * c ^ 2 - 4 * c + 11) * d -
    (c ^ 2 - 11 * c - 1)

/-- A fixed orientation of the order-twenty-five quintic component. -/
def orderTwentyFiveFiveDivisionFactor (c d : ℚ) : ℚ :=
  c ^ 5 +
    c ^ 4 *
      (-d ^ 5 + 25 * d ^ 4 - 200 * d ^ 3 + 525 * d ^ 2 -
        200 * d - 22) +
    c ^ 3 *
      (22 * d ^ 5 - 475 * d ^ 4 + 1675 * d ^ 3 + 9650 * d ^ 2 +
        2175 * d + 119) +
    c ^ 2 *
      (-119 * d ^ 5 + 2175 * d ^ 4 - 9650 * d ^ 3 + 1675 * d ^ 2 +
        475 * d + 22) +
    c *
      (-22 * d ^ 5 + 200 * d ^ 4 + 525 * d ^ 3 + 200 * d ^ 2 +
        25 * d + 1) -
    d ^ 5

/-- The opposite orientation of the order-twenty-five quintic component. -/
def orderTwentyFiveFiveDivisionReverseFactor (c d : ℚ) : ℚ :=
  c ^ 5 * d ^ 5 +
    c ^ 4 *
      (-22 * d ^ 5 + 200 * d ^ 4 + 525 * d ^ 3 + 200 * d ^ 2 +
        25 * d + 1) +
    c ^ 3 *
      (119 * d ^ 5 - 2175 * d ^ 4 + 9650 * d ^ 3 - 1675 * d ^ 2 -
        475 * d - 22) +
    c ^ 2 *
      (22 * d ^ 5 - 475 * d ^ 4 + 1675 * d ^ 3 + 9650 * d ^ 2 +
        2175 * d + 119) +
    c *
      (d ^ 5 - 25 * d ^ 4 + 200 * d ^ 3 - 525 * d ^ 2 +
        200 * d + 22) +
    1

/-- Exact factorization of the cleared invariant relation. -/
theorem orderTwentyFiveFiveDivisionRelation_factorization (c d : ℚ) :
    orderTwentyFiveFiveDivisionRelation c d =
      -(orderTwentyFiveFiveDivisionQuadratic c d *
        orderTwentyFiveFiveDivisionFactor c d *
        orderTwentyFiveFiveDivisionReverseFactor c d) := by
  simp only [orderTwentyFiveFiveDivisionRelation,
    orderTwentyFiveFiveDivisionQuadratic,
    orderTwentyFiveFiveDivisionFactor,
    orderTwentyFiveFiveDivisionReverseFactor,
    orderFiveC4Polynomial, orderFiveVeluTargetC4Polynomial]
  ring

/-- The completed-square discriminant calculation for the quadratic
component. -/
private theorem orderTwentyFiveFiveDivisionQuadratic_square_identity
    (c d : ℚ)
    (hzero : orderTwentyFiveFiveDivisionQuadratic c d = 0) :
    (2 * (c ^ 2 - 11 * c - 1) * d +
        (-11 * c ^ 2 - 4 * c + 11)) ^ 2 =
      125 * (c ^ 2 + 1) ^ 2 := by
  calc
    (2 * (c ^ 2 - 11 * c - 1) * d +
        (-11 * c ^ 2 - 4 * c + 11)) ^ 2 =
      4 * (c ^ 2 - 11 * c - 1) *
          orderTwentyFiveFiveDivisionQuadratic c d +
        (-11 * c ^ 2 - 4 * c + 11) ^ 2 +
        4 * (c ^ 2 - 11 * c - 1) ^ 2 := by
      simp only [orderTwentyFiveFiveDivisionQuadratic]
      ring
    _ = (-11 * c ^ 2 - 4 * c + 11) ^ 2 +
        4 * (c ^ 2 - 11 * c - 1) ^ 2 := by rw [hzero]; ring
    _ = 125 * (c ^ 2 + 1) ^ 2 := by ring

/-- The quadratic component has no rational point: its discriminant has
the nonsquare class of five. -/
theorem orderTwentyFiveFiveDivisionQuadratic_ne_zero (c d : ℚ) :
    orderTwentyFiveFiveDivisionQuadratic c d ≠ 0 := by
  intro hzero
  have hsquare :=
    orderTwentyFiveFiveDivisionQuadratic_square_identity c d hzero
  have hc : c ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg c]
  have hfive : ¬ IsSquare (5 : ℚ) := by
    intro h
    exact (by decide : Nat.Prime 5).not_isSquare
      (Rat.isSquare_natCast_iff.mp h)
  apply hfive
  refine ⟨(2 * (c ^ 2 - 11 * c - 1) * d +
      (-11 * c ^ 2 - 4 * c + 11)) / (5 * (c ^ 2 + 1)), ?_⟩
  field_simp [hc]
  nlinarith [hsquare]

/-- A zero of the invariant relation lies on one of its two rational
quintic components. -/
theorem orderTwentyFiveFiveDivisionFactor_or_reverse
    {c d : ℚ} (hrelation : orderTwentyFiveFiveDivisionRelation c d = 0) :
    orderTwentyFiveFiveDivisionFactor c d = 0 ∨
      orderTwentyFiveFiveDivisionReverseFactor c d = 0 := by
  have hzero :
      -(orderTwentyFiveFiveDivisionQuadratic c d *
        orderTwentyFiveFiveDivisionFactor c d *
        orderTwentyFiveFiveDivisionReverseFactor c d) = 0 := by
    rw [← orderTwentyFiveFiveDivisionRelation_factorization, hrelation]
  have hproduct :
      orderTwentyFiveFiveDivisionQuadratic c d *
        orderTwentyFiveFiveDivisionFactor c d *
        orderTwentyFiveFiveDivisionReverseFactor c d = 0 :=
    neg_eq_zero.mp hzero
  rcases mul_eq_zero.mp hproduct with hleft | hreverse
  · rcases mul_eq_zero.mp hleft with hquadratic | hforward
    · exact (orderTwentyFiveFiveDivisionQuadratic_ne_zero c d
        hquadratic).elim
    · exact Or.inl hforward
  · exact Or.inr hreverse

/-- The diamond involution `d ↦ -1/d` exchanges the two quintic
components. -/
theorem orderTwentyFiveFiveDivisionFactor_diamond
    (c d : ℚ) (hd : d ≠ 0) :
    d ^ 5 * orderTwentyFiveFiveDivisionFactor c (-1 / d) =
      orderTwentyFiveFiveDivisionReverseFactor c d := by
  simp only [orderTwentyFiveFiveDivisionFactor,
    orderTwentyFiveFiveDivisionReverseFactor]
  field_simp [hd]
  ring

/-- Every noncuspidal rational zero of the invariant relation can be
oriented onto the fixed quintic component. -/
theorem exists_orderTwentyFiveFiveDivisionFactor_of_relation
    {c d : ℚ} (hd : d ≠ 0)
    (hdfactor : d ^ 2 - 11 * d - 1 ≠ 0)
    (hrelation : orderTwentyFiveFiveDivisionRelation c d = 0) :
    ∃ d' : ℚ, d' ≠ 0 ∧ d' ^ 2 - 11 * d' - 1 ≠ 0 ∧
      orderTwentyFiveFiveDivisionFactor c d' = 0 := by
  rcases orderTwentyFiveFiveDivisionFactor_or_reverse hrelation with
      hforward | hreverse
  · exact ⟨d, hd, hdfactor, hforward⟩
  · have hd' : -1 / d ≠ 0 := div_ne_zero (by norm_num) hd
    have hdfactor' : (-1 / d) ^ 2 - 11 * (-1 / d) - 1 ≠ 0 := by
      intro hzero
      field_simp [hd] at hzero
      exact hdfactor (by nlinarith)
    have hdiamond := orderTwentyFiveFiveDivisionFactor_diamond c d hd
    rw [hreverse] at hdiamond
    have hforward' :
        orderTwentyFiveFiveDivisionFactor c (-1 / d) = 0 :=
      (mul_eq_zero.mp hdiamond).resolve_left (pow_ne_zero 5 hd)
    exact ⟨-1 / d, hd', hdfactor', hforward'⟩

/-- The quotient image of an exact five-division point lies, after choosing
the diamond orientation, on the fixed quintic component. -/
theorem exists_orderTwentyFiveFiveDivisionFactor_of_orderTwentyFive
    {c : ℚ} [(orderFiveCurve c).IsElliptic]
    {Q : (orderFiveCurve c).toAffine.Point}
    (hQ : addOrderOf Q = 25)
    (hfive : (5 : ℕ) • Q = orderFiveOrigin c) :
    ∃ d : ℚ, d ≠ 0 ∧ d ^ 2 - 11 * d - 1 ≠ 0 ∧
      orderTwentyFiveFiveDivisionFactor c d = 0 := by
  obtain ⟨d, hd, hdfactor, hrelation⟩ :=
    exists_orderFiveQuotientParameter_of_orderTwentyFive hQ hfive
  exact exists_orderTwentyFiveFiveDivisionFactor_of_relation
    hd hdfactor hrelation

/-- Global normalization package landing a hypothetical rational
order-twenty-five point on the fixed quintic five-division component. -/
theorem orderTwentyFive_fiveDivisionFactor_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h25 : addOrderOf P = 25) :
    ∃ (c d u : ℚ),
      c ≠ 0 ∧ c ^ 2 - 11 * c - 1 ≠ 0 ∧
        d ≠ 0 ∧ d ^ 2 - 11 * d - 1 ≠ 0 ∧ u ≠ 0 ∧
        orderTwentyFiveFiveDivisionFactor c d = 0 ∧
        u ^ 12 * E.Δ = (orderFiveCurve c).Δ ∧
        u ^ 4 * E.c₄ = (orderFiveCurve c).c₄ := by
  obtain ⟨c, d, u, hc, hcfactor, hd, hdfactor, hu,
      hrelation, hdisc, hc₄⟩ :=
    orderTwentyFive_two_orderFive_parameters_package E P h25
  obtain ⟨d', hd', hdfactor', hquintic⟩ :=
    exists_orderTwentyFiveFiveDivisionFactor_of_relation
      hd hdfactor hrelation
  exact ⟨c, d', u, hc, hcfactor, hd', hdfactor', hu,
    hquintic, hdisc, hc₄⟩

end MazurTorsion.Kubert
