/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Arithmetic.PointOrderReduction
import MazurTorsion.Arithmetic.OrderTwentyTwentyFour
import MazurTorsion.Kubert.OrderFourteen
import MazurTorsion.Kubert.OrderFifteen
import MazurTorsion.Kubert.OrderSixteenReduction

/-!
# Rational point orders after five composite-order exclusions

The elementary divisor reduction in `PointOrderReduction` asks callers to
exclude every large prime order and all eleven minimal composite Kubert
orders.  Orders fourteen, fifteen, sixteen, twenty, and twenty-four are
now unconditional.  This module packages those results into the reduction
interface, leaving callbacks only for large prime orders and the six
remaining members of `kubertForbiddenOrders`.

The callbacks are stated on `RationalTorsion E`, which is the weakest useful
interface: every point occurring in an exact finite-order obstruction already
belongs to that subgroup.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The composite point orders still left after the five unconditional
small-level exclusions integrated in this module. -/
def remainingKubertForbiddenOrders : Finset ℕ :=
  {18, 21, 25, 27, 35, 49}

omit [E.IsElliptic] in
/-- Inclusion of rational torsion into the rational point group preserves
exact additive order. -/
lemma addOrderOf_coe_rationalTorsion (x : RationalTorsion E) :
    addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_map_dvd
      (AddSubgroup.subtype (AddCommGroup.torsion (E⁄ℚ).Point)) x
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    apply Subtype.ext
    exact addOrderOf_nsmul_eq_zero (x : (E⁄ℚ).Point)

omit [E.IsElliptic] in
private lemma rationalTorsion_isOfFinAddOrder
    (x : RationalTorsion E) :
    IsOfFinAddOrder x := by
  obtain ⟨n, hn, hnx⟩ :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mp x.property
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  exact ⟨n, hn, Subtype.ext hnx⟩

/-- A rational torsion point has Mazur-allowed order once the still-open
large-prime and Kubert orders other than sixteen are excluded.

The order-sixteen callback is deliberately absent: it is discharged by
`Kubert.rationalPoint_addOrderOf_ne_sixteen`. -/
theorem rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_sixteen
    (x : RationalTorsion E)
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, d ≠ 16 →
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    addOrderOf x ∈ cyclicOrders := by
  apply addOrderOf_mem_cyclicOrders_of_order_obstructions x
    (rationalTorsion_isOfFinAddOrder E x) hprime
  intro d hd y
  by_cases hd16 : d = 16
  · subst d
    intro hy
    apply Kubert.rationalPoint_addOrderOf_ne_sixteen E
      (y : (E⁄ℚ).Point)
    rw [addOrderOf_coe_rationalTorsion E y, hy]
  · exact hkubert d hd hd16 y

/-- Pointwise order classification for the entire rational torsion subgroup,
with order sixteen discharged internally.  This is the callback shape used by
the downstream finite-group and cardinality reductions. -/
theorem rationalTorsion_orders_mem_cyclicOrders_of_obstructions_except_sixteen
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, d ≠ 16 →
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders :=
  fun x ↦
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_sixteen
      E x hprime hkubert

/-- A rational torsion point has Mazur-allowed order once the still-open
large-prime and Kubert orders other than fourteen and sixteen are excluded.
Both discharged orders are absent from the callback. -/
theorem rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_fourteen_sixteen
    (x : RationalTorsion E)
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, d ≠ 14 → d ≠ 16 →
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    addOrderOf x ∈ cyclicOrders := by
  apply
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_sixteen
      E x hprime
  intro d hd hd16 y
  by_cases hd14 : d = 14
  · subst d
    intro hy
    apply Kubert.rationalPoint_addOrderOf_ne_fourteen E
      (y : (E⁄ℚ).Point)
    rw [addOrderOf_coe_rationalTorsion E y, hy]
  · exact hkubert d hd hd14 hd16 y

/-- Pointwise order classification for rational torsion, with orders
fourteen and sixteen discharged internally. -/
theorem rationalTorsion_orders_mem_cyclicOrders_of_obstructions_except_fourteen_sixteen
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, d ≠ 14 → d ≠ 16 →
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders :=
  fun x ↦
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_fourteen_sixteen
      E x hprime hkubert

/-- A rational torsion point has Mazur-allowed order once the still-open
large-prime and Kubert orders other than fourteen, fifteen, and sixteen are
excluded.  All three discharged orders are absent from the callback. -/
theorem rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_fourteen_fifteen_sixteen
    (x : RationalTorsion E)
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, d ≠ 14 → d ≠ 15 → d ≠ 16 →
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    addOrderOf x ∈ cyclicOrders := by
  apply
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_fourteen_sixteen
      E x hprime
  intro d hd hd14 hd16 y
  by_cases hd15 : d = 15
  · subst d
    intro hy
    apply Kubert.rationalPoint_addOrderOf_ne_fifteen E
      (y : (E⁄ℚ).Point)
    rw [addOrderOf_coe_rationalTorsion E y, hy]
  · exact hkubert d hd hd14 hd15 hd16 y

/-- Pointwise order classification for rational torsion, with orders
fourteen, fifteen, and sixteen discharged internally. -/
theorem rationalTorsion_orders_mem_cyclicOrders_of_obstructions_except_fourteen_fifteen_sixteen
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ kubertForbiddenOrders, d ≠ 14 → d ≠ 15 → d ≠ 16 →
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders :=
  fun x ↦
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_fourteen_fifteen_sixteen
      E x hprime hkubert

/-- A rational torsion point has Mazur-allowed order once large prime
orders and the six genuinely remaining composite orders are excluded.
The already proved orders `14`, `15`, `16`, `20`, and `24` are absent
from this callback. -/
theorem rationalTorsion_addOrderOf_mem_cyclicOrders_of_remaining_obstructions
    (x : RationalTorsion E)
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ remainingKubertForbiddenOrders,
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    addOrderOf x ∈ cyclicOrders := by
  apply
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_obstructions_except_fourteen_fifteen_sixteen
      E x hprime
  intro d hd hd14 hd15 hd16 y
  by_cases hd20 : d = 20
  · subst d
    intro hy
    apply Kubert.rationalPoint_addOrderOf_ne_twenty E
      (y : (E⁄ℚ).Point)
    rw [addOrderOf_coe_rationalTorsion E y, hy]
  by_cases hd24 : d = 24
  · subst d
    intro hy
    apply Kubert.rationalPoint_addOrderOf_ne_twenty_four E
      (y : (E⁄ℚ).Point)
    rw [addOrderOf_coe_rationalTorsion E y, hy]
  apply hkubert d
  simpa [remainingKubertForbiddenOrders, kubertForbiddenOrders,
    hd14, hd15, hd16, hd20, hd24] using hd

/-- Pointwise order classification for rational torsion with only the six
remaining composite callbacks and the large-prime callback exposed. -/
theorem rationalTorsion_orders_mem_cyclicOrders_of_remaining_obstructions
    (hprime :
      ∀ (p : ℕ), p.Prime → 11 ≤ p →
        ∀ y : RationalTorsion E, addOrderOf y ≠ p)
    (hkubert :
      ∀ d ∈ remainingKubertForbiddenOrders,
        ∀ y : RationalTorsion E, addOrderOf y ≠ d) :
    ∀ x : RationalTorsion E, addOrderOf x ∈ cyclicOrders :=
  fun x ↦
    rationalTorsion_addOrderOf_mem_cyclicOrders_of_remaining_obstructions
      E x hprime hkubert

end MazurTorsion
