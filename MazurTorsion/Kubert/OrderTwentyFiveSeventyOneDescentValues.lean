/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleCohomology
import MazurTorsion.Kubert.OrderTwentyFiveSeventyOneDescentFunctions

/-!
# Rational values of the order-twenty-five 71-descent functions

The cusp-divisor calculation selects the additive combination

`12g₀ - 14g₁ - 5g₂ + 11g₃`.

For multiplicative modular units this becomes

`r₀^12 r₃^11 / (r₁^14 r₂^5)`.

This file evaluates that expression on the five actual Brunault orbit units
attached to a hypothetical exact-order-25 marked Tate point.  It proves that
all five values are nonzero and that their cyclic product is one, first in
`ℚˣ` and then in the quotient by 71st powers.

This is an arithmetic evaluation boundary, not a geometric identification:
the remaining modular-curve argument must still identify the Brunault roots
with the global functions whose principal divisors were constructed in
`OrderTwentyFiveSeventyOneDescentFunctions`.

`orderTwentyFive_markedSeventyOneKummerClass_product_eq_one` is the named
downstream consumer.
-/

namespace MazurTorsion.Kubert

open scoped BigOperators

/-- The multiplicative translation of the determinant-`71` row combination,
applied at one place in a cyclic five-term orbit. -/
def orderTwentyFiveSeventyOneDescentUnit
    {G : Type*} [CommGroup G] (r : Fin 5 → G) (i : Fin 5) : G :=
  r i ^ 12 * r (i + 3) ^ 11 / (r (i + 1) ^ 14 * r (i + 2) ^ 5)

/-- The product of the five cyclic descent values is the fourth power of the
orbit norm. -/
theorem orderTwentyFiveSeventyOneDescentUnit_prod
    {G : Type*} [CommGroup G] (r : Fin 5 → G) :
    ∏ i, orderTwentyFiveSeventyOneDescentUnit r i = (∏ i, r i) ^ 4 := by
  have hshift (j : Fin 5) :
      ∏ i, r (i + j) = ∏ i, r i :=
    (Equiv.addRight j).bijective.prod_comp r
  unfold orderTwentyFiveSeventyOneDescentUnit
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  rw [Finset.prod_pow, Finset.prod_pow, Finset.prod_pow,
    Finset.prod_pow]
  rw [hshift 3, hshift 1, hshift 2]
  rw [← pow_add, ← pow_add]
  norm_num
  rw [show 23 = 4 + 19 by norm_num, pow_add, mul_div_cancel_right]

/-- The five rational Brunault roots, in deck-transformation order. -/
def orderTwentyFiveMarkedBrunaultOrbit (b c : ℚ) : Fin 5 → ℚ :=
  ![orderTwentyFiveBrunaultXZero b c,
    orderTwentyFiveBrunaultXOne b c,
    orderTwentyFiveBrunaultXTwo b c,
    orderTwentyFiveBrunaultXThree b c,
    orderTwentyFiveBrunaultXFour b c]

/-- Every entry of the marked Brunault orbit is nonzero under the exact-order
hypotheses. -/
theorem orderTwentyFiveMarkedBrunaultOrbit_ne_zero
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    (i : Fin 5) :
    orderTwentyFiveMarkedBrunaultOrbit b c i ≠ 0 := by
  obtain ⟨hr0, hr1, hr2, hr3, hr4⟩ :=
    orderTwentyFiveBrunault_orbit_units_ne_zero b c hb h00 horder
  fin_cases i <;>
    simp_all [orderTwentyFiveMarkedBrunaultOrbit]

/-- The Brunault orbit lifted canonically to rational units. -/
def orderTwentyFiveMarkedBrunaultOrbitUnit
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    Fin 5 → ℚˣ :=
  fun i => Units.mk0 (orderTwentyFiveMarkedBrunaultOrbit b c i)
    (orderTwentyFiveMarkedBrunaultOrbit_ne_zero b c hb h00 horder i)

/-- The product of the five lifted Brunault roots is one. -/
theorem orderTwentyFiveMarkedBrunaultOrbitUnit_prod_eq_one
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    ∏ i, orderTwentyFiveMarkedBrunaultOrbitUnit b c hb h00 horder i = 1 := by
  apply Units.ext
  have hnorm :=
    orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
      b c hb h00 horder
  simp only [orderTwentyFiveOrbitRelationFive] at hnorm
  have hproduct := sub_eq_zero.mp hnorm
  simpa [orderTwentyFiveMarkedBrunaultOrbitUnit,
    orderTwentyFiveMarkedBrunaultOrbit, Fin.prod_univ_succ,
    mul_assoc] using hproduct

/-- The five evaluated determinant-`71` combinations multiply to one in
`ℚˣ`. -/
theorem orderTwentyFive_markedSeventyOneDescentUnit_product_eq_one
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    ∏ i, orderTwentyFiveSeventyOneDescentUnit
      (orderTwentyFiveMarkedBrunaultOrbitUnit b c hb h00 horder) i = 1 := by
  rw [orderTwentyFiveSeventyOneDescentUnit_prod,
    orderTwentyFiveMarkedBrunaultOrbitUnit_prod_eq_one]
  norm_num

/-- The class modulo rational 71st powers of one cyclically evaluated
descent unit. -/
def orderTwentyFiveMarkedSeventyOneKummerClass
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    (i : Fin 5) :
    AlgebraicGeometry.FiniteFlatCommGroupScheme.UnitKummerClasses ℚ 71 :=
  QuotientGroup.mk
    (orderTwentyFiveSeventyOneDescentUnit
      (orderTwentyFiveMarkedBrunaultOrbitUnit b c hb h00 horder) i)

/-- The five explicit rational 71-Kummer classes satisfy the norm-one cyclic
product relation.  This is the arithmetic consumer of the evaluated descent
units. -/
theorem orderTwentyFive_markedSeventyOneKummerClass_product_eq_one
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    ∏ i, orderTwentyFiveMarkedSeventyOneKummerClass
      b c hb h00 horder i = 1 := by
  simp only [orderTwentyFiveMarkedSeventyOneKummerClass]
  rw [← QuotientGroup.mk_prod,
    orderTwentyFive_markedSeventyOneDescentUnit_product_eq_one]
  exact QuotientGroup.mk_one _

end MazurTorsion.Kubert
