/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultMarkedPolynomial
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitIntegrality
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitPadic
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFiveCertificate
import MazurTorsion.Kubert.OrderTwentyFiveMarkedExclusionBridge

/-!
# The explicit marked-point boundary in the order-twenty-five exclusion

The checked Brunault and finite-field arguments exclude an exact-order-25
marked point as soon as its two Brunault coordinates are three-adic units.
This module records that direct implication.  It also gives a
single-orbit-coordinate boundary: valuation zero for the first raw coordinate
forces all five coordinates to be units through the checked cyclic equations.
A stronger five-coordinate integrality premise suffices as well, using the
checked norm-one relation to obtain nonzero reductions.

Neither premise follows from rational nonvanishing: cusp disks can carry
nonzero valuations whose sum is zero.  An unconditional endpoint must still
supply the minimal two-unit premise from a global integral-model, descent, or
cusp-exclusion argument.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The direct uniform marked-point input used by the Brunault bridge: the
two Brunault coordinates attached to every exact-order-25 marked
Tate point are three-adic units.  In particular, their canonical reductions
modulo three are defined and nonzero. -/
def orderTwentyFiveMarkedBrunaultPairThreeUnits : Prop :=
  ∀ (b c : ℚ) (_hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0),
    addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25 →
      orderTwentyFiveRatIsThreeUnit (orderTwentyFiveBrunaultU b c) ∧
        orderTwentyFiveRatIsThreeUnit (orderTwentyFiveBrunaultV b c)

/-- The single-coordinate form of the missing global input: the first raw
Lécacheux coordinate of every exact-order-25 marked Tate point has
three-adic valuation zero.  The raw relation certificates and valuation
classifier upgrade this premise to five explicit units. -/
def orderTwentyFiveMarkedRawOrbitFirstPadicValZero : Prop :=
  ∀ (b c : ℚ) (_hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0),
    addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25 →
      padicValRat 3
        (orderTwentyFiveRawOrbitXZero (b / c) (c ^ 2 / (b - c))) = 0

/-- A stronger marked-point input: all five raw Lécacheux orbit units are
integral at three.  The norm-one relation upgrades these values to units and
therefore implies `orderTwentyFiveMarkedBrunaultPairThreeUnits`. -/
def orderTwentyFiveMarkedRawOrbitThreeIntegrality : Prop :=
  ∀ (b c : ℚ) (_hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0),
    addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25 →
      orderTwentyFiveRatIsThreeIntegral
          (orderTwentyFiveRawOrbitXZero (b / c) (c ^ 2 / (b - c))) ∧
        orderTwentyFiveRatIsThreeIntegral
          (orderTwentyFiveRawOrbitXOne (b / c) (c ^ 2 / (b - c))) ∧
        orderTwentyFiveRatIsThreeIntegral
          (orderTwentyFiveRawOrbitXTwo (b / c) (c ^ 2 / (b - c))) ∧
        orderTwentyFiveRatIsThreeIntegral
          (orderTwentyFiveRawOrbitXThree (b / c) (c ^ 2 / (b - c))) ∧
        orderTwentyFiveRatIsThreeIntegral
          (orderTwentyFiveRawOrbitXFour (b / c) (c ^ 2 / (b - c)))

/-- Five-coordinate three-integrality at one marked point supplies the two
three-adic units required by the Brunault finite-field contradiction. -/
private theorem orderTwentyFiveBrunaultPair_threeUnits_of_marked_order_and_rawOrbit_threeIntegral
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    (h0 : orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveRawOrbitXZero (b / c) (c ^ 2 / (b - c))))
    (h1 : orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveRawOrbitXOne (b / c) (c ^ 2 / (b - c))))
    (h2 : orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveRawOrbitXTwo (b / c) (c ^ 2 / (b - c))))
    (h3 : orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveRawOrbitXThree (b / c) (c ^ 2 / (b - c))))
    (h4 : orderTwentyFiveRatIsThreeIntegral
      (orderTwentyFiveRawOrbitXFour (b / c) (c ^ 2 / (b - c)))) :
    orderTwentyFiveRatIsThreeUnit (orderTwentyFiveBrunaultU b c) ∧
      orderTwentyFiveRatIsThreeUnit (orderTwentyFiveBrunaultV b c) := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hopen : OrderTwentyFiveRawOrbitOpenCertificate r s := by
    simpa only [r, s] using
      orderTwentyFiveRawOrbit_openCertificate_of_marked_order
        b c hb h00 horder
  have hnorm :
      orderTwentyFiveOrbitRelationFive
          (orderTwentyFiveRawOrbitXZero r s)
          (orderTwentyFiveRawOrbitXOne r s)
          (orderTwentyFiveRawOrbitXTwo r s)
          (orderTwentyFiveRawOrbitXThree r s)
          (orderTwentyFiveRawOrbitXFour r s) = 0 :=
    orderTwentyFiveRawOrbit_relationFive_eq_zero
      r s hopen.r_ne_zero hopen.s_ne_zero hopen.r_sub_s_ne_zero
      hopen.s_sub_one_ne_zero hopen.seven_factor_ne_zero
      hopen.eight_factor_ne_zero hopen.eleven_factor_ne_zero
      hopen.twelve_factor_ne_zero hopen.yOne_denominator_ne_zero
      hopen.yTwo_denominator_ne_zero hopen.yFour_denominator_ne_zero
      hopen.yEight_denominator_ne_zero hopen.yNine_denominator_ne_zero
      hopen.sutherland_eq_zero
  have hpair :=
    orderTwentyFiveBrunaultPair_threeUnits_of_orbit_integral
      (orderTwentyFiveRawOrbitXZero r s)
      (orderTwentyFiveRawOrbitXOne r s)
      (orderTwentyFiveRawOrbitXTwo r s)
      (orderTwentyFiveRawOrbitXThree r s)
      (orderTwentyFiveRawOrbitXFour r s)
      (by simpa only [r, s] using h0)
      (by simpa only [r, s] using h1)
      (by simpa only [r, s] using h2)
      (by simpa only [r, s] using h3)
      (by simpa only [r, s] using h4) hnorm
  obtain ⟨hU, hV⟩ :=
    orderTwentyFiveBrunault_coordinates_eq_rawOrbit_of_marked_order
      b c hb h00 horder
  simpa only [r, s, hU, hV] using hpair

/-- The stronger five-coordinate integrality boundary implies the direct
two-unit boundary. -/
theorem orderTwentyFiveMarkedBrunaultPairThreeUnits_of_rawOrbitThreeIntegrality
    (hIntegral : orderTwentyFiveMarkedRawOrbitThreeIntegrality) :
    orderTwentyFiveMarkedBrunaultPairThreeUnits := by
  intro b c hb h00 horder
  obtain ⟨h0, h1, h2, h3, h4⟩ := hIntegral b c hb h00 horder
  exact
    orderTwentyFiveBrunaultPair_threeUnits_of_marked_order_and_rawOrbit_threeIntegral
      b c hb h00 horder h0 h1 h2 h3 h4

/-- A zero first raw-orbit valuation supplies the two Brunault units needed
by the finite-field obstruction.  All integrality and nonzero-reduction steps
are discharged through the checked raw cyclic equations. -/
theorem orderTwentyFiveMarkedBrunaultPairThreeUnits_of_firstRawOrbitPadicValZero
    (hVal : orderTwentyFiveMarkedRawOrbitFirstPadicValZero) :
    orderTwentyFiveMarkedBrunaultPairThreeUnits := by
  intro b c hb h00 horder
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hopen : OrderTwentyFiveRawOrbitOpenCertificate r s := by
    simpa only [r, s] using
      orderTwentyFiveRawOrbit_openCertificate_of_marked_order
        b c hb h00 horder
  have hfirst : padicValRat 3 (orderTwentyFiveRawOrbitXZero r s) = 0 := by
    simpa only [r, s] using hVal b c hb h00 horder
  obtain ⟨h0, -, h2, -, -⟩ :=
    orderTwentyFiveRawOrbit_threeUnits_of_openCertificate
      r s hopen hfirst
  obtain ⟨hU, hV⟩ :=
    orderTwentyFiveBrunault_coordinates_eq_rawOrbit_of_marked_order
      b c hb h00 horder
  rw [hU, hV]
  exact ⟨h0, (orderTwentyFiveRatIsThreeUnit_neg_iff _).mpr h2⟩

/-- A marked exact-order-25 point whose two Brunault coordinates are
three-adic units contradicts the checked characteristic-zero identity and
the kernel-checked enumeration over `F₃`. -/
private theorem orderTwentyFive_false_of_marked_order_and_brunaultPair_threeUnits
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    (hU : orderTwentyFiveRatIsThreeUnit
      (orderTwentyFiveBrunaultU b c))
    (hV : orderTwentyFiveRatIsThreeUnit
      (orderTwentyFiveBrunaultV b c)) :
    False := by
  exact
    (orderTwentyFiveBrunaultPolynomial_ne_zero_of_three_units
      (orderTwentyFiveBrunaultU b c)
      (orderTwentyFiveBrunaultV b c) hU hV)
    (orderTwentyFiveBrunaultPolynomial_eq_zero_of_marked_order
      b c hb h00 horder)

/-- The marked-pair three-unit premise, together with the checked Brunault
and finite-field certificates, excludes rational order twenty-five. -/
theorem rationalPoint_addOrderOf_ne_twentyFive_of_markedBrunaultPairThreeUnits
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hUnits : orderTwentyFiveMarkedBrunaultPairThreeUnits) :
    addOrderOf P ≠ 25 := by
  apply rationalPoint_addOrderOf_ne_twentyFive_of_marked_exclusion E P
  intro b c hb h00 horder
  obtain ⟨hU, hV⟩ := hUnits b c hb h00 horder
  exact orderTwentyFive_false_of_marked_order_and_brunaultPair_threeUnits
    b c hb h00 horder hU hV

/-- The stronger marked-orbit integrality premise excludes rational order
twenty-five through the direct pair-unit boundary. -/
theorem rationalPoint_addOrderOf_ne_twentyFive_of_markedRawOrbitThreeIntegrality
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hIntegral : orderTwentyFiveMarkedRawOrbitThreeIntegrality) :
    addOrderOf P ≠ 25 :=
  rationalPoint_addOrderOf_ne_twentyFive_of_markedBrunaultPairThreeUnits
    E P
    (orderTwentyFiveMarkedBrunaultPairThreeUnits_of_rawOrbitThreeIntegrality
      hIntegral)

/-- The explicit single-valuation global premise, together with the checked
raw orbit, Brunault polynomial, and `F₃` certificates, excludes rational order
twenty-five. -/
theorem rationalPoint_addOrderOf_ne_twentyFive_of_firstRawOrbitPadicValZero
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point)
    (hVal : orderTwentyFiveMarkedRawOrbitFirstPadicValZero) :
    addOrderOf P ≠ 25 :=
  rationalPoint_addOrderOf_ne_twentyFive_of_markedBrunaultPairThreeUnits
    E P
    (orderTwentyFiveMarkedBrunaultPairThreeUnits_of_firstRawOrbitPadicValZero
      hVal)

end MazurTorsion.Kubert
