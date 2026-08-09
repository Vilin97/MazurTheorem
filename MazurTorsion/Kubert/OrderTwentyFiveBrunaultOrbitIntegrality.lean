/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultIntegrality
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate

/-!
# Three-adic units in the order-twenty-five Brunault orbit

The norm-one relation upgrades *integrality* of all five Lécacheux orbit
coordinates to valuation zero.  This is the arithmetic step needed before
reducing Brunault's two coordinates modulo three: rational nonvanishing alone
does not suffice.

The five integrality hypotheses in this file are intentional.  Near a
rational cusp, the five orbit coordinates can have nonzero valuations whose
sum is zero, so neither the cyclic orbit relations nor rational nonvanishing
proves these hypotheses.  A downstream integral-model or cusp-exclusion
argument must supply them.
-/

namespace MazurTorsion.Kubert

/-- The product of two rational numbers integral at three is integral at
three. -/
theorem orderTwentyFiveRatIsThreeIntegral_mul
    {q r : ℚ}
    (hq : orderTwentyFiveRatIsThreeIntegral q)
    (hr : orderTwentyFiveRatIsThreeIntegral r) :
    orderTwentyFiveRatIsThreeIntegral (q * r) := by
  have hqDen : (q.den : ℤ) ≠ 0 := by
    exact_mod_cast q.den_nz
  have hrDen : (r.den : ℤ) ≠ 0 := by
    exact_mod_cast r.den_nz
  apply orderTwentyFiveRatIsThreeIntegral_of_eq_div
    (q * r) (q.num * r.num) ((q.den : ℤ) * (r.den : ℤ))
    (mul_ne_zero hqDen hrDen)
  · calc
      q * r =
          ((q.num : ℚ) / (q.den : ℚ)) *
            ((r.num : ℚ) / (r.den : ℚ)) := by
        rw [Rat.num_div_den q, Rat.num_div_den r]
      _ =
          ((q.num * r.num : ℤ) : ℚ) /
            (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ℚ) := by
        push_cast
        ring
  · simpa only [Int.cast_mul, Int.cast_natCast] using mul_ne_zero hq hr

/-- If two three-integral rational numbers multiply to one, the first is a
three-adic unit.  The proof clears their normalized denominators over the
integers before reducing modulo three. -/
theorem orderTwentyFiveRatIsThreeUnit_of_mul_eq_one
    {q r : ℚ}
    (hq : orderTwentyFiveRatIsThreeIntegral q)
    (hr : orderTwentyFiveRatIsThreeIntegral r)
    (hqr : q * r = 1) :
    orderTwentyFiveRatIsThreeUnit q := by
  refine ⟨hq, ?_⟩
  have hqDen : (q.den : ℚ) ≠ 0 := by
    exact_mod_cast q.den_nz
  have hrDen : (r.den : ℚ) ≠ 0 := by
    exact_mod_cast r.den_nz
  have hcrossRat :
      (q.num : ℚ) * (r.num : ℚ) =
        (q.den : ℚ) * (r.den : ℚ) := by
    rw [← Rat.num_div_den q, ← Rat.num_div_den r] at hqr
    field_simp [hqDen, hrDen] at hqr
    exact hqr
  have hcross :
      q.num * r.num = (q.den : ℤ) * (r.den : ℤ) := by
    exact_mod_cast hcrossRat
  have hcrossThree :
      (q.num : ZMod 3) * (r.num : ZMod 3) =
        (q.den : ZMod 3) * (r.den : ZMod 3) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ ↦ (z : ZMod 3)) hcross
  intro hqNum
  rw [hqNum, zero_mul] at hcrossThree
  exact (mul_ne_zero hq hr) hcrossThree.symm

private theorem orderTwentyFiveRatIsThreeUnit_of_five_product_eq_one_left
    (a b c d e : ℚ)
    (ha : orderTwentyFiveRatIsThreeIntegral a)
    (hb : orderTwentyFiveRatIsThreeIntegral b)
    (hc : orderTwentyFiveRatIsThreeIntegral c)
    (hd : orderTwentyFiveRatIsThreeIntegral d)
    (he : orderTwentyFiveRatIsThreeIntegral e)
    (hproduct : a * b * c * d * e = 1) :
    orderTwentyFiveRatIsThreeUnit a := by
  have hrest :
      orderTwentyFiveRatIsThreeIntegral (b * c * d * e) :=
    orderTwentyFiveRatIsThreeIntegral_mul
      (orderTwentyFiveRatIsThreeIntegral_mul
        (orderTwentyFiveRatIsThreeIntegral_mul hb hc) hd) he
  apply orderTwentyFiveRatIsThreeUnit_of_mul_eq_one ha hrest
  calc
    a * (b * c * d * e) = a * b * c * d * e := by ring
    _ = 1 := hproduct

/-- If all five Lécacheux orbit coordinates are integral at three and their
norm is one, then all five are three-adic units.  Thus every coordinate has a
well-defined nonzero reduction, not merely a nonzero rational value. -/
theorem orderTwentyFiveBrunaultOrbit_threeUnits_of_integral
    (a b c d e : ℚ)
    (ha : orderTwentyFiveRatIsThreeIntegral a)
    (hb : orderTwentyFiveRatIsThreeIntegral b)
    (hc : orderTwentyFiveRatIsThreeIntegral c)
    (hd : orderTwentyFiveRatIsThreeIntegral d)
    (he : orderTwentyFiveRatIsThreeIntegral e)
    (hnorm : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveRatIsThreeUnit a ∧
      orderTwentyFiveRatIsThreeUnit b ∧
      orderTwentyFiveRatIsThreeUnit c ∧
      orderTwentyFiveRatIsThreeUnit d ∧
      orderTwentyFiveRatIsThreeUnit e := by
  have hproduct : a * b * c * d * e = 1 := by
    exact sub_eq_zero.mp hnorm
  refine ⟨
    orderTwentyFiveRatIsThreeUnit_of_five_product_eq_one_left
      a b c d e ha hb hc hd he hproduct,
    ?_, ?_, ?_, ?_⟩
  · apply orderTwentyFiveRatIsThreeUnit_of_five_product_eq_one_left
      b c d e a hb hc hd he ha
    calc
      b * c * d * e * a = a * b * c * d * e := by ring
      _ = 1 := hproduct
  · apply orderTwentyFiveRatIsThreeUnit_of_five_product_eq_one_left
      c d e a b hc hd he ha hb
    calc
      c * d * e * a * b = a * b * c * d * e := by ring
      _ = 1 := hproduct
  · apply orderTwentyFiveRatIsThreeUnit_of_five_product_eq_one_left
      d e a b c hd he ha hb hc
    calc
      d * e * a * b * c = a * b * c * d * e := by ring
      _ = 1 := hproduct
  · apply orderTwentyFiveRatIsThreeUnit_of_five_product_eq_one_left
      e a b c d he ha hb hc hd
    calc
      e * a * b * c * d = a * b * c * d * e := by ring
      _ = 1 := hproduct

/-- Under the same integral norm-one hypotheses, all five canonical
reductions are explicitly nonzero in `ZMod 3`. -/
theorem orderTwentyFiveBrunaultOrbit_reductions_ne_zero_of_integral
    (a b c d e : ℚ)
    (ha : orderTwentyFiveRatIsThreeIntegral a)
    (hb : orderTwentyFiveRatIsThreeIntegral b)
    (hc : orderTwentyFiveRatIsThreeIntegral c)
    (hd : orderTwentyFiveRatIsThreeIntegral d)
    (he : orderTwentyFiveRatIsThreeIntegral e)
    (hnorm : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveRatReduction a ≠ 0 ∧
      orderTwentyFiveRatReduction b ≠ 0 ∧
      orderTwentyFiveRatReduction c ≠ 0 ∧
      orderTwentyFiveRatReduction d ≠ 0 ∧
      orderTwentyFiveRatReduction e ≠ 0 := by
  obtain ⟨haUnit, hbUnit, hcUnit, hdUnit, heUnit⟩ :=
    orderTwentyFiveBrunaultOrbit_threeUnits_of_integral
      a b c d e ha hb hc hd he hnorm
  exact ⟨
    orderTwentyFiveRatReduction_ne_zero haUnit,
    orderTwentyFiveRatReduction_ne_zero hbUnit,
    orderTwentyFiveRatReduction_ne_zero hcUnit,
    orderTwentyFiveRatReduction_ne_zero hdUnit,
    orderTwentyFiveRatReduction_ne_zero heUnit⟩

/-- The first and third orbit coordinates give Brunault's pair `(a,-c)`.
Five-coordinate integrality and norm one therefore put that pair in the
nonzero three-adic chart. -/
theorem orderTwentyFiveBrunaultPair_threeUnits_of_orbit_integral
    (a b c d e : ℚ)
    (ha : orderTwentyFiveRatIsThreeIntegral a)
    (hb : orderTwentyFiveRatIsThreeIntegral b)
    (hc : orderTwentyFiveRatIsThreeIntegral c)
    (hd : orderTwentyFiveRatIsThreeIntegral d)
    (he : orderTwentyFiveRatIsThreeIntegral e)
    (hnorm : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveRatIsThreeUnit a ∧
      orderTwentyFiveRatIsThreeUnit (-c) := by
  obtain ⟨haUnit, -, hcUnit, -, -⟩ :=
    orderTwentyFiveBrunaultOrbit_threeUnits_of_integral
      a b c d e ha hb hc hd he hnorm
  exact ⟨haUnit, (orderTwentyFiveRatIsThreeUnit_neg_iff c).mpr hcUnit⟩

/-- An integral norm-one orbit cannot also satisfy Brunault's
characteristic-zero equation: its first and third coordinates reduce to the
nonzero `F₃` chart excluded by the checked finite-field enumeration. -/
theorem orderTwentyFiveBrunaultPolynomial_ne_zero_of_orbit_integral
    (a b c d e : ℚ)
    (ha : orderTwentyFiveRatIsThreeIntegral a)
    (hb : orderTwentyFiveRatIsThreeIntegral b)
    (hc : orderTwentyFiveRatIsThreeIntegral c)
    (hd : orderTwentyFiveRatIsThreeIntegral d)
    (he : orderTwentyFiveRatIsThreeIntegral e)
    (hnorm : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveBrunaultPolynomial a (-c) ≠ 0 := by
  obtain ⟨haUnit, hcUnit⟩ :=
    orderTwentyFiveBrunaultPair_threeUnits_of_orbit_integral
      a b c d e ha hb hc hd he hnorm
  obtain ⟨haReduction, -, -, -, -⟩ :=
    orderTwentyFiveBrunaultOrbit_reductions_ne_zero_of_integral
      a b c d e ha hb hc hd he hnorm
  intro hpoly
  have hred := orderTwentyFiveBrunaultPolynomial_reduction_eq_zero
    a (-c) haUnit hcUnit hpoly
  exact orderTwentyFiveBrunaultPolynomial_f3_ne_zero_of_open
    (orderTwentyFiveRatReduction a)
    (orderTwentyFiveRatReduction (-c))
    ⟨haReduction, orderTwentyFiveRatReduction_ne_zero hcUnit⟩ hred

end MazurTorsion.Kubert
