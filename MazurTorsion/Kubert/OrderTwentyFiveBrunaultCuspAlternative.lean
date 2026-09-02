/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitPadic

/-!
# The three-adic cusp alternative for the order-twenty-five orbit

Although the scalar parameters `n` and `5 / n` satisfy a useful integrality
dichotomy, but that statement alone does not transport a rational point of
the Lehmer cover.  This file therefore makes no Fricke-descent assertion.

Instead, it combines the checked orbit-valuation classification with the
checked finite-field Brunault obstruction.  An open rational Lécacheux orbit
cannot have valuation vector zero: in that case its first and third
coordinates would give a three-unit zero of Brunault's polynomial.  Thus
every such orbit lies in one of the five explicit nonzero cusp rays.  A
downstream unconditional exclusion must rule out these cusp disks using
genuinely global information.
-/

namespace MazurTorsion.Kubert

/-- A nonexceptional rational Lécacheux orbit satisfying all five cyclic
relations and the norm-one relation has one of the five nonzero three-adic
cusp-ray valuation vectors.

The zero valuation vector is excluded by Brunault's equation and its checked
enumeration over `F₃`; rational nonvanishing is never used as a substitute
for nonzero reduction. -/
theorem orderTwentyFiveOrbit_padicValuation_is_cuspRay
    (a b c d e : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (haOne : a ≠ 1)
    (h₀ : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h₁ : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h₂ : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h₃ : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h₄ : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    ∃ t : ℤ, 0 < t ∧
      ((padicValRat 3 a = 3 * t ∧ padicValRat 3 b = -t ∧
          padicValRat 3 c = t ∧ padicValRat 3 d = -2 * t ∧
          padicValRat 3 e = -t) ∨
        (padicValRat 3 a = -t ∧ padicValRat 3 b = t ∧
          padicValRat 3 c = -2 * t ∧ padicValRat 3 d = -t ∧
          padicValRat 3 e = 3 * t) ∨
        (padicValRat 3 a = t ∧ padicValRat 3 b = -2 * t ∧
          padicValRat 3 c = -t ∧ padicValRat 3 d = 3 * t ∧
          padicValRat 3 e = -t) ∨
        (padicValRat 3 a = -2 * t ∧ padicValRat 3 b = -t ∧
          padicValRat 3 c = 3 * t ∧ padicValRat 3 d = -t ∧
          padicValRat 3 e = t) ∨
        (padicValRat 3 a = -t ∧ padicValRat 3 b = 3 * t ∧
          padicValRat 3 c = -t ∧ padicValRat 3 d = t ∧
          padicValRat 3 e = -2 * t)) := by
  rcases orderTwentyFiveOrbit_padicValuation_classification
      a b c d e ha hb hc hd he h₀ h₁ h₂ h₃ h₄ h₅ with hzero | hcusp
  · obtain ⟨haVal, -, hcVal, -, -⟩ := hzero
    have haUnit : orderTwentyFiveRatIsThreeUnit a :=
      (orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero a ha).mpr haVal
    have hcUnit : orderTwentyFiveRatIsThreeUnit c :=
      (orderTwentyFiveRatIsThreeUnit_iff_padicValRat_eq_zero c hc).mpr hcVal
    have hnegcUnit : orderTwentyFiveRatIsThreeUnit (-c) :=
      (orderTwentyFiveRatIsThreeUnit_neg_iff c).mpr hcUnit
    have hpoly : orderTwentyFiveBrunaultPolynomial a (-c) = 0 :=
      orderTwentyFiveBrunaultPolynomial_eq_zero_of_orbit
        a b c d e haOne h₀ h₁ h₂ h₃ h₄ h₅
    exact (orderTwentyFiveBrunaultPolynomial_ne_zero_of_three_units
      a (-c) haUnit hnegcUnit hpoly).elim
  · exact hcusp

end MazurTorsion.Kubert
