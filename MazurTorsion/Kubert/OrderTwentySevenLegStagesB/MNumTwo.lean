/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegStagesA.NumeratorSquare
public import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TTwo
public import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.WTwoX
public import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Scalars
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination

/-!
# The second kernel numerator term

The second independently elaborated numerator term.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tl_mnum₂ {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 2
      * (tlD0 f ξ + tlD1 f ξ) =
      ((((((tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ) + (tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ)) +
        ((tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ) + (tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ))) +
        (((tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ)) +
        ((tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ) + (tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ)))) +
        ((((tlWTwoXP0c16 f ξ + tlWTwoXP0c17 f ξ) + (tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ)) +
        ((tlWTwoXP0c20 f ξ + tlWTwoXP1c0 f ξ) + (tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ))) +
        (((tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ) + (tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ)) +
        ((tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ) + (tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ))))) +
        (((((tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ) + (tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ)) +
        ((tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ) + (tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ))) +
        (((tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ) + (tlWTwoXP1c21 f ξ + tlWTwoXP2c0 f ξ)) +
        ((tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ) + (tlWTwoXP2c3 f ξ + tlWTwoXP2c4 f ξ)))) +
        ((((tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ) + (tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ)) +
        ((tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ) + (tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ))) +
        (((tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ) + (tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ)) +
        ((tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ) + (tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ)))))) +
        (((((tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ) + (tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ)) +
        ((tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ) + (tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ))) +
        (((tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ) + (tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ)) +
        ((tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ) + (tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ)))) +
        ((((tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ) + (tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ)) +
        ((tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ) + (tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ))) +
        (((tlWTwoXP4c0 f ξ + tlWTwoXP4c1 f ξ) + (tlWTwoXP4c2 f ξ + tlWTwoXP4c3 f ξ)) +
        ((tlWTwoXP4c4 f ξ + tlWTwoXP4c5 f ξ) + tlWTwoXP4c6 f ξ)))) := by
  linear_combination
    -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) * (tlD0 f ξ + tlD1 f ξ) * tlNSq_val hT + -(3 * f * (f
      - 1) ^ 2 * (f ^ 2 + f - 1)) * tlTTwo_val hT - ((((((((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) +
      (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) + ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ +
      tlTTwoP0c7 f ξ))) + (((tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ) + (tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ))
      + ((tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ) + (tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ)))) + ((((tlTTwoP1c6
      f ξ + tlTTwoP1c7 f ξ) + (tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ)) + ((tlTTwoP1c10 f ξ + tlTTwoP1c11
      f ξ) + (tlTTwoP1c12 f ξ + tlTTwoP2c0 f ξ))) + (((tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ) +
      (tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ)) + ((tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ) + (tlTTwoP2c7 f ξ +
      tlTTwoP2c8 f ξ))))) + (((((tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ) + (tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ)) + ((tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ) + (tlTTwoP2c15 f ξ + tlTTwoP3c0 f
      ξ))) + (((tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ) + (tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ)) +
      ((tlTTwoP3c5 f ξ + tlTTwoP3c6 f ξ) + (tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ)))) + ((((tlTTwoP3c9 f
      ξ + tlTTwoP3c10 f ξ) + (tlTTwoP3c11 f ξ + tlTTwoP4c0 f ξ)) + ((tlTTwoP4c1 f ξ + tlTTwoP4c2 f
      ξ) + (tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ))) + (((tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ) + (tlTTwoP4c7
      f ξ + tlTTwoP4c8 f ξ)) + ((tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ) + (tlTTwoP4c11 f ξ +
      tlTTwoP4c12 f ξ)))))) + ((((((tlTTwoP4c13 f ξ + tlTTwoP5c0 f ξ) + (tlTTwoP5c1 f ξ +
      tlTTwoP5c2 f ξ)) + ((tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ) + (tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ)))
      + (((tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ) + (tlTTwoP5c9 f ξ + tlTTwoP5c10 f ξ)) + ((tlTTwoP5c11
      f ξ + tlTTwoP5c12 f ξ) + (tlTTwoP5c13 f ξ + tlTTwoP6c0 f ξ)))) + ((((tlTTwoP6c1 f ξ +
      tlTTwoP6c2 f ξ) + (tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ)) + ((tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ) +
      (tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ))) + (((tlTTwoP6c9 f ξ + tlTTwoP7c0 f ξ) + (tlTTwoP7c1 f ξ
      + tlTTwoP7c2 f ξ)) + ((tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ) + (tlTTwoP7c5 f ξ + tlTTwoP7c6 f
      ξ))))) + (((((tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ) + (tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ)) +
      ((tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ) + (tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ))) + (((tlTTwoP8c2 f
      ξ + tlTTwoP8c3 f ξ) + (tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ)) + ((tlTTwoP8c6 f ξ + tlTTwoP8c7 f
      ξ) + (tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ)))) + ((((tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ) +
      (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) + ((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ
      + tlTTwoP9c3 f ξ))) + (((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f
      ξ)) + ((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ))))))) +
      ((((((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)) +
      ((tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) + (tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ))) +
      (((tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ) + (tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ)) + ((tlTTwoP10c6
      f ξ + tlTTwoP10c7 f ξ) + (tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ)))) + ((((tlTTwoP10c10 f ξ +
      tlTTwoP10c11 f ξ) + (tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ)) + ((tlTTwoP11c2 f ξ + tlTTwoP11c3 f
      ξ) + (tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ))) + (((tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ) +
      (tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ)) + ((tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ) +
      (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ))))) + (((((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) +
      (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) + ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f
      ξ + tlTTwoP12c7 f ξ))) + (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ)) + ((tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ) + (tlTTwoP13c0 f ξ + tlTTwoP13c1
      f ξ)))) + ((((tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ) + (tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ)) +
      ((tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ) + (tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ))) +
      ((tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ) + tlTTwoP13c12 f ξ))))) * tl_brM2 f + tlWTwoX_val hT


end MazurTorsion.Kubert

end
