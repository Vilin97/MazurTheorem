/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOneSteps0To4
public import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.TOneSteps5To9
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination

/-!
# The first-power product value

The aggregate first-power product identity.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tlTOne_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f ξ +
      tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ + tlDSqP0c9 f ξ)) *
      ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        (((tlTOneP0c8 f ξ + tlTOneP1c0 f ξ) + (tlTOneP1c1 f ξ + tlTOneP1c2 f ξ)) +
        ((tlTOneP1c3 f ξ + tlTOneP1c4 f ξ) + (tlTOneP1c5 f ξ + tlTOneP1c6 f ξ)))) +
        ((((tlTOneP1c7 f ξ + tlTOneP1c8 f ξ) + (tlTOneP1c9 f ξ + tlTOneP2c0 f ξ)) +
        ((tlTOneP2c1 f ξ + tlTOneP2c2 f ξ) + (tlTOneP2c3 f ξ + tlTOneP2c4 f ξ))) +
        (((tlTOneP2c5 f ξ + tlTOneP2c6 f ξ) + (tlTOneP2c7 f ξ + tlTOneP2c8 f ξ)) +
        ((tlTOneP2c9 f ξ + tlTOneP2c10 f ξ) + (tlTOneP2c11 f ξ + tlTOneP3c0 f ξ))))) +
        (((((tlTOneP3c1 f ξ + tlTOneP3c2 f ξ) + (tlTOneP3c3 f ξ + tlTOneP3c4 f ξ)) +
        ((tlTOneP3c5 f ξ + tlTOneP3c6 f ξ) + (tlTOneP3c7 f ξ + tlTOneP3c8 f ξ))) +
        (((tlTOneP3c9 f ξ + tlTOneP3c10 f ξ) + (tlTOneP3c11 f ξ + tlTOneP3c12 f ξ)) +
        ((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)))) +
        ((((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ)) +
        ((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ))) +
        (((tlTOneP4c12 f ξ + tlTOneP5c0 f ξ) + (tlTOneP5c1 f ξ + tlTOneP5c2 f ξ)) +
        ((tlTOneP5c3 f ξ + tlTOneP5c4 f ξ) + (tlTOneP5c5 f ξ + tlTOneP5c6 f ξ)))))) +
        ((((((tlTOneP5c7 f ξ + tlTOneP5c8 f ξ) + (tlTOneP5c9 f ξ + tlTOneP5c10 f ξ)) +
        ((tlTOneP5c11 f ξ + tlTOneP5c12 f ξ) + (tlTOneP6c0 f ξ + tlTOneP6c1 f ξ))) +
        (((tlTOneP6c2 f ξ + tlTOneP6c3 f ξ) + (tlTOneP6c4 f ξ + tlTOneP6c5 f ξ)) +
        ((tlTOneP6c6 f ξ + tlTOneP6c7 f ξ) + (tlTOneP6c8 f ξ + tlTOneP6c9 f ξ)))) +
        ((((tlTOneP6c10 f ξ + tlTOneP6c11 f ξ) + (tlTOneP6c12 f ξ + tlTOneP7c0 f ξ)) +
        ((tlTOneP7c1 f ξ + tlTOneP7c2 f ξ) + (tlTOneP7c3 f ξ + tlTOneP7c4 f ξ))) +
        (((tlTOneP7c5 f ξ + tlTOneP7c6 f ξ) + (tlTOneP7c7 f ξ + tlTOneP7c8 f ξ)) +
        ((tlTOneP7c9 f ξ + tlTOneP7c10 f ξ) + (tlTOneP7c11 f ξ + tlTOneP7c12 f ξ))))) +
        (((((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        ((tlTOneP8c12 f ξ + tlTOneP9c0 f ξ) + (tlTOneP9c1 f ξ + tlTOneP9c2 f ξ)))) +
        ((((tlTOneP9c3 f ξ + tlTOneP9c4 f ξ) + (tlTOneP9c5 f ξ + tlTOneP9c6 f ξ)) +
        ((tlTOneP9c7 f ξ + tlTOneP9c8 f ξ) + (tlTOneP9c9 f ξ + tlTOneP9c10 f ξ))) +
        (tlTOneP9c11 f ξ + tlTOneP9c12 f ξ)))) := by
  linear_combination
    ((((tlTOne_s0 hT) + (tlTOne_s1 hT)) + ((tlTOne_s2 hT) + (tlTOne_s3 hT))) + (((tlTOne_s4 hT) +
      (tlTOne_s5 hT)) + ((tlTOne_s6 hT) + (tlTOne_s7 hT)))) + ((tlTOne_s8 hT) + (tlTOne_s9 hT))


end MazurTorsion.Kubert

end
