/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermThreeLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermThreeMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermThreeHigh

/-! Aggregate coefficient data for RelationFour term three. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def termThreeCoefficient (n : Nat) (s : ℚ) : ℚ :=
  if n ≤ 11 then termThreeCoefficientLow n s
  else if n ≤ 23 then termThreeCoefficientMid n s
  else if n ≤ 34 then termThreeCoefficientHigh n s
  else 0

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
