/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermZeroLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermZeroMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermZeroHigh

/-! Aggregate coefficient data for RelationFour term zero. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def termZeroCoefficient (n : Nat) (s : ℚ) : ℚ :=
  if n ≤ 11 then termZeroCoefficientLow n s
  else if n ≤ 23 then termZeroCoefficientMid n s
  else if n ≤ 34 then termZeroCoefficientHigh n s
  else 0

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
