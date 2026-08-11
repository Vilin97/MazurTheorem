/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermOneLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermOneMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermOneHigh

/-! Aggregate coefficient data for RelationFour term one. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def termOneCoefficient (n : Nat) (s : ℚ) : ℚ :=
  if n ≤ 11 then termOneCoefficientLow n s
  else if n ≤ 23 then termOneCoefficientMid n s
  else if n ≤ 34 then termOneCoefficientHigh n s
  else 0

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
