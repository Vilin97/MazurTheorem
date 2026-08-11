/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermTwoLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermTwoMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermTwoHigh

/-! Aggregate coefficient data for RelationFour term two. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def termTwoCoefficient (n : Nat) (s : ℚ) : ℚ :=
  if n ≤ 11 then termTwoCoefficientLow n s
  else if n ≤ 23 then termTwoCoefficientMid n s
  else if n ≤ 34 then termTwoCoefficientHigh n s
  else 0

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
