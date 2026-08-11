/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateNumerator
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateTermThree

/-! The aggregate coefficient predicate for the split RelationFour left side. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def lhsCoefficientEq (n : Nat) (s : ℚ) : Prop :=
  termZeroCoefficient n s + termOneCoefficient n s +
      termTwoCoefficient n s + termThreeCoefficient n s =
    numeratorCoefficient n s

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
