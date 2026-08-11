/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseTermThreeFinal

/-! Checked aggregate expansion for RelationFour term three. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

theorem termThree_eq_evalThirtyFive (r s : ℚ) :
    term3 r s = evalThirtyFive (fun n => termThreeCoefficient n s) r := by
  exact
    MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense.termThree_dense_expansion r s

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
