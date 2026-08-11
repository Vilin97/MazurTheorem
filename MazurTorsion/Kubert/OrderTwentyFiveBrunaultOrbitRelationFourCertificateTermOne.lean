/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseTermOneFinal

/-! Checked aggregate expansion for RelationFour term one. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

theorem termOne_eq_evalThirtyFive (r s : ℚ) :
    term1 r s = evalThirtyFive (fun n => termOneCoefficient n s) r := by
  exact
    MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense.termOne_dense_expansion r s

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
