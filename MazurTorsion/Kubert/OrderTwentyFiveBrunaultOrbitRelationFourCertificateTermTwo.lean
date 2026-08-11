/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseTermTwoFinal

/-! Checked aggregate expansion for RelationFour term two. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

theorem termTwo_eq_evalThirtyFive (r s : ℚ) :
    term2 r s = evalThirtyFive (fun n => termTwoCoefficient n s) r := by
  exact
    MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense.termTwo_dense_expansion r s

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
