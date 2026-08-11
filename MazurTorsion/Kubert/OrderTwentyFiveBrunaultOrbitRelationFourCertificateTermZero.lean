/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateDenseTermZeroFinal

/-! Checked aggregate expansion for RelationFour term zero. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

theorem termZero_eq_evalThirtyFive (r s : ℚ) :
    term0 r s = evalThirtyFive (fun n => termZeroCoefficient n s) r := by
  exact
    MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Dense.termZero_dense_expansion r s

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
