/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSupport

/-!
# Row zero of the raw numerator assembly certificate

This leaf checks one row of the rectangularized raw numerator identity.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomialRectangular

theorem assemblyRow0 :
    (rectangularize 83 121 assemblyData).getD 0 [] =
      (rectangularize 83 121 divisionReducedData).getD 0 [] := by
  decide


end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

