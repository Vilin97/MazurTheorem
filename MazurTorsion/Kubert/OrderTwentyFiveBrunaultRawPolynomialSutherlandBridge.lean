/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData

/-!
# Evaluation bridge for Sutherland's raw order-twenty-five polynomial

This leaf identifies the canonical dense table used by the exact-division
certificate with the public raw Sutherland polynomial.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial

/-- The canonical dense Sutherland table evaluates to the public raw equation. -/
theorem eval_divisionSutherlandPolynomial_eq_rawSutherlandF (r s : ℚ) :
    Two.eval divisionSutherlandPolynomial r s =
      orderTwentyFiveRawSutherlandF r s := by
  simp [divisionSutherlandPolynomial, Two.eval, One.eval, evalWith,
    orderTwentyFiveRawSutherlandF]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
