/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
import Mathlib.Tactic.NormNum

/-!
# Auxiliary primitive data for the raw order-twenty-five certificate

This leaf supplies the dense table for the factor `G`, consumed by both
canonical factorizations of `N` and `P9` in the X⁴ and V⁴ verifiers.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
def GData : Two :=
  [[0, 0, 1], [1, -3, 1]]

theorem eval_GData (r s : ℚ) :
    Two.eval GData r s =
      OrderTwentyFiveRawOrbitFactorCertificate.G r s := by
  norm_num [Two.eval, One.eval, evalWith, GData,
    OrderTwentyFiveRawOrbitFactorCertificate.G]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
