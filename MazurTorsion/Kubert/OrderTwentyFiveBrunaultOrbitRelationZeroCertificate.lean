/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolution
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHS

/-!
# Checked raw certificate for the first Lécacheux orbit relation

Exact polynomial division produced the generated coefficient data in the leaf
modules imported above.  Lean checks each shard and this small module combines
the two sides.  A public theorem over the raw orbit definitions is supplied
below the private certificate.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate

open Internal

private theorem polynomial_certificate (r s : ℚ) :
    term0 r s + term1 r s + term2 r s + term3 r s =
      rawF r s * qN r s := by
  rw [terms_eq_lhs, lhs_eq_H, rhs_eq_H]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate
