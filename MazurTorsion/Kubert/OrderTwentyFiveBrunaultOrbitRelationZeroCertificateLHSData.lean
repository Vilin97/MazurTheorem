/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateData

/-!
# Cleared rational terms for the first raw orbit relation

These implementation definitions contain the common denominator and the four
terms whose checked sum is the cleared first orbit relation.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

def qD (r s : ℚ) : ℚ :=
  r * s * B r s ^ 2 * C r s ^ 3 * K r s ^ 2 * D r s ^ 2 *
    E r s ^ 2 * J r s * P6 r s * P9 r s

def aa (r s : ℚ) : ℚ :=
  -(A r s * L r s * T r s) / (B r s * D r s ^ 2 * E r s)

def cc (r s : ℚ) : ℚ :=
  r * B r s * K r s ^ 3 * E r s * T r s * M r s * N r s /
    (s * C r s ^ 3 * D r s * J r s * P9 r s)

def aabb (r s : ℚ) : ℚ :=
  -(r * B r s ^ 3 * C r s * K r s * M r s * T r s) /
    (D r s ^ 2 * P6 r s)

def aadd (r s : ℚ) : ℚ :=
  A r s ^ 2 * C r s * J r s * L r s * T r s /
    (r * B r s ^ 2 * K r s ^ 2 * D r s ^ 2 * E r s ^ 2)

def term0 (r s : ℚ) : ℚ :=
  -(r * s * B r s * C r s ^ 3 * K r s ^ 2 * E r s * J r s *
      P6 r s * P9 r s * A r s * L r s * T r s) -
    0

def term1 (r s : ℚ) : ℚ :=
  -(r * B r s ^ 2 * K r s ^ 2 * D r s * E r s ^ 2 * P6 r s) *
      (r * B r s * K r s ^ 3 * E r s * T r s * M r s * N r s) +
    0

def term2 (r s : ℚ) : ℚ :=
  (r * s * B r s ^ 2 * C r s ^ 3 * K r s ^ 2 * E r s ^ 2 *
      J r s * P9 r s) *
      (r * B r s ^ 3 * C r s * K r s * M r s * T r s)

def term3 (r s : ℚ) : ℚ :=
  (s * C r s ^ 3 * J r s * P6 r s * P9 r s) *
      (A r s ^ 2 * C r s * J r s * L r s * T r s)

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
