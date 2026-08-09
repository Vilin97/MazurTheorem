/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors
import Mathlib.Tactic.Ring

/-!
# Bridge from generated relation-zero data to the raw orbit chart

The exact-division certificate uses expanded integer polynomials. This leaf
checks that the three expanded auxiliary factors and the expanded Sutherland
polynomial agree with the canonical raw-orbit definitions.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem N_eq_factor (r s : ℚ) :
    N r s = OrderTwentyFiveRawOrbitFactorCertificate.N r s := by
  simp only [N, OrderTwentyFiveRawOrbitFactorCertificate.N,
    OrderTwentyFiveRawOrbitFactorCertificate.A,
    OrderTwentyFiveRawOrbitFactorCertificate.C,
    OrderTwentyFiveRawOrbitFactorCertificate.G,
    OrderTwentyFiveRawOrbitFactorCertificate.K]
  ring

theorem P6_eq_factor (r s : ℚ) :
    P6 r s = OrderTwentyFiveRawOrbitFactorCertificate.P6 r s := by
  simp only [P6, OrderTwentyFiveRawOrbitFactorCertificate.P6,
    OrderTwentyFiveRawOrbitFactorCertificate.A,
    OrderTwentyFiveRawOrbitFactorCertificate.B,
    OrderTwentyFiveRawOrbitFactorCertificate.C,
    OrderTwentyFiveRawOrbitFactorCertificate.D,
    OrderTwentyFiveRawOrbitFactorCertificate.E,
    OrderTwentyFiveRawOrbitFactorCertificate.G,
    OrderTwentyFiveRawOrbitFactorCertificate.K]
  ring

theorem P9_eq_factor (r s : ℚ) :
    P9 r s = OrderTwentyFiveRawOrbitFactorCertificate.P9 r s := by
  simp only [P9, OrderTwentyFiveRawOrbitFactorCertificate.P9,
    OrderTwentyFiveRawOrbitFactorCertificate.B,
    OrderTwentyFiveRawOrbitFactorCertificate.D,
    OrderTwentyFiveRawOrbitFactorCertificate.E,
    OrderTwentyFiveRawOrbitFactorCertificate.G,
    OrderTwentyFiveRawOrbitFactorCertificate.L]
  ring

theorem rawF_eq_rawSutherlandF (r s : ℚ) :
    rawF r s = orderTwentyFiveRawSutherlandF r s := by
  simp only [rawF, rawFC0, rawFC1, rawFC2, rawFC3, rawFC4, rawFC5,
    rawFC6, rawFC7, rawFC8, rawFC9, rawFC10,
    orderTwentyFiveRawSutherlandF]
  ring

theorem qD_eq_factor (r s : ℚ) :
    qD r s =
      r * s * OrderTwentyFiveRawOrbitFactorCertificate.B r s ^ 2 *
        OrderTwentyFiveRawOrbitFactorCertificate.C r s ^ 3 *
        OrderTwentyFiveRawOrbitFactorCertificate.K r s ^ 2 *
        OrderTwentyFiveRawOrbitFactorCertificate.D r s ^ 2 *
        OrderTwentyFiveRawOrbitFactorCertificate.E r s ^ 2 *
        OrderTwentyFiveRawOrbitFactorCertificate.J r s *
        OrderTwentyFiveRawOrbitFactorCertificate.P6 r s *
        OrderTwentyFiveRawOrbitFactorCertificate.P9 r s := by
  rw [qD, P6_eq_factor, P9_eq_factor]
  rfl

theorem aa_eq_factor (r s : ℚ) :
    aa r s =
      -(OrderTwentyFiveRawOrbitFactorCertificate.A r s *
          OrderTwentyFiveRawOrbitFactorCertificate.L r s *
          OrderTwentyFiveRawOrbitFactorCertificate.T r s) /
        (OrderTwentyFiveRawOrbitFactorCertificate.B r s *
          OrderTwentyFiveRawOrbitFactorCertificate.D r s ^ 2 *
          OrderTwentyFiveRawOrbitFactorCertificate.E r s) := by
  rfl

theorem cc_eq_factor (r s : ℚ) :
    cc r s =
      r * OrderTwentyFiveRawOrbitFactorCertificate.B r s *
          OrderTwentyFiveRawOrbitFactorCertificate.K r s ^ 3 *
          OrderTwentyFiveRawOrbitFactorCertificate.E r s *
          OrderTwentyFiveRawOrbitFactorCertificate.T r s *
          OrderTwentyFiveRawOrbitFactorCertificate.M r s *
          OrderTwentyFiveRawOrbitFactorCertificate.N r s /
        (s * OrderTwentyFiveRawOrbitFactorCertificate.C r s ^ 3 *
          OrderTwentyFiveRawOrbitFactorCertificate.D r s *
          OrderTwentyFiveRawOrbitFactorCertificate.J r s *
          OrderTwentyFiveRawOrbitFactorCertificate.P9 r s) := by
  rw [cc, N_eq_factor, P9_eq_factor]
  rfl

theorem aabb_eq_factor (r s : ℚ) :
    aabb r s =
      -(r * OrderTwentyFiveRawOrbitFactorCertificate.B r s ^ 3 *
          OrderTwentyFiveRawOrbitFactorCertificate.C r s *
          OrderTwentyFiveRawOrbitFactorCertificate.K r s *
          OrderTwentyFiveRawOrbitFactorCertificate.M r s *
          OrderTwentyFiveRawOrbitFactorCertificate.T r s) /
        (OrderTwentyFiveRawOrbitFactorCertificate.D r s ^ 2 *
          OrderTwentyFiveRawOrbitFactorCertificate.P6 r s) := by
  rw [aabb, P6_eq_factor]
  rfl

theorem aadd_eq_factor (r s : ℚ) :
    aadd r s =
      OrderTwentyFiveRawOrbitFactorCertificate.A r s ^ 2 *
          OrderTwentyFiveRawOrbitFactorCertificate.C r s *
          OrderTwentyFiveRawOrbitFactorCertificate.J r s *
          OrderTwentyFiveRawOrbitFactorCertificate.L r s *
          OrderTwentyFiveRawOrbitFactorCertificate.T r s /
        (r * OrderTwentyFiveRawOrbitFactorCertificate.B r s ^ 2 *
          OrderTwentyFiveRawOrbitFactorCertificate.K r s ^ 2 *
          OrderTwentyFiveRawOrbitFactorCertificate.D r s ^ 2 *
          OrderTwentyFiveRawOrbitFactorCertificate.E r s ^ 2) := by
  rfl

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
