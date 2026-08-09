/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateTermZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateTermOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateTermTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateTermThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSCoefficientsLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSCoefficientsMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHSCoefficientsHigh
import Mathlib.Tactic.Ring

/-!
# Assembly of the checked cleared-denominator side

The four independently expanded terms and three bounded coefficient ranges are
assembled into the common exact-division target.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem terms_eq_lhs (r s : ℚ) :
    term0 r s + term1 r s + term2 r s + term3 r s = LHS r s := by
  rw [term0_expansion, term1_expansion, term2_expansion, term3_expansion]
  simp only [T0, T1, T2, T3, LHS,
    LC0,
    LC1,
    LC2,
    LC3,
    LC4,
    LC5,
    LC6,
    LC7,
    LC8,
    LC9,
    LC10,
    LC11,
    LC12,
    LC13,
    LC14,
    LC15,
    LC16,
    LC17,
    LC18,
    LC19,
    LC20,
    LC21,
    LC22,
    LC23,
    LC24,
    LC25,
    LC26,
    LC27,
    LC28,
    LC29,
    LC30,
    LC31,
    LC32,
    ]
  ring

theorem lhs_eq_H (r s : ℚ) :
    LHS r s = H r s := by
  simp only [LHS, H,
    lhs_coefficient_0,
    lhs_coefficient_1,
    lhs_coefficient_2,
    lhs_coefficient_3,
    lhs_coefficient_4,
    lhs_coefficient_5,
    lhs_coefficient_6,
    lhs_coefficient_7,
    lhs_coefficient_8,
    lhs_coefficient_9,
    lhs_coefficient_10,
    lhs_coefficient_11,
    lhs_coefficient_12,
    lhs_coefficient_13,
    lhs_coefficient_14,
    lhs_coefficient_15,
    lhs_coefficient_16,
    lhs_coefficient_17,
    lhs_coefficient_18,
    lhs_coefficient_19,
    lhs_coefficient_20,
    lhs_coefficient_21,
    lhs_coefficient_22,
    lhs_coefficient_23,
    lhs_coefficient_24,
    lhs_coefficient_25,
    lhs_coefficient_26,
    lhs_coefficient_27,
    lhs_coefficient_28,
    lhs_coefficient_29,
    lhs_coefficient_30,
    lhs_coefficient_31,
    lhs_coefficient_32,
    ]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
