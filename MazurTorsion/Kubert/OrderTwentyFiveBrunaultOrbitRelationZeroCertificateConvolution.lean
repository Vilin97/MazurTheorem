/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionMid
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionHigh
import Mathlib.Tactic.Ring

/-!
# Assembly of the checked right-hand side

The three bounded coefficient ranges are assembled into the exact-division target.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

def RawConv (r s : ℚ) : ℚ :=
  RawConvC32 s * r ^ 32
    + RawConvC31 s * r ^ 31
    + RawConvC30 s * r ^ 30
    + RawConvC29 s * r ^ 29
    + RawConvC28 s * r ^ 28
    + RawConvC27 s * r ^ 27
    + RawConvC26 s * r ^ 26
    + RawConvC25 s * r ^ 25
    + RawConvC24 s * r ^ 24
    + RawConvC23 s * r ^ 23
    + RawConvC22 s * r ^ 22
    + RawConvC21 s * r ^ 21
    + RawConvC20 s * r ^ 20
    + RawConvC19 s * r ^ 19
    + RawConvC18 s * r ^ 18
    + RawConvC17 s * r ^ 17
    + RawConvC16 s * r ^ 16
    + RawConvC15 s * r ^ 15
    + RawConvC14 s * r ^ 14
    + RawConvC13 s * r ^ 13
    + RawConvC12 s * r ^ 12
    + RawConvC11 s * r ^ 11
    + RawConvC10 s * r ^ 10
    + RawConvC9 s * r ^ 9
    + RawConvC8 s * r ^ 8
    + RawConvC7 s * r ^ 7
    + RawConvC6 s * r ^ 6
    + RawConvC5 s * r ^ 5
    + RawConvC4 s * r ^ 4
    + RawConvC3 s * r ^ 3
    + RawConvC2 s * r ^ 2
    + RawConvC1 s * r
    + RawConvC0 s

def RHS (r s : ℚ) : ℚ :=
  RHSC32 s * r ^ 32
    + RHSC31 s * r ^ 31
    + RHSC30 s * r ^ 30
    + RHSC29 s * r ^ 29
    + RHSC28 s * r ^ 28
    + RHSC27 s * r ^ 27
    + RHSC26 s * r ^ 26
    + RHSC25 s * r ^ 25
    + RHSC24 s * r ^ 24
    + RHSC23 s * r ^ 23
    + RHSC22 s * r ^ 22
    + RHSC21 s * r ^ 21
    + RHSC20 s * r ^ 20
    + RHSC19 s * r ^ 19
    + RHSC18 s * r ^ 18
    + RHSC17 s * r ^ 17
    + RHSC16 s * r ^ 16
    + RHSC15 s * r ^ 15
    + RHSC14 s * r ^ 14
    + RHSC13 s * r ^ 13
    + RHSC12 s * r ^ 12
    + RHSC11 s * r ^ 11
    + RHSC10 s * r ^ 10
    + RHSC9 s * r ^ 9
    + RHSC8 s * r ^ 8
    + RHSC7 s * r ^ 7
    + RHSC6 s * r ^ 6
    + RHSC5 s * r ^ 5
    + RHSC4 s * r ^ 4
    + RHSC3 s * r ^ 3
    + RHSC2 s * r ^ 2
    + RHSC1 s * r
    + RHSC0 s

theorem rawF_mul_QNE_eq_RawConv (r s : ℚ) :
    rawF r s * QNE r s = RawConv r s := by
  simp only [rawF, QNE, RawConv,
    RawConvC0,
    RawConvC1,
    RawConvC2,
    RawConvC3,
    RawConvC4,
    RawConvC5,
    RawConvC6,
    RawConvC7,
    RawConvC8,
    RawConvC9,
    RawConvC10,
    RawConvC11,
    RawConvC12,
    RawConvC13,
    RawConvC14,
    RawConvC15,
    RawConvC16,
    RawConvC17,
    RawConvC18,
    RawConvC19,
    RawConvC20,
    RawConvC21,
    RawConvC22,
    RawConvC23,
    RawConvC24,
    RawConvC25,
    RawConvC26,
    RawConvC27,
    RawConvC28,
    RawConvC29,
    RawConvC30,
    RawConvC31,
    RawConvC32,
    ]
  ring

theorem RawConv_eq_RHS (r s : ℚ) :
    RawConv r s = RHS r s := by
  simp only [RawConv, RHS,
    raw_convolution_coefficient_0,
    raw_convolution_coefficient_1,
    raw_convolution_coefficient_2,
    raw_convolution_coefficient_3,
    raw_convolution_coefficient_4,
    raw_convolution_coefficient_5,
    raw_convolution_coefficient_6,
    raw_convolution_coefficient_7,
    raw_convolution_coefficient_8,
    raw_convolution_coefficient_9,
    raw_convolution_coefficient_10,
    raw_convolution_coefficient_11,
    raw_convolution_coefficient_12,
    raw_convolution_coefficient_13,
    raw_convolution_coefficient_14,
    raw_convolution_coefficient_15,
    raw_convolution_coefficient_16,
    raw_convolution_coefficient_17,
    raw_convolution_coefficient_18,
    raw_convolution_coefficient_19,
    raw_convolution_coefficient_20,
    raw_convolution_coefficient_21,
    raw_convolution_coefficient_22,
    raw_convolution_coefficient_23,
    raw_convolution_coefficient_24,
    raw_convolution_coefficient_25,
    raw_convolution_coefficient_26,
    raw_convolution_coefficient_27,
    raw_convolution_coefficient_28,
    raw_convolution_coefficient_29,
    raw_convolution_coefficient_30,
    raw_convolution_coefficient_31,
    raw_convolution_coefficient_32,
    ]

theorem RHS_eq_H (r s : ℚ) : RHS r s = H r s := by
  simp only [RHS, H,
    rhs_coefficient_0,
    rhs_coefficient_1,
    rhs_coefficient_2,
    rhs_coefficient_3,
    rhs_coefficient_4,
    rhs_coefficient_5,
    rhs_coefficient_6,
    rhs_coefficient_7,
    rhs_coefficient_8,
    rhs_coefficient_9,
    rhs_coefficient_10,
    rhs_coefficient_11,
    rhs_coefficient_12,
    rhs_coefficient_13,
    rhs_coefficient_14,
    rhs_coefficient_15,
    rhs_coefficient_16,
    rhs_coefficient_17,
    rhs_coefficient_18,
    rhs_coefficient_19,
    rhs_coefficient_20,
    rhs_coefficient_21,
    rhs_coefficient_22,
    rhs_coefficient_23,
    rhs_coefficient_24,
    rhs_coefficient_25,
    rhs_coefficient_26,
    rhs_coefficient_27,
    rhs_coefficient_28,
    rhs_coefficient_29,
    rhs_coefficient_30,
    rhs_coefficient_31,
    rhs_coefficient_32,
    ]
theorem rhs_eq_H (r s : ℚ) :
    rawF r s * qN r s = H r s := by
  rw [qN_eq_QNE, rawF_mul_QNE_eq_RawConv, RawConv_eq_RHS, RHS_eq_H]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
