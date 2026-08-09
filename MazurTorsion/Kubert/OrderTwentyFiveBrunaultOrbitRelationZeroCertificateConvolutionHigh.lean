/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionA
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionB
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionC
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolutionD
import Mathlib.Tactic.Ring

/-!
# Checked convolution coefficients in outer degrees twenty-two through thirty-two

This leaf assembles only a bounded range of independently normalized row products.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

def RawConvC22 (s : ℚ) : ℚ :=
  rawFC0 s * QNE22 s + rawFC1 s * QNE21 s + rawFC2 s * QNE20 s + rawFC3 s * QNE19 s + rawFC4 s *
    QNE18 s + rawFC5 s * QNE17 s + rawFC6 s * QNE16 s + rawFC7 s * QNE15 s + rawFC8 s * QNE14 s
    + rawFC9 s * QNE13 s + rawFC10 s * QNE12 s

def RHSC22 (s : ℚ) : ℚ :=
  Pair0_22 s + Pair1_21 s + Pair2_20 s + Pair3_19 s + Pair4_18 s + Pair5_17 s + Pair6_16 s +
    Pair7_15 s + Pair8_14 s + Pair9_13 s + Pair10_12 s

theorem raw_convolution_coefficient_22 (s : ℚ) :
    RawConvC22 s = RHSC22 s := by
  simp only [RawConvC22, RHSC22,
    pair_0_22,
    pair_1_21,
    pair_2_20,
    pair_3_19,
    pair_4_18,
    pair_5_17,
    pair_6_16,
    pair_7_15,
    pair_8_14,
    pair_9_13,
    pair_10_12,
    ]

theorem rhs_coefficient_22 (s : ℚ) :
    RHSC22 s = HC22 s := by
  simp only [RHSC22, HC22,
    Pair0_22,
    Pair1_21,
    Pair2_20,
    Pair3_19,
    Pair4_18,
    Pair5_17,
    Pair6_16,
    Pair7_15,
    Pair8_14,
    Pair9_13,
    Pair10_12,
    ]
  ring

def RawConvC23 (s : ℚ) : ℚ :=
  rawFC1 s * QNE22 s + rawFC2 s * QNE21 s + rawFC3 s * QNE20 s + rawFC4 s * QNE19 s + rawFC5 s *
    QNE18 s + rawFC6 s * QNE17 s + rawFC7 s * QNE16 s + rawFC8 s * QNE15 s + rawFC9 s * QNE14 s
    + rawFC10 s * QNE13 s

def RHSC23 (s : ℚ) : ℚ :=
  Pair1_22 s + Pair2_21 s + Pair3_20 s + Pair4_19 s + Pair5_18 s + Pair6_17 s + Pair7_16 s +
    Pair8_15 s + Pair9_14 s + Pair10_13 s

theorem raw_convolution_coefficient_23 (s : ℚ) :
    RawConvC23 s = RHSC23 s := by
  simp only [RawConvC23, RHSC23,
    pair_1_22,
    pair_2_21,
    pair_3_20,
    pair_4_19,
    pair_5_18,
    pair_6_17,
    pair_7_16,
    pair_8_15,
    pair_9_14,
    pair_10_13,
    ]

theorem rhs_coefficient_23 (s : ℚ) :
    RHSC23 s = HC23 s := by
  simp only [RHSC23, HC23,
    Pair1_22,
    Pair2_21,
    Pair3_20,
    Pair4_19,
    Pair5_18,
    Pair6_17,
    Pair7_16,
    Pair8_15,
    Pair9_14,
    Pair10_13,
    ]
  ring

def RawConvC24 (s : ℚ) : ℚ :=
  rawFC2 s * QNE22 s + rawFC3 s * QNE21 s + rawFC4 s * QNE20 s + rawFC5 s * QNE19 s + rawFC6 s *
    QNE18 s + rawFC7 s * QNE17 s + rawFC8 s * QNE16 s + rawFC9 s * QNE15 s + rawFC10 s * QNE14 s

def RHSC24 (s : ℚ) : ℚ :=
  Pair2_22 s + Pair3_21 s + Pair4_20 s + Pair5_19 s + Pair6_18 s + Pair7_17 s + Pair8_16 s +
    Pair9_15 s + Pair10_14 s

theorem raw_convolution_coefficient_24 (s : ℚ) :
    RawConvC24 s = RHSC24 s := by
  simp only [RawConvC24, RHSC24,
    pair_2_22,
    pair_3_21,
    pair_4_20,
    pair_5_19,
    pair_6_18,
    pair_7_17,
    pair_8_16,
    pair_9_15,
    pair_10_14,
    ]

theorem rhs_coefficient_24 (s : ℚ) :
    RHSC24 s = HC24 s := by
  simp only [RHSC24, HC24,
    Pair2_22,
    Pair3_21,
    Pair4_20,
    Pair5_19,
    Pair6_18,
    Pair7_17,
    Pair8_16,
    Pair9_15,
    Pair10_14,
    ]
  ring

def RawConvC25 (s : ℚ) : ℚ :=
  rawFC3 s * QNE22 s + rawFC4 s * QNE21 s + rawFC5 s * QNE20 s + rawFC6 s * QNE19 s + rawFC7 s *
    QNE18 s + rawFC8 s * QNE17 s + rawFC9 s * QNE16 s + rawFC10 s * QNE15 s

def RHSC25 (s : ℚ) : ℚ :=
  Pair3_22 s + Pair4_21 s + Pair5_20 s + Pair6_19 s + Pair7_18 s + Pair8_17 s + Pair9_16 s +
    Pair10_15 s

theorem raw_convolution_coefficient_25 (s : ℚ) :
    RawConvC25 s = RHSC25 s := by
  simp only [RawConvC25, RHSC25,
    pair_3_22,
    pair_4_21,
    pair_5_20,
    pair_6_19,
    pair_7_18,
    pair_8_17,
    pair_9_16,
    pair_10_15,
    ]

theorem rhs_coefficient_25 (s : ℚ) :
    RHSC25 s = HC25 s := by
  simp only [RHSC25, HC25,
    Pair3_22,
    Pair4_21,
    Pair5_20,
    Pair6_19,
    Pair7_18,
    Pair8_17,
    Pair9_16,
    Pair10_15,
    ]
  ring

def RawConvC26 (s : ℚ) : ℚ :=
  rawFC4 s * QNE22 s + rawFC5 s * QNE21 s + rawFC6 s * QNE20 s + rawFC7 s * QNE19 s + rawFC8 s *
    QNE18 s + rawFC9 s * QNE17 s + rawFC10 s * QNE16 s

def RHSC26 (s : ℚ) : ℚ :=
  Pair4_22 s + Pair5_21 s + Pair6_20 s + Pair7_19 s + Pair8_18 s + Pair9_17 s + Pair10_16 s

theorem raw_convolution_coefficient_26 (s : ℚ) :
    RawConvC26 s = RHSC26 s := by
  simp only [RawConvC26, RHSC26,
    pair_4_22,
    pair_5_21,
    pair_6_20,
    pair_7_19,
    pair_8_18,
    pair_9_17,
    pair_10_16,
    ]

theorem rhs_coefficient_26 (s : ℚ) :
    RHSC26 s = HC26 s := by
  simp only [RHSC26, HC26,
    Pair4_22,
    Pair5_21,
    Pair6_20,
    Pair7_19,
    Pair8_18,
    Pair9_17,
    Pair10_16,
    ]
  ring

def RawConvC27 (s : ℚ) : ℚ :=
  rawFC5 s * QNE22 s + rawFC6 s * QNE21 s + rawFC7 s * QNE20 s + rawFC8 s * QNE19 s + rawFC9 s *
    QNE18 s + rawFC10 s * QNE17 s

def RHSC27 (s : ℚ) : ℚ :=
  Pair5_22 s + Pair6_21 s + Pair7_20 s + Pair8_19 s + Pair9_18 s + Pair10_17 s

theorem raw_convolution_coefficient_27 (s : ℚ) :
    RawConvC27 s = RHSC27 s := by
  simp only [RawConvC27, RHSC27,
    pair_5_22,
    pair_6_21,
    pair_7_20,
    pair_8_19,
    pair_9_18,
    pair_10_17,
    ]

theorem rhs_coefficient_27 (s : ℚ) :
    RHSC27 s = HC27 s := by
  simp only [RHSC27, HC27,
    Pair5_22,
    Pair6_21,
    Pair7_20,
    Pair8_19,
    Pair9_18,
    Pair10_17,
    ]
  ring

def RawConvC28 (s : ℚ) : ℚ :=
  rawFC6 s * QNE22 s + rawFC7 s * QNE21 s + rawFC8 s * QNE20 s + rawFC9 s * QNE19 s + rawFC10 s
    * QNE18 s

def RHSC28 (s : ℚ) : ℚ :=
  Pair6_22 s + Pair7_21 s + Pair8_20 s + Pair9_19 s + Pair10_18 s

theorem raw_convolution_coefficient_28 (s : ℚ) :
    RawConvC28 s = RHSC28 s := by
  simp only [RawConvC28, RHSC28,
    pair_6_22,
    pair_7_21,
    pair_8_20,
    pair_9_19,
    pair_10_18,
    ]

theorem rhs_coefficient_28 (s : ℚ) :
    RHSC28 s = HC28 s := by
  simp only [RHSC28, HC28,
    Pair6_22,
    Pair7_21,
    Pair8_20,
    Pair9_19,
    Pair10_18,
    ]
  ring

def RawConvC29 (s : ℚ) : ℚ :=
  rawFC7 s * QNE22 s + rawFC8 s * QNE21 s + rawFC9 s * QNE20 s + rawFC10 s * QNE19 s

def RHSC29 (s : ℚ) : ℚ :=
  Pair7_22 s + Pair8_21 s + Pair9_20 s + Pair10_19 s

theorem raw_convolution_coefficient_29 (s : ℚ) :
    RawConvC29 s = RHSC29 s := by
  simp only [RawConvC29, RHSC29,
    pair_7_22,
    pair_8_21,
    pair_9_20,
    pair_10_19,
    ]

theorem rhs_coefficient_29 (s : ℚ) :
    RHSC29 s = HC29 s := by
  simp only [RHSC29, HC29,
    Pair7_22,
    Pair8_21,
    Pair9_20,
    Pair10_19,
    ]
  ring

def RawConvC30 (s : ℚ) : ℚ :=
  rawFC8 s * QNE22 s + rawFC9 s * QNE21 s + rawFC10 s * QNE20 s

def RHSC30 (s : ℚ) : ℚ :=
  Pair8_22 s + Pair9_21 s + Pair10_20 s

theorem raw_convolution_coefficient_30 (s : ℚ) :
    RawConvC30 s = RHSC30 s := by
  simp only [RawConvC30, RHSC30,
    pair_8_22,
    pair_9_21,
    pair_10_20,
    ]

theorem rhs_coefficient_30 (s : ℚ) :
    RHSC30 s = HC30 s := by
  simp only [RHSC30, HC30,
    Pair8_22,
    Pair9_21,
    Pair10_20,
    ]
  ring

def RawConvC31 (s : ℚ) : ℚ :=
  rawFC9 s * QNE22 s + rawFC10 s * QNE21 s

def RHSC31 (s : ℚ) : ℚ :=
  Pair9_22 s + Pair10_21 s

theorem raw_convolution_coefficient_31 (s : ℚ) :
    RawConvC31 s = RHSC31 s := by
  simp only [RawConvC31, RHSC31,
    pair_9_22,
    pair_10_21,
    ]

theorem rhs_coefficient_31 (s : ℚ) :
    RHSC31 s = HC31 s := by
  simp only [RHSC31, HC31,
    Pair9_22,
    Pair10_21,
    ]
  ring

def RawConvC32 (s : ℚ) : ℚ :=
  rawFC10 s * QNE22 s

def RHSC32 (s : ℚ) : ℚ :=
  Pair10_22 s

theorem raw_convolution_coefficient_32 (s : ℚ) :
    RawConvC32 s = RHSC32 s := by
  simp only [RawConvC32, RHSC32,
    pair_10_22,
    ]

theorem rhs_coefficient_32 (s : ℚ) :
    RHSC32 s = HC32 s := by
  simp only [RHSC32, HC32,
    Pair10_22,
    ]

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
