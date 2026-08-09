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
# Checked convolution coefficients in outer degrees eleven through twenty-one

This leaf assembles only a bounded range of independently normalized row products.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

def RawConvC11 (s : ℚ) : ℚ :=
  rawFC0 s * QNE11 s + rawFC1 s * QNE10 s + rawFC2 s * QNE9 s + rawFC3 s * QNE8 s + rawFC4 s *
    QNE7 s + rawFC5 s * QNE6 s + rawFC6 s * QNE5 s + rawFC7 s * QNE4 s + rawFC8 s * QNE3 s +
    rawFC9 s * QNE2 s + rawFC10 s * QNE1 s

def RHSC11 (s : ℚ) : ℚ :=
  Pair0_11 s + Pair1_10 s + Pair2_9 s + Pair3_8 s + Pair4_7 s + Pair5_6 s + Pair6_5 s + Pair7_4
    s + Pair8_3 s + Pair9_2 s + Pair10_1 s

theorem raw_convolution_coefficient_11 (s : ℚ) :
    RawConvC11 s = RHSC11 s := by
  simp only [RawConvC11, RHSC11,
    pair_0_11,
    pair_1_10,
    pair_2_9,
    pair_3_8,
    pair_4_7,
    pair_5_6,
    pair_6_5,
    pair_7_4,
    pair_8_3,
    pair_9_2,
    pair_10_1,
    ]

theorem rhs_coefficient_11 (s : ℚ) :
    RHSC11 s = HC11 s := by
  simp only [RHSC11, HC11,
    Pair0_11,
    Pair1_10,
    Pair2_9,
    Pair3_8,
    Pair4_7,
    Pair5_6,
    Pair6_5,
    Pair7_4,
    Pair8_3,
    Pair9_2,
    Pair10_1,
    ]
  ring

def RawConvC12 (s : ℚ) : ℚ :=
  rawFC0 s * QNE12 s + rawFC1 s * QNE11 s + rawFC2 s * QNE10 s + rawFC3 s * QNE9 s + rawFC4 s *
    QNE8 s + rawFC5 s * QNE7 s + rawFC6 s * QNE6 s + rawFC7 s * QNE5 s + rawFC8 s * QNE4 s +
    rawFC9 s * QNE3 s + rawFC10 s * QNE2 s

def RHSC12 (s : ℚ) : ℚ :=
  Pair0_12 s + Pair1_11 s + Pair2_10 s + Pair3_9 s + Pair4_8 s + Pair5_7 s + Pair6_6 s + Pair7_5
    s + Pair8_4 s + Pair9_3 s + Pair10_2 s

theorem raw_convolution_coefficient_12 (s : ℚ) :
    RawConvC12 s = RHSC12 s := by
  simp only [RawConvC12, RHSC12,
    pair_0_12,
    pair_1_11,
    pair_2_10,
    pair_3_9,
    pair_4_8,
    pair_5_7,
    pair_6_6,
    pair_7_5,
    pair_8_4,
    pair_9_3,
    pair_10_2,
    ]

theorem rhs_coefficient_12 (s : ℚ) :
    RHSC12 s = HC12 s := by
  simp only [RHSC12, HC12,
    Pair0_12,
    Pair1_11,
    Pair2_10,
    Pair3_9,
    Pair4_8,
    Pair5_7,
    Pair6_6,
    Pair7_5,
    Pair8_4,
    Pair9_3,
    Pair10_2,
    ]
  ring

def RawConvC13 (s : ℚ) : ℚ :=
  rawFC0 s * QNE13 s + rawFC1 s * QNE12 s + rawFC2 s * QNE11 s + rawFC3 s * QNE10 s + rawFC4 s *
    QNE9 s + rawFC5 s * QNE8 s + rawFC6 s * QNE7 s + rawFC7 s * QNE6 s + rawFC8 s * QNE5 s +
    rawFC9 s * QNE4 s + rawFC10 s * QNE3 s

def RHSC13 (s : ℚ) : ℚ :=
  Pair0_13 s + Pair1_12 s + Pair2_11 s + Pair3_10 s + Pair4_9 s + Pair5_8 s + Pair6_7 s +
    Pair7_6 s + Pair8_5 s + Pair9_4 s + Pair10_3 s

theorem raw_convolution_coefficient_13 (s : ℚ) :
    RawConvC13 s = RHSC13 s := by
  simp only [RawConvC13, RHSC13,
    pair_0_13,
    pair_1_12,
    pair_2_11,
    pair_3_10,
    pair_4_9,
    pair_5_8,
    pair_6_7,
    pair_7_6,
    pair_8_5,
    pair_9_4,
    pair_10_3,
    ]

theorem rhs_coefficient_13 (s : ℚ) :
    RHSC13 s = HC13 s := by
  simp only [RHSC13, HC13,
    Pair0_13,
    Pair1_12,
    Pair2_11,
    Pair3_10,
    Pair4_9,
    Pair5_8,
    Pair6_7,
    Pair7_6,
    Pair8_5,
    Pair9_4,
    Pair10_3,
    ]
  ring

def RawConvC14 (s : ℚ) : ℚ :=
  rawFC0 s * QNE14 s + rawFC1 s * QNE13 s + rawFC2 s * QNE12 s + rawFC3 s * QNE11 s + rawFC4 s *
    QNE10 s + rawFC5 s * QNE9 s + rawFC6 s * QNE8 s + rawFC7 s * QNE7 s + rawFC8 s * QNE6 s +
    rawFC9 s * QNE5 s + rawFC10 s * QNE4 s

def RHSC14 (s : ℚ) : ℚ :=
  Pair0_14 s + Pair1_13 s + Pair2_12 s + Pair3_11 s + Pair4_10 s + Pair5_9 s + Pair6_8 s +
    Pair7_7 s + Pair8_6 s + Pair9_5 s + Pair10_4 s

theorem raw_convolution_coefficient_14 (s : ℚ) :
    RawConvC14 s = RHSC14 s := by
  simp only [RawConvC14, RHSC14,
    pair_0_14,
    pair_1_13,
    pair_2_12,
    pair_3_11,
    pair_4_10,
    pair_5_9,
    pair_6_8,
    pair_7_7,
    pair_8_6,
    pair_9_5,
    pair_10_4,
    ]

theorem rhs_coefficient_14 (s : ℚ) :
    RHSC14 s = HC14 s := by
  simp only [RHSC14, HC14,
    Pair0_14,
    Pair1_13,
    Pair2_12,
    Pair3_11,
    Pair4_10,
    Pair5_9,
    Pair6_8,
    Pair7_7,
    Pair8_6,
    Pair9_5,
    Pair10_4,
    ]
  ring

def RawConvC15 (s : ℚ) : ℚ :=
  rawFC0 s * QNE15 s + rawFC1 s * QNE14 s + rawFC2 s * QNE13 s + rawFC3 s * QNE12 s + rawFC4 s *
    QNE11 s + rawFC5 s * QNE10 s + rawFC6 s * QNE9 s + rawFC7 s * QNE8 s + rawFC8 s * QNE7 s +
    rawFC9 s * QNE6 s + rawFC10 s * QNE5 s

def RHSC15 (s : ℚ) : ℚ :=
  Pair0_15 s + Pair1_14 s + Pair2_13 s + Pair3_12 s + Pair4_11 s + Pair5_10 s + Pair6_9 s +
    Pair7_8 s + Pair8_7 s + Pair9_6 s + Pair10_5 s

theorem raw_convolution_coefficient_15 (s : ℚ) :
    RawConvC15 s = RHSC15 s := by
  simp only [RawConvC15, RHSC15,
    pair_0_15,
    pair_1_14,
    pair_2_13,
    pair_3_12,
    pair_4_11,
    pair_5_10,
    pair_6_9,
    pair_7_8,
    pair_8_7,
    pair_9_6,
    pair_10_5,
    ]

theorem rhs_coefficient_15 (s : ℚ) :
    RHSC15 s = HC15 s := by
  simp only [RHSC15, HC15,
    Pair0_15,
    Pair1_14,
    Pair2_13,
    Pair3_12,
    Pair4_11,
    Pair5_10,
    Pair6_9,
    Pair7_8,
    Pair8_7,
    Pair9_6,
    Pair10_5,
    ]
  ring

def RawConvC16 (s : ℚ) : ℚ :=
  rawFC0 s * QNE16 s + rawFC1 s * QNE15 s + rawFC2 s * QNE14 s + rawFC3 s * QNE13 s + rawFC4 s *
    QNE12 s + rawFC5 s * QNE11 s + rawFC6 s * QNE10 s + rawFC7 s * QNE9 s + rawFC8 s * QNE8 s +
    rawFC9 s * QNE7 s + rawFC10 s * QNE6 s

def RHSC16 (s : ℚ) : ℚ :=
  Pair0_16 s + Pair1_15 s + Pair2_14 s + Pair3_13 s + Pair4_12 s + Pair5_11 s + Pair6_10 s +
    Pair7_9 s + Pair8_8 s + Pair9_7 s + Pair10_6 s

theorem raw_convolution_coefficient_16 (s : ℚ) :
    RawConvC16 s = RHSC16 s := by
  simp only [RawConvC16, RHSC16,
    pair_0_16,
    pair_1_15,
    pair_2_14,
    pair_3_13,
    pair_4_12,
    pair_5_11,
    pair_6_10,
    pair_7_9,
    pair_8_8,
    pair_9_7,
    pair_10_6,
    ]

theorem rhs_coefficient_16 (s : ℚ) :
    RHSC16 s = HC16 s := by
  simp only [RHSC16, HC16,
    Pair0_16,
    Pair1_15,
    Pair2_14,
    Pair3_13,
    Pair4_12,
    Pair5_11,
    Pair6_10,
    Pair7_9,
    Pair8_8,
    Pair9_7,
    Pair10_6,
    ]
  ring

def RawConvC17 (s : ℚ) : ℚ :=
  rawFC0 s * QNE17 s + rawFC1 s * QNE16 s + rawFC2 s * QNE15 s + rawFC3 s * QNE14 s + rawFC4 s *
    QNE13 s + rawFC5 s * QNE12 s + rawFC6 s * QNE11 s + rawFC7 s * QNE10 s + rawFC8 s * QNE9 s +
    rawFC9 s * QNE8 s + rawFC10 s * QNE7 s

def RHSC17 (s : ℚ) : ℚ :=
  Pair0_17 s + Pair1_16 s + Pair2_15 s + Pair3_14 s + Pair4_13 s + Pair5_12 s + Pair6_11 s +
    Pair7_10 s + Pair8_9 s + Pair9_8 s + Pair10_7 s

theorem raw_convolution_coefficient_17 (s : ℚ) :
    RawConvC17 s = RHSC17 s := by
  simp only [RawConvC17, RHSC17,
    pair_0_17,
    pair_1_16,
    pair_2_15,
    pair_3_14,
    pair_4_13,
    pair_5_12,
    pair_6_11,
    pair_7_10,
    pair_8_9,
    pair_9_8,
    pair_10_7,
    ]

theorem rhs_coefficient_17 (s : ℚ) :
    RHSC17 s = HC17 s := by
  simp only [RHSC17, HC17,
    Pair0_17,
    Pair1_16,
    Pair2_15,
    Pair3_14,
    Pair4_13,
    Pair5_12,
    Pair6_11,
    Pair7_10,
    Pair8_9,
    Pair9_8,
    Pair10_7,
    ]
  ring

def RawConvC18 (s : ℚ) : ℚ :=
  rawFC0 s * QNE18 s + rawFC1 s * QNE17 s + rawFC2 s * QNE16 s + rawFC3 s * QNE15 s + rawFC4 s *
    QNE14 s + rawFC5 s * QNE13 s + rawFC6 s * QNE12 s + rawFC7 s * QNE11 s + rawFC8 s * QNE10 s
    + rawFC9 s * QNE9 s + rawFC10 s * QNE8 s

def RHSC18 (s : ℚ) : ℚ :=
  Pair0_18 s + Pair1_17 s + Pair2_16 s + Pair3_15 s + Pair4_14 s + Pair5_13 s + Pair6_12 s +
    Pair7_11 s + Pair8_10 s + Pair9_9 s + Pair10_8 s

theorem raw_convolution_coefficient_18 (s : ℚ) :
    RawConvC18 s = RHSC18 s := by
  simp only [RawConvC18, RHSC18,
    pair_0_18,
    pair_1_17,
    pair_2_16,
    pair_3_15,
    pair_4_14,
    pair_5_13,
    pair_6_12,
    pair_7_11,
    pair_8_10,
    pair_9_9,
    pair_10_8,
    ]

theorem rhs_coefficient_18 (s : ℚ) :
    RHSC18 s = HC18 s := by
  simp only [RHSC18, HC18,
    Pair0_18,
    Pair1_17,
    Pair2_16,
    Pair3_15,
    Pair4_14,
    Pair5_13,
    Pair6_12,
    Pair7_11,
    Pair8_10,
    Pair9_9,
    Pair10_8,
    ]
  ring

def RawConvC19 (s : ℚ) : ℚ :=
  rawFC0 s * QNE19 s + rawFC1 s * QNE18 s + rawFC2 s * QNE17 s + rawFC3 s * QNE16 s + rawFC4 s *
    QNE15 s + rawFC5 s * QNE14 s + rawFC6 s * QNE13 s + rawFC7 s * QNE12 s + rawFC8 s * QNE11 s
    + rawFC9 s * QNE10 s + rawFC10 s * QNE9 s

def RHSC19 (s : ℚ) : ℚ :=
  Pair0_19 s + Pair1_18 s + Pair2_17 s + Pair3_16 s + Pair4_15 s + Pair5_14 s + Pair6_13 s +
    Pair7_12 s + Pair8_11 s + Pair9_10 s + Pair10_9 s

theorem raw_convolution_coefficient_19 (s : ℚ) :
    RawConvC19 s = RHSC19 s := by
  simp only [RawConvC19, RHSC19,
    pair_0_19,
    pair_1_18,
    pair_2_17,
    pair_3_16,
    pair_4_15,
    pair_5_14,
    pair_6_13,
    pair_7_12,
    pair_8_11,
    pair_9_10,
    pair_10_9,
    ]

theorem rhs_coefficient_19 (s : ℚ) :
    RHSC19 s = HC19 s := by
  simp only [RHSC19, HC19,
    Pair0_19,
    Pair1_18,
    Pair2_17,
    Pair3_16,
    Pair4_15,
    Pair5_14,
    Pair6_13,
    Pair7_12,
    Pair8_11,
    Pair9_10,
    Pair10_9,
    ]
  ring

def RawConvC20 (s : ℚ) : ℚ :=
  rawFC0 s * QNE20 s + rawFC1 s * QNE19 s + rawFC2 s * QNE18 s + rawFC3 s * QNE17 s + rawFC4 s *
    QNE16 s + rawFC5 s * QNE15 s + rawFC6 s * QNE14 s + rawFC7 s * QNE13 s + rawFC8 s * QNE12 s
    + rawFC9 s * QNE11 s + rawFC10 s * QNE10 s

def RHSC20 (s : ℚ) : ℚ :=
  Pair0_20 s + Pair1_19 s + Pair2_18 s + Pair3_17 s + Pair4_16 s + Pair5_15 s + Pair6_14 s +
    Pair7_13 s + Pair8_12 s + Pair9_11 s + Pair10_10 s

theorem raw_convolution_coefficient_20 (s : ℚ) :
    RawConvC20 s = RHSC20 s := by
  simp only [RawConvC20, RHSC20,
    pair_0_20,
    pair_1_19,
    pair_2_18,
    pair_3_17,
    pair_4_16,
    pair_5_15,
    pair_6_14,
    pair_7_13,
    pair_8_12,
    pair_9_11,
    pair_10_10,
    ]

theorem rhs_coefficient_20 (s : ℚ) :
    RHSC20 s = HC20 s := by
  simp only [RHSC20, HC20,
    Pair0_20,
    Pair1_19,
    Pair2_18,
    Pair3_17,
    Pair4_16,
    Pair5_15,
    Pair6_14,
    Pair7_13,
    Pair8_12,
    Pair9_11,
    Pair10_10,
    ]
  ring

def RawConvC21 (s : ℚ) : ℚ :=
  rawFC0 s * QNE21 s + rawFC1 s * QNE20 s + rawFC2 s * QNE19 s + rawFC3 s * QNE18 s + rawFC4 s *
    QNE17 s + rawFC5 s * QNE16 s + rawFC6 s * QNE15 s + rawFC7 s * QNE14 s + rawFC8 s * QNE13 s
    + rawFC9 s * QNE12 s + rawFC10 s * QNE11 s

def RHSC21 (s : ℚ) : ℚ :=
  Pair0_21 s + Pair1_20 s + Pair2_19 s + Pair3_18 s + Pair4_17 s + Pair5_16 s + Pair6_15 s +
    Pair7_14 s + Pair8_13 s + Pair9_12 s + Pair10_11 s

theorem raw_convolution_coefficient_21 (s : ℚ) :
    RawConvC21 s = RHSC21 s := by
  simp only [RawConvC21, RHSC21,
    pair_0_21,
    pair_1_20,
    pair_2_19,
    pair_3_18,
    pair_4_17,
    pair_5_16,
    pair_6_15,
    pair_7_14,
    pair_8_13,
    pair_9_12,
    pair_10_11,
    ]

theorem rhs_coefficient_21 (s : ℚ) :
    RHSC21 s = HC21 s := by
  simp only [RHSC21, HC21,
    Pair0_21,
    Pair1_20,
    Pair2_19,
    Pair3_18,
    Pair4_17,
    Pair5_16,
    Pair6_15,
    Pair7_14,
    Pair8_13,
    Pair9_12,
    Pair10_11,
    ]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
