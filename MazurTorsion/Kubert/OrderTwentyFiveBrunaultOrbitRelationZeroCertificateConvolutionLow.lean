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
# Checked convolution coefficients in outer degrees zero through ten

This leaf assembles only a bounded range of independently normalized row products.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

def RawConvC0 (s : ℚ) : ℚ :=
  rawFC0 s * QNE0 s

def RHSC0 (s : ℚ) : ℚ :=
  Pair0_0 s

theorem raw_convolution_coefficient_0 (s : ℚ) :
    RawConvC0 s = RHSC0 s := by
  simp only [RawConvC0, RHSC0,
    pair_0_0,
    ]

theorem rhs_coefficient_0 (s : ℚ) :
    RHSC0 s = HC0 s := by
  simp only [RHSC0, HC0,
    Pair0_0,
    ]

def RawConvC1 (s : ℚ) : ℚ :=
  rawFC0 s * QNE1 s + rawFC1 s * QNE0 s

def RHSC1 (s : ℚ) : ℚ :=
  Pair0_1 s + Pair1_0 s

theorem raw_convolution_coefficient_1 (s : ℚ) :
    RawConvC1 s = RHSC1 s := by
  simp only [RawConvC1, RHSC1,
    pair_0_1,
    pair_1_0,
    ]

theorem rhs_coefficient_1 (s : ℚ) :
    RHSC1 s = HC1 s := by
  simp only [RHSC1, HC1,
    Pair0_1,
    Pair1_0,
    ]
  ring

def RawConvC2 (s : ℚ) : ℚ :=
  rawFC0 s * QNE2 s + rawFC1 s * QNE1 s + rawFC2 s * QNE0 s

def RHSC2 (s : ℚ) : ℚ :=
  Pair0_2 s + Pair1_1 s + Pair2_0 s

theorem raw_convolution_coefficient_2 (s : ℚ) :
    RawConvC2 s = RHSC2 s := by
  simp only [RawConvC2, RHSC2,
    pair_0_2,
    pair_1_1,
    pair_2_0,
    ]

theorem rhs_coefficient_2 (s : ℚ) :
    RHSC2 s = HC2 s := by
  simp only [RHSC2, HC2,
    Pair0_2,
    Pair1_1,
    Pair2_0,
    ]
  ring

def RawConvC3 (s : ℚ) : ℚ :=
  rawFC0 s * QNE3 s + rawFC1 s * QNE2 s + rawFC2 s * QNE1 s + rawFC3 s * QNE0 s

def RHSC3 (s : ℚ) : ℚ :=
  Pair0_3 s + Pair1_2 s + Pair2_1 s + Pair3_0 s

theorem raw_convolution_coefficient_3 (s : ℚ) :
    RawConvC3 s = RHSC3 s := by
  simp only [RawConvC3, RHSC3,
    pair_0_3,
    pair_1_2,
    pair_2_1,
    pair_3_0,
    ]

theorem rhs_coefficient_3 (s : ℚ) :
    RHSC3 s = HC3 s := by
  simp only [RHSC3, HC3,
    Pair0_3,
    Pair1_2,
    Pair2_1,
    Pair3_0,
    ]
  ring

def RawConvC4 (s : ℚ) : ℚ :=
  rawFC0 s * QNE4 s + rawFC1 s * QNE3 s + rawFC2 s * QNE2 s + rawFC3 s * QNE1 s + rawFC4 s *
    QNE0 s

def RHSC4 (s : ℚ) : ℚ :=
  Pair0_4 s + Pair1_3 s + Pair2_2 s + Pair3_1 s + Pair4_0 s

theorem raw_convolution_coefficient_4 (s : ℚ) :
    RawConvC4 s = RHSC4 s := by
  simp only [RawConvC4, RHSC4,
    pair_0_4,
    pair_1_3,
    pair_2_2,
    pair_3_1,
    pair_4_0,
    ]

theorem rhs_coefficient_4 (s : ℚ) :
    RHSC4 s = HC4 s := by
  simp only [RHSC4, HC4,
    Pair0_4,
    Pair1_3,
    Pair2_2,
    Pair3_1,
    Pair4_0,
    ]
  ring

def RawConvC5 (s : ℚ) : ℚ :=
  rawFC0 s * QNE5 s + rawFC1 s * QNE4 s + rawFC2 s * QNE3 s + rawFC3 s * QNE2 s + rawFC4 s *
    QNE1 s + rawFC5 s * QNE0 s

def RHSC5 (s : ℚ) : ℚ :=
  Pair0_5 s + Pair1_4 s + Pair2_3 s + Pair3_2 s + Pair4_1 s + Pair5_0 s

theorem raw_convolution_coefficient_5 (s : ℚ) :
    RawConvC5 s = RHSC5 s := by
  simp only [RawConvC5, RHSC5,
    pair_0_5,
    pair_1_4,
    pair_2_3,
    pair_3_2,
    pair_4_1,
    pair_5_0,
    ]

theorem rhs_coefficient_5 (s : ℚ) :
    RHSC5 s = HC5 s := by
  simp only [RHSC5, HC5,
    Pair0_5,
    Pair1_4,
    Pair2_3,
    Pair3_2,
    Pair4_1,
    Pair5_0,
    ]
  ring

def RawConvC6 (s : ℚ) : ℚ :=
  rawFC0 s * QNE6 s + rawFC1 s * QNE5 s + rawFC2 s * QNE4 s + rawFC3 s * QNE3 s + rawFC4 s *
    QNE2 s + rawFC5 s * QNE1 s + rawFC6 s * QNE0 s

def RHSC6 (s : ℚ) : ℚ :=
  Pair0_6 s + Pair1_5 s + Pair2_4 s + Pair3_3 s + Pair4_2 s + Pair5_1 s + Pair6_0 s

theorem raw_convolution_coefficient_6 (s : ℚ) :
    RawConvC6 s = RHSC6 s := by
  simp only [RawConvC6, RHSC6,
    pair_0_6,
    pair_1_5,
    pair_2_4,
    pair_3_3,
    pair_4_2,
    pair_5_1,
    pair_6_0,
    ]

theorem rhs_coefficient_6 (s : ℚ) :
    RHSC6 s = HC6 s := by
  simp only [RHSC6, HC6,
    Pair0_6,
    Pair1_5,
    Pair2_4,
    Pair3_3,
    Pair4_2,
    Pair5_1,
    Pair6_0,
    ]
  ring

def RawConvC7 (s : ℚ) : ℚ :=
  rawFC0 s * QNE7 s + rawFC1 s * QNE6 s + rawFC2 s * QNE5 s + rawFC3 s * QNE4 s + rawFC4 s *
    QNE3 s + rawFC5 s * QNE2 s + rawFC6 s * QNE1 s + rawFC7 s * QNE0 s

def RHSC7 (s : ℚ) : ℚ :=
  Pair0_7 s + Pair1_6 s + Pair2_5 s + Pair3_4 s + Pair4_3 s + Pair5_2 s + Pair6_1 s + Pair7_0 s

theorem raw_convolution_coefficient_7 (s : ℚ) :
    RawConvC7 s = RHSC7 s := by
  simp only [RawConvC7, RHSC7,
    pair_0_7,
    pair_1_6,
    pair_2_5,
    pair_3_4,
    pair_4_3,
    pair_5_2,
    pair_6_1,
    pair_7_0,
    ]

theorem rhs_coefficient_7 (s : ℚ) :
    RHSC7 s = HC7 s := by
  simp only [RHSC7, HC7,
    Pair0_7,
    Pair1_6,
    Pair2_5,
    Pair3_4,
    Pair4_3,
    Pair5_2,
    Pair6_1,
    Pair7_0,
    ]
  ring

def RawConvC8 (s : ℚ) : ℚ :=
  rawFC0 s * QNE8 s + rawFC1 s * QNE7 s + rawFC2 s * QNE6 s + rawFC3 s * QNE5 s + rawFC4 s *
    QNE4 s + rawFC5 s * QNE3 s + rawFC6 s * QNE2 s + rawFC7 s * QNE1 s + rawFC8 s * QNE0 s

def RHSC8 (s : ℚ) : ℚ :=
  Pair0_8 s + Pair1_7 s + Pair2_6 s + Pair3_5 s + Pair4_4 s + Pair5_3 s + Pair6_2 s + Pair7_1 s
    + Pair8_0 s

theorem raw_convolution_coefficient_8 (s : ℚ) :
    RawConvC8 s = RHSC8 s := by
  simp only [RawConvC8, RHSC8,
    pair_0_8,
    pair_1_7,
    pair_2_6,
    pair_3_5,
    pair_4_4,
    pair_5_3,
    pair_6_2,
    pair_7_1,
    pair_8_0,
    ]

theorem rhs_coefficient_8 (s : ℚ) :
    RHSC8 s = HC8 s := by
  simp only [RHSC8, HC8,
    Pair0_8,
    Pair1_7,
    Pair2_6,
    Pair3_5,
    Pair4_4,
    Pair5_3,
    Pair6_2,
    Pair7_1,
    Pair8_0,
    ]
  ring

def RawConvC9 (s : ℚ) : ℚ :=
  rawFC0 s * QNE9 s + rawFC1 s * QNE8 s + rawFC2 s * QNE7 s + rawFC3 s * QNE6 s + rawFC4 s *
    QNE5 s + rawFC5 s * QNE4 s + rawFC6 s * QNE3 s + rawFC7 s * QNE2 s + rawFC8 s * QNE1 s +
    rawFC9 s * QNE0 s

def RHSC9 (s : ℚ) : ℚ :=
  Pair0_9 s + Pair1_8 s + Pair2_7 s + Pair3_6 s + Pair4_5 s + Pair5_4 s + Pair6_3 s + Pair7_2 s
    + Pair8_1 s + Pair9_0 s

theorem raw_convolution_coefficient_9 (s : ℚ) :
    RawConvC9 s = RHSC9 s := by
  simp only [RawConvC9, RHSC9,
    pair_0_9,
    pair_1_8,
    pair_2_7,
    pair_3_6,
    pair_4_5,
    pair_5_4,
    pair_6_3,
    pair_7_2,
    pair_8_1,
    pair_9_0,
    ]

theorem rhs_coefficient_9 (s : ℚ) :
    RHSC9 s = HC9 s := by
  simp only [RHSC9, HC9,
    Pair0_9,
    Pair1_8,
    Pair2_7,
    Pair3_6,
    Pair4_5,
    Pair5_4,
    Pair6_3,
    Pair7_2,
    Pair8_1,
    Pair9_0,
    ]
  ring

def RawConvC10 (s : ℚ) : ℚ :=
  rawFC0 s * QNE10 s + rawFC1 s * QNE9 s + rawFC2 s * QNE8 s + rawFC3 s * QNE7 s + rawFC4 s *
    QNE6 s + rawFC5 s * QNE5 s + rawFC6 s * QNE4 s + rawFC7 s * QNE3 s + rawFC8 s * QNE2 s +
    rawFC9 s * QNE1 s + rawFC10 s * QNE0 s

def RHSC10 (s : ℚ) : ℚ :=
  Pair0_10 s + Pair1_9 s + Pair2_8 s + Pair3_7 s + Pair4_6 s + Pair5_5 s + Pair6_4 s + Pair7_3 s
    + Pair8_2 s + Pair9_1 s + Pair10_0 s

theorem raw_convolution_coefficient_10 (s : ℚ) :
    RawConvC10 s = RHSC10 s := by
  simp only [RawConvC10, RHSC10,
    pair_0_10,
    pair_1_9,
    pair_2_8,
    pair_3_7,
    pair_4_6,
    pair_5_5,
    pair_6_4,
    pair_7_3,
    pair_8_2,
    pair_9_1,
    pair_10_0,
    ]

theorem rhs_coefficient_10 (s : ℚ) :
    RHSC10 s = HC10 s := by
  simp only [RHSC10, HC10,
    Pair0_10,
    Pair1_9,
    Pair2_8,
    Pair3_7,
    Pair4_6,
    Pair5_5,
    Pair6_4,
    Pair7_3,
    Pair8_2,
    Pair9_1,
    Pair10_0,
    ]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
