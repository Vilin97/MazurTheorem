/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataMidLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataMidHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataMidLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataMidHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataHigh

/-!
# Shared data for the raw order-twenty-five division certificate

This leaf gives the row shards one canonical copy of Sutherland's polynomial,
the generated exact quotient, and the generated reduced numerator.  The data
are semantic only after the separate kernel-checked row certificates consume
every coefficient.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial

def divisionSutherlandPolynomial : Two :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 3, -6, 10, -15, 21, -28, 6],
    [0, 0, 0, 15, -45, 75, -91, 96, -126, 266, -231, 126, -56, 21, -6, 1],
    [0, 0, 0, -105, 340, -540, 470, 5, -705, 569, -181, 45, -35, 25, -9, 1],
    [0, 0, 0, 455, -1740, 3435, -4615, 4299, -1623, -433, 609, -165,
      -49, 48, -12, 1],
    [-1, 15, -120, -685, 3660, -8214, 12520, -15060, 12270, -6145,
      1587, 90, -245, 90, -15, 1],
    [5, -70, 555, -388, -2441, 7227, -11195, 14630, -15408, 11834,
      -6558, 2655, -770, 151, -18, 1],
    [-10, 126, -996, 2166, -1551, -789, 1289, -144, -351, 161, -21],
    [10, -105, 840, -2320, 3051, -1659, -185, 690, -345, 74, -6],
    [-5, 35, -294, 968, -1732, 1836, -1205, 494, -123, 17, -1],
    [1]]

def divisionQuotientData : Two :=
  QuotientDataLow ++ QuotientDataMidLow ++ QuotientDataMidHigh ++
    QuotientDataHigh

def divisionReducedData : Two :=
  ReducedDataLow ++ ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh

theorem divisionSutherland_outerSupport :
    divisionSutherlandPolynomial.length = 11 := by
  decide

theorem divisionSutherland_innerSupport :
    ∀ row ∈ divisionSutherlandPolynomial, row.length ≤ 16 := by
  decide

theorem divisionQuotient_outerSupport : divisionQuotientData.length = 73 := by
  simp [divisionQuotientData, QuotientDataLow, QuotientDataMidLow,
    QuotientDataMidHigh, QuotientDataHigh]

theorem divisionReduced_outerSupport : divisionReducedData.length = 83 := by
  simp [divisionReducedData, ReducedDataLow, ReducedDataMidLow,
    ReducedDataMidHigh, ReducedDataHigh]

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
