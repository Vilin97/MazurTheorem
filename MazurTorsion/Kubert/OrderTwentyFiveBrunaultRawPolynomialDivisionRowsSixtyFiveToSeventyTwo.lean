/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 65 through 72 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow65_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  rw [show 65 = 55 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 55 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow65_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 65 = 55 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow65_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 65 = 55 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow65_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 65 = 55 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow65_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 65 = 55 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow65_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 65 = 55 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow65_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 65 = 55 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow65_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 95 := by
  rw [show 65 = 55 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow65_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 96 := by
  rw [show 65 = 55 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow65_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 97 := by
  rw [show 65 = 55 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 98 := by
  rw [show 65 = 55 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 99 := by
  rw [show 65 = 55 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 100 := by
  rw [show 65 = 55 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 101 := by
  rw [show 65 = 55 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 102 := by
  rw [show 65 = 55 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 103 := by
  rw [show 65 = 55 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 104 := by
  rw [show 65 = 55 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 105 := by
  rw [show 65 = 55 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 106 := by
  rw [show 65 = 55 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 107 := by
  rw [show 65 = 55 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 108 := by
  rw [show 65 = 55 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 109 := by
  rw [show 65 = 55 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 110 := by
  rw [show 65 = 55 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 111 := by
  rw [show 65 = 55 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 112 := by
  rw [show 65 = 55 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 113 := by
  rw [show 65 = 55 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 114 := by
  rw [show 65 = 55 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 115 := by
  rw [show 65 = 55 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 116 := by
  rw [show 65 = 55 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 117 := by
  rw [show 65 = 55 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 118 := by
  rw [show 65 = 55 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 119 := by
  rw [show 65 = 55 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 120 := by
  rw [show 65 = 55 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      55 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        65 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow65_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 65 j := by
  by_cases h15 : j < 15
  · exact divisionRow65_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow65_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow65_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow65_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow65_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow65_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow65_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow65_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow65_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow65_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow65_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow65_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow65_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow65_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow65_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow65_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow65_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow65_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow65_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow65_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow65_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow65_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow65_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow65_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow65_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow65_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow65_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow65_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow65_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow65_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow65_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow65_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow65_column120

private theorem divisionRow65_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 65 j =
      ((rectangularize 83 121 divisionReducedData).getD 65 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow65_windowCoefficients j hj

private theorem divisionRow65_targetSupport :
    (divisionReducedData.getD 65 []).length ≤ 121 := by
  rw [show 65 = 63 + 2 by omega,
    ← getD_drop_window divisionReducedData 63 2 []]
  change (ReducedDataHigh.getD 2 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 2 0 []]
  decide

private theorem divisionRow65_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 65) =
      (rectangularize 83 121 divisionReducedData).getD 65 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 65
    ((rectangularize 83 121 divisionReducedData).getD 65 [])
  · rw [show 65 = 55 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        55 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 65 []).length ≤ 121 := by
      exact divisionRow65_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 65 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow65_coefficients

private theorem divisionRow66_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  rw [show 66 = 56 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 56 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow66_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 66 = 56 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow66_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 66 = 56 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow66_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 66 = 56 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow66_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 66 = 56 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow66_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 66 = 56 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow66_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 66 = 56 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow66_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 95 := by
  rw [show 66 = 56 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow66_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 96 := by
  rw [show 66 = 56 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 97 := by
  rw [show 66 = 56 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 98 := by
  rw [show 66 = 56 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 99 := by
  rw [show 66 = 56 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 100 := by
  rw [show 66 = 56 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 101 := by
  rw [show 66 = 56 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 102 := by
  rw [show 66 = 56 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 103 := by
  rw [show 66 = 56 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 104 := by
  rw [show 66 = 56 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 105 := by
  rw [show 66 = 56 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 106 := by
  rw [show 66 = 56 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 107 := by
  rw [show 66 = 56 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 108 := by
  rw [show 66 = 56 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 109 := by
  rw [show 66 = 56 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 110 := by
  rw [show 66 = 56 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 111 := by
  rw [show 66 = 56 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 112 := by
  rw [show 66 = 56 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 113 := by
  rw [show 66 = 56 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 114 := by
  rw [show 66 = 56 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 115 := by
  rw [show 66 = 56 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 116 := by
  rw [show 66 = 56 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 117 := by
  rw [show 66 = 56 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 118 := by
  rw [show 66 = 56 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 119 := by
  rw [show 66 = 56 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 120 := by
  rw [show 66 = 56 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      56 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        66 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow66_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 66 j := by
  by_cases h15 : j < 15
  · exact divisionRow66_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow66_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow66_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow66_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow66_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow66_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow66_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow66_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow66_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow66_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow66_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow66_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow66_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow66_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow66_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow66_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow66_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow66_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow66_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow66_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow66_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow66_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow66_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow66_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow66_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow66_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow66_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow66_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow66_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow66_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow66_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow66_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow66_column120

private theorem divisionRow66_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 66 j =
      ((rectangularize 83 121 divisionReducedData).getD 66 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow66_windowCoefficients j hj

private theorem divisionRow66_targetSupport :
    (divisionReducedData.getD 66 []).length ≤ 121 := by
  rw [show 66 = 63 + 3 by omega,
    ← getD_drop_window divisionReducedData 63 3 []]
  change (ReducedDataHigh.getD 3 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 3 0 []]
  decide

private theorem divisionRow66_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 66) =
      (rectangularize 83 121 divisionReducedData).getD 66 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 66
    ((rectangularize 83 121 divisionReducedData).getD 66 [])
  · rw [show 66 = 56 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        56 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 66 []).length ≤ 121 := by
      exact divisionRow66_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 66 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow66_coefficients

private theorem divisionRow67_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  rw [show 67 = 57 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 57 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow67_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 67 = 57 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow67_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 67 = 57 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow67_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 67 = 57 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow67_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 67 = 57 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow67_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 67 = 57 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow67_columns90To93
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 94) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 67 = 57 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow67_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 94 := by
  rw [show 67 = 57 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 95 := by
  rw [show 67 = 57 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 96 := by
  rw [show 67 = 57 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 97 := by
  rw [show 67 = 57 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 98 := by
  rw [show 67 = 57 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 99 := by
  rw [show 67 = 57 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 100 := by
  rw [show 67 = 57 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 101 := by
  rw [show 67 = 57 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 102 := by
  rw [show 67 = 57 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 103 := by
  rw [show 67 = 57 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 104 := by
  rw [show 67 = 57 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 105 := by
  rw [show 67 = 57 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 106 := by
  rw [show 67 = 57 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 107 := by
  rw [show 67 = 57 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 108 := by
  rw [show 67 = 57 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 109 := by
  rw [show 67 = 57 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 110 := by
  rw [show 67 = 57 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 111 := by
  rw [show 67 = 57 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 112 := by
  rw [show 67 = 57 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 113 := by
  rw [show 67 = 57 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 114 := by
  rw [show 67 = 57 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 115 := by
  rw [show 67 = 57 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 116 := by
  rw [show 67 = 57 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 117 := by
  rw [show 67 = 57 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 118 := by
  rw [show 67 = 57 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 119 := by
  rw [show 67 = 57 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 120 := by
  rw [show 67 = 57 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      57 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        67 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow67_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 67 j := by
  by_cases h15 : j < 15
  · exact divisionRow67_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow67_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow67_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow67_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow67_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow67_columns75To89 j (by omega) h90
  by_cases h94 : j < 94
  · exact divisionRow67_columns90To93 j (by omega) h94
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow67_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow67_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow67_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow67_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow67_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow67_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow67_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow67_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow67_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow67_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow67_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow67_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow67_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow67_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow67_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow67_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow67_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow67_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow67_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow67_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow67_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow67_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow67_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow67_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow67_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow67_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow67_column120

private theorem divisionRow67_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 67 j =
      ((rectangularize 83 121 divisionReducedData).getD 67 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow67_windowCoefficients j hj

private theorem divisionRow67_targetSupport :
    (divisionReducedData.getD 67 []).length ≤ 121 := by
  rw [show 67 = 63 + 4 by omega,
    ← getD_drop_window divisionReducedData 63 4 []]
  change (ReducedDataHigh.getD 4 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 4 0 []]
  decide

private theorem divisionRow67_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 67) =
      (rectangularize 83 121 divisionReducedData).getD 67 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 67
    ((rectangularize 83 121 divisionReducedData).getD 67 [])
  · rw [show 67 = 57 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        57 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 67 []).length ≤ 121 := by
      exact divisionRow67_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 67 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow67_coefficients

private theorem divisionRow68_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  rw [show 68 = 58 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 58 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow68_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 68 = 58 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow68_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 68 = 58 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow68_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 68 = 58 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow68_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 68 = 58 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow68_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 68 = 58 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow68_columns90To91
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 92) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 68 = 58 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow68_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 92 := by
  rw [show 68 = 58 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 93 := by
  rw [show 68 = 58 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 94 := by
  rw [show 68 = 58 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 95 := by
  rw [show 68 = 58 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 96 := by
  rw [show 68 = 58 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 97 := by
  rw [show 68 = 58 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 98 := by
  rw [show 68 = 58 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 99 := by
  rw [show 68 = 58 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 100 := by
  rw [show 68 = 58 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 101 := by
  rw [show 68 = 58 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 102 := by
  rw [show 68 = 58 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 103 := by
  rw [show 68 = 58 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 104 := by
  rw [show 68 = 58 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 105 := by
  rw [show 68 = 58 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 106 := by
  rw [show 68 = 58 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 107 := by
  rw [show 68 = 58 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 108 := by
  rw [show 68 = 58 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 109 := by
  rw [show 68 = 58 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 110 := by
  rw [show 68 = 58 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 111 := by
  rw [show 68 = 58 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 112 := by
  rw [show 68 = 58 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 113 := by
  rw [show 68 = 58 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 114 := by
  rw [show 68 = 58 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 115 := by
  rw [show 68 = 58 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 116 := by
  rw [show 68 = 58 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 117 := by
  rw [show 68 = 58 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 118 := by
  rw [show 68 = 58 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 119 := by
  rw [show 68 = 58 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 120 := by
  rw [show 68 = 58 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      58 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        68 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow68_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 68 j := by
  by_cases h15 : j < 15
  · exact divisionRow68_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow68_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow68_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow68_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow68_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow68_columns75To89 j (by omega) h90
  by_cases h92 : j < 92
  · exact divisionRow68_columns90To91 j (by omega) h92
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow68_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow68_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow68_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow68_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow68_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow68_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow68_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow68_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow68_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow68_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow68_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow68_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow68_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow68_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow68_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow68_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow68_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow68_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow68_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow68_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow68_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow68_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow68_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow68_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow68_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow68_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow68_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow68_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow68_column120

private theorem divisionRow68_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 68 j =
      ((rectangularize 83 121 divisionReducedData).getD 68 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow68_windowCoefficients j hj

private theorem divisionRow68_targetSupport :
    (divisionReducedData.getD 68 []).length ≤ 121 := by
  rw [show 68 = 63 + 5 by omega,
    ← getD_drop_window divisionReducedData 63 5 []]
  change (ReducedDataHigh.getD 5 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 5 0 []]
  decide

private theorem divisionRow68_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 68) =
      (rectangularize 83 121 divisionReducedData).getD 68 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 68
    ((rectangularize 83 121 divisionReducedData).getD 68 [])
  · rw [show 68 = 58 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        58 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 68 []).length ≤ 121 := by
      exact divisionRow68_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 68 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow68_coefficients

private theorem divisionRow69_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  rw [show 69 = 59 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 59 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow69_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 69 = 59 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow69_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 69 = 59 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow69_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 69 = 59 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow69_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 69 = 59 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow69_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 69 = 59 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow69_columns90To90
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 91) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 69 = 59 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j
  decide

private theorem divisionRow69_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 91 := by
  rw [show 69 = 59 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 92 := by
  rw [show 69 = 59 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 93 := by
  rw [show 69 = 59 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 94 := by
  rw [show 69 = 59 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 95 := by
  rw [show 69 = 59 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 96 := by
  rw [show 69 = 59 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 97 := by
  rw [show 69 = 59 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 98 := by
  rw [show 69 = 59 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 99 := by
  rw [show 69 = 59 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 100 := by
  rw [show 69 = 59 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 101 := by
  rw [show 69 = 59 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 102 := by
  rw [show 69 = 59 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 103 := by
  rw [show 69 = 59 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 104 := by
  rw [show 69 = 59 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 105 := by
  rw [show 69 = 59 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 106 := by
  rw [show 69 = 59 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 107 := by
  rw [show 69 = 59 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 108 := by
  rw [show 69 = 59 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 109 := by
  rw [show 69 = 59 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 110 := by
  rw [show 69 = 59 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 111 := by
  rw [show 69 = 59 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 112 := by
  rw [show 69 = 59 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 113 := by
  rw [show 69 = 59 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 114 := by
  rw [show 69 = 59 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 115 := by
  rw [show 69 = 59 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 116 := by
  rw [show 69 = 59 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 117 := by
  rw [show 69 = 59 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 118 := by
  rw [show 69 = 59 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 119 := by
  rw [show 69 = 59 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 120 := by
  rw [show 69 = 59 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      59 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        69 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow69_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 69 j := by
  by_cases h15 : j < 15
  · exact divisionRow69_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow69_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow69_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow69_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow69_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow69_columns75To89 j (by omega) h90
  by_cases h91 : j < 91
  · exact divisionRow69_columns90To90 j (by omega) h91
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow69_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow69_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow69_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow69_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow69_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow69_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow69_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow69_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow69_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow69_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow69_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow69_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow69_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow69_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow69_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow69_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow69_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow69_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow69_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow69_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow69_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow69_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow69_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow69_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow69_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow69_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow69_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow69_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow69_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow69_column120

private theorem divisionRow69_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 69 j =
      ((rectangularize 83 121 divisionReducedData).getD 69 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow69_windowCoefficients j hj

private theorem divisionRow69_targetSupport :
    (divisionReducedData.getD 69 []).length ≤ 121 := by
  rw [show 69 = 63 + 6 by omega,
    ← getD_drop_window divisionReducedData 63 6 []]
  change (ReducedDataHigh.getD 6 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 6 0 []]
  decide

private theorem divisionRow69_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 69) =
      (rectangularize 83 121 divisionReducedData).getD 69 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 69
    ((rectangularize 83 121 divisionReducedData).getD 69 [])
  · rw [show 69 = 59 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        59 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 69 []).length ≤ 121 := by
      exact divisionRow69_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 69 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow69_coefficients

private theorem divisionRow70_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  rw [show 70 = 60 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 60 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow70_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 70 = 60 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow70_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 70 = 60 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow70_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 70 = 60 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow70_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 70 = 60 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow70_columns75To87
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 88) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 70 = 60 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow70_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 88 := by
  rw [show 70 = 60 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 89 := by
  rw [show 70 = 60 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 90 := by
  rw [show 70 = 60 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 91 := by
  rw [show 70 = 60 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 92 := by
  rw [show 70 = 60 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 93 := by
  rw [show 70 = 60 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 94 := by
  rw [show 70 = 60 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 95 := by
  rw [show 70 = 60 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 96 := by
  rw [show 70 = 60 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 97 := by
  rw [show 70 = 60 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 98 := by
  rw [show 70 = 60 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 99 := by
  rw [show 70 = 60 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 100 := by
  rw [show 70 = 60 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 101 := by
  rw [show 70 = 60 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 102 := by
  rw [show 70 = 60 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 103 := by
  rw [show 70 = 60 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 104 := by
  rw [show 70 = 60 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 105 := by
  rw [show 70 = 60 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 106 := by
  rw [show 70 = 60 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 107 := by
  rw [show 70 = 60 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 108 := by
  rw [show 70 = 60 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 109 := by
  rw [show 70 = 60 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 110 := by
  rw [show 70 = 60 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 111 := by
  rw [show 70 = 60 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 112 := by
  rw [show 70 = 60 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 113 := by
  rw [show 70 = 60 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 114 := by
  rw [show 70 = 60 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 115 := by
  rw [show 70 = 60 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 116 := by
  rw [show 70 = 60 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 117 := by
  rw [show 70 = 60 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 118 := by
  rw [show 70 = 60 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 119 := by
  rw [show 70 = 60 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 120 := by
  rw [show 70 = 60 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      60 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        70 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow70_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 70 j := by
  by_cases h15 : j < 15
  · exact divisionRow70_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow70_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow70_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow70_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow70_columns60To74 j (by omega) h75
  by_cases h88 : j < 88
  · exact divisionRow70_columns75To87 j (by omega) h88
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow70_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow70_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow70_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow70_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow70_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow70_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow70_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow70_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow70_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow70_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow70_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow70_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow70_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow70_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow70_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow70_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow70_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow70_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow70_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow70_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow70_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow70_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow70_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow70_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow70_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow70_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow70_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow70_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow70_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow70_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow70_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow70_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow70_column120

private theorem divisionRow70_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 70 j =
      ((rectangularize 83 121 divisionReducedData).getD 70 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow70_windowCoefficients j hj

private theorem divisionRow70_targetSupport :
    (divisionReducedData.getD 70 []).length ≤ 121 := by
  rw [show 70 = 63 + 7 by omega,
    ← getD_drop_window divisionReducedData 63 7 []]
  change (ReducedDataHigh.getD 7 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 7 0 []]
  decide

private theorem divisionRow70_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 70) =
      (rectangularize 83 121 divisionReducedData).getD 70 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 70
    ((rectangularize 83 121 divisionReducedData).getD 70 [])
  · rw [show 70 = 60 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        60 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 70 []).length ≤ 121 := by
      exact divisionRow70_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 70 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow70_coefficients

private theorem divisionRow71_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  rw [show 71 = 61 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 61 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow71_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 71 = 61 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow71_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 71 = 61 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow71_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 71 = 61 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow71_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 71 = 61 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow71_columns75To85
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 86) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 71 = 61 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow71_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 86 := by
  rw [show 71 = 61 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 87 := by
  rw [show 71 = 61 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 88 := by
  rw [show 71 = 61 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 89 := by
  rw [show 71 = 61 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 90 := by
  rw [show 71 = 61 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 91 := by
  rw [show 71 = 61 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 92 := by
  rw [show 71 = 61 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 93 := by
  rw [show 71 = 61 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 94 := by
  rw [show 71 = 61 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 95 := by
  rw [show 71 = 61 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 96 := by
  rw [show 71 = 61 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 97 := by
  rw [show 71 = 61 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 98 := by
  rw [show 71 = 61 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 99 := by
  rw [show 71 = 61 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 100 := by
  rw [show 71 = 61 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 101 := by
  rw [show 71 = 61 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 102 := by
  rw [show 71 = 61 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 103 := by
  rw [show 71 = 61 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 104 := by
  rw [show 71 = 61 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 105 := by
  rw [show 71 = 61 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 106 := by
  rw [show 71 = 61 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 107 := by
  rw [show 71 = 61 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 108 := by
  rw [show 71 = 61 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 109 := by
  rw [show 71 = 61 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 110 := by
  rw [show 71 = 61 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 111 := by
  rw [show 71 = 61 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 112 := by
  rw [show 71 = 61 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 113 := by
  rw [show 71 = 61 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 114 := by
  rw [show 71 = 61 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 115 := by
  rw [show 71 = 61 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 116 := by
  rw [show 71 = 61 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 117 := by
  rw [show 71 = 61 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 118 := by
  rw [show 71 = 61 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 119 := by
  rw [show 71 = 61 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 120 := by
  rw [show 71 = 61 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      61 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        71 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow71_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 71 j := by
  by_cases h15 : j < 15
  · exact divisionRow71_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow71_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow71_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow71_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow71_columns60To74 j (by omega) h75
  by_cases h86 : j < 86
  · exact divisionRow71_columns75To85 j (by omega) h86
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow71_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow71_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow71_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow71_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow71_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow71_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow71_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow71_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow71_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow71_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow71_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow71_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow71_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow71_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow71_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow71_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow71_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow71_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow71_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow71_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow71_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow71_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow71_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow71_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow71_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow71_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow71_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow71_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow71_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow71_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow71_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow71_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow71_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow71_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow71_column120

private theorem divisionRow71_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 71 j =
      ((rectangularize 83 121 divisionReducedData).getD 71 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow71_windowCoefficients j hj

private theorem divisionRow71_targetSupport :
    (divisionReducedData.getD 71 []).length ≤ 121 := by
  rw [show 71 = 63 + 8 by omega,
    ← getD_drop_window divisionReducedData 63 8 []]
  change (ReducedDataHigh.getD 8 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 8 0 []]
  decide

private theorem divisionRow71_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 71) =
      (rectangularize 83 121 divisionReducedData).getD 71 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 71
    ((rectangularize 83 121 divisionReducedData).getD 71 [])
  · rw [show 71 = 61 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        61 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 71 []).length ≤ 121 := by
      exact divisionRow71_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 71 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow71_coefficients

private theorem divisionRow72_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  rw [show 72 = 62 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 62 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow72_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 72 = 62 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow72_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 72 = 62 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow72_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 72 = 62 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow72_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 72 = 62 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow72_columns75To83
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 84) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 72 = 62 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow72_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 84 := by
  rw [show 72 = 62 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 85 := by
  rw [show 72 = 62 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 86 := by
  rw [show 72 = 62 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 87 := by
  rw [show 72 = 62 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 88 := by
  rw [show 72 = 62 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 89 := by
  rw [show 72 = 62 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 90 := by
  rw [show 72 = 62 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 91 := by
  rw [show 72 = 62 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 92 := by
  rw [show 72 = 62 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 93 := by
  rw [show 72 = 62 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 94 := by
  rw [show 72 = 62 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 95 := by
  rw [show 72 = 62 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 96 := by
  rw [show 72 = 62 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 97 := by
  rw [show 72 = 62 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 98 := by
  rw [show 72 = 62 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 99 := by
  rw [show 72 = 62 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 100 := by
  rw [show 72 = 62 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 101 := by
  rw [show 72 = 62 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 102 := by
  rw [show 72 = 62 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 103 := by
  rw [show 72 = 62 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 104 := by
  rw [show 72 = 62 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 105 := by
  rw [show 72 = 62 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 106 := by
  rw [show 72 = 62 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 107 := by
  rw [show 72 = 62 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 108 := by
  rw [show 72 = 62 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 109 := by
  rw [show 72 = 62 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 110 := by
  rw [show 72 = 62 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 111 := by
  rw [show 72 = 62 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 112 := by
  rw [show 72 = 62 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 113 := by
  rw [show 72 = 62 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 114 := by
  rw [show 72 = 62 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 115 := by
  rw [show 72 = 62 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 116 := by
  rw [show 72 = 62 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 117 := by
  rw [show 72 = 62 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 118 := by
  rw [show 72 = 62 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 119 := by
  rw [show 72 = 62 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 120 := by
  rw [show 72 = 62 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      62 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        72 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow72_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 72 j := by
  by_cases h15 : j < 15
  · exact divisionRow72_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow72_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow72_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow72_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow72_columns60To74 j (by omega) h75
  by_cases h84 : j < 84
  · exact divisionRow72_columns75To83 j (by omega) h84
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow72_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow72_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow72_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow72_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow72_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow72_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow72_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow72_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow72_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow72_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow72_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow72_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow72_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow72_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow72_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow72_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow72_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow72_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow72_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow72_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow72_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow72_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow72_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow72_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow72_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow72_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow72_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow72_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow72_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow72_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow72_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow72_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow72_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow72_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow72_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow72_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow72_column120

private theorem divisionRow72_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 72 j =
      ((rectangularize 83 121 divisionReducedData).getD 72 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow72_windowCoefficients j hj

private theorem divisionRow72_targetSupport :
    (divisionReducedData.getD 72 []).length ≤ 121 := by
  rw [show 72 = 63 + 9 by omega,
    ← getD_drop_window divisionReducedData 63 9 []]
  change (ReducedDataHigh.getD 9 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 9 0 []]
  decide

private theorem divisionRow72_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 72) =
      (rectangularize 83 121 divisionReducedData).getD 72 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 72
    ((rectangularize 83 121 divisionReducedData).getD 72 [])
  · rw [show 72 = 62 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        62 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 72 []).length ≤ 121 := by
      exact divisionRow72_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 72 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow72_coefficients

/-- The complete exact-division certificates for rows 65 through 72. -/
theorem divisionRowsSixtyFiveToSeventyTwo_spec (n : ℕ)
    (hLower : 65 ≤ n) (hUpper : n < 73) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow65_spec
  · exact divisionRow66_spec
  · exact divisionRow67_spec
  · exact divisionRow68_spec
  · exact divisionRow69_spec
  · exact divisionRow70_spec
  · exact divisionRow71_spec
  · exact divisionRow72_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
