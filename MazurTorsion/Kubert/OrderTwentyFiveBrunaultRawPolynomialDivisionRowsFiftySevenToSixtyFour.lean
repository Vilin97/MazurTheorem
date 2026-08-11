/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 57 through 64 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow57_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  rw [show 57 = 47 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 47 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow57_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 57 = 47 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow57_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 57 = 47 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow57_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 57 = 47 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow57_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 57 = 47 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow57_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 57 = 47 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow57_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 57 = 47 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow57_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 95 := by
  rw [show 57 = 47 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 96 := by
  rw [show 57 = 47 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 97 := by
  rw [show 57 = 47 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 98 := by
  rw [show 57 = 47 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 99 := by
  rw [show 57 = 47 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 100 := by
  rw [show 57 = 47 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 101 := by
  rw [show 57 = 47 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 102 := by
  rw [show 57 = 47 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 103 := by
  rw [show 57 = 47 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 104 := by
  rw [show 57 = 47 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 105 := by
  rw [show 57 = 47 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 106 := by
  rw [show 57 = 47 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 107 := by
  rw [show 57 = 47 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow57_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 108 := by
  rw [show 57 = 47 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 109 := by
  rw [show 57 = 47 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 110 := by
  rw [show 57 = 47 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 111 := by
  rw [show 57 = 47 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 112 := by
  rw [show 57 = 47 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 113 := by
  rw [show 57 = 47 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 114 := by
  rw [show 57 = 47 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 115 := by
  rw [show 57 = 47 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 116 := by
  rw [show 57 = 47 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 117 := by
  rw [show 57 = 47 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 118 := by
  rw [show 57 = 47 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 119 := by
  rw [show 57 = 47 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 120 := by
  rw [show 57 = 47 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      47 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        57 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow57_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 57 j := by
  by_cases h15 : j < 15
  · exact divisionRow57_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow57_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow57_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow57_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow57_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow57_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow57_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow57_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow57_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow57_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow57_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow57_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow57_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow57_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow57_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow57_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow57_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow57_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow57_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow57_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow57_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow57_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow57_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow57_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow57_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow57_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow57_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow57_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow57_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow57_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow57_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow57_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow57_column120

private theorem divisionRow57_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 57 j =
      ((rectangularize 83 121 divisionReducedData).getD 57 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow57_windowCoefficients j hj

private theorem divisionRow57_targetSupport :
    (divisionReducedData.getD 57 []).length ≤ 121 := by
  rw [show 57 = 42 + 15 by omega,
    ← getD_drop_window divisionReducedData 42 15 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      15 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 15 0 []]
  decide

private theorem divisionRow57_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 57) =
      (rectangularize 83 121 divisionReducedData).getD 57 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 57
    ((rectangularize 83 121 divisionReducedData).getD 57 [])
  · rw [show 57 = 47 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        47 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 57 []).length ≤ 121 := by
      exact divisionRow57_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 57 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow57_coefficients

private theorem divisionRow58_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  rw [show 58 = 48 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 48 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow58_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 58 = 48 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow58_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 58 = 48 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow58_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 58 = 48 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow58_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 58 = 48 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow58_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 58 = 48 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow58_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 58 = 48 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow58_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 95 := by
  rw [show 58 = 48 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 96 := by
  rw [show 58 = 48 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 97 := by
  rw [show 58 = 48 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 98 := by
  rw [show 58 = 48 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 99 := by
  rw [show 58 = 48 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 100 := by
  rw [show 58 = 48 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 101 := by
  rw [show 58 = 48 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 102 := by
  rw [show 58 = 48 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 103 := by
  rw [show 58 = 48 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 104 := by
  rw [show 58 = 48 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 105 := by
  rw [show 58 = 48 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 106 := by
  rw [show 58 = 48 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow58_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 107 := by
  rw [show 58 = 48 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 108 := by
  rw [show 58 = 48 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 109 := by
  rw [show 58 = 48 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 110 := by
  rw [show 58 = 48 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 111 := by
  rw [show 58 = 48 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 112 := by
  rw [show 58 = 48 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 113 := by
  rw [show 58 = 48 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 114 := by
  rw [show 58 = 48 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 115 := by
  rw [show 58 = 48 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 116 := by
  rw [show 58 = 48 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 117 := by
  rw [show 58 = 48 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 118 := by
  rw [show 58 = 48 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 119 := by
  rw [show 58 = 48 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 120 := by
  rw [show 58 = 48 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      48 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        58 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow58_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 58 j := by
  by_cases h15 : j < 15
  · exact divisionRow58_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow58_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow58_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow58_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow58_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow58_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow58_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow58_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow58_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow58_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow58_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow58_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow58_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow58_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow58_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow58_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow58_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow58_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow58_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow58_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow58_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow58_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow58_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow58_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow58_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow58_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow58_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow58_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow58_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow58_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow58_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow58_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow58_column120

private theorem divisionRow58_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 58 j =
      ((rectangularize 83 121 divisionReducedData).getD 58 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow58_windowCoefficients j hj

private theorem divisionRow58_targetSupport :
    (divisionReducedData.getD 58 []).length ≤ 121 := by
  rw [show 58 = 42 + 16 by omega,
    ← getD_drop_window divisionReducedData 42 16 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      16 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 16 0 []]
  decide

private theorem divisionRow58_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 58) =
      (rectangularize 83 121 divisionReducedData).getD 58 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 58
    ((rectangularize 83 121 divisionReducedData).getD 58 [])
  · rw [show 58 = 48 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        48 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 58 []).length ≤ 121 := by
      exact divisionRow58_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 58 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow58_coefficients

private theorem divisionRow59_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  rw [show 59 = 49 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 49 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow59_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 59 = 49 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow59_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 59 = 49 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow59_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 59 = 49 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow59_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 59 = 49 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow59_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 59 = 49 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow59_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 59 = 49 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow59_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 95 := by
  rw [show 59 = 49 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 96 := by
  rw [show 59 = 49 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 97 := by
  rw [show 59 = 49 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 98 := by
  rw [show 59 = 49 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 99 := by
  rw [show 59 = 49 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 100 := by
  rw [show 59 = 49 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 101 := by
  rw [show 59 = 49 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 102 := by
  rw [show 59 = 49 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 103 := by
  rw [show 59 = 49 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 104 := by
  rw [show 59 = 49 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 105 := by
  rw [show 59 = 49 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow59_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 106 := by
  rw [show 59 = 49 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 107 := by
  rw [show 59 = 49 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 108 := by
  rw [show 59 = 49 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 109 := by
  rw [show 59 = 49 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 110 := by
  rw [show 59 = 49 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 111 := by
  rw [show 59 = 49 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 112 := by
  rw [show 59 = 49 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 113 := by
  rw [show 59 = 49 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 114 := by
  rw [show 59 = 49 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 115 := by
  rw [show 59 = 49 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 116 := by
  rw [show 59 = 49 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 117 := by
  rw [show 59 = 49 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 118 := by
  rw [show 59 = 49 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 119 := by
  rw [show 59 = 49 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 120 := by
  rw [show 59 = 49 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      49 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        59 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow59_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 59 j := by
  by_cases h15 : j < 15
  · exact divisionRow59_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow59_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow59_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow59_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow59_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow59_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow59_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow59_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow59_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow59_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow59_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow59_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow59_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow59_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow59_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow59_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow59_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow59_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow59_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow59_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow59_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow59_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow59_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow59_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow59_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow59_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow59_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow59_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow59_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow59_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow59_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow59_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow59_column120

private theorem divisionRow59_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 59 j =
      ((rectangularize 83 121 divisionReducedData).getD 59 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow59_windowCoefficients j hj

private theorem divisionRow59_targetSupport :
    (divisionReducedData.getD 59 []).length ≤ 121 := by
  rw [show 59 = 42 + 17 by omega,
    ← getD_drop_window divisionReducedData 42 17 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      17 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 17 0 []]
  decide

private theorem divisionRow59_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 59) =
      (rectangularize 83 121 divisionReducedData).getD 59 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 59
    ((rectangularize 83 121 divisionReducedData).getD 59 [])
  · rw [show 59 = 49 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        49 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 59 []).length ≤ 121 := by
      exact divisionRow59_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 59 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow59_coefficients

private theorem divisionRow60_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  rw [show 60 = 50 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 50 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow60_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 60 = 50 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow60_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 60 = 50 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow60_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 60 = 50 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow60_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 60 = 50 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow60_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 60 = 50 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow60_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 60 = 50 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow60_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 95 := by
  rw [show 60 = 50 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 96 := by
  rw [show 60 = 50 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 97 := by
  rw [show 60 = 50 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 98 := by
  rw [show 60 = 50 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 99 := by
  rw [show 60 = 50 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 100 := by
  rw [show 60 = 50 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 101 := by
  rw [show 60 = 50 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 102 := by
  rw [show 60 = 50 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 103 := by
  rw [show 60 = 50 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow60_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 104 := by
  rw [show 60 = 50 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 105 := by
  rw [show 60 = 50 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 106 := by
  rw [show 60 = 50 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 107 := by
  rw [show 60 = 50 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 108 := by
  rw [show 60 = 50 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 109 := by
  rw [show 60 = 50 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 110 := by
  rw [show 60 = 50 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 111 := by
  rw [show 60 = 50 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 112 := by
  rw [show 60 = 50 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 113 := by
  rw [show 60 = 50 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 114 := by
  rw [show 60 = 50 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 115 := by
  rw [show 60 = 50 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 116 := by
  rw [show 60 = 50 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 117 := by
  rw [show 60 = 50 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 118 := by
  rw [show 60 = 50 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 119 := by
  rw [show 60 = 50 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 120 := by
  rw [show 60 = 50 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      50 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        60 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow60_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 60 j := by
  by_cases h15 : j < 15
  · exact divisionRow60_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow60_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow60_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow60_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow60_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow60_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow60_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow60_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow60_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow60_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow60_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow60_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow60_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow60_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow60_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow60_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow60_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow60_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow60_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow60_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow60_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow60_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow60_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow60_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow60_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow60_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow60_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow60_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow60_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow60_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow60_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow60_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow60_column120

private theorem divisionRow60_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 60 j =
      ((rectangularize 83 121 divisionReducedData).getD 60 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow60_windowCoefficients j hj

private theorem divisionRow60_targetSupport :
    (divisionReducedData.getD 60 []).length ≤ 121 := by
  rw [show 60 = 42 + 18 by omega,
    ← getD_drop_window divisionReducedData 42 18 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      18 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 18 0 []]
  decide

private theorem divisionRow60_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 60) =
      (rectangularize 83 121 divisionReducedData).getD 60 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 60
    ((rectangularize 83 121 divisionReducedData).getD 60 [])
  · rw [show 60 = 50 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        50 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 60 []).length ≤ 121 := by
      exact divisionRow60_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 60 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow60_coefficients

private theorem divisionRow61_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  rw [show 61 = 51 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 51 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow61_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 61 = 51 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow61_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 61 = 51 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow61_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 61 = 51 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow61_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 61 = 51 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow61_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 61 = 51 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow61_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 61 = 51 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow61_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 95 := by
  rw [show 61 = 51 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 96 := by
  rw [show 61 = 51 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 97 := by
  rw [show 61 = 51 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 98 := by
  rw [show 61 = 51 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 99 := by
  rw [show 61 = 51 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 100 := by
  rw [show 61 = 51 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 101 := by
  rw [show 61 = 51 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 102 := by
  rw [show 61 = 51 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow61_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 103 := by
  rw [show 61 = 51 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 104 := by
  rw [show 61 = 51 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 105 := by
  rw [show 61 = 51 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 106 := by
  rw [show 61 = 51 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 107 := by
  rw [show 61 = 51 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 108 := by
  rw [show 61 = 51 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 109 := by
  rw [show 61 = 51 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 110 := by
  rw [show 61 = 51 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 111 := by
  rw [show 61 = 51 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 112 := by
  rw [show 61 = 51 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 113 := by
  rw [show 61 = 51 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 114 := by
  rw [show 61 = 51 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 115 := by
  rw [show 61 = 51 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 116 := by
  rw [show 61 = 51 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 117 := by
  rw [show 61 = 51 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 118 := by
  rw [show 61 = 51 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 119 := by
  rw [show 61 = 51 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 120 := by
  rw [show 61 = 51 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      51 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        61 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow61_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 61 j := by
  by_cases h15 : j < 15
  · exact divisionRow61_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow61_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow61_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow61_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow61_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow61_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow61_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow61_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow61_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow61_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow61_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow61_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow61_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow61_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow61_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow61_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow61_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow61_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow61_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow61_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow61_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow61_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow61_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow61_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow61_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow61_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow61_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow61_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow61_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow61_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow61_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow61_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow61_column120

private theorem divisionRow61_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 61 j =
      ((rectangularize 83 121 divisionReducedData).getD 61 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow61_windowCoefficients j hj

private theorem divisionRow61_targetSupport :
    (divisionReducedData.getD 61 []).length ≤ 121 := by
  rw [show 61 = 42 + 19 by omega,
    ← getD_drop_window divisionReducedData 42 19 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      19 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 19 0 []]
  decide

private theorem divisionRow61_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 61) =
      (rectangularize 83 121 divisionReducedData).getD 61 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 61
    ((rectangularize 83 121 divisionReducedData).getD 61 [])
  · rw [show 61 = 51 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        51 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 61 []).length ≤ 121 := by
      exact divisionRow61_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 61 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow61_coefficients

private theorem divisionRow62_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  rw [show 62 = 52 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 52 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow62_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 62 = 52 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow62_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 62 = 52 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow62_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 62 = 52 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow62_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 62 = 52 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow62_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 62 = 52 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow62_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 62 = 52 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow62_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 95 := by
  rw [show 62 = 52 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 96 := by
  rw [show 62 = 52 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 97 := by
  rw [show 62 = 52 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 98 := by
  rw [show 62 = 52 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 99 := by
  rw [show 62 = 52 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 100 := by
  rw [show 62 = 52 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 101 := by
  rw [show 62 = 52 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow62_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 102 := by
  rw [show 62 = 52 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 103 := by
  rw [show 62 = 52 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 104 := by
  rw [show 62 = 52 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 105 := by
  rw [show 62 = 52 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 106 := by
  rw [show 62 = 52 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 107 := by
  rw [show 62 = 52 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 108 := by
  rw [show 62 = 52 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 109 := by
  rw [show 62 = 52 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 110 := by
  rw [show 62 = 52 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 111 := by
  rw [show 62 = 52 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 112 := by
  rw [show 62 = 52 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 113 := by
  rw [show 62 = 52 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 114 := by
  rw [show 62 = 52 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 115 := by
  rw [show 62 = 52 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 116 := by
  rw [show 62 = 52 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 117 := by
  rw [show 62 = 52 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 118 := by
  rw [show 62 = 52 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 119 := by
  rw [show 62 = 52 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 120 := by
  rw [show 62 = 52 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      52 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        62 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow62_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 62 j := by
  by_cases h15 : j < 15
  · exact divisionRow62_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow62_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow62_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow62_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow62_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow62_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow62_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow62_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow62_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow62_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow62_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow62_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow62_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow62_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow62_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow62_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow62_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow62_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow62_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow62_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow62_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow62_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow62_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow62_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow62_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow62_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow62_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow62_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow62_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow62_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow62_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow62_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow62_column120

private theorem divisionRow62_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 62 j =
      ((rectangularize 83 121 divisionReducedData).getD 62 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow62_windowCoefficients j hj

private theorem divisionRow62_targetSupport :
    (divisionReducedData.getD 62 []).length ≤ 121 := by
  rw [show 62 = 42 + 20 by omega,
    ← getD_drop_window divisionReducedData 42 20 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      20 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 20 0 []]
  decide

private theorem divisionRow62_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 62) =
      (rectangularize 83 121 divisionReducedData).getD 62 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 62
    ((rectangularize 83 121 divisionReducedData).getD 62 [])
  · rw [show 62 = 52 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        52 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 62 []).length ≤ 121 := by
      exact divisionRow62_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 62 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow62_coefficients

private theorem divisionRow63_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  rw [show 63 = 53 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 53 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow63_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 63 = 53 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow63_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 63 = 53 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow63_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 63 = 53 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow63_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 63 = 53 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow63_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 63 = 53 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow63_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 63 = 53 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow63_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 95 := by
  rw [show 63 = 53 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow63_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 96 := by
  rw [show 63 = 53 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow63_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 97 := by
  rw [show 63 = 53 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow63_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 98 := by
  rw [show 63 = 53 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow63_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 99 := by
  rw [show 63 = 53 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 100 := by
  rw [show 63 = 53 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 101 := by
  rw [show 63 = 53 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 102 := by
  rw [show 63 = 53 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 103 := by
  rw [show 63 = 53 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 104 := by
  rw [show 63 = 53 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 105 := by
  rw [show 63 = 53 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 106 := by
  rw [show 63 = 53 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 107 := by
  rw [show 63 = 53 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 108 := by
  rw [show 63 = 53 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 109 := by
  rw [show 63 = 53 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 110 := by
  rw [show 63 = 53 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 111 := by
  rw [show 63 = 53 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 112 := by
  rw [show 63 = 53 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 113 := by
  rw [show 63 = 53 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 114 := by
  rw [show 63 = 53 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 115 := by
  rw [show 63 = 53 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 116 := by
  rw [show 63 = 53 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 117 := by
  rw [show 63 = 53 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 118 := by
  rw [show 63 = 53 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 119 := by
  rw [show 63 = 53 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 120 := by
  rw [show 63 = 53 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      53 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        63 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow63_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 63 j := by
  by_cases h15 : j < 15
  · exact divisionRow63_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow63_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow63_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow63_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow63_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow63_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow63_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow63_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow63_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow63_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow63_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow63_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow63_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow63_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow63_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow63_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow63_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow63_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow63_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow63_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow63_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow63_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow63_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow63_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow63_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow63_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow63_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow63_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow63_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow63_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow63_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow63_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow63_column120

private theorem divisionRow63_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 63 j =
      ((rectangularize 83 121 divisionReducedData).getD 63 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow63_windowCoefficients j hj

private theorem divisionRow63_targetSupport :
    (divisionReducedData.getD 63 []).length ≤ 121 := by
  rw [show 63 = 63 + 0 by omega,
    ← getD_drop_window divisionReducedData 63 0 []]
  change (ReducedDataHigh.getD 0 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 0 0 []]
  decide

private theorem divisionRow63_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 63) =
      (rectangularize 83 121 divisionReducedData).getD 63 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 63
    ((rectangularize 83 121 divisionReducedData).getD 63 [])
  · rw [show 63 = 53 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        53 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 63 []).length ≤ 121 := by
      exact divisionRow63_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 63 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow63_coefficients

private theorem divisionRow64_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  rw [show 64 = 54 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 54 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow64_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 64 = 54 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow64_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 64 = 54 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow64_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 64 = 54 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow64_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 64 = 54 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow64_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 64 = 54 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow64_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 64 = 54 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow64_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 95 := by
  rw [show 64 = 54 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow64_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 96 := by
  rw [show 64 = 54 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow64_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 97 := by
  rw [show 64 = 54 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow64_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 98 := by
  rw [show 64 = 54 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow64_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 99 := by
  rw [show 64 = 54 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 100 := by
  rw [show 64 = 54 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 101 := by
  rw [show 64 = 54 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 102 := by
  rw [show 64 = 54 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 103 := by
  rw [show 64 = 54 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 104 := by
  rw [show 64 = 54 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 105 := by
  rw [show 64 = 54 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 106 := by
  rw [show 64 = 54 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 107 := by
  rw [show 64 = 54 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 108 := by
  rw [show 64 = 54 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 109 := by
  rw [show 64 = 54 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 110 := by
  rw [show 64 = 54 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 111 := by
  rw [show 64 = 54 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 112 := by
  rw [show 64 = 54 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 113 := by
  rw [show 64 = 54 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 114 := by
  rw [show 64 = 54 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 115 := by
  rw [show 64 = 54 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 116 := by
  rw [show 64 = 54 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 117 := by
  rw [show 64 = 54 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 118 := by
  rw [show 64 = 54 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 119 := by
  rw [show 64 = 54 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 120 := by
  rw [show 64 = 54 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      54 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        64 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow64_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 64 j := by
  by_cases h15 : j < 15
  · exact divisionRow64_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow64_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow64_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow64_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow64_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow64_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow64_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow64_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow64_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow64_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow64_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow64_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow64_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow64_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow64_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow64_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow64_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow64_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow64_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow64_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow64_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow64_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow64_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow64_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow64_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow64_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow64_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow64_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow64_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow64_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow64_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow64_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow64_column120

private theorem divisionRow64_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 64 j =
      ((rectangularize 83 121 divisionReducedData).getD 64 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow64_windowCoefficients j hj

private theorem divisionRow64_targetSupport :
    (divisionReducedData.getD 64 []).length ≤ 121 := by
  rw [show 64 = 63 + 1 by omega,
    ← getD_drop_window divisionReducedData 63 1 []]
  change (ReducedDataHigh.getD 1 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 1 0 []]
  decide

private theorem divisionRow64_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 64) =
      (rectangularize 83 121 divisionReducedData).getD 64 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 64
    ((rectangularize 83 121 divisionReducedData).getD 64 [])
  · rw [show 64 = 54 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        54 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 64 []).length ≤ 121 := by
      exact divisionRow64_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 64 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow64_coefficients

/-- The complete exact-division certificates for rows 57 through 64. -/
theorem divisionRowsFiftySevenToSixtyFour_spec (n : ℕ)
    (hLower : 57 ≤ n) (hUpper : n < 65) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow57_spec
  · exact divisionRow58_spec
  · exact divisionRow59_spec
  · exact divisionRow60_spec
  · exact divisionRow61_spec
  · exact divisionRow62_spec
  · exact divisionRow63_spec
  · exact divisionRow64_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
