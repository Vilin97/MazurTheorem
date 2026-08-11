/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 49 through 56 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow49_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  rw [show 49 = 39 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 39 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow49_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 49 = 39 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow49_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 49 = 39 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow49_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 49 = 39 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow49_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 49 = 39 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow49_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 49 = 39 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow49_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 49 = 39 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow49_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 95 := by
  rw [show 49 = 39 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 96 := by
  rw [show 49 = 39 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 97 := by
  rw [show 49 = 39 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 98 := by
  rw [show 49 = 39 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 99 := by
  rw [show 49 = 39 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 100 := by
  rw [show 49 = 39 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 101 := by
  rw [show 49 = 39 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 102 := by
  rw [show 49 = 39 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 103 := by
  rw [show 49 = 39 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 104 := by
  rw [show 49 = 39 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 105 := by
  rw [show 49 = 39 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 106 := by
  rw [show 49 = 39 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 107 := by
  rw [show 49 = 39 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 108 := by
  rw [show 49 = 39 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 109 := by
  rw [show 49 = 39 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 110 := by
  rw [show 49 = 39 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 111 := by
  rw [show 49 = 39 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 112 := by
  rw [show 49 = 39 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 113 := by
  rw [show 49 = 39 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 114 := by
  rw [show 49 = 39 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 115 := by
  rw [show 49 = 39 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 116 := by
  rw [show 49 = 39 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 117 := by
  rw [show 49 = 39 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 118 := by
  rw [show 49 = 39 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow49_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 119 := by
  rw [show 49 = 39 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        49 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow49_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 120 := by
  rw [show 49 = 39 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      39 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        49 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow49_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 49 j := by
  by_cases h15 : j < 15
  · exact divisionRow49_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow49_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow49_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow49_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow49_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow49_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow49_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow49_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow49_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow49_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow49_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow49_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow49_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow49_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow49_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow49_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow49_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow49_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow49_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow49_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow49_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow49_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow49_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow49_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow49_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow49_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow49_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow49_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow49_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow49_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow49_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow49_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow49_column120

private theorem divisionRow49_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 49 j =
      ((rectangularize 83 121 divisionReducedData).getD 49 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow49_windowCoefficients j hj

private theorem divisionRow49_targetSupport :
    (divisionReducedData.getD 49 []).length ≤ 121 := by
  rw [show 49 = 42 + 7 by omega,
    ← getD_drop_window divisionReducedData 42 7 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      7 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 7 0 []]
  decide

private theorem divisionRow49_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 49) =
      (rectangularize 83 121 divisionReducedData).getD 49 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 49
    ((rectangularize 83 121 divisionReducedData).getD 49 [])
  · rw [show 49 = 39 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        39 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 49 []).length ≤ 121 := by
      exact divisionRow49_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 49 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow49_coefficients

private theorem divisionRow50_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  rw [show 50 = 40 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 40 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow50_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 50 = 40 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow50_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 50 = 40 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow50_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 50 = 40 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow50_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 50 = 40 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow50_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 50 = 40 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow50_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 50 = 40 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow50_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 95 := by
  rw [show 50 = 40 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 96 := by
  rw [show 50 = 40 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 97 := by
  rw [show 50 = 40 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 98 := by
  rw [show 50 = 40 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 99 := by
  rw [show 50 = 40 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 100 := by
  rw [show 50 = 40 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 101 := by
  rw [show 50 = 40 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 102 := by
  rw [show 50 = 40 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 103 := by
  rw [show 50 = 40 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 104 := by
  rw [show 50 = 40 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 105 := by
  rw [show 50 = 40 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 106 := by
  rw [show 50 = 40 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 107 := by
  rw [show 50 = 40 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 108 := by
  rw [show 50 = 40 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 109 := by
  rw [show 50 = 40 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 110 := by
  rw [show 50 = 40 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 111 := by
  rw [show 50 = 40 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 112 := by
  rw [show 50 = 40 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 113 := by
  rw [show 50 = 40 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 114 := by
  rw [show 50 = 40 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 115 := by
  rw [show 50 = 40 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 116 := by
  rw [show 50 = 40 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow50_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 117 := by
  rw [show 50 = 40 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        50 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow50_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 118 := by
  rw [show 50 = 40 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        50 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow50_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 119 := by
  rw [show 50 = 40 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        50 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow50_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 120 := by
  rw [show 50 = 40 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      40 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        50 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow50_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 50 j := by
  by_cases h15 : j < 15
  · exact divisionRow50_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow50_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow50_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow50_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow50_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow50_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow50_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow50_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow50_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow50_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow50_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow50_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow50_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow50_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow50_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow50_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow50_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow50_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow50_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow50_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow50_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow50_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow50_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow50_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow50_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow50_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow50_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow50_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow50_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow50_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow50_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow50_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow50_column120

private theorem divisionRow50_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 50 j =
      ((rectangularize 83 121 divisionReducedData).getD 50 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow50_windowCoefficients j hj

private theorem divisionRow50_targetSupport :
    (divisionReducedData.getD 50 []).length ≤ 121 := by
  rw [show 50 = 42 + 8 by omega,
    ← getD_drop_window divisionReducedData 42 8 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      8 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 8 0 []]
  decide

private theorem divisionRow50_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 50) =
      (rectangularize 83 121 divisionReducedData).getD 50 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 50
    ((rectangularize 83 121 divisionReducedData).getD 50 [])
  · rw [show 50 = 40 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        40 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 50 []).length ≤ 121 := by
      exact divisionRow50_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 50 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow50_coefficients

private theorem divisionRow51_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  rw [show 51 = 41 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 41 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow51_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 51 = 41 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow51_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 51 = 41 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow51_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 51 = 41 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow51_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 51 = 41 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow51_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 51 = 41 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow51_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 51 = 41 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow51_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 95 := by
  rw [show 51 = 41 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 96 := by
  rw [show 51 = 41 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 97 := by
  rw [show 51 = 41 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 98 := by
  rw [show 51 = 41 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 99 := by
  rw [show 51 = 41 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 100 := by
  rw [show 51 = 41 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 101 := by
  rw [show 51 = 41 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 102 := by
  rw [show 51 = 41 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 103 := by
  rw [show 51 = 41 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 104 := by
  rw [show 51 = 41 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 105 := by
  rw [show 51 = 41 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 106 := by
  rw [show 51 = 41 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 107 := by
  rw [show 51 = 41 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 108 := by
  rw [show 51 = 41 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 109 := by
  rw [show 51 = 41 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 110 := by
  rw [show 51 = 41 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 111 := by
  rw [show 51 = 41 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 112 := by
  rw [show 51 = 41 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 113 := by
  rw [show 51 = 41 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 114 := by
  rw [show 51 = 41 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 115 := by
  rw [show 51 = 41 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow51_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 116 := by
  rw [show 51 = 41 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        51 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow51_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 117 := by
  rw [show 51 = 41 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        51 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow51_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 118 := by
  rw [show 51 = 41 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        51 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow51_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 119 := by
  rw [show 51 = 41 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        51 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow51_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 120 := by
  rw [show 51 = 41 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      41 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        51 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow51_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 51 j := by
  by_cases h15 : j < 15
  · exact divisionRow51_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow51_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow51_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow51_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow51_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow51_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow51_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow51_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow51_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow51_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow51_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow51_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow51_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow51_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow51_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow51_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow51_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow51_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow51_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow51_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow51_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow51_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow51_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow51_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow51_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow51_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow51_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow51_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow51_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow51_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow51_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow51_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow51_column120

private theorem divisionRow51_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 51 j =
      ((rectangularize 83 121 divisionReducedData).getD 51 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow51_windowCoefficients j hj

private theorem divisionRow51_targetSupport :
    (divisionReducedData.getD 51 []).length ≤ 121 := by
  rw [show 51 = 42 + 9 by omega,
    ← getD_drop_window divisionReducedData 42 9 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      9 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 9 0 []]
  decide

private theorem divisionRow51_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 51) =
      (rectangularize 83 121 divisionReducedData).getD 51 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 51
    ((rectangularize 83 121 divisionReducedData).getD 51 [])
  · rw [show 51 = 41 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        41 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 51 []).length ≤ 121 := by
      exact divisionRow51_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 51 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow51_coefficients

private theorem divisionRow52_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  rw [show 52 = 42 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 42 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow52_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 52 = 42 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow52_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 52 = 42 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow52_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 52 = 42 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow52_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 52 = 42 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow52_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 52 = 42 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow52_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 52 = 42 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow52_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 95 := by
  rw [show 52 = 42 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 96 := by
  rw [show 52 = 42 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 97 := by
  rw [show 52 = 42 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 98 := by
  rw [show 52 = 42 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 99 := by
  rw [show 52 = 42 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 100 := by
  rw [show 52 = 42 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 101 := by
  rw [show 52 = 42 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 102 := by
  rw [show 52 = 42 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 103 := by
  rw [show 52 = 42 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 104 := by
  rw [show 52 = 42 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 105 := by
  rw [show 52 = 42 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 106 := by
  rw [show 52 = 42 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 107 := by
  rw [show 52 = 42 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 108 := by
  rw [show 52 = 42 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 109 := by
  rw [show 52 = 42 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 110 := by
  rw [show 52 = 42 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 111 := by
  rw [show 52 = 42 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 112 := by
  rw [show 52 = 42 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 113 := by
  rw [show 52 = 42 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 114 := by
  rw [show 52 = 42 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow52_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 115 := by
  rw [show 52 = 42 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        52 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow52_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 116 := by
  rw [show 52 = 42 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        52 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow52_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 117 := by
  rw [show 52 = 42 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        52 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow52_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 118 := by
  rw [show 52 = 42 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        52 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow52_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 119 := by
  rw [show 52 = 42 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        52 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow52_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 120 := by
  rw [show 52 = 42 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      42 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        52 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow52_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 52 j := by
  by_cases h15 : j < 15
  · exact divisionRow52_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow52_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow52_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow52_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow52_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow52_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow52_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow52_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow52_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow52_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow52_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow52_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow52_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow52_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow52_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow52_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow52_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow52_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow52_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow52_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow52_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow52_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow52_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow52_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow52_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow52_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow52_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow52_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow52_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow52_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow52_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow52_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow52_column120

private theorem divisionRow52_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 52 j =
      ((rectangularize 83 121 divisionReducedData).getD 52 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow52_windowCoefficients j hj

private theorem divisionRow52_targetSupport :
    (divisionReducedData.getD 52 []).length ≤ 121 := by
  rw [show 52 = 42 + 10 by omega,
    ← getD_drop_window divisionReducedData 42 10 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      10 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 10 0 []]
  decide

private theorem divisionRow52_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 52) =
      (rectangularize 83 121 divisionReducedData).getD 52 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 52
    ((rectangularize 83 121 divisionReducedData).getD 52 [])
  · rw [show 52 = 42 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        42 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 52 []).length ≤ 121 := by
      exact divisionRow52_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 52 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow52_coefficients

private theorem divisionRow53_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  rw [show 53 = 43 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 43 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow53_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 53 = 43 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow53_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 53 = 43 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow53_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 53 = 43 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow53_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 53 = 43 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow53_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 53 = 43 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow53_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 53 = 43 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow53_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 95 := by
  rw [show 53 = 43 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 96 := by
  rw [show 53 = 43 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 97 := by
  rw [show 53 = 43 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 98 := by
  rw [show 53 = 43 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 99 := by
  rw [show 53 = 43 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 100 := by
  rw [show 53 = 43 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 101 := by
  rw [show 53 = 43 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 102 := by
  rw [show 53 = 43 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 103 := by
  rw [show 53 = 43 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 104 := by
  rw [show 53 = 43 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 105 := by
  rw [show 53 = 43 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 106 := by
  rw [show 53 = 43 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 107 := by
  rw [show 53 = 43 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 108 := by
  rw [show 53 = 43 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 109 := by
  rw [show 53 = 43 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 110 := by
  rw [show 53 = 43 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 111 := by
  rw [show 53 = 43 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 112 := by
  rw [show 53 = 43 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow53_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 113 := by
  rw [show 53 = 43 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 114 := by
  rw [show 53 = 43 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 115 := by
  rw [show 53 = 43 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 116 := by
  rw [show 53 = 43 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 117 := by
  rw [show 53 = 43 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 118 := by
  rw [show 53 = 43 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 119 := by
  rw [show 53 = 43 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 120 := by
  rw [show 53 = 43 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      43 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        53 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow53_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 53 j := by
  by_cases h15 : j < 15
  · exact divisionRow53_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow53_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow53_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow53_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow53_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow53_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow53_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow53_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow53_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow53_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow53_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow53_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow53_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow53_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow53_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow53_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow53_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow53_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow53_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow53_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow53_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow53_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow53_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow53_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow53_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow53_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow53_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow53_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow53_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow53_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow53_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow53_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow53_column120

private theorem divisionRow53_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 53 j =
      ((rectangularize 83 121 divisionReducedData).getD 53 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow53_windowCoefficients j hj

private theorem divisionRow53_targetSupport :
    (divisionReducedData.getD 53 []).length ≤ 121 := by
  rw [show 53 = 42 + 11 by omega,
    ← getD_drop_window divisionReducedData 42 11 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      11 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 11 0 []]
  decide

private theorem divisionRow53_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 53) =
      (rectangularize 83 121 divisionReducedData).getD 53 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 53
    ((rectangularize 83 121 divisionReducedData).getD 53 [])
  · rw [show 53 = 43 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        43 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 53 []).length ≤ 121 := by
      exact divisionRow53_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 53 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow53_coefficients

private theorem divisionRow54_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  rw [show 54 = 44 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 44 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow54_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 54 = 44 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow54_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 54 = 44 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow54_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 54 = 44 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow54_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 54 = 44 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow54_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 54 = 44 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow54_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 54 = 44 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow54_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 95 := by
  rw [show 54 = 44 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 96 := by
  rw [show 54 = 44 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 97 := by
  rw [show 54 = 44 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 98 := by
  rw [show 54 = 44 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 99 := by
  rw [show 54 = 44 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 100 := by
  rw [show 54 = 44 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 101 := by
  rw [show 54 = 44 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 102 := by
  rw [show 54 = 44 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 103 := by
  rw [show 54 = 44 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 104 := by
  rw [show 54 = 44 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 105 := by
  rw [show 54 = 44 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 106 := by
  rw [show 54 = 44 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 107 := by
  rw [show 54 = 44 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 108 := by
  rw [show 54 = 44 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 109 := by
  rw [show 54 = 44 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 110 := by
  rw [show 54 = 44 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 111 := by
  rw [show 54 = 44 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow54_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 112 := by
  rw [show 54 = 44 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 113 := by
  rw [show 54 = 44 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 114 := by
  rw [show 54 = 44 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 115 := by
  rw [show 54 = 44 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 116 := by
  rw [show 54 = 44 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 117 := by
  rw [show 54 = 44 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 118 := by
  rw [show 54 = 44 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 119 := by
  rw [show 54 = 44 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 120 := by
  rw [show 54 = 44 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      44 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        54 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow54_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 54 j := by
  by_cases h15 : j < 15
  · exact divisionRow54_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow54_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow54_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow54_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow54_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow54_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow54_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow54_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow54_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow54_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow54_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow54_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow54_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow54_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow54_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow54_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow54_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow54_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow54_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow54_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow54_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow54_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow54_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow54_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow54_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow54_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow54_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow54_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow54_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow54_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow54_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow54_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow54_column120

private theorem divisionRow54_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 54 j =
      ((rectangularize 83 121 divisionReducedData).getD 54 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow54_windowCoefficients j hj

private theorem divisionRow54_targetSupport :
    (divisionReducedData.getD 54 []).length ≤ 121 := by
  rw [show 54 = 42 + 12 by omega,
    ← getD_drop_window divisionReducedData 42 12 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      12 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 12 0 []]
  decide

private theorem divisionRow54_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 54) =
      (rectangularize 83 121 divisionReducedData).getD 54 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 54
    ((rectangularize 83 121 divisionReducedData).getD 54 [])
  · rw [show 54 = 44 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        44 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 54 []).length ≤ 121 := by
      exact divisionRow54_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 54 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow54_coefficients

private theorem divisionRow55_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  rw [show 55 = 45 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 45 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow55_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 55 = 45 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow55_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 55 = 45 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow55_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 55 = 45 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow55_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 55 = 45 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow55_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 55 = 45 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow55_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 55 = 45 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow55_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 95 := by
  rw [show 55 = 45 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 96 := by
  rw [show 55 = 45 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 97 := by
  rw [show 55 = 45 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 98 := by
  rw [show 55 = 45 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 99 := by
  rw [show 55 = 45 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 100 := by
  rw [show 55 = 45 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 101 := by
  rw [show 55 = 45 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 102 := by
  rw [show 55 = 45 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 103 := by
  rw [show 55 = 45 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 104 := by
  rw [show 55 = 45 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 105 := by
  rw [show 55 = 45 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 106 := by
  rw [show 55 = 45 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 107 := by
  rw [show 55 = 45 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 108 := by
  rw [show 55 = 45 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 109 := by
  rw [show 55 = 45 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 110 := by
  rw [show 55 = 45 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow55_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 111 := by
  rw [show 55 = 45 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 112 := by
  rw [show 55 = 45 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 113 := by
  rw [show 55 = 45 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 114 := by
  rw [show 55 = 45 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 115 := by
  rw [show 55 = 45 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 116 := by
  rw [show 55 = 45 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 117 := by
  rw [show 55 = 45 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 118 := by
  rw [show 55 = 45 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 119 := by
  rw [show 55 = 45 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 120 := by
  rw [show 55 = 45 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      45 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        55 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow55_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 55 j := by
  by_cases h15 : j < 15
  · exact divisionRow55_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow55_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow55_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow55_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow55_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow55_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow55_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow55_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow55_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow55_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow55_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow55_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow55_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow55_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow55_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow55_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow55_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow55_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow55_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow55_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow55_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow55_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow55_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow55_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow55_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow55_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow55_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow55_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow55_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow55_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow55_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow55_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow55_column120

private theorem divisionRow55_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 55 j =
      ((rectangularize 83 121 divisionReducedData).getD 55 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow55_windowCoefficients j hj

private theorem divisionRow55_targetSupport :
    (divisionReducedData.getD 55 []).length ≤ 121 := by
  rw [show 55 = 42 + 13 by omega,
    ← getD_drop_window divisionReducedData 42 13 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      13 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 13 0 []]
  decide

private theorem divisionRow55_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 55) =
      (rectangularize 83 121 divisionReducedData).getD 55 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 55
    ((rectangularize 83 121 divisionReducedData).getD 55 [])
  · rw [show 55 = 45 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        45 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 55 []).length ≤ 121 := by
      exact divisionRow55_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 55 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow55_coefficients

private theorem divisionRow56_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  rw [show 56 = 46 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 46 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow56_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 56 = 46 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow56_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 56 = 46 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow56_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 56 = 46 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow56_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 56 = 46 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow56_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 56 = 46 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow56_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 56 = 46 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow56_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 95 := by
  rw [show 56 = 46 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 96 := by
  rw [show 56 = 46 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 97 := by
  rw [show 56 = 46 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 98 := by
  rw [show 56 = 46 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 99 := by
  rw [show 56 = 46 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 100 := by
  rw [show 56 = 46 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 101 := by
  rw [show 56 = 46 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 102 := by
  rw [show 56 = 46 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 103 := by
  rw [show 56 = 46 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 104 := by
  rw [show 56 = 46 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 105 := by
  rw [show 56 = 46 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 106 := by
  rw [show 56 = 46 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 107 := by
  rw [show 56 = 46 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 108 := by
  rw [show 56 = 46 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 109 := by
  rw [show 56 = 46 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow56_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 110 := by
  rw [show 56 = 46 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 111 := by
  rw [show 56 = 46 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 112 := by
  rw [show 56 = 46 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 113 := by
  rw [show 56 = 46 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 114 := by
  rw [show 56 = 46 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 115 := by
  rw [show 56 = 46 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 116 := by
  rw [show 56 = 46 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 117 := by
  rw [show 56 = 46 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 118 := by
  rw [show 56 = 46 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 119 := by
  rw [show 56 = 46 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 120 := by
  rw [show 56 = 46 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      46 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        56 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow56_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 56 j := by
  by_cases h15 : j < 15
  · exact divisionRow56_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow56_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow56_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow56_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow56_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow56_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow56_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow56_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow56_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow56_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow56_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow56_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow56_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow56_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow56_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow56_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow56_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow56_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow56_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow56_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow56_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow56_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow56_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow56_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow56_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow56_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow56_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow56_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow56_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow56_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow56_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow56_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow56_column120

private theorem divisionRow56_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 56 j =
      ((rectangularize 83 121 divisionReducedData).getD 56 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow56_windowCoefficients j hj

private theorem divisionRow56_targetSupport :
    (divisionReducedData.getD 56 []).length ≤ 121 := by
  rw [show 56 = 42 + 14 by omega,
    ← getD_drop_window divisionReducedData 42 14 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      14 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 14 0 []]
  decide

private theorem divisionRow56_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 56) =
      (rectangularize 83 121 divisionReducedData).getD 56 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 56
    ((rectangularize 83 121 divisionReducedData).getD 56 [])
  · rw [show 56 = 46 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        46 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 56 []).length ≤ 121 := by
      exact divisionRow56_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 56 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow56_coefficients

/-- The complete exact-division certificates for rows 49 through 56. -/
theorem divisionRowsFortyNineToFiftySix_spec (n : ℕ)
    (hLower : 49 ≤ n) (hUpper : n < 57) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow49_spec
  · exact divisionRow50_spec
  · exact divisionRow51_spec
  · exact divisionRow52_spec
  · exact divisionRow53_spec
  · exact divisionRow54_spec
  · exact divisionRow55_spec
  · exact divisionRow56_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
