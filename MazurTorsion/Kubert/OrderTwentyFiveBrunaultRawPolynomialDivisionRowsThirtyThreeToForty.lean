/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 33 through 40 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow33_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  rw [show 33 = 23 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 23 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow33_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 33 = 23 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow33_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 33 = 23 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow33_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 33 = 23 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow33_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 33 = 23 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow33_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 33 = 23 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow33_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 33 = 23 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow33_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 95 := by
  rw [show 33 = 23 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 96 := by
  rw [show 33 = 23 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 97 := by
  rw [show 33 = 23 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 98 := by
  rw [show 33 = 23 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 99 := by
  rw [show 33 = 23 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 100 := by
  rw [show 33 = 23 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 101 := by
  rw [show 33 = 23 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 102 := by
  rw [show 33 = 23 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 103 := by
  rw [show 33 = 23 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 104 := by
  rw [show 33 = 23 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 105 := by
  rw [show 33 = 23 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 106 := by
  rw [show 33 = 23 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 107 := by
  rw [show 33 = 23 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 108 := by
  rw [show 33 = 23 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 109 := by
  rw [show 33 = 23 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 110 := by
  rw [show 33 = 23 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 111 := by
  rw [show 33 = 23 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 112 := by
  rw [show 33 = 23 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 113 := by
  rw [show 33 = 23 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 114 := by
  rw [show 33 = 23 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 115 := by
  rw [show 33 = 23 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 116 := by
  rw [show 33 = 23 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 117 := by
  rw [show 33 = 23 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 118 := by
  rw [show 33 = 23 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 119 := by
  rw [show 33 = 23 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 120 := by
  rw [show 33 = 23 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      23 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow33_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 33 j := by
  by_cases h15 : j < 15
  · exact divisionRow33_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow33_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow33_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow33_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow33_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow33_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow33_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow33_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow33_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow33_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow33_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow33_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow33_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow33_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow33_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow33_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow33_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow33_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow33_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow33_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow33_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow33_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow33_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow33_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow33_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow33_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow33_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow33_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow33_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow33_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow33_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow33_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow33_column120

private theorem divisionRow33_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 33 j =
      ((rectangularize 83 121 divisionReducedData).getD 33 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow33_windowCoefficients j hj

private theorem divisionRow33_targetSupport :
    (divisionReducedData.getD 33 []).length ≤ 121 := by
  rw [show 33 = 21 + 12 by omega,
    ← getD_drop_window divisionReducedData 21 12 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      12 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    12 0 []]
  decide

private theorem divisionRow33_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 33) =
      (rectangularize 83 121 divisionReducedData).getD 33 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 33
    ((rectangularize 83 121 divisionReducedData).getD 33 [])
  · rw [show 33 = 23 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        23 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 33 []).length ≤ 121 := by
      exact divisionRow33_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 33 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow33_coefficients

private theorem divisionRow34_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  rw [show 34 = 24 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 24 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow34_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 34 = 24 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow34_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 34 = 24 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow34_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 34 = 24 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow34_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 34 = 24 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow34_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 34 = 24 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow34_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 34 = 24 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow34_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 95 := by
  rw [show 34 = 24 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 96 := by
  rw [show 34 = 24 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 97 := by
  rw [show 34 = 24 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 98 := by
  rw [show 34 = 24 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 99 := by
  rw [show 34 = 24 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 100 := by
  rw [show 34 = 24 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 101 := by
  rw [show 34 = 24 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 102 := by
  rw [show 34 = 24 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 103 := by
  rw [show 34 = 24 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 104 := by
  rw [show 34 = 24 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 105 := by
  rw [show 34 = 24 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 106 := by
  rw [show 34 = 24 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 107 := by
  rw [show 34 = 24 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 108 := by
  rw [show 34 = 24 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 109 := by
  rw [show 34 = 24 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 110 := by
  rw [show 34 = 24 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 111 := by
  rw [show 34 = 24 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 112 := by
  rw [show 34 = 24 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 113 := by
  rw [show 34 = 24 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 114 := by
  rw [show 34 = 24 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 115 := by
  rw [show 34 = 24 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 116 := by
  rw [show 34 = 24 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 117 := by
  rw [show 34 = 24 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 118 := by
  rw [show 34 = 24 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 119 := by
  rw [show 34 = 24 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow34_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 120 := by
  rw [show 34 = 24 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      24 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        34 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow34_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 34 j := by
  by_cases h15 : j < 15
  · exact divisionRow34_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow34_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow34_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow34_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow34_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow34_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow34_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow34_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow34_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow34_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow34_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow34_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow34_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow34_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow34_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow34_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow34_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow34_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow34_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow34_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow34_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow34_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow34_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow34_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow34_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow34_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow34_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow34_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow34_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow34_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow34_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow34_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow34_column120

private theorem divisionRow34_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 34 j =
      ((rectangularize 83 121 divisionReducedData).getD 34 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow34_windowCoefficients j hj

private theorem divisionRow34_targetSupport :
    (divisionReducedData.getD 34 []).length ≤ 121 := by
  rw [show 34 = 21 + 13 by omega,
    ← getD_drop_window divisionReducedData 21 13 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      13 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    13 0 []]
  decide

private theorem divisionRow34_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 34) =
      (rectangularize 83 121 divisionReducedData).getD 34 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 34
    ((rectangularize 83 121 divisionReducedData).getD 34 [])
  · rw [show 34 = 24 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        24 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 34 []).length ≤ 121 := by
      exact divisionRow34_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 34 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow34_coefficients

private theorem divisionRow35_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  rw [show 35 = 25 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 25 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow35_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 35 = 25 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow35_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 35 = 25 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow35_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 35 = 25 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow35_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 35 = 25 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow35_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 35 = 25 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow35_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 35 = 25 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow35_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 95 := by
  rw [show 35 = 25 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 96 := by
  rw [show 35 = 25 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 97 := by
  rw [show 35 = 25 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 98 := by
  rw [show 35 = 25 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 99 := by
  rw [show 35 = 25 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 100 := by
  rw [show 35 = 25 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 101 := by
  rw [show 35 = 25 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 102 := by
  rw [show 35 = 25 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 103 := by
  rw [show 35 = 25 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 104 := by
  rw [show 35 = 25 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 105 := by
  rw [show 35 = 25 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 106 := by
  rw [show 35 = 25 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 107 := by
  rw [show 35 = 25 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 108 := by
  rw [show 35 = 25 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 109 := by
  rw [show 35 = 25 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 110 := by
  rw [show 35 = 25 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 111 := by
  rw [show 35 = 25 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 112 := by
  rw [show 35 = 25 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 113 := by
  rw [show 35 = 25 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 114 := by
  rw [show 35 = 25 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 115 := by
  rw [show 35 = 25 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 116 := by
  rw [show 35 = 25 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 117 := by
  rw [show 35 = 25 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 118 := by
  rw [show 35 = 25 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 119 := by
  rw [show 35 = 25 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 120 := by
  rw [show 35 = 25 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      25 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow35_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 35 j := by
  by_cases h15 : j < 15
  · exact divisionRow35_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow35_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow35_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow35_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow35_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow35_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow35_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow35_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow35_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow35_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow35_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow35_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow35_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow35_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow35_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow35_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow35_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow35_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow35_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow35_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow35_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow35_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow35_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow35_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow35_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow35_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow35_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow35_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow35_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow35_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow35_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow35_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow35_column120

private theorem divisionRow35_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 35 j =
      ((rectangularize 83 121 divisionReducedData).getD 35 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow35_windowCoefficients j hj

private theorem divisionRow35_targetSupport :
    (divisionReducedData.getD 35 []).length ≤ 121 := by
  rw [show 35 = 21 + 14 by omega,
    ← getD_drop_window divisionReducedData 21 14 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      14 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    14 0 []]
  decide

private theorem divisionRow35_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 35) =
      (rectangularize 83 121 divisionReducedData).getD 35 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 35
    ((rectangularize 83 121 divisionReducedData).getD 35 [])
  · rw [show 35 = 25 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        25 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 35 []).length ≤ 121 := by
      exact divisionRow35_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 35 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow35_coefficients

private theorem divisionRow36_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  rw [show 36 = 26 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 26 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow36_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 36 = 26 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow36_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 36 = 26 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow36_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 36 = 26 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow36_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 36 = 26 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow36_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 36 = 26 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow36_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 36 = 26 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow36_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 95 := by
  rw [show 36 = 26 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 96 := by
  rw [show 36 = 26 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 97 := by
  rw [show 36 = 26 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 98 := by
  rw [show 36 = 26 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 99 := by
  rw [show 36 = 26 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 100 := by
  rw [show 36 = 26 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 101 := by
  rw [show 36 = 26 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 102 := by
  rw [show 36 = 26 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 103 := by
  rw [show 36 = 26 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 104 := by
  rw [show 36 = 26 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 105 := by
  rw [show 36 = 26 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 106 := by
  rw [show 36 = 26 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 107 := by
  rw [show 36 = 26 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 108 := by
  rw [show 36 = 26 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 109 := by
  rw [show 36 = 26 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 110 := by
  rw [show 36 = 26 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 111 := by
  rw [show 36 = 26 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 112 := by
  rw [show 36 = 26 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 113 := by
  rw [show 36 = 26 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 114 := by
  rw [show 36 = 26 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 115 := by
  rw [show 36 = 26 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 116 := by
  rw [show 36 = 26 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 117 := by
  rw [show 36 = 26 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 118 := by
  rw [show 36 = 26 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 119 := by
  rw [show 36 = 26 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 120 := by
  rw [show 36 = 26 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      26 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow36_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 36 j := by
  by_cases h15 : j < 15
  · exact divisionRow36_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow36_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow36_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow36_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow36_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow36_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow36_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow36_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow36_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow36_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow36_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow36_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow36_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow36_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow36_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow36_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow36_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow36_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow36_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow36_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow36_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow36_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow36_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow36_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow36_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow36_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow36_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow36_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow36_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow36_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow36_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow36_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow36_column120

private theorem divisionRow36_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 36 j =
      ((rectangularize 83 121 divisionReducedData).getD 36 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow36_windowCoefficients j hj

private theorem divisionRow36_targetSupport :
    (divisionReducedData.getD 36 []).length ≤ 121 := by
  rw [show 36 = 21 + 15 by omega,
    ← getD_drop_window divisionReducedData 21 15 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      15 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    15 0 []]
  decide

private theorem divisionRow36_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 36) =
      (rectangularize 83 121 divisionReducedData).getD 36 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 36
    ((rectangularize 83 121 divisionReducedData).getD 36 [])
  · rw [show 36 = 26 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        26 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 36 []).length ≤ 121 := by
      exact divisionRow36_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 36 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow36_coefficients

private theorem divisionRow37_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  rw [show 37 = 27 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 27 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow37_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 37 = 27 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow37_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 37 = 27 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow37_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 37 = 27 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow37_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 37 = 27 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow37_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 37 = 27 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow37_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 37 = 27 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow37_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 95 := by
  rw [show 37 = 27 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 96 := by
  rw [show 37 = 27 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 97 := by
  rw [show 37 = 27 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 98 := by
  rw [show 37 = 27 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 99 := by
  rw [show 37 = 27 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 100 := by
  rw [show 37 = 27 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 101 := by
  rw [show 37 = 27 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 102 := by
  rw [show 37 = 27 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 103 := by
  rw [show 37 = 27 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 104 := by
  rw [show 37 = 27 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 105 := by
  rw [show 37 = 27 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 106 := by
  rw [show 37 = 27 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 107 := by
  rw [show 37 = 27 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 108 := by
  rw [show 37 = 27 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 109 := by
  rw [show 37 = 27 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 110 := by
  rw [show 37 = 27 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 111 := by
  rw [show 37 = 27 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 112 := by
  rw [show 37 = 27 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 113 := by
  rw [show 37 = 27 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 114 := by
  rw [show 37 = 27 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 115 := by
  rw [show 37 = 27 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 116 := by
  rw [show 37 = 27 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 117 := by
  rw [show 37 = 27 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 118 := by
  rw [show 37 = 27 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 119 := by
  rw [show 37 = 27 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow37_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 120 := by
  rw [show 37 = 27 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      27 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        37 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow37_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 37 j := by
  by_cases h15 : j < 15
  · exact divisionRow37_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow37_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow37_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow37_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow37_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow37_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow37_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow37_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow37_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow37_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow37_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow37_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow37_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow37_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow37_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow37_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow37_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow37_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow37_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow37_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow37_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow37_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow37_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow37_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow37_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow37_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow37_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow37_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow37_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow37_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow37_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow37_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow37_column120

private theorem divisionRow37_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 37 j =
      ((rectangularize 83 121 divisionReducedData).getD 37 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow37_windowCoefficients j hj

private theorem divisionRow37_targetSupport :
    (divisionReducedData.getD 37 []).length ≤ 121 := by
  rw [show 37 = 21 + 16 by omega,
    ← getD_drop_window divisionReducedData 21 16 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      16 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    16 0 []]
  decide

private theorem divisionRow37_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 37) =
      (rectangularize 83 121 divisionReducedData).getD 37 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 37
    ((rectangularize 83 121 divisionReducedData).getD 37 [])
  · rw [show 37 = 27 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        27 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 37 []).length ≤ 121 := by
      exact divisionRow37_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 37 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow37_coefficients

private theorem divisionRow38_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  rw [show 38 = 28 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 28 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow38_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 38 = 28 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow38_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 38 = 28 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow38_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 38 = 28 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow38_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 38 = 28 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow38_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 38 = 28 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow38_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 38 = 28 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow38_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 95 := by
  rw [show 38 = 28 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 96 := by
  rw [show 38 = 28 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 97 := by
  rw [show 38 = 28 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 98 := by
  rw [show 38 = 28 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 99 := by
  rw [show 38 = 28 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 100 := by
  rw [show 38 = 28 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 101 := by
  rw [show 38 = 28 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 102 := by
  rw [show 38 = 28 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 103 := by
  rw [show 38 = 28 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 104 := by
  rw [show 38 = 28 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 105 := by
  rw [show 38 = 28 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 106 := by
  rw [show 38 = 28 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 107 := by
  rw [show 38 = 28 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 108 := by
  rw [show 38 = 28 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 109 := by
  rw [show 38 = 28 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 110 := by
  rw [show 38 = 28 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 111 := by
  rw [show 38 = 28 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 112 := by
  rw [show 38 = 28 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 113 := by
  rw [show 38 = 28 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 114 := by
  rw [show 38 = 28 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 115 := by
  rw [show 38 = 28 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 116 := by
  rw [show 38 = 28 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 117 := by
  rw [show 38 = 28 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 118 := by
  rw [show 38 = 28 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 119 := by
  rw [show 38 = 28 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 120 := by
  rw [show 38 = 28 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      28 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow38_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 38 j := by
  by_cases h15 : j < 15
  · exact divisionRow38_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow38_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow38_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow38_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow38_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow38_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow38_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow38_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow38_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow38_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow38_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow38_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow38_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow38_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow38_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow38_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow38_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow38_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow38_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow38_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow38_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow38_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow38_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow38_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow38_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow38_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow38_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow38_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow38_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow38_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow38_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow38_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow38_column120

private theorem divisionRow38_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 38 j =
      ((rectangularize 83 121 divisionReducedData).getD 38 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow38_windowCoefficients j hj

private theorem divisionRow38_targetSupport :
    (divisionReducedData.getD 38 []).length ≤ 121 := by
  rw [show 38 = 21 + 17 by omega,
    ← getD_drop_window divisionReducedData 21 17 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      17 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    17 0 []]
  decide

private theorem divisionRow38_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 38) =
      (rectangularize 83 121 divisionReducedData).getD 38 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 38
    ((rectangularize 83 121 divisionReducedData).getD 38 [])
  · rw [show 38 = 28 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        28 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 38 []).length ≤ 121 := by
      exact divisionRow38_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 38 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow38_coefficients

private theorem divisionRow39_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  rw [show 39 = 29 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 29 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow39_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 39 = 29 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow39_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 39 = 29 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow39_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 39 = 29 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow39_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 39 = 29 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow39_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 39 = 29 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow39_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 39 = 29 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow39_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 95 := by
  rw [show 39 = 29 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 96 := by
  rw [show 39 = 29 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 97 := by
  rw [show 39 = 29 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 98 := by
  rw [show 39 = 29 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 99 := by
  rw [show 39 = 29 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 100 := by
  rw [show 39 = 29 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 101 := by
  rw [show 39 = 29 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 102 := by
  rw [show 39 = 29 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 103 := by
  rw [show 39 = 29 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 104 := by
  rw [show 39 = 29 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 105 := by
  rw [show 39 = 29 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 106 := by
  rw [show 39 = 29 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 107 := by
  rw [show 39 = 29 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 108 := by
  rw [show 39 = 29 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 109 := by
  rw [show 39 = 29 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 110 := by
  rw [show 39 = 29 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 111 := by
  rw [show 39 = 29 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 112 := by
  rw [show 39 = 29 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 113 := by
  rw [show 39 = 29 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 114 := by
  rw [show 39 = 29 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 115 := by
  rw [show 39 = 29 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 116 := by
  rw [show 39 = 29 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 117 := by
  rw [show 39 = 29 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 118 := by
  rw [show 39 = 29 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 119 := by
  rw [show 39 = 29 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 120 := by
  rw [show 39 = 29 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      29 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow39_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 39 j := by
  by_cases h15 : j < 15
  · exact divisionRow39_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow39_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow39_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow39_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow39_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow39_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow39_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow39_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow39_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow39_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow39_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow39_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow39_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow39_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow39_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow39_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow39_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow39_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow39_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow39_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow39_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow39_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow39_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow39_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow39_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow39_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow39_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow39_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow39_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow39_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow39_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow39_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow39_column120

private theorem divisionRow39_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 39 j =
      ((rectangularize 83 121 divisionReducedData).getD 39 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow39_windowCoefficients j hj

private theorem divisionRow39_targetSupport :
    (divisionReducedData.getD 39 []).length ≤ 121 := by
  rw [show 39 = 21 + 18 by omega,
    ← getD_drop_window divisionReducedData 21 18 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      18 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    18 0 []]
  decide

private theorem divisionRow39_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 39) =
      (rectangularize 83 121 divisionReducedData).getD 39 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 39
    ((rectangularize 83 121 divisionReducedData).getD 39 [])
  · rw [show 39 = 29 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        29 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 39 []).length ≤ 121 := by
      exact divisionRow39_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 39 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow39_coefficients

private theorem divisionRow40_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  rw [show 40 = 30 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 30 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow40_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 40 = 30 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow40_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 40 = 30 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow40_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 40 = 30 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow40_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 40 = 30 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow40_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 40 = 30 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow40_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 40 = 30 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow40_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 95 := by
  rw [show 40 = 30 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 96 := by
  rw [show 40 = 30 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 97 := by
  rw [show 40 = 30 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 98 := by
  rw [show 40 = 30 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 99 := by
  rw [show 40 = 30 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 100 := by
  rw [show 40 = 30 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 101 := by
  rw [show 40 = 30 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 102 := by
  rw [show 40 = 30 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 103 := by
  rw [show 40 = 30 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 104 := by
  rw [show 40 = 30 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 105 := by
  rw [show 40 = 30 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 106 := by
  rw [show 40 = 30 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 107 := by
  rw [show 40 = 30 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 108 := by
  rw [show 40 = 30 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 109 := by
  rw [show 40 = 30 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 110 := by
  rw [show 40 = 30 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 111 := by
  rw [show 40 = 30 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 112 := by
  rw [show 40 = 30 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 113 := by
  rw [show 40 = 30 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 114 := by
  rw [show 40 = 30 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 115 := by
  rw [show 40 = 30 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 116 := by
  rw [show 40 = 30 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 117 := by
  rw [show 40 = 30 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 118 := by
  rw [show 40 = 30 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 119 := by
  rw [show 40 = 30 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 120 := by
  rw [show 40 = 30 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      30 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow40_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 40 j := by
  by_cases h15 : j < 15
  · exact divisionRow40_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow40_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow40_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow40_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow40_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow40_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow40_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow40_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow40_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow40_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow40_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow40_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow40_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow40_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow40_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow40_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow40_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow40_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow40_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow40_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow40_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow40_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow40_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow40_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow40_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow40_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow40_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow40_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow40_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow40_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow40_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow40_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow40_column120

private theorem divisionRow40_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 40 j =
      ((rectangularize 83 121 divisionReducedData).getD 40 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow40_windowCoefficients j hj

private theorem divisionRow40_targetSupport :
    (divisionReducedData.getD 40 []).length ≤ 121 := by
  rw [show 40 = 21 + 19 by omega,
    ← getD_drop_window divisionReducedData 21 19 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      19 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    19 0 []]
  decide

private theorem divisionRow40_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 40) =
      (rectangularize 83 121 divisionReducedData).getD 40 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 40
    ((rectangularize 83 121 divisionReducedData).getD 40 [])
  · rw [show 40 = 30 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        30 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 40 []).length ≤ 121 := by
      exact divisionRow40_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 40 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow40_coefficients

/-- The complete exact-division certificates for rows 33 through 40. -/
theorem divisionRowsThirtyThreeToForty_spec (n : ℕ)
    (hLower : 33 ≤ n) (hUpper : n < 41) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow33_spec
  · exact divisionRow34_spec
  · exact divisionRow35_spec
  · exact divisionRow36_spec
  · exact divisionRow37_spec
  · exact divisionRow38_spec
  · exact divisionRow39_spec
  · exact divisionRow40_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
