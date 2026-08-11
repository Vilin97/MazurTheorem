/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 41 through 48 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow41_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  rw [show 41 = 31 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 31 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow41_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 41 = 31 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow41_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 41 = 31 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow41_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 41 = 31 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow41_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 41 = 31 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow41_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 41 = 31 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow41_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 41 = 31 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow41_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 95 := by
  rw [show 41 = 31 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 96 := by
  rw [show 41 = 31 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 97 := by
  rw [show 41 = 31 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 98 := by
  rw [show 41 = 31 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 99 := by
  rw [show 41 = 31 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 100 := by
  rw [show 41 = 31 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 101 := by
  rw [show 41 = 31 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 102 := by
  rw [show 41 = 31 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 103 := by
  rw [show 41 = 31 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 104 := by
  rw [show 41 = 31 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 105 := by
  rw [show 41 = 31 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 106 := by
  rw [show 41 = 31 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 107 := by
  rw [show 41 = 31 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 108 := by
  rw [show 41 = 31 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 109 := by
  rw [show 41 = 31 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 110 := by
  rw [show 41 = 31 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 111 := by
  rw [show 41 = 31 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 112 := by
  rw [show 41 = 31 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 113 := by
  rw [show 41 = 31 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 114 := by
  rw [show 41 = 31 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 115 := by
  rw [show 41 = 31 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 116 := by
  rw [show 41 = 31 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 117 := by
  rw [show 41 = 31 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 118 := by
  rw [show 41 = 31 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 119 := by
  rw [show 41 = 31 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 120 := by
  rw [show 41 = 31 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      31 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow41_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 41 j := by
  by_cases h15 : j < 15
  · exact divisionRow41_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow41_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow41_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow41_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow41_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow41_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow41_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow41_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow41_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow41_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow41_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow41_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow41_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow41_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow41_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow41_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow41_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow41_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow41_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow41_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow41_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow41_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow41_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow41_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow41_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow41_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow41_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow41_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow41_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow41_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow41_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow41_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow41_column120

private theorem divisionRow41_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 41 j =
      ((rectangularize 83 121 divisionReducedData).getD 41 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow41_windowCoefficients j hj

private theorem divisionRow41_targetSupport :
    (divisionReducedData.getD 41 []).length ≤ 121 := by
  rw [show 41 = 21 + 20 by omega,
    ← getD_drop_window divisionReducedData 21 20 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      20 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    20 0 []]
  decide

private theorem divisionRow41_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 41) =
      (rectangularize 83 121 divisionReducedData).getD 41 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 41
    ((rectangularize 83 121 divisionReducedData).getD 41 [])
  · rw [show 41 = 31 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        31 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 41 []).length ≤ 121 := by
      exact divisionRow41_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 41 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow41_coefficients

private theorem divisionRow42_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  rw [show 42 = 32 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 32 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow42_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 42 = 32 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow42_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 42 = 32 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow42_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 42 = 32 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow42_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 42 = 32 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow42_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 42 = 32 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow42_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 42 = 32 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow42_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 95 := by
  rw [show 42 = 32 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 96 := by
  rw [show 42 = 32 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 97 := by
  rw [show 42 = 32 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 98 := by
  rw [show 42 = 32 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 99 := by
  rw [show 42 = 32 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 100 := by
  rw [show 42 = 32 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 101 := by
  rw [show 42 = 32 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 102 := by
  rw [show 42 = 32 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 103 := by
  rw [show 42 = 32 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 104 := by
  rw [show 42 = 32 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 105 := by
  rw [show 42 = 32 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 106 := by
  rw [show 42 = 32 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 107 := by
  rw [show 42 = 32 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 108 := by
  rw [show 42 = 32 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 109 := by
  rw [show 42 = 32 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 110 := by
  rw [show 42 = 32 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 111 := by
  rw [show 42 = 32 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 112 := by
  rw [show 42 = 32 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 113 := by
  rw [show 42 = 32 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 114 := by
  rw [show 42 = 32 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 115 := by
  rw [show 42 = 32 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 116 := by
  rw [show 42 = 32 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 117 := by
  rw [show 42 = 32 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 118 := by
  rw [show 42 = 32 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 119 := by
  rw [show 42 = 32 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 120 := by
  rw [show 42 = 32 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      32 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow42_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 42 j := by
  by_cases h15 : j < 15
  · exact divisionRow42_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow42_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow42_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow42_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow42_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow42_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow42_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow42_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow42_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow42_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow42_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow42_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow42_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow42_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow42_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow42_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow42_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow42_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow42_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow42_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow42_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow42_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow42_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow42_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow42_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow42_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow42_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow42_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow42_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow42_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow42_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow42_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow42_column120

private theorem divisionRow42_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 42 j =
      ((rectangularize 83 121 divisionReducedData).getD 42 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow42_windowCoefficients j hj

private theorem divisionRow42_targetSupport :
    (divisionReducedData.getD 42 []).length ≤ 121 := by
  rw [show 42 = 42 + 0 by omega,
    ← getD_drop_window divisionReducedData 42 0 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      0 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 0 0 []]
  decide

private theorem divisionRow42_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 42) =
      (rectangularize 83 121 divisionReducedData).getD 42 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 42
    ((rectangularize 83 121 divisionReducedData).getD 42 [])
  · rw [show 42 = 32 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        32 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 42 []).length ≤ 121 := by
      exact divisionRow42_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 42 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow42_coefficients

private theorem divisionRow43_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  rw [show 43 = 33 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 33 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow43_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 43 = 33 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow43_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 43 = 33 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow43_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 43 = 33 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow43_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 43 = 33 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow43_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 43 = 33 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow43_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 43 = 33 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow43_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 95 := by
  rw [show 43 = 33 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 96 := by
  rw [show 43 = 33 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 97 := by
  rw [show 43 = 33 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 98 := by
  rw [show 43 = 33 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 99 := by
  rw [show 43 = 33 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 100 := by
  rw [show 43 = 33 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 101 := by
  rw [show 43 = 33 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 102 := by
  rw [show 43 = 33 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 103 := by
  rw [show 43 = 33 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 104 := by
  rw [show 43 = 33 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 105 := by
  rw [show 43 = 33 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 106 := by
  rw [show 43 = 33 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 107 := by
  rw [show 43 = 33 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 108 := by
  rw [show 43 = 33 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 109 := by
  rw [show 43 = 33 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 110 := by
  rw [show 43 = 33 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 111 := by
  rw [show 43 = 33 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 112 := by
  rw [show 43 = 33 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 113 := by
  rw [show 43 = 33 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 114 := by
  rw [show 43 = 33 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 115 := by
  rw [show 43 = 33 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 116 := by
  rw [show 43 = 33 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 117 := by
  rw [show 43 = 33 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 118 := by
  rw [show 43 = 33 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 119 := by
  rw [show 43 = 33 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 120 := by
  rw [show 43 = 33 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      33 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow43_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 43 j := by
  by_cases h15 : j < 15
  · exact divisionRow43_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow43_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow43_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow43_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow43_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow43_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow43_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow43_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow43_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow43_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow43_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow43_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow43_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow43_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow43_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow43_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow43_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow43_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow43_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow43_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow43_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow43_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow43_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow43_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow43_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow43_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow43_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow43_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow43_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow43_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow43_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow43_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow43_column120

private theorem divisionRow43_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 43 j =
      ((rectangularize 83 121 divisionReducedData).getD 43 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow43_windowCoefficients j hj

private theorem divisionRow43_targetSupport :
    (divisionReducedData.getD 43 []).length ≤ 121 := by
  rw [show 43 = 42 + 1 by omega,
    ← getD_drop_window divisionReducedData 42 1 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      1 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 1 0 []]
  decide

private theorem divisionRow43_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 43) =
      (rectangularize 83 121 divisionReducedData).getD 43 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 43
    ((rectangularize 83 121 divisionReducedData).getD 43 [])
  · rw [show 43 = 33 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        33 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 43 []).length ≤ 121 := by
      exact divisionRow43_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 43 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow43_coefficients

private theorem divisionRow44_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  rw [show 44 = 34 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 34 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow44_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 44 = 34 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow44_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 44 = 34 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow44_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 44 = 34 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow44_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 44 = 34 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow44_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 44 = 34 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow44_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 44 = 34 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow44_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 95 := by
  rw [show 44 = 34 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 96 := by
  rw [show 44 = 34 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 97 := by
  rw [show 44 = 34 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 98 := by
  rw [show 44 = 34 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 99 := by
  rw [show 44 = 34 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 100 := by
  rw [show 44 = 34 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 101 := by
  rw [show 44 = 34 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 102 := by
  rw [show 44 = 34 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 103 := by
  rw [show 44 = 34 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 104 := by
  rw [show 44 = 34 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 105 := by
  rw [show 44 = 34 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 106 := by
  rw [show 44 = 34 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 107 := by
  rw [show 44 = 34 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 108 := by
  rw [show 44 = 34 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 109 := by
  rw [show 44 = 34 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 110 := by
  rw [show 44 = 34 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 111 := by
  rw [show 44 = 34 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 112 := by
  rw [show 44 = 34 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 113 := by
  rw [show 44 = 34 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 114 := by
  rw [show 44 = 34 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 115 := by
  rw [show 44 = 34 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 116 := by
  rw [show 44 = 34 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 117 := by
  rw [show 44 = 34 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 118 := by
  rw [show 44 = 34 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 119 := by
  rw [show 44 = 34 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow44_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 120 := by
  rw [show 44 = 34 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      34 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        44 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow44_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 44 j := by
  by_cases h15 : j < 15
  · exact divisionRow44_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow44_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow44_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow44_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow44_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow44_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow44_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow44_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow44_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow44_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow44_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow44_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow44_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow44_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow44_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow44_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow44_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow44_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow44_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow44_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow44_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow44_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow44_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow44_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow44_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow44_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow44_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow44_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow44_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow44_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow44_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow44_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow44_column120

private theorem divisionRow44_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 44 j =
      ((rectangularize 83 121 divisionReducedData).getD 44 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow44_windowCoefficients j hj

private theorem divisionRow44_targetSupport :
    (divisionReducedData.getD 44 []).length ≤ 121 := by
  rw [show 44 = 42 + 2 by omega,
    ← getD_drop_window divisionReducedData 42 2 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      2 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 2 0 []]
  decide

private theorem divisionRow44_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 44) =
      (rectangularize 83 121 divisionReducedData).getD 44 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 44
    ((rectangularize 83 121 divisionReducedData).getD 44 [])
  · rw [show 44 = 34 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        34 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 44 []).length ≤ 121 := by
      exact divisionRow44_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 44 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow44_coefficients

private theorem divisionRow45_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  rw [show 45 = 35 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 35 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow45_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 45 = 35 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow45_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 45 = 35 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow45_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 45 = 35 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow45_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 45 = 35 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow45_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 45 = 35 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow45_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 45 = 35 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow45_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 95 := by
  rw [show 45 = 35 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 96 := by
  rw [show 45 = 35 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 97 := by
  rw [show 45 = 35 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 98 := by
  rw [show 45 = 35 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 99 := by
  rw [show 45 = 35 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 100 := by
  rw [show 45 = 35 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 101 := by
  rw [show 45 = 35 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 102 := by
  rw [show 45 = 35 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 103 := by
  rw [show 45 = 35 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 104 := by
  rw [show 45 = 35 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 105 := by
  rw [show 45 = 35 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 106 := by
  rw [show 45 = 35 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 107 := by
  rw [show 45 = 35 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 108 := by
  rw [show 45 = 35 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 109 := by
  rw [show 45 = 35 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 110 := by
  rw [show 45 = 35 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 111 := by
  rw [show 45 = 35 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 112 := by
  rw [show 45 = 35 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 113 := by
  rw [show 45 = 35 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 114 := by
  rw [show 45 = 35 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 115 := by
  rw [show 45 = 35 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 116 := by
  rw [show 45 = 35 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 117 := by
  rw [show 45 = 35 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 118 := by
  rw [show 45 = 35 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 119 := by
  rw [show 45 = 35 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow45_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 120 := by
  rw [show 45 = 35 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      35 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        45 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow45_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 45 j := by
  by_cases h15 : j < 15
  · exact divisionRow45_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow45_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow45_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow45_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow45_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow45_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow45_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow45_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow45_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow45_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow45_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow45_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow45_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow45_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow45_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow45_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow45_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow45_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow45_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow45_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow45_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow45_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow45_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow45_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow45_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow45_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow45_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow45_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow45_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow45_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow45_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow45_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow45_column120

private theorem divisionRow45_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 45 j =
      ((rectangularize 83 121 divisionReducedData).getD 45 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow45_windowCoefficients j hj

private theorem divisionRow45_targetSupport :
    (divisionReducedData.getD 45 []).length ≤ 121 := by
  rw [show 45 = 42 + 3 by omega,
    ← getD_drop_window divisionReducedData 42 3 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      3 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 3 0 []]
  decide

private theorem divisionRow45_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 45) =
      (rectangularize 83 121 divisionReducedData).getD 45 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 45
    ((rectangularize 83 121 divisionReducedData).getD 45 [])
  · rw [show 45 = 35 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        35 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 45 []).length ≤ 121 := by
      exact divisionRow45_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 45 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow45_coefficients

private theorem divisionRow46_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  rw [show 46 = 36 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 36 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow46_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 46 = 36 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow46_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 46 = 36 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow46_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 46 = 36 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow46_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 46 = 36 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow46_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 46 = 36 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow46_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 46 = 36 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow46_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 95 := by
  rw [show 46 = 36 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 96 := by
  rw [show 46 = 36 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 97 := by
  rw [show 46 = 36 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 98 := by
  rw [show 46 = 36 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 99 := by
  rw [show 46 = 36 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 100 := by
  rw [show 46 = 36 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 101 := by
  rw [show 46 = 36 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 102 := by
  rw [show 46 = 36 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 103 := by
  rw [show 46 = 36 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 104 := by
  rw [show 46 = 36 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 105 := by
  rw [show 46 = 36 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 106 := by
  rw [show 46 = 36 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 107 := by
  rw [show 46 = 36 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 108 := by
  rw [show 46 = 36 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 109 := by
  rw [show 46 = 36 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 110 := by
  rw [show 46 = 36 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 111 := by
  rw [show 46 = 36 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 112 := by
  rw [show 46 = 36 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 113 := by
  rw [show 46 = 36 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 114 := by
  rw [show 46 = 36 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 115 := by
  rw [show 46 = 36 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 116 := by
  rw [show 46 = 36 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 117 := by
  rw [show 46 = 36 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 118 := by
  rw [show 46 = 36 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 119 := by
  rw [show 46 = 36 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 120 := by
  rw [show 46 = 36 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      36 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow46_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 46 j := by
  by_cases h15 : j < 15
  · exact divisionRow46_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow46_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow46_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow46_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow46_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow46_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow46_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow46_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow46_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow46_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow46_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow46_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow46_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow46_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow46_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow46_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow46_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow46_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow46_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow46_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow46_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow46_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow46_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow46_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow46_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow46_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow46_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow46_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow46_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow46_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow46_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow46_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow46_column120

private theorem divisionRow46_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 46 j =
      ((rectangularize 83 121 divisionReducedData).getD 46 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow46_windowCoefficients j hj

private theorem divisionRow46_targetSupport :
    (divisionReducedData.getD 46 []).length ≤ 121 := by
  rw [show 46 = 42 + 4 by omega,
    ← getD_drop_window divisionReducedData 42 4 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      4 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 4 0 []]
  decide

private theorem divisionRow46_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 46) =
      (rectangularize 83 121 divisionReducedData).getD 46 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 46
    ((rectangularize 83 121 divisionReducedData).getD 46 [])
  · rw [show 46 = 36 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        36 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 46 []).length ≤ 121 := by
      exact divisionRow46_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 46 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow46_coefficients

private theorem divisionRow47_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  rw [show 47 = 37 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 37 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow47_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 47 = 37 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow47_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 47 = 37 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow47_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 47 = 37 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow47_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 47 = 37 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow47_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 47 = 37 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow47_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 47 = 37 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow47_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 95 := by
  rw [show 47 = 37 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 96 := by
  rw [show 47 = 37 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 97 := by
  rw [show 47 = 37 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 98 := by
  rw [show 47 = 37 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 99 := by
  rw [show 47 = 37 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 100 := by
  rw [show 47 = 37 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 101 := by
  rw [show 47 = 37 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 102 := by
  rw [show 47 = 37 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 103 := by
  rw [show 47 = 37 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 104 := by
  rw [show 47 = 37 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 105 := by
  rw [show 47 = 37 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 106 := by
  rw [show 47 = 37 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 107 := by
  rw [show 47 = 37 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 108 := by
  rw [show 47 = 37 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 109 := by
  rw [show 47 = 37 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 110 := by
  rw [show 47 = 37 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 111 := by
  rw [show 47 = 37 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 112 := by
  rw [show 47 = 37 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 113 := by
  rw [show 47 = 37 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 114 := by
  rw [show 47 = 37 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 115 := by
  rw [show 47 = 37 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 116 := by
  rw [show 47 = 37 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 117 := by
  rw [show 47 = 37 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 118 := by
  rw [show 47 = 37 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 119 := by
  rw [show 47 = 37 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow47_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 120 := by
  rw [show 47 = 37 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      37 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        47 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow47_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 47 j := by
  by_cases h15 : j < 15
  · exact divisionRow47_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow47_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow47_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow47_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow47_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow47_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow47_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow47_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow47_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow47_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow47_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow47_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow47_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow47_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow47_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow47_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow47_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow47_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow47_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow47_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow47_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow47_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow47_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow47_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow47_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow47_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow47_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow47_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow47_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow47_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow47_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow47_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow47_column120

private theorem divisionRow47_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 47 j =
      ((rectangularize 83 121 divisionReducedData).getD 47 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow47_windowCoefficients j hj

private theorem divisionRow47_targetSupport :
    (divisionReducedData.getD 47 []).length ≤ 121 := by
  rw [show 47 = 42 + 5 by omega,
    ← getD_drop_window divisionReducedData 42 5 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      5 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 5 0 []]
  decide

private theorem divisionRow47_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 47) =
      (rectangularize 83 121 divisionReducedData).getD 47 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 47
    ((rectangularize 83 121 divisionReducedData).getD 47 [])
  · rw [show 47 = 37 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        37 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 47 []).length ≤ 121 := by
      exact divisionRow47_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 47 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow47_coefficients

private theorem divisionRow48_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  rw [show 48 = 38 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 38 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow48_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 48 = 38 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow48_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 48 = 38 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow48_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 48 = 38 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow48_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 48 = 38 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow48_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 48 = 38 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow48_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 48 = 38 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow48_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 95 := by
  rw [show 48 = 38 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 96 := by
  rw [show 48 = 38 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 97 := by
  rw [show 48 = 38 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 98 := by
  rw [show 48 = 38 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 99 := by
  rw [show 48 = 38 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 100 := by
  rw [show 48 = 38 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 101 := by
  rw [show 48 = 38 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 102 := by
  rw [show 48 = 38 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 103 := by
  rw [show 48 = 38 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 104 := by
  rw [show 48 = 38 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 105 := by
  rw [show 48 = 38 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 106 := by
  rw [show 48 = 38 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 107 := by
  rw [show 48 = 38 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 108 := by
  rw [show 48 = 38 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 109 := by
  rw [show 48 = 38 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 110 := by
  rw [show 48 = 38 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 111 := by
  rw [show 48 = 38 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 112 := by
  rw [show 48 = 38 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 113 := by
  rw [show 48 = 38 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 114 := by
  rw [show 48 = 38 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 115 := by
  rw [show 48 = 38 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 116 := by
  rw [show 48 = 38 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 117 := by
  rw [show 48 = 38 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 118 := by
  rw [show 48 = 38 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 119 := by
  rw [show 48 = 38 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow48_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 120 := by
  rw [show 48 = 38 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      38 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        48 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow48_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 48 j := by
  by_cases h15 : j < 15
  · exact divisionRow48_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow48_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow48_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow48_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow48_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow48_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow48_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow48_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow48_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow48_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow48_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow48_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow48_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow48_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow48_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow48_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow48_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow48_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow48_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow48_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow48_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow48_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow48_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow48_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow48_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow48_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow48_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow48_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow48_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow48_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow48_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow48_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow48_column120

private theorem divisionRow48_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 48 j =
      ((rectangularize 83 121 divisionReducedData).getD 48 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow48_windowCoefficients j hj

private theorem divisionRow48_targetSupport :
    (divisionReducedData.getD 48 []).length ≤ 121 := by
  rw [show 48 = 42 + 6 by omega,
    ← getD_drop_window divisionReducedData 42 6 []]
  change
    ((ReducedDataMidHigh ++ ReducedDataHigh).getD
      6 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidHigh ++ ReducedDataHigh) 6 0 []]
  decide

private theorem divisionRow48_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 48) =
      (rectangularize 83 121 divisionReducedData).getD 48 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 48
    ((rectangularize 83 121 divisionReducedData).getD 48 [])
  · rw [show 48 = 38 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        38 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 48 []).length ≤ 121 := by
      exact divisionRow48_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 48 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow48_coefficients

/-- The complete exact-division certificates for rows 41 through 48. -/
theorem divisionRowsFortyOneToFortyEight_spec (n : ℕ)
    (hLower : 41 ≤ n) (hUpper : n < 49) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow41_spec
  · exact divisionRow42_spec
  · exact divisionRow43_spec
  · exact divisionRow44_spec
  · exact divisionRow45_spec
  · exact divisionRow46_spec
  · exact divisionRow47_spec
  · exact divisionRow48_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
