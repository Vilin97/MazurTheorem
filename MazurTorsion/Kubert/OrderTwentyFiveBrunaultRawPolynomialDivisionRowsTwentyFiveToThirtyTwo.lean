/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 25 through 32 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow25_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  rw [show 25 = 15 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 15 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow25_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 25 = 15 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow25_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 25 = 15 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow25_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 25 = 15 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow25_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 25 = 15 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow25_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 25 = 15 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow25_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 25 = 15 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow25_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 95 := by
  rw [show 25 = 15 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 96 := by
  rw [show 25 = 15 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 97 := by
  rw [show 25 = 15 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 98 := by
  rw [show 25 = 15 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 99 := by
  rw [show 25 = 15 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 100 := by
  rw [show 25 = 15 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 101 := by
  rw [show 25 = 15 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 102 := by
  rw [show 25 = 15 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 103 := by
  rw [show 25 = 15 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 104 := by
  rw [show 25 = 15 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 105 := by
  rw [show 25 = 15 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 106 := by
  rw [show 25 = 15 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 107 := by
  rw [show 25 = 15 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 108 := by
  rw [show 25 = 15 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 109 := by
  rw [show 25 = 15 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 110 := by
  rw [show 25 = 15 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 111 := by
  rw [show 25 = 15 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 112 := by
  rw [show 25 = 15 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 113 := by
  rw [show 25 = 15 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 114 := by
  rw [show 25 = 15 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 115 := by
  rw [show 25 = 15 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 116 := by
  rw [show 25 = 15 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 117 := by
  rw [show 25 = 15 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 118 := by
  rw [show 25 = 15 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow25_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 119 := by
  rw [show 25 = 15 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        25 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow25_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 120 := by
  rw [show 25 = 15 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      15 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        25 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow25_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 25 j := by
  by_cases h15 : j < 15
  · exact divisionRow25_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow25_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow25_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow25_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow25_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow25_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow25_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow25_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow25_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow25_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow25_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow25_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow25_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow25_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow25_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow25_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow25_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow25_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow25_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow25_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow25_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow25_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow25_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow25_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow25_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow25_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow25_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow25_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow25_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow25_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow25_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow25_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow25_column120

private theorem divisionRow25_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 25 j =
      ((rectangularize 83 121 divisionReducedData).getD 25 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow25_windowCoefficients j hj

private theorem divisionRow25_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 25) =
      (rectangularize 83 121 divisionReducedData).getD 25 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 25
    ((rectangularize 83 121 divisionReducedData).getD 25 [])
  · rw [show 25 = 15 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        15 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 25 []).length ≤ 121 := by
      rw [show 25 = 21 + 4 by omega,
        ← getD_drop_window divisionReducedData 21 4 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          4 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        4 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 25 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow25_coefficients

private theorem divisionRow26_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  rw [show 26 = 16 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 16 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow26_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 26 = 16 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow26_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 26 = 16 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow26_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 26 = 16 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow26_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 26 = 16 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow26_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 26 = 16 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow26_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 26 = 16 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow26_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 95 := by
  rw [show 26 = 16 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 96 := by
  rw [show 26 = 16 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 97 := by
  rw [show 26 = 16 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 98 := by
  rw [show 26 = 16 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 99 := by
  rw [show 26 = 16 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 100 := by
  rw [show 26 = 16 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 101 := by
  rw [show 26 = 16 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 102 := by
  rw [show 26 = 16 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 103 := by
  rw [show 26 = 16 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 104 := by
  rw [show 26 = 16 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 105 := by
  rw [show 26 = 16 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 106 := by
  rw [show 26 = 16 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 107 := by
  rw [show 26 = 16 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 108 := by
  rw [show 26 = 16 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 109 := by
  rw [show 26 = 16 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 110 := by
  rw [show 26 = 16 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 111 := by
  rw [show 26 = 16 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 112 := by
  rw [show 26 = 16 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 113 := by
  rw [show 26 = 16 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 114 := by
  rw [show 26 = 16 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 115 := by
  rw [show 26 = 16 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 116 := by
  rw [show 26 = 16 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 117 := by
  rw [show 26 = 16 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 118 := by
  rw [show 26 = 16 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow26_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 119 := by
  rw [show 26 = 16 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        26 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow26_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 120 := by
  rw [show 26 = 16 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      16 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        26 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow26_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 26 j := by
  by_cases h15 : j < 15
  · exact divisionRow26_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow26_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow26_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow26_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow26_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow26_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow26_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow26_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow26_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow26_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow26_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow26_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow26_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow26_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow26_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow26_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow26_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow26_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow26_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow26_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow26_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow26_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow26_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow26_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow26_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow26_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow26_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow26_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow26_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow26_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow26_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow26_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow26_column120

private theorem divisionRow26_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 26 j =
      ((rectangularize 83 121 divisionReducedData).getD 26 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow26_windowCoefficients j hj

private theorem divisionRow26_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 26) =
      (rectangularize 83 121 divisionReducedData).getD 26 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 26
    ((rectangularize 83 121 divisionReducedData).getD 26 [])
  · rw [show 26 = 16 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        16 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 26 []).length ≤ 121 := by
      rw [show 26 = 21 + 5 by omega,
        ← getD_drop_window divisionReducedData 21 5 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          5 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        5 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 26 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow26_coefficients

private theorem divisionRow27_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  rw [show 27 = 17 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 17 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow27_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 27 = 17 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow27_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 27 = 17 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow27_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 27 = 17 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow27_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 27 = 17 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow27_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 27 = 17 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow27_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 27 = 17 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow27_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 95 := by
  rw [show 27 = 17 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 96 := by
  rw [show 27 = 17 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 97 := by
  rw [show 27 = 17 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 98 := by
  rw [show 27 = 17 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 99 := by
  rw [show 27 = 17 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 100 := by
  rw [show 27 = 17 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 101 := by
  rw [show 27 = 17 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 102 := by
  rw [show 27 = 17 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 103 := by
  rw [show 27 = 17 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 104 := by
  rw [show 27 = 17 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 105 := by
  rw [show 27 = 17 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 106 := by
  rw [show 27 = 17 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 107 := by
  rw [show 27 = 17 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 108 := by
  rw [show 27 = 17 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 109 := by
  rw [show 27 = 17 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 110 := by
  rw [show 27 = 17 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 111 := by
  rw [show 27 = 17 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 112 := by
  rw [show 27 = 17 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 113 := by
  rw [show 27 = 17 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 114 := by
  rw [show 27 = 17 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 115 := by
  rw [show 27 = 17 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 116 := by
  rw [show 27 = 17 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 117 := by
  rw [show 27 = 17 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 118 := by
  rw [show 27 = 17 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 119 := by
  rw [show 27 = 17 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow27_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 120 := by
  rw [show 27 = 17 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      17 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        27 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow27_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 27 j := by
  by_cases h15 : j < 15
  · exact divisionRow27_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow27_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow27_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow27_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow27_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow27_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow27_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow27_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow27_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow27_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow27_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow27_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow27_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow27_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow27_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow27_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow27_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow27_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow27_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow27_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow27_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow27_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow27_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow27_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow27_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow27_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow27_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow27_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow27_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow27_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow27_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow27_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow27_column120

private theorem divisionRow27_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 27 j =
      ((rectangularize 83 121 divisionReducedData).getD 27 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow27_windowCoefficients j hj

private theorem divisionRow27_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 27) =
      (rectangularize 83 121 divisionReducedData).getD 27 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 27
    ((rectangularize 83 121 divisionReducedData).getD 27 [])
  · rw [show 27 = 17 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        17 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 27 []).length ≤ 121 := by
      rw [show 27 = 21 + 6 by omega,
        ← getD_drop_window divisionReducedData 21 6 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          6 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        6 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 27 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow27_coefficients

private theorem divisionRow28_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  rw [show 28 = 18 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 18 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow28_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 28 = 18 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow28_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 28 = 18 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow28_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 28 = 18 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow28_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 28 = 18 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow28_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 28 = 18 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow28_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 28 = 18 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow28_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 95 := by
  rw [show 28 = 18 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 96 := by
  rw [show 28 = 18 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 97 := by
  rw [show 28 = 18 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 98 := by
  rw [show 28 = 18 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 99 := by
  rw [show 28 = 18 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 100 := by
  rw [show 28 = 18 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 101 := by
  rw [show 28 = 18 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 102 := by
  rw [show 28 = 18 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 103 := by
  rw [show 28 = 18 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 104 := by
  rw [show 28 = 18 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 105 := by
  rw [show 28 = 18 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 106 := by
  rw [show 28 = 18 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 107 := by
  rw [show 28 = 18 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 108 := by
  rw [show 28 = 18 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 109 := by
  rw [show 28 = 18 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 110 := by
  rw [show 28 = 18 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 111 := by
  rw [show 28 = 18 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 112 := by
  rw [show 28 = 18 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 113 := by
  rw [show 28 = 18 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 114 := by
  rw [show 28 = 18 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 115 := by
  rw [show 28 = 18 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 116 := by
  rw [show 28 = 18 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 117 := by
  rw [show 28 = 18 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 118 := by
  rw [show 28 = 18 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 119 := by
  rw [show 28 = 18 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow28_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 120 := by
  rw [show 28 = 18 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      18 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        28 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow28_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 28 j := by
  by_cases h15 : j < 15
  · exact divisionRow28_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow28_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow28_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow28_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow28_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow28_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow28_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow28_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow28_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow28_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow28_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow28_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow28_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow28_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow28_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow28_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow28_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow28_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow28_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow28_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow28_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow28_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow28_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow28_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow28_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow28_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow28_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow28_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow28_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow28_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow28_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow28_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow28_column120

private theorem divisionRow28_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 28 j =
      ((rectangularize 83 121 divisionReducedData).getD 28 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow28_windowCoefficients j hj

private theorem divisionRow28_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 28) =
      (rectangularize 83 121 divisionReducedData).getD 28 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 28
    ((rectangularize 83 121 divisionReducedData).getD 28 [])
  · rw [show 28 = 18 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        18 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 28 []).length ≤ 121 := by
      rw [show 28 = 21 + 7 by omega,
        ← getD_drop_window divisionReducedData 21 7 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          7 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        7 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 28 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow28_coefficients

private theorem divisionRow29_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  rw [show 29 = 19 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 19 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow29_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 29 = 19 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow29_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 29 = 19 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow29_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 29 = 19 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow29_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 29 = 19 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow29_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 29 = 19 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow29_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 29 = 19 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow29_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 95 := by
  rw [show 29 = 19 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 96 := by
  rw [show 29 = 19 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 97 := by
  rw [show 29 = 19 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 98 := by
  rw [show 29 = 19 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 99 := by
  rw [show 29 = 19 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 100 := by
  rw [show 29 = 19 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 101 := by
  rw [show 29 = 19 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 102 := by
  rw [show 29 = 19 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 103 := by
  rw [show 29 = 19 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 104 := by
  rw [show 29 = 19 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 105 := by
  rw [show 29 = 19 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 106 := by
  rw [show 29 = 19 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 107 := by
  rw [show 29 = 19 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 108 := by
  rw [show 29 = 19 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 109 := by
  rw [show 29 = 19 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 110 := by
  rw [show 29 = 19 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 111 := by
  rw [show 29 = 19 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 112 := by
  rw [show 29 = 19 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 113 := by
  rw [show 29 = 19 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 114 := by
  rw [show 29 = 19 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 115 := by
  rw [show 29 = 19 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 116 := by
  rw [show 29 = 19 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 117 := by
  rw [show 29 = 19 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 118 := by
  rw [show 29 = 19 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 119 := by
  rw [show 29 = 19 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow29_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 120 := by
  rw [show 29 = 19 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      19 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        29 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow29_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 29 j := by
  by_cases h15 : j < 15
  · exact divisionRow29_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow29_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow29_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow29_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow29_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow29_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow29_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow29_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow29_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow29_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow29_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow29_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow29_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow29_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow29_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow29_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow29_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow29_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow29_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow29_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow29_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow29_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow29_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow29_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow29_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow29_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow29_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow29_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow29_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow29_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow29_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow29_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow29_column120

private theorem divisionRow29_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 29 j =
      ((rectangularize 83 121 divisionReducedData).getD 29 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow29_windowCoefficients j hj

private theorem divisionRow29_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 29) =
      (rectangularize 83 121 divisionReducedData).getD 29 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 29
    ((rectangularize 83 121 divisionReducedData).getD 29 [])
  · rw [show 29 = 19 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        19 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 29 []).length ≤ 121 := by
      rw [show 29 = 21 + 8 by omega,
        ← getD_drop_window divisionReducedData 21 8 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          8 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        8 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 29 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow29_coefficients

private theorem divisionRow30_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  rw [show 30 = 20 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 20 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow30_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 30 = 20 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow30_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 30 = 20 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow30_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 30 = 20 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow30_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 30 = 20 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow30_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 30 = 20 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow30_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 30 = 20 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow30_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 95 := by
  rw [show 30 = 20 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 96 := by
  rw [show 30 = 20 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 97 := by
  rw [show 30 = 20 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 98 := by
  rw [show 30 = 20 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 99 := by
  rw [show 30 = 20 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 100 := by
  rw [show 30 = 20 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 101 := by
  rw [show 30 = 20 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 102 := by
  rw [show 30 = 20 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 103 := by
  rw [show 30 = 20 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 104 := by
  rw [show 30 = 20 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 105 := by
  rw [show 30 = 20 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 106 := by
  rw [show 30 = 20 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 107 := by
  rw [show 30 = 20 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 108 := by
  rw [show 30 = 20 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 109 := by
  rw [show 30 = 20 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 110 := by
  rw [show 30 = 20 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 111 := by
  rw [show 30 = 20 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 112 := by
  rw [show 30 = 20 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 113 := by
  rw [show 30 = 20 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 114 := by
  rw [show 30 = 20 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 115 := by
  rw [show 30 = 20 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 116 := by
  rw [show 30 = 20 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 117 := by
  rw [show 30 = 20 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 118 := by
  rw [show 30 = 20 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 119 := by
  rw [show 30 = 20 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 120 := by
  rw [show 30 = 20 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      20 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow30_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 30 j := by
  by_cases h15 : j < 15
  · exact divisionRow30_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow30_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow30_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow30_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow30_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow30_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow30_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow30_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow30_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow30_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow30_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow30_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow30_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow30_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow30_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow30_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow30_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow30_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow30_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow30_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow30_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow30_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow30_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow30_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow30_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow30_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow30_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow30_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow30_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow30_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow30_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow30_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow30_column120

private theorem divisionRow30_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 30 j =
      ((rectangularize 83 121 divisionReducedData).getD 30 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow30_windowCoefficients j hj

private theorem divisionRow30_targetSupport :
    (divisionReducedData.getD 30 []).length ≤ 121 := by
  rw [show 30 = 21 + 9 by omega,
    ← getD_drop_window divisionReducedData 21 9 []]
  change
    ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
      9 []).length ≤ 121
  rw [← getD_drop_window
    (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
    9 0 []]
  decide

private theorem divisionRow30_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 30) =
      (rectangularize 83 121 divisionReducedData).getD 30 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 30
    ((rectangularize 83 121 divisionReducedData).getD 30 [])
  · rw [show 30 = 20 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        20 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 30 []).length ≤ 121 := by
      exact divisionRow30_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 30 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow30_coefficients

private theorem divisionRow31_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  rw [show 31 = 21 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 21 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow31_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 31 = 21 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow31_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 31 = 21 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow31_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 31 = 21 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow31_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 31 = 21 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow31_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 31 = 21 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow31_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 31 = 21 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow31_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 95 := by
  rw [show 31 = 21 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 96 := by
  rw [show 31 = 21 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 97 := by
  rw [show 31 = 21 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 98 := by
  rw [show 31 = 21 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 99 := by
  rw [show 31 = 21 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 100 := by
  rw [show 31 = 21 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 101 := by
  rw [show 31 = 21 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 102 := by
  rw [show 31 = 21 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 103 := by
  rw [show 31 = 21 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 104 := by
  rw [show 31 = 21 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 105 := by
  rw [show 31 = 21 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 106 := by
  rw [show 31 = 21 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 107 := by
  rw [show 31 = 21 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 108 := by
  rw [show 31 = 21 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 109 := by
  rw [show 31 = 21 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 110 := by
  rw [show 31 = 21 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 111 := by
  rw [show 31 = 21 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 112 := by
  rw [show 31 = 21 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 113 := by
  rw [show 31 = 21 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 114 := by
  rw [show 31 = 21 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 115 := by
  rw [show 31 = 21 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 116 := by
  rw [show 31 = 21 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 117 := by
  rw [show 31 = 21 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 118 := by
  rw [show 31 = 21 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 119 := by
  rw [show 31 = 21 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow31_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 120 := by
  rw [show 31 = 21 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      21 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        31 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow31_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 31 j := by
  by_cases h15 : j < 15
  · exact divisionRow31_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow31_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow31_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow31_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow31_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow31_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow31_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow31_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow31_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow31_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow31_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow31_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow31_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow31_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow31_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow31_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow31_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow31_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow31_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow31_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow31_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow31_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow31_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow31_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow31_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow31_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow31_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow31_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow31_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow31_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow31_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow31_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow31_column120

private theorem divisionRow31_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 31 j =
      ((rectangularize 83 121 divisionReducedData).getD 31 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow31_windowCoefficients j hj

private theorem divisionRow31_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 31) =
      (rectangularize 83 121 divisionReducedData).getD 31 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 31
    ((rectangularize 83 121 divisionReducedData).getD 31 [])
  · rw [show 31 = 21 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        21 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 31 []).length ≤ 121 := by
      rw [show 31 = 21 + 10 by omega,
        ← getD_drop_window divisionReducedData 21 10 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          10 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        10 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 31 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow31_coefficients

private theorem divisionRow32_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  rw [show 32 = 22 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 22 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow32_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 32 = 22 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow32_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 32 = 22 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow32_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 32 = 22 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow32_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 32 = 22 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow32_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 32 = 22 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow32_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 32 = 22 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow32_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 95 := by
  rw [show 32 = 22 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 96 := by
  rw [show 32 = 22 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 97 := by
  rw [show 32 = 22 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 98 := by
  rw [show 32 = 22 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 99 := by
  rw [show 32 = 22 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 100 := by
  rw [show 32 = 22 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 101 := by
  rw [show 32 = 22 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 102 := by
  rw [show 32 = 22 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 103 := by
  rw [show 32 = 22 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 104 := by
  rw [show 32 = 22 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 105 := by
  rw [show 32 = 22 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 106 := by
  rw [show 32 = 22 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 107 := by
  rw [show 32 = 22 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 108 := by
  rw [show 32 = 22 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 109 := by
  rw [show 32 = 22 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 110 := by
  rw [show 32 = 22 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 111 := by
  rw [show 32 = 22 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 112 := by
  rw [show 32 = 22 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 113 := by
  rw [show 32 = 22 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 114 := by
  rw [show 32 = 22 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 115 := by
  rw [show 32 = 22 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 116 := by
  rw [show 32 = 22 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 117 := by
  rw [show 32 = 22 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 118 := by
  rw [show 32 = 22 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 119 := by
  rw [show 32 = 22 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow32_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 120 := by
  rw [show 32 = 22 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      22 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        32 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow32_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 32 j := by
  by_cases h15 : j < 15
  · exact divisionRow32_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow32_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow32_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow32_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow32_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow32_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow32_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow32_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow32_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow32_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow32_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow32_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow32_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow32_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow32_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow32_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow32_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow32_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow32_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow32_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow32_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow32_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow32_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow32_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow32_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow32_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow32_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow32_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow32_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow32_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow32_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow32_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow32_column120

private theorem divisionRow32_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 32 j =
      ((rectangularize 83 121 divisionReducedData).getD 32 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow32_windowCoefficients j hj

private theorem divisionRow32_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 32) =
      (rectangularize 83 121 divisionReducedData).getD 32 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 32
    ((rectangularize 83 121 divisionReducedData).getD 32 [])
  · rw [show 32 = 22 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        22 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 32 []).length ≤ 121 := by
      rw [show 32 = 21 + 11 by omega,
        ← getD_drop_window divisionReducedData 21 11 []]
      change
        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh).getD
          11 []).length ≤ 121
      rw [← getD_drop_window
        (ReducedDataMidLow ++ ReducedDataMidHigh ++ ReducedDataHigh)
        11 0 []]
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 32 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow32_coefficients

/-- The complete exact-division certificates for rows 25 through 32. -/
theorem divisionRowsTwentyFiveToThirtyTwo_spec (n : ℕ)
    (hLower : 25 ≤ n) (hUpper : n < 33) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow25_spec
  · exact divisionRow26_spec
  · exact divisionRow27_spec
  · exact divisionRow28_spec
  · exact divisionRow29_spec
  · exact divisionRow30_spec
  · exact divisionRow31_spec
  · exact divisionRow32_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
