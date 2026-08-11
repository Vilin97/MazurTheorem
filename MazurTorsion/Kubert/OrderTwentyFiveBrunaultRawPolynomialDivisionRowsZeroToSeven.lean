/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows zero through seven of the raw order-twenty-five division certificate

Every finite coefficient declaration has the reviewed bounded fan-out, and
only the aggregate row-range theorem is exported.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow0_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  interval_cases j <;> decide

private theorem divisionRow0_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 0 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow0_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 0 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow0_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 0 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow0_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 0 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow0_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 0 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow0_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 0 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow0_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 0 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow0_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 0 j := by
  by_cases h15 : j < 15
  · exact divisionRow0_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow0_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow0_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow0_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow0_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow0_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow0_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow0_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow0_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow0_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow0_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow0_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow0_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow0_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow0_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow0_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow0_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow0_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow0_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow0_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow0_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow0_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow0_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow0_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow0_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow0_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow0_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow0_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow0_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow0_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow0_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow0_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow0_column120

private theorem divisionRow0_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 0 j =
      ((rectangularize 83 121 divisionReducedData).getD 0 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow0_windowCoefficients j hj

private theorem divisionRow0_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 0) =
      (rectangularize 83 121 divisionReducedData).getD 0 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 0
    ((rectangularize 83 121 divisionReducedData).getD 0 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 0 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 0 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow0_coefficients

private theorem divisionRow1_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  interval_cases j <;> decide

private theorem divisionRow1_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 1 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow1_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 1 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow1_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 1 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow1_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 1 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow1_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 1 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow1_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 1 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow1_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 1 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow1_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 1 j := by
  by_cases h15 : j < 15
  · exact divisionRow1_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow1_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow1_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow1_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow1_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow1_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow1_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow1_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow1_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow1_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow1_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow1_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow1_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow1_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow1_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow1_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow1_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow1_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow1_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow1_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow1_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow1_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow1_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow1_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow1_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow1_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow1_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow1_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow1_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow1_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow1_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow1_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow1_column120

private theorem divisionRow1_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 1 j =
      ((rectangularize 83 121 divisionReducedData).getD 1 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow1_windowCoefficients j hj

private theorem divisionRow1_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 1) =
      (rectangularize 83 121 divisionReducedData).getD 1 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 1
    ((rectangularize 83 121 divisionReducedData).getD 1 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 1 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 1 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow1_coefficients

private theorem divisionRow2_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  interval_cases j <;> decide

private theorem divisionRow2_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 2 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow2_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 2 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow2_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 2 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow2_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 2 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow2_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 2 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow2_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 2 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow2_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 2 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow2_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 2 j := by
  by_cases h15 : j < 15
  · exact divisionRow2_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow2_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow2_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow2_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow2_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow2_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow2_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow2_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow2_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow2_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow2_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow2_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow2_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow2_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow2_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow2_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow2_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow2_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow2_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow2_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow2_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow2_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow2_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow2_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow2_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow2_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow2_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow2_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow2_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow2_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow2_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow2_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow2_column120

private theorem divisionRow2_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 2 j =
      ((rectangularize 83 121 divisionReducedData).getD 2 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow2_windowCoefficients j hj

private theorem divisionRow2_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 2) =
      (rectangularize 83 121 divisionReducedData).getD 2 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 2
    ((rectangularize 83 121 divisionReducedData).getD 2 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 2 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 2 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow2_coefficients

private theorem divisionRow3_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  interval_cases j <;> decide

private theorem divisionRow3_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 3 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow3_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 3 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow3_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 3 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow3_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 3 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow3_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 3 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow3_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 3 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow3_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 3 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow3_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 3 j := by
  by_cases h15 : j < 15
  · exact divisionRow3_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow3_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow3_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow3_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow3_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow3_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow3_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow3_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow3_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow3_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow3_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow3_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow3_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow3_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow3_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow3_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow3_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow3_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow3_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow3_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow3_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow3_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow3_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow3_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow3_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow3_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow3_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow3_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow3_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow3_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow3_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow3_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow3_column120

private theorem divisionRow3_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 3 j =
      ((rectangularize 83 121 divisionReducedData).getD 3 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow3_windowCoefficients j hj

private theorem divisionRow3_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 3) =
      (rectangularize 83 121 divisionReducedData).getD 3 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 3
    ((rectangularize 83 121 divisionReducedData).getD 3 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 3 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 3 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow3_coefficients

private theorem divisionRow4_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  interval_cases j <;> decide

private theorem divisionRow4_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 4 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow4_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 4 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow4_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 4 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow4_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 4 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow4_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 4 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow4_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 4 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow4_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 4 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow4_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 4 j := by
  by_cases h15 : j < 15
  · exact divisionRow4_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow4_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow4_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow4_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow4_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow4_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow4_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow4_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow4_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow4_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow4_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow4_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow4_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow4_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow4_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow4_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow4_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow4_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow4_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow4_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow4_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow4_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow4_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow4_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow4_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow4_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow4_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow4_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow4_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow4_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow4_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow4_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow4_column120

private theorem divisionRow4_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 4 j =
      ((rectangularize 83 121 divisionReducedData).getD 4 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow4_windowCoefficients j hj

private theorem divisionRow4_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 4) =
      (rectangularize 83 121 divisionReducedData).getD 4 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 4
    ((rectangularize 83 121 divisionReducedData).getD 4 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 4 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 4 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow4_coefficients

private theorem divisionRow5_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  interval_cases j <;> decide

private theorem divisionRow5_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 5 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow5_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 5 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow5_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 5 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow5_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 5 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow5_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 5 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow5_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 5 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow5_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 5 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow5_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 5 j := by
  by_cases h15 : j < 15
  · exact divisionRow5_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow5_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow5_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow5_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow5_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow5_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow5_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow5_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow5_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow5_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow5_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow5_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow5_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow5_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow5_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow5_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow5_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow5_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow5_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow5_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow5_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow5_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow5_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow5_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow5_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow5_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow5_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow5_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow5_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow5_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow5_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow5_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow5_column120

private theorem divisionRow5_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 5 j =
      ((rectangularize 83 121 divisionReducedData).getD 5 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow5_windowCoefficients j hj

private theorem divisionRow5_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 5) =
      (rectangularize 83 121 divisionReducedData).getD 5 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 5
    ((rectangularize 83 121 divisionReducedData).getD 5 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 5 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 5 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow5_coefficients

private theorem divisionRow6_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  interval_cases j <;> decide

private theorem divisionRow6_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 6 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow6_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 6 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow6_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 6 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow6_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 6 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow6_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 6 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow6_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 6 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow6_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 6 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow6_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 6 j := by
  by_cases h15 : j < 15
  · exact divisionRow6_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow6_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow6_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow6_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow6_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow6_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow6_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow6_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow6_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow6_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow6_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow6_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow6_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow6_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow6_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow6_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow6_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow6_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow6_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow6_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow6_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow6_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow6_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow6_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow6_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow6_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow6_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow6_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow6_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow6_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow6_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow6_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow6_column120

private theorem divisionRow6_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 6 j =
      ((rectangularize 83 121 divisionReducedData).getD 6 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow6_windowCoefficients j hj

private theorem divisionRow6_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 6) =
      (rectangularize 83 121 divisionReducedData).getD 6 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 6
    ((rectangularize 83 121 divisionReducedData).getD 6 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 6 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 6 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow6_coefficients

private theorem divisionRow7_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  interval_cases j <;> decide

private theorem divisionRow7_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 7 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow7_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 7 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow7_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 7 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow7_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 7 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow7_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 7 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow7_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 7 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow7_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 7 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow7_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 7 j := by
  by_cases h15 : j < 15
  · exact divisionRow7_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow7_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow7_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow7_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow7_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow7_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow7_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow7_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow7_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow7_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow7_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow7_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow7_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow7_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow7_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow7_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow7_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow7_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow7_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow7_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow7_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow7_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow7_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow7_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow7_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow7_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow7_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow7_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow7_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow7_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow7_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow7_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow7_column120

private theorem divisionRow7_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 7 j =
      ((rectangularize 83 121 divisionReducedData).getD 7 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow7_windowCoefficients j hj

private theorem divisionRow7_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 7) =
      (rectangularize 83 121 divisionReducedData).getD 7 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 7
    ((rectangularize 83 121 divisionReducedData).getD 7 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 7 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 7 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow7_coefficients

/-- The complete exact-division certificates for rows zero through seven. -/
theorem divisionRowsZeroToSeven_spec (n : ℕ) (hn : n < 8) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow0_spec
  · exact divisionRow1_spec
  · exact divisionRow2_spec
  · exact divisionRow3_spec
  · exact divisionRow4_spec
  · exact divisionRow5_spec
  · exact divisionRow6_spec
  · exact divisionRow7_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
