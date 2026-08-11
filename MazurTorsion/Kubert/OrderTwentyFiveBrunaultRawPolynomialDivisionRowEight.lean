/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Row eight of the raw order-twenty-five division certificate

Each finite coefficient declaration contains at most fifteen cases.  Columns
at least fifteen are transported to the exact sixteen-wide inner convolution
window before kernel reduction.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow8_columns0To14
    (j : ℕ) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  interval_cases j <;> decide

private theorem divisionRow8_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 8 (j - 15) 15 divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow8_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 8 (j - 15) 15 divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow8_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 8 (j - 15) 15 divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow8_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 8 (j - 15) 15 divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow8_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 8 (j - 15) 15 divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow8_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 8 (j - 15) 15 divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow8_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 84 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 85 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 86 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 87 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 88 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 89 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 90 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 91 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 92 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 93 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 94 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 95 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 96 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 97 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 98 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 99 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 100 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 101 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 102 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 103 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 104 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 8 105 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow8_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 8 j := by
  by_cases h15 : j < 15
  · exact divisionRow8_columns0To14 j h15
  by_cases h30 : j < 30
  · exact divisionRow8_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow8_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow8_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow8_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow8_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow8_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow8_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow8_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow8_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow8_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow8_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow8_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow8_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow8_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow8_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow8_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow8_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow8_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow8_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow8_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow8_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow8_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow8_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow8_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow8_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow8_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow8_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow8_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow8_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow8_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow8_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow8_column120

private theorem divisionRow8_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 8 j =
      ((rectangularize 83 121 divisionReducedData).getD 8 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow8_windowCoefficients j hj

/-- The complete row-eight exact-division certificate. -/
theorem divisionRowEight_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 8) =
      (rectangularize 83 121 divisionReducedData).getD 8 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 8
    ((rectangularize 83 121 divisionReducedData).getD 8 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 8 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 8 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow8_coefficients

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
