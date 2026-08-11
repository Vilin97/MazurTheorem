/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 17 through 24 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow17_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  rw [show 17 = 7 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 7 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow17_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 17 = 7 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow17_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 17 = 7 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow17_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 17 = 7 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow17_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 17 = 7 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow17_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 17 = 7 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow17_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 17 = 7 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow17_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 95 := by
  rw [show 17 = 7 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 96 := by
  rw [show 17 = 7 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 97 := by
  rw [show 17 = 7 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 98 := by
  rw [show 17 = 7 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 99 := by
  rw [show 17 = 7 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 100 := by
  rw [show 17 = 7 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 101 := by
  rw [show 17 = 7 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 102 := by
  rw [show 17 = 7 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 103 := by
  rw [show 17 = 7 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 104 := by
  rw [show 17 = 7 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 105 := by
  rw [show 17 = 7 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 106 := by
  rw [show 17 = 7 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 107 := by
  rw [show 17 = 7 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 108 := by
  rw [show 17 = 7 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 109 := by
  rw [show 17 = 7 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 110 := by
  rw [show 17 = 7 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 111 := by
  rw [show 17 = 7 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 112 := by
  rw [show 17 = 7 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 113 := by
  rw [show 17 = 7 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 114 := by
  rw [show 17 = 7 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 115 := by
  rw [show 17 = 7 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow17_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 116 := by
  rw [show 17 = 7 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        17 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow17_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 117 := by
  rw [show 17 = 7 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        17 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow17_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 118 := by
  rw [show 17 = 7 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        17 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow17_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 119 := by
  rw [show 17 = 7 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        17 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow17_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 120 := by
  rw [show 17 = 7 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      7 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        17 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow17_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 17 j := by
  by_cases h15 : j < 15
  · exact divisionRow17_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow17_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow17_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow17_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow17_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow17_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow17_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow17_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow17_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow17_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow17_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow17_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow17_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow17_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow17_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow17_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow17_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow17_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow17_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow17_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow17_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow17_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow17_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow17_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow17_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow17_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow17_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow17_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow17_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow17_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow17_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow17_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow17_column120

private theorem divisionRow17_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 17 j =
      ((rectangularize 83 121 divisionReducedData).getD 17 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow17_windowCoefficients j hj

private theorem divisionRow17_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 17) =
      (rectangularize 83 121 divisionReducedData).getD 17 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 17
    ((rectangularize 83 121 divisionReducedData).getD 17 [])
  · rw [show 17 = 7 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        7 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 17 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 17 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow17_coefficients

private theorem divisionRow18_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  rw [show 18 = 8 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 8 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow18_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 18 = 8 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow18_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 18 = 8 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow18_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 18 = 8 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow18_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 18 = 8 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow18_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 18 = 8 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow18_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 18 = 8 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow18_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 95 := by
  rw [show 18 = 8 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 96 := by
  rw [show 18 = 8 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 97 := by
  rw [show 18 = 8 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 98 := by
  rw [show 18 = 8 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 99 := by
  rw [show 18 = 8 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 100 := by
  rw [show 18 = 8 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 101 := by
  rw [show 18 = 8 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 102 := by
  rw [show 18 = 8 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 103 := by
  rw [show 18 = 8 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 104 := by
  rw [show 18 = 8 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 105 := by
  rw [show 18 = 8 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 106 := by
  rw [show 18 = 8 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 107 := by
  rw [show 18 = 8 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 108 := by
  rw [show 18 = 8 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 109 := by
  rw [show 18 = 8 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 110 := by
  rw [show 18 = 8 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 111 := by
  rw [show 18 = 8 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 112 := by
  rw [show 18 = 8 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 113 := by
  rw [show 18 = 8 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 114 := by
  rw [show 18 = 8 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 115 := by
  rw [show 18 = 8 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 116 := by
  rw [show 18 = 8 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow18_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 117 := by
  rw [show 18 = 8 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        18 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow18_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 118 := by
  rw [show 18 = 8 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        18 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow18_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 119 := by
  rw [show 18 = 8 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        18 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow18_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 120 := by
  rw [show 18 = 8 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      8 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        18 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow18_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 18 j := by
  by_cases h15 : j < 15
  · exact divisionRow18_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow18_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow18_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow18_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow18_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow18_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow18_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow18_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow18_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow18_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow18_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow18_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow18_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow18_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow18_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow18_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow18_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow18_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow18_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow18_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow18_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow18_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow18_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow18_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow18_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow18_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow18_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow18_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow18_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow18_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow18_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow18_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow18_column120

private theorem divisionRow18_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 18 j =
      ((rectangularize 83 121 divisionReducedData).getD 18 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow18_windowCoefficients j hj

private theorem divisionRow18_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 18) =
      (rectangularize 83 121 divisionReducedData).getD 18 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 18
    ((rectangularize 83 121 divisionReducedData).getD 18 [])
  · rw [show 18 = 8 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        8 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 18 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 18 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow18_coefficients

private theorem divisionRow19_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  rw [show 19 = 9 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 9 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow19_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 19 = 9 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow19_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 19 = 9 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow19_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 19 = 9 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow19_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 19 = 9 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow19_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 19 = 9 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow19_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 19 = 9 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow19_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 95 := by
  rw [show 19 = 9 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 96 := by
  rw [show 19 = 9 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 97 := by
  rw [show 19 = 9 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 98 := by
  rw [show 19 = 9 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 99 := by
  rw [show 19 = 9 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 100 := by
  rw [show 19 = 9 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 101 := by
  rw [show 19 = 9 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 102 := by
  rw [show 19 = 9 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 103 := by
  rw [show 19 = 9 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 104 := by
  rw [show 19 = 9 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 105 := by
  rw [show 19 = 9 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 106 := by
  rw [show 19 = 9 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 107 := by
  rw [show 19 = 9 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 108 := by
  rw [show 19 = 9 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 109 := by
  rw [show 19 = 9 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 110 := by
  rw [show 19 = 9 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 111 := by
  rw [show 19 = 9 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 112 := by
  rw [show 19 = 9 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 113 := by
  rw [show 19 = 9 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 114 := by
  rw [show 19 = 9 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 115 := by
  rw [show 19 = 9 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 116 := by
  rw [show 19 = 9 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow19_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 117 := by
  rw [show 19 = 9 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        19 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow19_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 118 := by
  rw [show 19 = 9 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        19 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow19_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 119 := by
  rw [show 19 = 9 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        19 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow19_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 120 := by
  rw [show 19 = 9 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      9 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        19 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow19_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 19 j := by
  by_cases h15 : j < 15
  · exact divisionRow19_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow19_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow19_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow19_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow19_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow19_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow19_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow19_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow19_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow19_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow19_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow19_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow19_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow19_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow19_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow19_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow19_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow19_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow19_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow19_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow19_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow19_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow19_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow19_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow19_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow19_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow19_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow19_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow19_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow19_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow19_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow19_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow19_column120

private theorem divisionRow19_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 19 j =
      ((rectangularize 83 121 divisionReducedData).getD 19 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow19_windowCoefficients j hj

private theorem divisionRow19_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 19) =
      (rectangularize 83 121 divisionReducedData).getD 19 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 19
    ((rectangularize 83 121 divisionReducedData).getD 19 [])
  · rw [show 19 = 9 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        9 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 19 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 19 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow19_coefficients

private theorem divisionRow20_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  rw [show 20 = 10 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 10 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow20_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 20 = 10 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow20_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 20 = 10 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow20_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 20 = 10 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow20_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 20 = 10 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow20_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 20 = 10 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow20_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 20 = 10 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow20_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 95 := by
  rw [show 20 = 10 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 96 := by
  rw [show 20 = 10 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 97 := by
  rw [show 20 = 10 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 98 := by
  rw [show 20 = 10 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 99 := by
  rw [show 20 = 10 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 100 := by
  rw [show 20 = 10 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 101 := by
  rw [show 20 = 10 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 102 := by
  rw [show 20 = 10 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 103 := by
  rw [show 20 = 10 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 104 := by
  rw [show 20 = 10 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 105 := by
  rw [show 20 = 10 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 106 := by
  rw [show 20 = 10 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 107 := by
  rw [show 20 = 10 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 108 := by
  rw [show 20 = 10 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 109 := by
  rw [show 20 = 10 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 110 := by
  rw [show 20 = 10 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 111 := by
  rw [show 20 = 10 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 112 := by
  rw [show 20 = 10 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 113 := by
  rw [show 20 = 10 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 114 := by
  rw [show 20 = 10 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 115 := by
  rw [show 20 = 10 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 116 := by
  rw [show 20 = 10 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow20_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 117 := by
  rw [show 20 = 10 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        20 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow20_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 118 := by
  rw [show 20 = 10 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        20 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow20_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 119 := by
  rw [show 20 = 10 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        20 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow20_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 120 := by
  rw [show 20 = 10 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      10 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        20 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow20_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 20 j := by
  by_cases h15 : j < 15
  · exact divisionRow20_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow20_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow20_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow20_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow20_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow20_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow20_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow20_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow20_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow20_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow20_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow20_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow20_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow20_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow20_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow20_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow20_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow20_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow20_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow20_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow20_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow20_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow20_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow20_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow20_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow20_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow20_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow20_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow20_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow20_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow20_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow20_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow20_column120

private theorem divisionRow20_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 20 j =
      ((rectangularize 83 121 divisionReducedData).getD 20 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow20_windowCoefficients j hj

private theorem divisionRow20_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 20) =
      (rectangularize 83 121 divisionReducedData).getD 20 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 20
    ((rectangularize 83 121 divisionReducedData).getD 20 [])
  · rw [show 20 = 10 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        10 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 20 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 20 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow20_coefficients

private theorem divisionRow21_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  rw [show 21 = 11 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 11 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow21_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 21 = 11 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow21_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 21 = 11 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow21_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 21 = 11 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow21_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 21 = 11 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow21_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 21 = 11 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow21_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 21 = 11 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow21_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 95 := by
  rw [show 21 = 11 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 96 := by
  rw [show 21 = 11 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 97 := by
  rw [show 21 = 11 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 98 := by
  rw [show 21 = 11 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 99 := by
  rw [show 21 = 11 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 100 := by
  rw [show 21 = 11 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 101 := by
  rw [show 21 = 11 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 102 := by
  rw [show 21 = 11 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 103 := by
  rw [show 21 = 11 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 104 := by
  rw [show 21 = 11 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 105 := by
  rw [show 21 = 11 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 106 := by
  rw [show 21 = 11 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 107 := by
  rw [show 21 = 11 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 108 := by
  rw [show 21 = 11 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 109 := by
  rw [show 21 = 11 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 110 := by
  rw [show 21 = 11 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 111 := by
  rw [show 21 = 11 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 112 := by
  rw [show 21 = 11 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 113 := by
  rw [show 21 = 11 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 114 := by
  rw [show 21 = 11 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 115 := by
  rw [show 21 = 11 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 116 := by
  rw [show 21 = 11 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 117 := by
  rw [show 21 = 11 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow21_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 118 := by
  rw [show 21 = 11 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        21 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow21_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 119 := by
  rw [show 21 = 11 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        21 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow21_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 120 := by
  rw [show 21 = 11 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      11 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        21 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow21_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 21 j := by
  by_cases h15 : j < 15
  · exact divisionRow21_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow21_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow21_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow21_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow21_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow21_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow21_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow21_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow21_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow21_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow21_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow21_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow21_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow21_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow21_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow21_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow21_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow21_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow21_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow21_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow21_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow21_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow21_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow21_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow21_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow21_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow21_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow21_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow21_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow21_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow21_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow21_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow21_column120

private theorem divisionRow21_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 21 j =
      ((rectangularize 83 121 divisionReducedData).getD 21 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow21_windowCoefficients j hj

private theorem divisionRow21_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 21) =
      (rectangularize 83 121 divisionReducedData).getD 21 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 21
    ((rectangularize 83 121 divisionReducedData).getD 21 [])
  · rw [show 21 = 11 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        11 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 21 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 21 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow21_coefficients

private theorem divisionRow22_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  rw [show 22 = 12 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 12 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow22_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 22 = 12 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow22_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 22 = 12 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow22_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 22 = 12 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow22_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 22 = 12 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow22_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 22 = 12 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow22_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 22 = 12 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow22_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 95 := by
  rw [show 22 = 12 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 96 := by
  rw [show 22 = 12 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 97 := by
  rw [show 22 = 12 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 98 := by
  rw [show 22 = 12 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 99 := by
  rw [show 22 = 12 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 100 := by
  rw [show 22 = 12 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 101 := by
  rw [show 22 = 12 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 102 := by
  rw [show 22 = 12 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 103 := by
  rw [show 22 = 12 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 104 := by
  rw [show 22 = 12 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 105 := by
  rw [show 22 = 12 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 106 := by
  rw [show 22 = 12 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 107 := by
  rw [show 22 = 12 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 108 := by
  rw [show 22 = 12 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 109 := by
  rw [show 22 = 12 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 110 := by
  rw [show 22 = 12 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 111 := by
  rw [show 22 = 12 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 112 := by
  rw [show 22 = 12 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 113 := by
  rw [show 22 = 12 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 114 := by
  rw [show 22 = 12 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 115 := by
  rw [show 22 = 12 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 116 := by
  rw [show 22 = 12 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 117 := by
  rw [show 22 = 12 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow22_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 118 := by
  rw [show 22 = 12 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        22 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow22_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 119 := by
  rw [show 22 = 12 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        22 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow22_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 120 := by
  rw [show 22 = 12 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      12 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        22 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow22_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 22 j := by
  by_cases h15 : j < 15
  · exact divisionRow22_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow22_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow22_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow22_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow22_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow22_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow22_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow22_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow22_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow22_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow22_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow22_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow22_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow22_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow22_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow22_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow22_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow22_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow22_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow22_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow22_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow22_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow22_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow22_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow22_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow22_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow22_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow22_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow22_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow22_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow22_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow22_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow22_column120

private theorem divisionRow22_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 22 j =
      ((rectangularize 83 121 divisionReducedData).getD 22 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow22_windowCoefficients j hj

private theorem divisionRow22_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 22) =
      (rectangularize 83 121 divisionReducedData).getD 22 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 22
    ((rectangularize 83 121 divisionReducedData).getD 22 [])
  · rw [show 22 = 12 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        12 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 22 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 22 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow22_coefficients

private theorem divisionRow23_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  rw [show 23 = 13 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 13 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow23_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 23 = 13 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow23_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 23 = 13 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow23_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 23 = 13 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow23_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 23 = 13 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow23_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 23 = 13 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow23_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 23 = 13 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow23_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 95 := by
  rw [show 23 = 13 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 96 := by
  rw [show 23 = 13 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 97 := by
  rw [show 23 = 13 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 98 := by
  rw [show 23 = 13 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 99 := by
  rw [show 23 = 13 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 100 := by
  rw [show 23 = 13 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 101 := by
  rw [show 23 = 13 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 102 := by
  rw [show 23 = 13 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 103 := by
  rw [show 23 = 13 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 104 := by
  rw [show 23 = 13 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 105 := by
  rw [show 23 = 13 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 106 := by
  rw [show 23 = 13 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 107 := by
  rw [show 23 = 13 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 108 := by
  rw [show 23 = 13 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 109 := by
  rw [show 23 = 13 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 110 := by
  rw [show 23 = 13 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 111 := by
  rw [show 23 = 13 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 112 := by
  rw [show 23 = 13 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 113 := by
  rw [show 23 = 13 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 114 := by
  rw [show 23 = 13 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 115 := by
  rw [show 23 = 13 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 116 := by
  rw [show 23 = 13 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 117 := by
  rw [show 23 = 13 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow23_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 118 := by
  rw [show 23 = 13 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        23 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow23_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 119 := by
  rw [show 23 = 13 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        23 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow23_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 120 := by
  rw [show 23 = 13 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      13 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        23 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow23_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 23 j := by
  by_cases h15 : j < 15
  · exact divisionRow23_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow23_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow23_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow23_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow23_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow23_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow23_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow23_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow23_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow23_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow23_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow23_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow23_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow23_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow23_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow23_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow23_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow23_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow23_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow23_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow23_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow23_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow23_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow23_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow23_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow23_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow23_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow23_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow23_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow23_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow23_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow23_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow23_column120

private theorem divisionRow23_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 23 j =
      ((rectangularize 83 121 divisionReducedData).getD 23 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow23_windowCoefficients j hj

private theorem divisionRow23_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 23) =
      (rectangularize 83 121 divisionReducedData).getD 23 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 23
    ((rectangularize 83 121 divisionReducedData).getD 23 [])
  · rw [show 23 = 13 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        13 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 23 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 23 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow23_coefficients

private theorem divisionRow24_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  rw [show 24 = 14 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 14 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow24_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 24 = 14 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow24_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 24 = 14 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow24_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 24 = 14 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow24_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 24 = 14 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow24_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 24 = 14 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow24_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 24 = 14 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow24_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 95 := by
  rw [show 24 = 14 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 96 := by
  rw [show 24 = 14 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 97 := by
  rw [show 24 = 14 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 98 := by
  rw [show 24 = 14 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 99 := by
  rw [show 24 = 14 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 100 := by
  rw [show 24 = 14 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 101 := by
  rw [show 24 = 14 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 102 := by
  rw [show 24 = 14 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 103 := by
  rw [show 24 = 14 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 104 := by
  rw [show 24 = 14 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 105 := by
  rw [show 24 = 14 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 106 := by
  rw [show 24 = 14 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 107 := by
  rw [show 24 = 14 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 108 := by
  rw [show 24 = 14 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 109 := by
  rw [show 24 = 14 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 110 := by
  rw [show 24 = 14 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 111 := by
  rw [show 24 = 14 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 112 := by
  rw [show 24 = 14 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 113 := by
  rw [show 24 = 14 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 114 := by
  rw [show 24 = 14 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 115 := by
  rw [show 24 = 14 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 116 := by
  rw [show 24 = 14 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 117 := by
  rw [show 24 = 14 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 118 := by
  rw [show 24 = 14 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow24_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 119 := by
  rw [show 24 = 14 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        24 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow24_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 120 := by
  rw [show 24 = 14 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      14 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        24 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow24_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 24 j := by
  by_cases h15 : j < 15
  · exact divisionRow24_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow24_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow24_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow24_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow24_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow24_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow24_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow24_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow24_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow24_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow24_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow24_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow24_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow24_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow24_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow24_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow24_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow24_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow24_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow24_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow24_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow24_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow24_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow24_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow24_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow24_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow24_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow24_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow24_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow24_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow24_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow24_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow24_column120

private theorem divisionRow24_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 24 j =
      ((rectangularize 83 121 divisionReducedData).getD 24 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow24_windowCoefficients j hj

private theorem divisionRow24_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 24) =
      (rectangularize 83 121 divisionReducedData).getD 24 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 24
    ((rectangularize 83 121 divisionReducedData).getD 24 [])
  · rw [show 24 = 14 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        14 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 24 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 24 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow24_coefficients

/-- The complete exact-division certificates for rows 17 through 24. -/
theorem divisionRowsSeventeenToTwentyFour_spec (n : ℕ)
    (hLower : 17 ≤ n) (hUpper : n < 25) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow17_spec
  · exact divisionRow18_spec
  · exact divisionRow19_spec
  · exact divisionRow20_spec
  · exact divisionRow21_spec
  · exact divisionRow22_spec
  · exact divisionRow23_spec
  · exact divisionRow24_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
