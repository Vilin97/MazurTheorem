/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows nine through sixteen of the raw order-twenty-five division certificate

Rows at least ten use the exact eleven-row outer convolution window.  Every
finite coefficient declaration uses the reviewed bounded fan-out.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow9_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  interval_cases j <;> decide

private theorem divisionRow9_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 9 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow9_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 9 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow9_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 9 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow9_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 9 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow9_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 9 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow9_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [hSplit, mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
    divisionQuotientData 9 (j - 15) 15
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow9_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 95 := by
  rw [show 95 = 80 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 80 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow9_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 96 := by
  rw [show 96 = 81 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 81 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow9_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 97 := by
  rw [show 97 = 82 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 82 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow9_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 98 := by
  rw [show 98 = 83 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 83 15 divisionSutherland_innerSupport]
  decide

private theorem divisionRow9_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 99 := by
  rw [show 99 = 84 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 84 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 100 := by
  rw [show 100 = 85 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 85 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 101 := by
  rw [show 101 = 86 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 86 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 102 := by
  rw [show 102 = 87 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 87 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 103 := by
  rw [show 103 = 88 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 88 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 104 := by
  rw [show 104 = 89 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 89 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 105 := by
  rw [show 105 = 90 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 90 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 106 := by
  rw [show 106 = 91 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 91 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 107 := by
  rw [show 107 = 92 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 92 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 108 := by
  rw [show 108 = 93 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 93 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 109 := by
  rw [show 109 = 94 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 94 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 110 := by
  rw [show 110 = 95 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 95 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 111 := by
  rw [show 111 = 96 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 96 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 112 := by
  rw [show 112 = 97 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 97 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 113 := by
  rw [show 113 = 98 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 98 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 114 := by
  rw [show 114 = 99 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 99 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 115 := by
  rw [show 115 = 100 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 100 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 116 := by
  rw [show 116 = 101 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 101 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 117 := by
  rw [show 117 = 102 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 102 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 118 := by
  rw [show 118 = 103 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 103 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 119 := by
  rw [show 119 = 104 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 104 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 120 := by
  rw [show 120 = 105 + 15 by omega,
    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial
      divisionQuotientData 9 105 15 divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 9 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        9 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow9_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 9 j := by
  by_cases h15 : j < 15
  · exact divisionRow9_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow9_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow9_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow9_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow9_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow9_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow9_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow9_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow9_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow9_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow9_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow9_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow9_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow9_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow9_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow9_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow9_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow9_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow9_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow9_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow9_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow9_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow9_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow9_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow9_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow9_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow9_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow9_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow9_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow9_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow9_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow9_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow9_column120

private theorem divisionRow9_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 9 j =
      ((rectangularize 83 121 divisionReducedData).getD 9 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow9_windowCoefficients j hj

private theorem divisionRow9_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 9) =
      (rectangularize 83 121 divisionReducedData).getD 9 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 9
    ((rectangularize 83 121 divisionReducedData).getD 9 [])
  · decide
  · have hTargetSupport :
        (divisionReducedData.getD 9 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 9 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow9_coefficients

private theorem divisionRow10_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  rw [show 10 = 0 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 0 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow10_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 10 = 0 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow10_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 10 = 0 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow10_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 10 = 0 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow10_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 10 = 0 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow10_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 10 = 0 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow10_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 10 = 0 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow10_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 95 := by
  rw [show 10 = 0 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 96 := by
  rw [show 10 = 0 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 97 := by
  rw [show 10 = 0 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 98 := by
  rw [show 10 = 0 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 99 := by
  rw [show 10 = 0 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 100 := by
  rw [show 10 = 0 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 101 := by
  rw [show 10 = 0 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow10_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 102 := by
  rw [show 10 = 0 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 103 := by
  rw [show 10 = 0 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 104 := by
  rw [show 10 = 0 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 105 := by
  rw [show 10 = 0 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 106 := by
  rw [show 10 = 0 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 107 := by
  rw [show 10 = 0 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 108 := by
  rw [show 10 = 0 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 109 := by
  rw [show 10 = 0 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 110 := by
  rw [show 10 = 0 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 111 := by
  rw [show 10 = 0 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 112 := by
  rw [show 10 = 0 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 113 := by
  rw [show 10 = 0 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 114 := by
  rw [show 10 = 0 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 115 := by
  rw [show 10 = 0 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 116 := by
  rw [show 10 = 0 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 117 := by
  rw [show 10 = 0 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 118 := by
  rw [show 10 = 0 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 119 := by
  rw [show 10 = 0 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 120 := by
  rw [show 10 = 0 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      0 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        10 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow10_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 10 j := by
  by_cases h15 : j < 15
  · exact divisionRow10_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow10_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow10_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow10_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow10_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow10_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow10_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow10_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow10_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow10_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow10_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow10_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow10_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow10_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow10_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow10_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow10_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow10_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow10_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow10_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow10_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow10_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow10_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow10_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow10_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow10_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow10_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow10_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow10_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow10_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow10_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow10_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow10_column120

private theorem divisionRow10_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 10 j =
      ((rectangularize 83 121 divisionReducedData).getD 10 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow10_windowCoefficients j hj

private theorem divisionRow10_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 10) =
      (rectangularize 83 121 divisionReducedData).getD 10 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 10
    ((rectangularize 83 121 divisionReducedData).getD 10 [])
  · rw [show 10 = 0 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        0 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 10 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 10 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow10_coefficients

private theorem divisionRow11_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  rw [show 11 = 1 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 1 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow11_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 11 = 1 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow11_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 11 = 1 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow11_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 11 = 1 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow11_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 11 = 1 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow11_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 11 = 1 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow11_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 11 = 1 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow11_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 95 := by
  rw [show 11 = 1 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 96 := by
  rw [show 11 = 1 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 97 := by
  rw [show 11 = 1 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 98 := by
  rw [show 11 = 1 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 99 := by
  rw [show 11 = 1 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 100 := by
  rw [show 11 = 1 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 101 := by
  rw [show 11 = 1 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 102 := by
  rw [show 11 = 1 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 103 := by
  rw [show 11 = 1 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 104 := by
  rw [show 11 = 1 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow11_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 105 := by
  rw [show 11 = 1 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 106 := by
  rw [show 11 = 1 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 107 := by
  rw [show 11 = 1 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 108 := by
  rw [show 11 = 1 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 109 := by
  rw [show 11 = 1 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 110 := by
  rw [show 11 = 1 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 111 := by
  rw [show 11 = 1 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 112 := by
  rw [show 11 = 1 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 113 := by
  rw [show 11 = 1 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 114 := by
  rw [show 11 = 1 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 115 := by
  rw [show 11 = 1 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 116 := by
  rw [show 11 = 1 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 117 := by
  rw [show 11 = 1 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 118 := by
  rw [show 11 = 1 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 119 := by
  rw [show 11 = 1 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 120 := by
  rw [show 11 = 1 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      1 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        11 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow11_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 11 j := by
  by_cases h15 : j < 15
  · exact divisionRow11_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow11_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow11_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow11_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow11_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow11_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow11_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow11_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow11_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow11_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow11_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow11_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow11_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow11_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow11_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow11_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow11_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow11_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow11_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow11_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow11_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow11_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow11_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow11_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow11_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow11_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow11_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow11_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow11_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow11_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow11_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow11_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow11_column120

private theorem divisionRow11_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 11 j =
      ((rectangularize 83 121 divisionReducedData).getD 11 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow11_windowCoefficients j hj

private theorem divisionRow11_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 11) =
      (rectangularize 83 121 divisionReducedData).getD 11 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 11
    ((rectangularize 83 121 divisionReducedData).getD 11 [])
  · rw [show 11 = 1 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        1 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 11 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 11 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow11_coefficients

private theorem divisionRow12_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  rw [show 12 = 2 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 2 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow12_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 12 = 2 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow12_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 12 = 2 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow12_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 12 = 2 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow12_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 12 = 2 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow12_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 12 = 2 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow12_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 12 = 2 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow12_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 95 := by
  rw [show 12 = 2 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 96 := by
  rw [show 12 = 2 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 97 := by
  rw [show 12 = 2 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 98 := by
  rw [show 12 = 2 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 99 := by
  rw [show 12 = 2 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 100 := by
  rw [show 12 = 2 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 101 := by
  rw [show 12 = 2 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 102 := by
  rw [show 12 = 2 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 103 := by
  rw [show 12 = 2 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 104 := by
  rw [show 12 = 2 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 105 := by
  rw [show 12 = 2 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 106 := by
  rw [show 12 = 2 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow12_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 107 := by
  rw [show 12 = 2 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 108 := by
  rw [show 12 = 2 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 109 := by
  rw [show 12 = 2 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 110 := by
  rw [show 12 = 2 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 111 := by
  rw [show 12 = 2 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 112 := by
  rw [show 12 = 2 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 113 := by
  rw [show 12 = 2 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 114 := by
  rw [show 12 = 2 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 115 := by
  rw [show 12 = 2 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 116 := by
  rw [show 12 = 2 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 117 := by
  rw [show 12 = 2 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 118 := by
  rw [show 12 = 2 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 119 := by
  rw [show 12 = 2 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 120 := by
  rw [show 12 = 2 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      2 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        12 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow12_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 12 j := by
  by_cases h15 : j < 15
  · exact divisionRow12_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow12_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow12_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow12_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow12_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow12_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow12_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow12_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow12_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow12_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow12_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow12_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow12_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow12_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow12_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow12_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow12_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow12_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow12_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow12_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow12_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow12_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow12_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow12_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow12_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow12_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow12_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow12_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow12_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow12_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow12_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow12_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow12_column120

private theorem divisionRow12_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 12 j =
      ((rectangularize 83 121 divisionReducedData).getD 12 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow12_windowCoefficients j hj

private theorem divisionRow12_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 12) =
      (rectangularize 83 121 divisionReducedData).getD 12 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 12
    ((rectangularize 83 121 divisionReducedData).getD 12 [])
  · rw [show 12 = 2 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        2 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 12 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 12 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow12_coefficients

private theorem divisionRow13_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  rw [show 13 = 3 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 3 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow13_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 13 = 3 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow13_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 13 = 3 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow13_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 13 = 3 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow13_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 13 = 3 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow13_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 13 = 3 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow13_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 13 = 3 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow13_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 95 := by
  rw [show 13 = 3 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 96 := by
  rw [show 13 = 3 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 97 := by
  rw [show 13 = 3 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 98 := by
  rw [show 13 = 3 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 99 := by
  rw [show 13 = 3 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 100 := by
  rw [show 13 = 3 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 101 := by
  rw [show 13 = 3 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 102 := by
  rw [show 13 = 3 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 103 := by
  rw [show 13 = 3 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 104 := by
  rw [show 13 = 3 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 105 := by
  rw [show 13 = 3 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 106 := by
  rw [show 13 = 3 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 107 := by
  rw [show 13 = 3 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 108 := by
  rw [show 13 = 3 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 109 := by
  rw [show 13 = 3 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow13_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 110 := by
  rw [show 13 = 3 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 111 := by
  rw [show 13 = 3 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 112 := by
  rw [show 13 = 3 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 113 := by
  rw [show 13 = 3 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 114 := by
  rw [show 13 = 3 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 115 := by
  rw [show 13 = 3 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 116 := by
  rw [show 13 = 3 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 117 := by
  rw [show 13 = 3 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 118 := by
  rw [show 13 = 3 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 119 := by
  rw [show 13 = 3 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 120 := by
  rw [show 13 = 3 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      3 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        13 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow13_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 13 j := by
  by_cases h15 : j < 15
  · exact divisionRow13_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow13_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow13_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow13_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow13_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow13_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow13_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow13_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow13_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow13_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow13_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow13_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow13_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow13_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow13_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow13_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow13_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow13_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow13_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow13_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow13_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow13_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow13_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow13_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow13_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow13_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow13_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow13_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow13_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow13_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow13_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow13_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow13_column120

private theorem divisionRow13_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 13 j =
      ((rectangularize 83 121 divisionReducedData).getD 13 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow13_windowCoefficients j hj

private theorem divisionRow13_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 13) =
      (rectangularize 83 121 divisionReducedData).getD 13 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 13
    ((rectangularize 83 121 divisionReducedData).getD 13 [])
  · rw [show 13 = 3 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        3 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 13 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 13 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow13_coefficients

private theorem divisionRow14_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  rw [show 14 = 4 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 4 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow14_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 14 = 4 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow14_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 14 = 4 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow14_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 14 = 4 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow14_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 14 = 4 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow14_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 14 = 4 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow14_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 14 = 4 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow14_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 95 := by
  rw [show 14 = 4 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 96 := by
  rw [show 14 = 4 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 97 := by
  rw [show 14 = 4 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 98 := by
  rw [show 14 = 4 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 99 := by
  rw [show 14 = 4 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 100 := by
  rw [show 14 = 4 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 101 := by
  rw [show 14 = 4 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 102 := by
  rw [show 14 = 4 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 103 := by
  rw [show 14 = 4 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 104 := by
  rw [show 14 = 4 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 105 := by
  rw [show 14 = 4 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 106 := by
  rw [show 14 = 4 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 107 := by
  rw [show 14 = 4 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 108 := by
  rw [show 14 = 4 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 109 := by
  rw [show 14 = 4 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 110 := by
  rw [show 14 = 4 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 111 := by
  rw [show 14 = 4 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow14_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 112 := by
  rw [show 14 = 4 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 113 := by
  rw [show 14 = 4 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 114 := by
  rw [show 14 = 4 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 115 := by
  rw [show 14 = 4 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 116 := by
  rw [show 14 = 4 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 117 := by
  rw [show 14 = 4 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 118 := by
  rw [show 14 = 4 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 119 := by
  rw [show 14 = 4 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 120 := by
  rw [show 14 = 4 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      4 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        14 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow14_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 14 j := by
  by_cases h15 : j < 15
  · exact divisionRow14_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow14_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow14_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow14_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow14_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow14_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow14_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow14_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow14_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow14_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow14_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow14_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow14_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow14_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow14_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow14_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow14_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow14_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow14_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow14_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow14_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow14_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow14_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow14_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow14_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow14_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow14_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow14_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow14_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow14_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow14_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow14_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow14_column120

private theorem divisionRow14_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 14 j =
      ((rectangularize 83 121 divisionReducedData).getD 14 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow14_windowCoefficients j hj

private theorem divisionRow14_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 14) =
      (rectangularize 83 121 divisionReducedData).getD 14 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 14
    ((rectangularize 83 121 divisionReducedData).getD 14 [])
  · rw [show 14 = 4 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        4 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 14 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 14 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow14_coefficients

private theorem divisionRow15_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  rw [show 15 = 5 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 5 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow15_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 15 = 5 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow15_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 15 = 5 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow15_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 15 = 5 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow15_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 15 = 5 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow15_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 15 = 5 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow15_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 15 = 5 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow15_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 95 := by
  rw [show 15 = 5 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 96 := by
  rw [show 15 = 5 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 97 := by
  rw [show 15 = 5 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 98 := by
  rw [show 15 = 5 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 99 := by
  rw [show 15 = 5 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 100 := by
  rw [show 15 = 5 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 101 := by
  rw [show 15 = 5 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 102 := by
  rw [show 15 = 5 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 103 := by
  rw [show 15 = 5 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 104 := by
  rw [show 15 = 5 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 105 := by
  rw [show 15 = 5 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 106 := by
  rw [show 15 = 5 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 107 := by
  rw [show 15 = 5 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 108 := by
  rw [show 15 = 5 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 109 := by
  rw [show 15 = 5 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 110 := by
  rw [show 15 = 5 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 111 := by
  rw [show 15 = 5 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 112 := by
  rw [show 15 = 5 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 113 := by
  rw [show 15 = 5 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow15_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 114 := by
  rw [show 15 = 5 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 115 := by
  rw [show 15 = 5 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 116 := by
  rw [show 15 = 5 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 117 := by
  rw [show 15 = 5 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 118 := by
  rw [show 15 = 5 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 119 := by
  rw [show 15 = 5 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 120 := by
  rw [show 15 = 5 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      5 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        15 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow15_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 15 j := by
  by_cases h15 : j < 15
  · exact divisionRow15_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow15_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow15_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow15_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow15_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow15_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow15_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow15_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow15_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow15_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow15_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow15_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow15_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow15_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow15_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow15_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow15_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow15_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow15_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow15_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow15_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow15_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow15_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow15_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow15_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow15_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow15_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow15_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow15_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow15_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow15_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow15_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow15_column120

private theorem divisionRow15_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 15 j =
      ((rectangularize 83 121 divisionReducedData).getD 15 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow15_windowCoefficients j hj

private theorem divisionRow15_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 15) =
      (rectangularize 83 121 divisionReducedData).getD 15 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 15
    ((rectangularize 83 121 divisionReducedData).getD 15 [])
  · rw [show 15 = 5 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        5 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 15 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 15 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow15_coefficients

private theorem divisionRow16_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  rw [show 16 = 6 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 6 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow16_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 16 = 6 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow16_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 16 = 6 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow16_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 16 = 6 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow16_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 16 = 6 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow16_columns75To89
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 90) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 16 = 6 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow16_columns90To94
    (j : ℕ) (hLower : 90 ≤ j) (hUpper : j < 95) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 16 = 6 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow16_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 95 := by
  rw [show 16 = 6 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 96 := by
  rw [show 16 = 6 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 97 := by
  rw [show 16 = 6 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 98 := by
  rw [show 16 = 6 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 99 := by
  rw [show 16 = 6 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 100 := by
  rw [show 16 = 6 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 101 := by
  rw [show 16 = 6 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 102 := by
  rw [show 16 = 6 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 103 := by
  rw [show 16 = 6 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 104 := by
  rw [show 16 = 6 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 105 := by
  rw [show 16 = 6 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 106 := by
  rw [show 16 = 6 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 107 := by
  rw [show 16 = 6 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 108 := by
  rw [show 16 = 6 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 109 := by
  rw [show 16 = 6 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 110 := by
  rw [show 16 = 6 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 111 := by
  rw [show 16 = 6 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 112 := by
  rw [show 16 = 6 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 113 := by
  rw [show 16 = 6 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 114 := by
  rw [show 16 = 6 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 115 := by
  rw [show 16 = 6 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  decide

private theorem divisionRow16_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 116 := by
  rw [show 16 = 6 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        16 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow16_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 117 := by
  rw [show 16 = 6 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        16 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow16_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 118 := by
  rw [show 16 = 6 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        16 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow16_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 119 := by
  rw [show 16 = 6 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        16 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow16_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 120 := by
  rw [show 16 = 6 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      6 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        16 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow16_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 16 j := by
  by_cases h15 : j < 15
  · exact divisionRow16_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow16_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow16_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow16_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow16_columns60To74 j (by omega) h75
  by_cases h90 : j < 90
  · exact divisionRow16_columns75To89 j (by omega) h90
  by_cases h95 : j < 95
  · exact divisionRow16_columns90To94 j (by omega) h95
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow16_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow16_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow16_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow16_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow16_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow16_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow16_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow16_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow16_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow16_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow16_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow16_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow16_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow16_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow16_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow16_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow16_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow16_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow16_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow16_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow16_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow16_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow16_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow16_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow16_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow16_column120

private theorem divisionRow16_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 16 j =
      ((rectangularize 83 121 divisionReducedData).getD 16 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow16_windowCoefficients j hj

private theorem divisionRow16_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 16) =
      (rectangularize 83 121 divisionReducedData).getD 16 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 16
    ((rectangularize 83 121 divisionReducedData).getD 16 [])
  · rw [show 16 = 6 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        6 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 16 []).length ≤ 121 := by
      decide
    rw [getD_rectangularize 83 121 divisionReducedData 16 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow16_coefficients

/-- The complete exact-division certificates for rows nine through sixteen. -/
theorem divisionRowsNineToSixteen_spec (n : ℕ)
    (hLower : 9 ≤ n) (hUpper : n < 17) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow9_spec
  · exact divisionRow10_spec
  · exact divisionRow11_spec
  · exact divisionRow12_spec
  · exact divisionRow13_spec
  · exact divisionRow14_spec
  · exact divisionRow15_spec
  · exact divisionRow16_spec

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
