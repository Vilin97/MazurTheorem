/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialWindow
import Mathlib.Tactic.IntervalCases

/-!
# Rows 73 through 82 of the raw order-twenty-five division certificate

Every finite coefficient is checked through bounded outer and inner windows.
Padded zero tails additionally split the outer scalar sum into kernel-checked halves.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate

private theorem divisionRow73_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  rw [show 73 = 63 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 63 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow73_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 73 = 63 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow73_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 73 = 63 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow73_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 73 = 63 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow73_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 73 = 63 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow73_columns75To81
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 82) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 73 = 63 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow73_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 82 := by
  rw [show 73 = 63 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 83 := by
  rw [show 73 = 63 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 84 := by
  rw [show 73 = 63 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 85 := by
  rw [show 73 = 63 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 86 := by
  rw [show 73 = 63 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 87 := by
  rw [show 73 = 63 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 88 := by
  rw [show 73 = 63 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 89 := by
  rw [show 73 = 63 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 90 := by
  rw [show 73 = 63 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 91 := by
  rw [show 73 = 63 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 92 := by
  rw [show 73 = 63 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 93 := by
  rw [show 73 = 63 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 94 := by
  rw [show 73 = 63 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 95 := by
  rw [show 73 = 63 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 96 := by
  rw [show 73 = 63 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 97 := by
  rw [show 73 = 63 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 98 := by
  rw [show 73 = 63 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 99 := by
  rw [show 73 = 63 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 100 := by
  rw [show 73 = 63 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 101 := by
  rw [show 73 = 63 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 102 := by
  rw [show 73 = 63 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 103 := by
  rw [show 73 = 63 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 104 := by
  rw [show 73 = 63 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 105 := by
  rw [show 73 = 63 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 106 := by
  rw [show 73 = 63 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 107 := by
  rw [show 73 = 63 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 108 := by
  rw [show 73 = 63 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 109 := by
  rw [show 73 = 63 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 110 := by
  rw [show 73 = 63 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 111 := by
  rw [show 73 = 63 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 112 := by
  rw [show 73 = 63 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 113 := by
  rw [show 73 = 63 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 114 := by
  rw [show 73 = 63 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 115 := by
  rw [show 73 = 63 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 116 := by
  rw [show 73 = 63 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 117 := by
  rw [show 73 = 63 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 118 := by
  rw [show 73 = 63 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 119 := by
  rw [show 73 = 63 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 120 := by
  rw [show 73 = 63 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      63 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        73 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow73_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 73 j := by
  by_cases h15 : j < 15
  · exact divisionRow73_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow73_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow73_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow73_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow73_columns60To74 j (by omega) h75
  by_cases h82 : j < 82
  · exact divisionRow73_columns75To81 j (by omega) h82
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow73_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow73_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow73_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow73_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow73_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow73_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow73_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow73_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow73_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow73_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow73_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow73_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow73_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow73_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow73_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow73_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow73_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow73_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow73_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow73_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow73_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow73_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow73_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow73_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow73_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow73_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow73_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow73_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow73_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow73_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow73_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow73_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow73_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow73_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow73_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow73_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow73_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow73_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow73_column120

private theorem divisionRow73_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 73 j =
      ((rectangularize 83 121 divisionReducedData).getD 73 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow73_windowCoefficients j hj

private theorem divisionRow73_targetSupport :
    (divisionReducedData.getD 73 []).length ≤ 121 := by
  rw [show 73 = 63 + 10 by omega,
    ← getD_drop_window divisionReducedData 63 10 []]
  change (ReducedDataHigh.getD 10 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 10 0 []]
  decide

private theorem divisionRow73_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 73) =
      (rectangularize 83 121 divisionReducedData).getD 73 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 73
    ((rectangularize 83 121 divisionReducedData).getD 73 [])
  · rw [show 73 = 63 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        63 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 73 []).length ≤ 121 := by
      exact divisionRow73_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 73 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow73_coefficients

private theorem divisionRow74_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  rw [show 74 = 64 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 64 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow74_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 74 = 64 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow74_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 74 = 64 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow74_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 74 = 64 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow74_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 74 = 64 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow74_columns75To79
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 80) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 74 = 64 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow74_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 80 := by
  rw [show 74 = 64 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 81 := by
  rw [show 74 = 64 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 82 := by
  rw [show 74 = 64 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 83 := by
  rw [show 74 = 64 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 84 := by
  rw [show 74 = 64 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 85 := by
  rw [show 74 = 64 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 86 := by
  rw [show 74 = 64 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 87 := by
  rw [show 74 = 64 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 88 := by
  rw [show 74 = 64 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 89 := by
  rw [show 74 = 64 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 90 := by
  rw [show 74 = 64 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 91 := by
  rw [show 74 = 64 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 92 := by
  rw [show 74 = 64 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 93 := by
  rw [show 74 = 64 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 94 := by
  rw [show 74 = 64 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 95 := by
  rw [show 74 = 64 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 96 := by
  rw [show 74 = 64 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 97 := by
  rw [show 74 = 64 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 98 := by
  rw [show 74 = 64 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 99 := by
  rw [show 74 = 64 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 100 := by
  rw [show 74 = 64 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 101 := by
  rw [show 74 = 64 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 102 := by
  rw [show 74 = 64 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 103 := by
  rw [show 74 = 64 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 104 := by
  rw [show 74 = 64 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 105 := by
  rw [show 74 = 64 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 106 := by
  rw [show 74 = 64 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 107 := by
  rw [show 74 = 64 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 108 := by
  rw [show 74 = 64 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 109 := by
  rw [show 74 = 64 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 110 := by
  rw [show 74 = 64 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 111 := by
  rw [show 74 = 64 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 112 := by
  rw [show 74 = 64 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 113 := by
  rw [show 74 = 64 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 114 := by
  rw [show 74 = 64 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 115 := by
  rw [show 74 = 64 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 116 := by
  rw [show 74 = 64 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 117 := by
  rw [show 74 = 64 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 118 := by
  rw [show 74 = 64 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 119 := by
  rw [show 74 = 64 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 120 := by
  rw [show 74 = 64 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      64 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        74 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow74_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 74 j := by
  by_cases h15 : j < 15
  · exact divisionRow74_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow74_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow74_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow74_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow74_columns60To74 j (by omega) h75
  by_cases h80 : j < 80
  · exact divisionRow74_columns75To79 j (by omega) h80
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow74_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow74_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow74_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow74_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow74_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow74_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow74_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow74_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow74_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow74_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow74_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow74_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow74_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow74_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow74_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow74_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow74_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow74_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow74_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow74_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow74_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow74_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow74_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow74_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow74_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow74_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow74_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow74_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow74_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow74_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow74_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow74_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow74_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow74_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow74_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow74_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow74_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow74_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow74_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow74_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow74_column120

private theorem divisionRow74_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 74 j =
      ((rectangularize 83 121 divisionReducedData).getD 74 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow74_windowCoefficients j hj

private theorem divisionRow74_targetSupport :
    (divisionReducedData.getD 74 []).length ≤ 121 := by
  rw [show 74 = 63 + 11 by omega,
    ← getD_drop_window divisionReducedData 63 11 []]
  change (ReducedDataHigh.getD 11 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 11 0 []]
  decide

private theorem divisionRow74_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 74) =
      (rectangularize 83 121 divisionReducedData).getD 74 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 74
    ((rectangularize 83 121 divisionReducedData).getD 74 [])
  · rw [show 74 = 64 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        64 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 74 []).length ≤ 121 := by
      exact divisionRow74_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 74 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow74_coefficients

private theorem divisionRow75_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  rw [show 75 = 65 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 65 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow75_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 75 = 65 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow75_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 75 = 65 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow75_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 75 = 65 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow75_columns60To74
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 75) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 75 = 65 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow75_columns75To75
    (j : ℕ) (hLower : 75 ≤ j) (hUpper : j < 76) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 75 = 65 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j
  decide

private theorem divisionRow75_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 76 := by
  rw [show 75 = 65 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 77 := by
  rw [show 75 = 65 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 78 := by
  rw [show 75 = 65 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 79 := by
  rw [show 75 = 65 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 80 := by
  rw [show 75 = 65 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 81 := by
  rw [show 75 = 65 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 82 := by
  rw [show 75 = 65 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 83 := by
  rw [show 75 = 65 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 84 := by
  rw [show 75 = 65 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 85 := by
  rw [show 75 = 65 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 86 := by
  rw [show 75 = 65 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 87 := by
  rw [show 75 = 65 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 88 := by
  rw [show 75 = 65 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 89 := by
  rw [show 75 = 65 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 90 := by
  rw [show 75 = 65 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 91 := by
  rw [show 75 = 65 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 92 := by
  rw [show 75 = 65 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 93 := by
  rw [show 75 = 65 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 94 := by
  rw [show 75 = 65 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 95 := by
  rw [show 75 = 65 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 96 := by
  rw [show 75 = 65 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 97 := by
  rw [show 75 = 65 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 98 := by
  rw [show 75 = 65 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 99 := by
  rw [show 75 = 65 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 100 := by
  rw [show 75 = 65 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 101 := by
  rw [show 75 = 65 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 102 := by
  rw [show 75 = 65 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 103 := by
  rw [show 75 = 65 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 104 := by
  rw [show 75 = 65 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 105 := by
  rw [show 75 = 65 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 106 := by
  rw [show 75 = 65 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 107 := by
  rw [show 75 = 65 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 108 := by
  rw [show 75 = 65 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 109 := by
  rw [show 75 = 65 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 110 := by
  rw [show 75 = 65 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 111 := by
  rw [show 75 = 65 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 112 := by
  rw [show 75 = 65 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 113 := by
  rw [show 75 = 65 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 114 := by
  rw [show 75 = 65 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 115 := by
  rw [show 75 = 65 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 116 := by
  rw [show 75 = 65 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 117 := by
  rw [show 75 = 65 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 118 := by
  rw [show 75 = 65 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 119 := by
  rw [show 75 = 65 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 120 := by
  rw [show 75 = 65 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      65 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        75 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow75_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 75 j := by
  by_cases h15 : j < 15
  · exact divisionRow75_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow75_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow75_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow75_columns45To59 j (by omega) h60
  by_cases h75 : j < 75
  · exact divisionRow75_columns60To74 j (by omega) h75
  by_cases h76 : j < 76
  · exact divisionRow75_columns75To75 j (by omega) h76
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow75_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow75_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow75_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow75_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow75_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow75_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow75_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow75_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow75_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow75_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow75_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow75_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow75_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow75_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow75_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow75_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow75_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow75_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow75_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow75_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow75_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow75_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow75_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow75_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow75_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow75_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow75_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow75_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow75_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow75_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow75_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow75_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow75_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow75_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow75_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow75_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow75_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow75_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow75_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow75_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow75_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow75_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow75_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow75_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow75_column120

private theorem divisionRow75_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 75 j =
      ((rectangularize 83 121 divisionReducedData).getD 75 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow75_windowCoefficients j hj

private theorem divisionRow75_targetSupport :
    (divisionReducedData.getD 75 []).length ≤ 121 := by
  rw [show 75 = 63 + 12 by omega,
    ← getD_drop_window divisionReducedData 63 12 []]
  change (ReducedDataHigh.getD 12 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 12 0 []]
  decide

private theorem divisionRow75_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 75) =
      (rectangularize 83 121 divisionReducedData).getD 75 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 75
    ((rectangularize 83 121 divisionReducedData).getD 75 [])
  · rw [show 75 = 65 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        65 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 75 []).length ≤ 121 := by
      exact divisionRow75_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 75 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow75_coefficients

private theorem divisionRow76_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 j := by
  rw [show 76 = 66 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 66 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow76_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 76 = 66 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow76_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 76 = 66 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow76_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 76 = 66 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow76_columns60To71
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 72) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 76 = 66 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow76_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 72 := by
  rw [show 76 = 66 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 73 := by
  rw [show 76 = 66 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 74 := by
  rw [show 76 = 66 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 75 := by
  rw [show 76 = 66 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 76 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (66 + 10) (61 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (66 + 10) (61 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 77 := by
  rw [show 76 = 66 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 78 := by
  rw [show 76 = 66 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 79 := by
  rw [show 76 = 66 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 80 := by
  rw [show 76 = 66 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 81 := by
  rw [show 76 = 66 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 82 := by
  rw [show 76 = 66 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 83 := by
  rw [show 76 = 66 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 84 := by
  rw [show 76 = 66 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 85 := by
  rw [show 76 = 66 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 86 := by
  rw [show 76 = 66 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 87 := by
  rw [show 76 = 66 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 88 := by
  rw [show 76 = 66 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 89 := by
  rw [show 76 = 66 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 90 := by
  rw [show 76 = 66 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 91 := by
  rw [show 76 = 66 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 92 := by
  rw [show 76 = 66 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 93 := by
  rw [show 76 = 66 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 94 := by
  rw [show 76 = 66 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 95 := by
  rw [show 76 = 66 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 96 := by
  rw [show 76 = 66 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 97 := by
  rw [show 76 = 66 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 98 := by
  rw [show 76 = 66 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 99 := by
  rw [show 76 = 66 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 100 := by
  rw [show 76 = 66 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 101 := by
  rw [show 76 = 66 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 102 := by
  rw [show 76 = 66 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 103 := by
  rw [show 76 = 66 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 104 := by
  rw [show 76 = 66 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 105 := by
  rw [show 76 = 66 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 106 := by
  rw [show 76 = 66 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 107 := by
  rw [show 76 = 66 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 108 := by
  rw [show 76 = 66 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 109 := by
  rw [show 76 = 66 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 110 := by
  rw [show 76 = 66 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 111 := by
  rw [show 76 = 66 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 112 := by
  rw [show 76 = 66 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 113 := by
  rw [show 76 = 66 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 114 := by
  rw [show 76 = 66 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 115 := by
  rw [show 76 = 66 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 116 := by
  rw [show 76 = 66 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 117 := by
  rw [show 76 = 66 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 118 := by
  rw [show 76 = 66 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 119 := by
  rw [show 76 = 66 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 120 := by
  rw [show 76 = 66 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      66 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        76 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow76_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 76 j := by
  by_cases h15 : j < 15
  · exact divisionRow76_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow76_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow76_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow76_columns45To59 j (by omega) h60
  by_cases h72 : j < 72
  · exact divisionRow76_columns60To71 j (by omega) h72
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow76_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow76_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow76_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow76_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow76_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow76_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow76_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow76_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow76_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow76_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow76_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow76_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow76_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow76_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow76_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow76_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow76_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow76_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow76_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow76_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow76_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow76_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow76_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow76_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow76_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow76_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow76_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow76_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow76_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow76_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow76_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow76_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow76_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow76_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow76_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow76_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow76_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow76_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow76_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow76_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow76_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow76_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow76_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow76_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow76_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow76_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow76_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow76_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow76_column120

private theorem divisionRow76_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 76 j =
      ((rectangularize 83 121 divisionReducedData).getD 76 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow76_windowCoefficients j hj

private theorem divisionRow76_targetSupport :
    (divisionReducedData.getD 76 []).length ≤ 121 := by
  rw [show 76 = 63 + 13 by omega,
    ← getD_drop_window divisionReducedData 63 13 []]
  change (ReducedDataHigh.getD 13 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 13 0 []]
  decide

private theorem divisionRow76_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 76) =
      (rectangularize 83 121 divisionReducedData).getD 76 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 76
    ((rectangularize 83 121 divisionReducedData).getD 76 [])
  · rw [show 76 = 66 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        66 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 76 []).length ≤ 121 := by
      exact divisionRow76_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 76 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow76_coefficients

private theorem divisionRow77_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 j := by
  rw [show 77 = 67 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 67 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow77_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 77 = 67 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow77_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 77 = 67 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow77_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 77 = 67 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow77_columns60To67
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 68) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 77 = 67 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow77_column68 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 68 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 68 := by
  rw [show 77 = 67 + 10 by omega, show 68 = 53 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 53 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 68 = 0 := by
    rw [show 68 = 53 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 53 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column69 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 69 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 69 := by
  rw [show 77 = 67 + 10 by omega, show 69 = 54 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 54 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 69 = 0 := by
    rw [show 69 = 54 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 54 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column70 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 70 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 70 := by
  rw [show 77 = 67 + 10 by omega, show 70 = 55 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 55 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 70 = 0 := by
    rw [show 70 = 55 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 55 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column71 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 71 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 71 := by
  rw [show 77 = 67 + 10 by omega, show 71 = 56 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 56 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 71 = 0 := by
    rw [show 71 = 56 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 56 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 72 := by
  rw [show 77 = 67 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 73 := by
  rw [show 77 = 67 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 74 := by
  rw [show 77 = 67 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 75 := by
  rw [show 77 = 67 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 76 := by
  rw [show 77 = 67 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 77 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (67 + 10) (62 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (67 + 10) (62 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 78 := by
  rw [show 77 = 67 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 79 := by
  rw [show 77 = 67 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 80 := by
  rw [show 77 = 67 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 81 := by
  rw [show 77 = 67 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 82 := by
  rw [show 77 = 67 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 83 := by
  rw [show 77 = 67 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 84 := by
  rw [show 77 = 67 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 85 := by
  rw [show 77 = 67 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 86 := by
  rw [show 77 = 67 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 87 := by
  rw [show 77 = 67 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 88 := by
  rw [show 77 = 67 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 89 := by
  rw [show 77 = 67 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 90 := by
  rw [show 77 = 67 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 91 := by
  rw [show 77 = 67 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 92 := by
  rw [show 77 = 67 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 93 := by
  rw [show 77 = 67 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 94 := by
  rw [show 77 = 67 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 95 := by
  rw [show 77 = 67 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 96 := by
  rw [show 77 = 67 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 97 := by
  rw [show 77 = 67 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 98 := by
  rw [show 77 = 67 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 99 := by
  rw [show 77 = 67 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 100 := by
  rw [show 77 = 67 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 101 := by
  rw [show 77 = 67 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 102 := by
  rw [show 77 = 67 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 103 := by
  rw [show 77 = 67 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 104 := by
  rw [show 77 = 67 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 105 := by
  rw [show 77 = 67 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 106 := by
  rw [show 77 = 67 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 107 := by
  rw [show 77 = 67 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 108 := by
  rw [show 77 = 67 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 109 := by
  rw [show 77 = 67 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 110 := by
  rw [show 77 = 67 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 111 := by
  rw [show 77 = 67 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 112 := by
  rw [show 77 = 67 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 113 := by
  rw [show 77 = 67 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 114 := by
  rw [show 77 = 67 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 115 := by
  rw [show 77 = 67 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 116 := by
  rw [show 77 = 67 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 117 := by
  rw [show 77 = 67 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 118 := by
  rw [show 77 = 67 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 119 := by
  rw [show 77 = 67 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 120 := by
  rw [show 77 = 67 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      67 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        77 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow77_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 77 j := by
  by_cases h15 : j < 15
  · exact divisionRow77_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow77_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow77_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow77_columns45To59 j (by omega) h60
  by_cases h68 : j < 68
  · exact divisionRow77_columns60To67 j (by omega) h68
  by_cases h69 : j < 69
  · have hj68 : j = 68 := by omega
    subst j
    exact divisionRow77_column68
  by_cases h70 : j < 70
  · have hj69 : j = 69 := by omega
    subst j
    exact divisionRow77_column69
  by_cases h71 : j < 71
  · have hj70 : j = 70 := by omega
    subst j
    exact divisionRow77_column70
  by_cases h72 : j < 72
  · have hj71 : j = 71 := by omega
    subst j
    exact divisionRow77_column71
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow77_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow77_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow77_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow77_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow77_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow77_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow77_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow77_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow77_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow77_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow77_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow77_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow77_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow77_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow77_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow77_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow77_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow77_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow77_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow77_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow77_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow77_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow77_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow77_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow77_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow77_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow77_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow77_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow77_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow77_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow77_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow77_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow77_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow77_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow77_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow77_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow77_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow77_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow77_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow77_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow77_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow77_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow77_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow77_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow77_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow77_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow77_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow77_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow77_column120

private theorem divisionRow77_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 77 j =
      ((rectangularize 83 121 divisionReducedData).getD 77 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow77_windowCoefficients j hj

private theorem divisionRow77_targetSupport :
    (divisionReducedData.getD 77 []).length ≤ 121 := by
  rw [show 77 = 63 + 14 by omega,
    ← getD_drop_window divisionReducedData 63 14 []]
  change (ReducedDataHigh.getD 14 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 14 0 []]
  decide

private theorem divisionRow77_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 77) =
      (rectangularize 83 121 divisionReducedData).getD 77 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 77
    ((rectangularize 83 121 divisionReducedData).getD 77 [])
  · rw [show 77 = 67 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        67 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 77 []).length ≤ 121 := by
      exact divisionRow77_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 77 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow77_coefficients

private theorem divisionRow78_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 j := by
  rw [show 78 = 68 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 68 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow78_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 78 = 68 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow78_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 78 = 68 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow78_columns45To59
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 60) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 78 = 68 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow78_columns60To63
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 64) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 78 = 68 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow78_column64 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 64 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 64 := by
  rw [show 78 = 68 + 10 by omega, show 64 = 49 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 49 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 64 = 0 := by
    rw [show 64 = 49 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 49 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column65 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 65 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 65 := by
  rw [show 78 = 68 + 10 by omega, show 65 = 50 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 50 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 65 = 0 := by
    rw [show 65 = 50 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 50 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column66 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 66 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 66 := by
  rw [show 78 = 68 + 10 by omega, show 66 = 51 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 51 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 66 = 0 := by
    rw [show 66 = 51 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 51 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column67 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 67 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 67 := by
  rw [show 78 = 68 + 10 by omega, show 67 = 52 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 52 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 67 = 0 := by
    rw [show 67 = 52 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 52 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column68 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 68 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 68 := by
  rw [show 78 = 68 + 10 by omega, show 68 = 53 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 53 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 68 = 0 := by
    rw [show 68 = 53 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 53 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column69 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 69 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 69 := by
  rw [show 78 = 68 + 10 by omega, show 69 = 54 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 54 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 69 = 0 := by
    rw [show 69 = 54 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 54 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column70 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 70 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 70 := by
  rw [show 78 = 68 + 10 by omega, show 70 = 55 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 55 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 70 = 0 := by
    rw [show 70 = 55 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 55 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column71 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 71 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 71 := by
  rw [show 78 = 68 + 10 by omega, show 71 = 56 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 56 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 71 = 0 := by
    rw [show 71 = 56 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 56 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 72 := by
  rw [show 78 = 68 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 73 := by
  rw [show 78 = 68 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 74 := by
  rw [show 78 = 68 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 75 := by
  rw [show 78 = 68 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 76 := by
  rw [show 78 = 68 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 77 := by
  rw [show 78 = 68 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 78 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (68 + 10) (63 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (68 + 10) (63 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 79 := by
  rw [show 78 = 68 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 80 := by
  rw [show 78 = 68 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 81 := by
  rw [show 78 = 68 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 82 := by
  rw [show 78 = 68 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 83 := by
  rw [show 78 = 68 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 84 := by
  rw [show 78 = 68 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 85 := by
  rw [show 78 = 68 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 86 := by
  rw [show 78 = 68 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 87 := by
  rw [show 78 = 68 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 88 := by
  rw [show 78 = 68 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 89 := by
  rw [show 78 = 68 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 90 := by
  rw [show 78 = 68 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 91 := by
  rw [show 78 = 68 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 92 := by
  rw [show 78 = 68 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 93 := by
  rw [show 78 = 68 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 94 := by
  rw [show 78 = 68 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 95 := by
  rw [show 78 = 68 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 96 := by
  rw [show 78 = 68 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 97 := by
  rw [show 78 = 68 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 98 := by
  rw [show 78 = 68 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 99 := by
  rw [show 78 = 68 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 100 := by
  rw [show 78 = 68 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 101 := by
  rw [show 78 = 68 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 102 := by
  rw [show 78 = 68 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 103 := by
  rw [show 78 = 68 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 104 := by
  rw [show 78 = 68 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 105 := by
  rw [show 78 = 68 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 106 := by
  rw [show 78 = 68 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 107 := by
  rw [show 78 = 68 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 108 := by
  rw [show 78 = 68 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 109 := by
  rw [show 78 = 68 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 110 := by
  rw [show 78 = 68 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 111 := by
  rw [show 78 = 68 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 112 := by
  rw [show 78 = 68 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 113 := by
  rw [show 78 = 68 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 114 := by
  rw [show 78 = 68 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 115 := by
  rw [show 78 = 68 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 116 := by
  rw [show 78 = 68 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 117 := by
  rw [show 78 = 68 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 118 := by
  rw [show 78 = 68 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 119 := by
  rw [show 78 = 68 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 120 := by
  rw [show 78 = 68 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      68 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        78 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow78_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 78 j := by
  by_cases h15 : j < 15
  · exact divisionRow78_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow78_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow78_columns30To44 j (by omega) h45
  by_cases h60 : j < 60
  · exact divisionRow78_columns45To59 j (by omega) h60
  by_cases h64 : j < 64
  · exact divisionRow78_columns60To63 j (by omega) h64
  by_cases h65 : j < 65
  · have hj64 : j = 64 := by omega
    subst j
    exact divisionRow78_column64
  by_cases h66 : j < 66
  · have hj65 : j = 65 := by omega
    subst j
    exact divisionRow78_column65
  by_cases h67 : j < 67
  · have hj66 : j = 66 := by omega
    subst j
    exact divisionRow78_column66
  by_cases h68 : j < 68
  · have hj67 : j = 67 := by omega
    subst j
    exact divisionRow78_column67
  by_cases h69 : j < 69
  · have hj68 : j = 68 := by omega
    subst j
    exact divisionRow78_column68
  by_cases h70 : j < 70
  · have hj69 : j = 69 := by omega
    subst j
    exact divisionRow78_column69
  by_cases h71 : j < 71
  · have hj70 : j = 70 := by omega
    subst j
    exact divisionRow78_column70
  by_cases h72 : j < 72
  · have hj71 : j = 71 := by omega
    subst j
    exact divisionRow78_column71
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow78_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow78_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow78_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow78_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow78_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow78_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow78_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow78_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow78_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow78_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow78_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow78_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow78_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow78_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow78_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow78_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow78_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow78_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow78_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow78_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow78_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow78_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow78_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow78_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow78_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow78_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow78_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow78_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow78_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow78_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow78_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow78_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow78_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow78_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow78_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow78_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow78_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow78_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow78_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow78_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow78_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow78_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow78_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow78_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow78_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow78_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow78_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow78_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow78_column120

private theorem divisionRow78_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 78 j =
      ((rectangularize 83 121 divisionReducedData).getD 78 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow78_windowCoefficients j hj

private theorem divisionRow78_targetSupport :
    (divisionReducedData.getD 78 []).length ≤ 121 := by
  rw [show 78 = 63 + 15 by omega,
    ← getD_drop_window divisionReducedData 63 15 []]
  change (ReducedDataHigh.getD 15 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 15 0 []]
  decide

private theorem divisionRow78_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 78) =
      (rectangularize 83 121 divisionReducedData).getD 78 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 78
    ((rectangularize 83 121 divisionReducedData).getD 78 [])
  · rw [show 78 = 68 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        68 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 78 []).length ≤ 121 := by
      exact divisionRow78_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 78 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow78_coefficients

private theorem divisionRow79_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 j := by
  rw [show 79 = 69 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 69 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow79_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 79 = 69 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow79_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 79 = 69 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow79_columns45To57
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 58) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 79 = 69 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow79_column58 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 58 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 58 := by
  rw [show 79 = 69 + 10 by omega, show 58 = 43 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 43 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 58 = 0 := by
    rw [show 58 = 43 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 43 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column59 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 59 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 59 := by
  rw [show 79 = 69 + 10 by omega, show 59 = 44 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 44 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 59 = 0 := by
    rw [show 59 = 44 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 44 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column60 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 60 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 60 := by
  rw [show 79 = 69 + 10 by omega, show 60 = 45 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 45 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 60 = 0 := by
    rw [show 60 = 45 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 45 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column61 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 61 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 61 := by
  rw [show 79 = 69 + 10 by omega, show 61 = 46 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 46 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 61 = 0 := by
    rw [show 61 = 46 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 46 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column62 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 62 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 62 := by
  rw [show 79 = 69 + 10 by omega, show 62 = 47 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 47 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 62 = 0 := by
    rw [show 62 = 47 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 47 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column63 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 63 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 63 := by
  rw [show 79 = 69 + 10 by omega, show 63 = 48 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 48 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 63 = 0 := by
    rw [show 63 = 48 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 48 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column64 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 64 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 64 := by
  rw [show 79 = 69 + 10 by omega, show 64 = 49 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 49 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 64 = 0 := by
    rw [show 64 = 49 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 49 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column65 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 65 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 65 := by
  rw [show 79 = 69 + 10 by omega, show 65 = 50 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 50 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 65 = 0 := by
    rw [show 65 = 50 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 50 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column66 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 66 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 66 := by
  rw [show 79 = 69 + 10 by omega, show 66 = 51 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 51 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 66 = 0 := by
    rw [show 66 = 51 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 51 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column67 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 67 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 67 := by
  rw [show 79 = 69 + 10 by omega, show 67 = 52 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 52 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 67 = 0 := by
    rw [show 67 = 52 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 52 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column68 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 68 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 68 := by
  rw [show 79 = 69 + 10 by omega, show 68 = 53 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 53 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 68 = 0 := by
    rw [show 68 = 53 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 53 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column69 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 69 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 69 := by
  rw [show 79 = 69 + 10 by omega, show 69 = 54 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 54 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 69 = 0 := by
    rw [show 69 = 54 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 54 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column70 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 70 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 70 := by
  rw [show 79 = 69 + 10 by omega, show 70 = 55 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 55 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 70 = 0 := by
    rw [show 70 = 55 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 55 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column71 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 71 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 71 := by
  rw [show 79 = 69 + 10 by omega, show 71 = 56 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 56 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 71 = 0 := by
    rw [show 71 = 56 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 56 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 72 := by
  rw [show 79 = 69 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 73 := by
  rw [show 79 = 69 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 74 := by
  rw [show 79 = 69 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 75 := by
  rw [show 79 = 69 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 76 := by
  rw [show 79 = 69 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 77 := by
  rw [show 79 = 69 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 78 := by
  rw [show 79 = 69 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 79 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (69 + 10) (64 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (69 + 10) (64 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 80 := by
  rw [show 79 = 69 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 81 := by
  rw [show 79 = 69 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 82 := by
  rw [show 79 = 69 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 83 := by
  rw [show 79 = 69 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 84 := by
  rw [show 79 = 69 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 85 := by
  rw [show 79 = 69 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 86 := by
  rw [show 79 = 69 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 87 := by
  rw [show 79 = 69 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 88 := by
  rw [show 79 = 69 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 89 := by
  rw [show 79 = 69 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 90 := by
  rw [show 79 = 69 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 91 := by
  rw [show 79 = 69 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 92 := by
  rw [show 79 = 69 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 93 := by
  rw [show 79 = 69 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 94 := by
  rw [show 79 = 69 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 95 := by
  rw [show 79 = 69 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 96 := by
  rw [show 79 = 69 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 97 := by
  rw [show 79 = 69 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 98 := by
  rw [show 79 = 69 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 99 := by
  rw [show 79 = 69 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 100 := by
  rw [show 79 = 69 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 101 := by
  rw [show 79 = 69 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 102 := by
  rw [show 79 = 69 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 103 := by
  rw [show 79 = 69 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 104 := by
  rw [show 79 = 69 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 105 := by
  rw [show 79 = 69 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 106 := by
  rw [show 79 = 69 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 107 := by
  rw [show 79 = 69 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 108 := by
  rw [show 79 = 69 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 109 := by
  rw [show 79 = 69 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 110 := by
  rw [show 79 = 69 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 111 := by
  rw [show 79 = 69 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 112 := by
  rw [show 79 = 69 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 113 := by
  rw [show 79 = 69 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 114 := by
  rw [show 79 = 69 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 115 := by
  rw [show 79 = 69 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 116 := by
  rw [show 79 = 69 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 117 := by
  rw [show 79 = 69 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 118 := by
  rw [show 79 = 69 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 119 := by
  rw [show 79 = 69 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 120 := by
  rw [show 79 = 69 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      69 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        79 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow79_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 79 j := by
  by_cases h15 : j < 15
  · exact divisionRow79_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow79_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow79_columns30To44 j (by omega) h45
  by_cases h58 : j < 58
  · exact divisionRow79_columns45To57 j (by omega) h58
  by_cases h59 : j < 59
  · have hj58 : j = 58 := by omega
    subst j
    exact divisionRow79_column58
  by_cases h60 : j < 60
  · have hj59 : j = 59 := by omega
    subst j
    exact divisionRow79_column59
  by_cases h61 : j < 61
  · have hj60 : j = 60 := by omega
    subst j
    exact divisionRow79_column60
  by_cases h62 : j < 62
  · have hj61 : j = 61 := by omega
    subst j
    exact divisionRow79_column61
  by_cases h63 : j < 63
  · have hj62 : j = 62 := by omega
    subst j
    exact divisionRow79_column62
  by_cases h64 : j < 64
  · have hj63 : j = 63 := by omega
    subst j
    exact divisionRow79_column63
  by_cases h65 : j < 65
  · have hj64 : j = 64 := by omega
    subst j
    exact divisionRow79_column64
  by_cases h66 : j < 66
  · have hj65 : j = 65 := by omega
    subst j
    exact divisionRow79_column65
  by_cases h67 : j < 67
  · have hj66 : j = 66 := by omega
    subst j
    exact divisionRow79_column66
  by_cases h68 : j < 68
  · have hj67 : j = 67 := by omega
    subst j
    exact divisionRow79_column67
  by_cases h69 : j < 69
  · have hj68 : j = 68 := by omega
    subst j
    exact divisionRow79_column68
  by_cases h70 : j < 70
  · have hj69 : j = 69 := by omega
    subst j
    exact divisionRow79_column69
  by_cases h71 : j < 71
  · have hj70 : j = 70 := by omega
    subst j
    exact divisionRow79_column70
  by_cases h72 : j < 72
  · have hj71 : j = 71 := by omega
    subst j
    exact divisionRow79_column71
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow79_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow79_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow79_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow79_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow79_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow79_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow79_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow79_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow79_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow79_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow79_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow79_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow79_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow79_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow79_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow79_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow79_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow79_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow79_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow79_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow79_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow79_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow79_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow79_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow79_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow79_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow79_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow79_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow79_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow79_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow79_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow79_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow79_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow79_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow79_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow79_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow79_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow79_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow79_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow79_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow79_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow79_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow79_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow79_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow79_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow79_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow79_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow79_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow79_column120

private theorem divisionRow79_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 79 j =
      ((rectangularize 83 121 divisionReducedData).getD 79 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow79_windowCoefficients j hj

private theorem divisionRow79_targetSupport :
    (divisionReducedData.getD 79 []).length ≤ 121 := by
  rw [show 79 = 63 + 16 by omega,
    ← getD_drop_window divisionReducedData 63 16 []]
  change (ReducedDataHigh.getD 16 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 16 0 []]
  decide

private theorem divisionRow79_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 79) =
      (rectangularize 83 121 divisionReducedData).getD 79 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 79
    ((rectangularize 83 121 divisionReducedData).getD 79 [])
  · rw [show 79 = 69 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        69 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 79 []).length ≤ 121 := by
      exact divisionRow79_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 79 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow79_coefficients

private theorem divisionRow80_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 j := by
  rw [show 80 = 70 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 70 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow80_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 80 = 70 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow80_columns30To44
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 45) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 80 = 70 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow80_columns45To51
    (j : ℕ) (hLower : 45 ≤ j) (hUpper : j < 52) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 80 = 70 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow80_column52 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 52 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 52 := by
  rw [show 80 = 70 + 10 by omega, show 52 = 37 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 37 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 52 = 0 := by
    rw [show 52 = 37 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 37 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column53 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 53 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 53 := by
  rw [show 80 = 70 + 10 by omega, show 53 = 38 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 38 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 53 = 0 := by
    rw [show 53 = 38 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 38 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column54 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 54 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 54 := by
  rw [show 80 = 70 + 10 by omega, show 54 = 39 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 39 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 54 = 0 := by
    rw [show 54 = 39 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 39 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column55 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 55 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 55 := by
  rw [show 80 = 70 + 10 by omega, show 55 = 40 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 40 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 55 = 0 := by
    rw [show 55 = 40 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 40 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column56 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 56 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 56 := by
  rw [show 80 = 70 + 10 by omega, show 56 = 41 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 41 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 56 = 0 := by
    rw [show 56 = 41 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 41 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column57 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 57 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 57 := by
  rw [show 80 = 70 + 10 by omega, show 57 = 42 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 42 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 57 = 0 := by
    rw [show 57 = 42 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 42 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column58 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 58 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 58 := by
  rw [show 80 = 70 + 10 by omega, show 58 = 43 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 43 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 58 = 0 := by
    rw [show 58 = 43 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 43 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column59 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 59 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 59 := by
  rw [show 80 = 70 + 10 by omega, show 59 = 44 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 44 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 59 = 0 := by
    rw [show 59 = 44 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 44 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column60 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 60 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 60 := by
  rw [show 80 = 70 + 10 by omega, show 60 = 45 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 45 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 60 = 0 := by
    rw [show 60 = 45 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 45 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column61 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 61 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 61 := by
  rw [show 80 = 70 + 10 by omega, show 61 = 46 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 46 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 61 = 0 := by
    rw [show 61 = 46 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 46 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column62 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 62 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 62 := by
  rw [show 80 = 70 + 10 by omega, show 62 = 47 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 47 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 62 = 0 := by
    rw [show 62 = 47 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 47 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column63 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 63 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 63 := by
  rw [show 80 = 70 + 10 by omega, show 63 = 48 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 48 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 63 = 0 := by
    rw [show 63 = 48 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 48 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column64 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 64 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 64 := by
  rw [show 80 = 70 + 10 by omega, show 64 = 49 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 49 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 64 = 0 := by
    rw [show 64 = 49 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 49 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column65 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 65 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 65 := by
  rw [show 80 = 70 + 10 by omega, show 65 = 50 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 50 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 65 = 0 := by
    rw [show 65 = 50 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 50 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column66 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 66 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 66 := by
  rw [show 80 = 70 + 10 by omega, show 66 = 51 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 51 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 66 = 0 := by
    rw [show 66 = 51 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 51 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column67 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 67 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 67 := by
  rw [show 80 = 70 + 10 by omega, show 67 = 52 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 52 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 67 = 0 := by
    rw [show 67 = 52 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 52 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column68 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 68 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 68 := by
  rw [show 80 = 70 + 10 by omega, show 68 = 53 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 53 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 68 = 0 := by
    rw [show 68 = 53 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 53 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column69 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 69 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 69 := by
  rw [show 80 = 70 + 10 by omega, show 69 = 54 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 54 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 69 = 0 := by
    rw [show 69 = 54 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 54 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column70 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 70 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 70 := by
  rw [show 80 = 70 + 10 by omega, show 70 = 55 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 55 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 70 = 0 := by
    rw [show 70 = 55 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 55 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column71 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 71 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 71 := by
  rw [show 80 = 70 + 10 by omega, show 71 = 56 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 56 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 71 = 0 := by
    rw [show 71 = 56 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 56 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 72 := by
  rw [show 80 = 70 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 73 := by
  rw [show 80 = 70 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 74 := by
  rw [show 80 = 70 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 75 := by
  rw [show 80 = 70 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 76 := by
  rw [show 80 = 70 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 77 := by
  rw [show 80 = 70 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 78 := by
  rw [show 80 = 70 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 79 := by
  rw [show 80 = 70 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 80 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (70 + 10) (65 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (70 + 10) (65 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 81 := by
  rw [show 80 = 70 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 82 := by
  rw [show 80 = 70 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 83 := by
  rw [show 80 = 70 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 84 := by
  rw [show 80 = 70 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 85 := by
  rw [show 80 = 70 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 86 := by
  rw [show 80 = 70 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 87 := by
  rw [show 80 = 70 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 88 := by
  rw [show 80 = 70 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 89 := by
  rw [show 80 = 70 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 90 := by
  rw [show 80 = 70 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 91 := by
  rw [show 80 = 70 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 92 := by
  rw [show 80 = 70 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 93 := by
  rw [show 80 = 70 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 94 := by
  rw [show 80 = 70 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 95 := by
  rw [show 80 = 70 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 96 := by
  rw [show 80 = 70 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 97 := by
  rw [show 80 = 70 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 98 := by
  rw [show 80 = 70 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 99 := by
  rw [show 80 = 70 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 100 := by
  rw [show 80 = 70 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 101 := by
  rw [show 80 = 70 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 102 := by
  rw [show 80 = 70 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 103 := by
  rw [show 80 = 70 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 104 := by
  rw [show 80 = 70 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 105 := by
  rw [show 80 = 70 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 106 := by
  rw [show 80 = 70 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 107 := by
  rw [show 80 = 70 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 108 := by
  rw [show 80 = 70 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 109 := by
  rw [show 80 = 70 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 110 := by
  rw [show 80 = 70 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 111 := by
  rw [show 80 = 70 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 112 := by
  rw [show 80 = 70 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 113 := by
  rw [show 80 = 70 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 114 := by
  rw [show 80 = 70 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 115 := by
  rw [show 80 = 70 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 116 := by
  rw [show 80 = 70 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 117 := by
  rw [show 80 = 70 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 118 := by
  rw [show 80 = 70 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 119 := by
  rw [show 80 = 70 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 120 := by
  rw [show 80 = 70 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      70 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        80 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow80_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 80 j := by
  by_cases h15 : j < 15
  · exact divisionRow80_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow80_columns15To29 j (by omega) h30
  by_cases h45 : j < 45
  · exact divisionRow80_columns30To44 j (by omega) h45
  by_cases h52 : j < 52
  · exact divisionRow80_columns45To51 j (by omega) h52
  by_cases h53 : j < 53
  · have hj52 : j = 52 := by omega
    subst j
    exact divisionRow80_column52
  by_cases h54 : j < 54
  · have hj53 : j = 53 := by omega
    subst j
    exact divisionRow80_column53
  by_cases h55 : j < 55
  · have hj54 : j = 54 := by omega
    subst j
    exact divisionRow80_column54
  by_cases h56 : j < 56
  · have hj55 : j = 55 := by omega
    subst j
    exact divisionRow80_column55
  by_cases h57 : j < 57
  · have hj56 : j = 56 := by omega
    subst j
    exact divisionRow80_column56
  by_cases h58 : j < 58
  · have hj57 : j = 57 := by omega
    subst j
    exact divisionRow80_column57
  by_cases h59 : j < 59
  · have hj58 : j = 58 := by omega
    subst j
    exact divisionRow80_column58
  by_cases h60 : j < 60
  · have hj59 : j = 59 := by omega
    subst j
    exact divisionRow80_column59
  by_cases h61 : j < 61
  · have hj60 : j = 60 := by omega
    subst j
    exact divisionRow80_column60
  by_cases h62 : j < 62
  · have hj61 : j = 61 := by omega
    subst j
    exact divisionRow80_column61
  by_cases h63 : j < 63
  · have hj62 : j = 62 := by omega
    subst j
    exact divisionRow80_column62
  by_cases h64 : j < 64
  · have hj63 : j = 63 := by omega
    subst j
    exact divisionRow80_column63
  by_cases h65 : j < 65
  · have hj64 : j = 64 := by omega
    subst j
    exact divisionRow80_column64
  by_cases h66 : j < 66
  · have hj65 : j = 65 := by omega
    subst j
    exact divisionRow80_column65
  by_cases h67 : j < 67
  · have hj66 : j = 66 := by omega
    subst j
    exact divisionRow80_column66
  by_cases h68 : j < 68
  · have hj67 : j = 67 := by omega
    subst j
    exact divisionRow80_column67
  by_cases h69 : j < 69
  · have hj68 : j = 68 := by omega
    subst j
    exact divisionRow80_column68
  by_cases h70 : j < 70
  · have hj69 : j = 69 := by omega
    subst j
    exact divisionRow80_column69
  by_cases h71 : j < 71
  · have hj70 : j = 70 := by omega
    subst j
    exact divisionRow80_column70
  by_cases h72 : j < 72
  · have hj71 : j = 71 := by omega
    subst j
    exact divisionRow80_column71
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow80_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow80_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow80_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow80_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow80_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow80_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow80_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow80_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow80_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow80_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow80_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow80_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow80_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow80_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow80_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow80_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow80_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow80_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow80_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow80_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow80_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow80_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow80_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow80_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow80_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow80_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow80_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow80_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow80_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow80_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow80_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow80_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow80_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow80_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow80_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow80_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow80_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow80_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow80_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow80_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow80_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow80_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow80_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow80_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow80_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow80_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow80_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow80_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow80_column120

private theorem divisionRow80_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 80 j =
      ((rectangularize 83 121 divisionReducedData).getD 80 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow80_windowCoefficients j hj

private theorem divisionRow80_targetSupport :
    (divisionReducedData.getD 80 []).length ≤ 121 := by
  rw [show 80 = 63 + 17 by omega,
    ← getD_drop_window divisionReducedData 63 17 []]
  change (ReducedDataHigh.getD 17 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 17 0 []]
  decide

private theorem divisionRow80_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 80) =
      (rectangularize 83 121 divisionReducedData).getD 80 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 80
    ((rectangularize 83 121 divisionReducedData).getD 80 [])
  · rw [show 80 = 70 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        70 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 80 []).length ≤ 121 := by
      exact divisionRow80_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 80 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow80_coefficients

private theorem divisionRow81_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 j := by
  rw [show 81 = 71 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 71 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow81_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 81 = 71 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow81_columns30To43
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 44) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 81 = 71 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow81_column44 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 44 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 44 := by
  rw [show 81 = 71 + 10 by omega, show 44 = 29 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 29 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 44 = 0 := by
    rw [show 44 = 29 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 29 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column45 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 45 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 45 := by
  rw [show 81 = 71 + 10 by omega, show 45 = 30 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 30 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 45 = 0 := by
    rw [show 45 = 30 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 30 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column46 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 46 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 46 := by
  rw [show 81 = 71 + 10 by omega, show 46 = 31 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 31 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 46 = 0 := by
    rw [show 46 = 31 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 31 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column47 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 47 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 47 := by
  rw [show 81 = 71 + 10 by omega, show 47 = 32 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 32 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 47 = 0 := by
    rw [show 47 = 32 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 32 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column48 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 48 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 48 := by
  rw [show 81 = 71 + 10 by omega, show 48 = 33 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 33 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 48 = 0 := by
    rw [show 48 = 33 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 33 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column49 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 49 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 49 := by
  rw [show 81 = 71 + 10 by omega, show 49 = 34 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 34 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 49 = 0 := by
    rw [show 49 = 34 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 34 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column50 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 50 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 50 := by
  rw [show 81 = 71 + 10 by omega, show 50 = 35 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 35 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 50 = 0 := by
    rw [show 50 = 35 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 35 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column51 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 51 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 51 := by
  rw [show 81 = 71 + 10 by omega, show 51 = 36 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 36 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 51 = 0 := by
    rw [show 51 = 36 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 36 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column52 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 52 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 52 := by
  rw [show 81 = 71 + 10 by omega, show 52 = 37 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 37 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 52 = 0 := by
    rw [show 52 = 37 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 37 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column53 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 53 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 53 := by
  rw [show 81 = 71 + 10 by omega, show 53 = 38 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 38 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 53 = 0 := by
    rw [show 53 = 38 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 38 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column54 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 54 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 54 := by
  rw [show 81 = 71 + 10 by omega, show 54 = 39 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 39 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 54 = 0 := by
    rw [show 54 = 39 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 39 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column55 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 55 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 55 := by
  rw [show 81 = 71 + 10 by omega, show 55 = 40 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 40 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 55 = 0 := by
    rw [show 55 = 40 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 40 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column56 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 56 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 56 := by
  rw [show 81 = 71 + 10 by omega, show 56 = 41 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 41 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 56 = 0 := by
    rw [show 56 = 41 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 41 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column57 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 57 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 57 := by
  rw [show 81 = 71 + 10 by omega, show 57 = 42 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 42 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 57 = 0 := by
    rw [show 57 = 42 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 42 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column58 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 58 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 58 := by
  rw [show 81 = 71 + 10 by omega, show 58 = 43 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 43 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 58 = 0 := by
    rw [show 58 = 43 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 43 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column59 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 59 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 59 := by
  rw [show 81 = 71 + 10 by omega, show 59 = 44 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 44 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 59 = 0 := by
    rw [show 59 = 44 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 44 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column60 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 60 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 60 := by
  rw [show 81 = 71 + 10 by omega, show 60 = 45 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 45 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 60 = 0 := by
    rw [show 60 = 45 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 45 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column61 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 61 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 61 := by
  rw [show 81 = 71 + 10 by omega, show 61 = 46 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 46 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 61 = 0 := by
    rw [show 61 = 46 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 46 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column62 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 62 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 62 := by
  rw [show 81 = 71 + 10 by omega, show 62 = 47 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 47 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 62 = 0 := by
    rw [show 62 = 47 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 47 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column63 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 63 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 63 := by
  rw [show 81 = 71 + 10 by omega, show 63 = 48 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 48 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 63 = 0 := by
    rw [show 63 = 48 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 48 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column64 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 64 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 64 := by
  rw [show 81 = 71 + 10 by omega, show 64 = 49 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 49 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 64 = 0 := by
    rw [show 64 = 49 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 49 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column65 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 65 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 65 := by
  rw [show 81 = 71 + 10 by omega, show 65 = 50 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 50 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 65 = 0 := by
    rw [show 65 = 50 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 50 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column66 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 66 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 66 := by
  rw [show 81 = 71 + 10 by omega, show 66 = 51 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 51 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 66 = 0 := by
    rw [show 66 = 51 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 51 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column67 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 67 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 67 := by
  rw [show 81 = 71 + 10 by omega, show 67 = 52 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 52 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 67 = 0 := by
    rw [show 67 = 52 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 52 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column68 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 68 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 68 := by
  rw [show 81 = 71 + 10 by omega, show 68 = 53 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 53 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 68 = 0 := by
    rw [show 68 = 53 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 53 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column69 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 69 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 69 := by
  rw [show 81 = 71 + 10 by omega, show 69 = 54 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 54 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 69 = 0 := by
    rw [show 69 = 54 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 54 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column70 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 70 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 70 := by
  rw [show 81 = 71 + 10 by omega, show 70 = 55 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 55 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 70 = 0 := by
    rw [show 70 = 55 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 55 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column71 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 71 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 71 := by
  rw [show 81 = 71 + 10 by omega, show 71 = 56 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 56 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 71 = 0 := by
    rw [show 71 = 56 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 56 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 72 := by
  rw [show 81 = 71 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 73 := by
  rw [show 81 = 71 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 74 := by
  rw [show 81 = 71 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 75 := by
  rw [show 81 = 71 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 76 := by
  rw [show 81 = 71 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 77 := by
  rw [show 81 = 71 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 78 := by
  rw [show 81 = 71 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 79 := by
  rw [show 81 = 71 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 80 := by
  rw [show 81 = 71 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 81 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (71 + 10) (66 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (71 + 10) (66 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 82 := by
  rw [show 81 = 71 + 10 by omega, show 82 = 67 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 83 := by
  rw [show 81 = 71 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 84 := by
  rw [show 81 = 71 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 85 := by
  rw [show 81 = 71 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 86 := by
  rw [show 81 = 71 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 87 := by
  rw [show 81 = 71 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 88 := by
  rw [show 81 = 71 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 89 := by
  rw [show 81 = 71 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 90 := by
  rw [show 81 = 71 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 91 := by
  rw [show 81 = 71 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 92 := by
  rw [show 81 = 71 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 93 := by
  rw [show 81 = 71 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 94 := by
  rw [show 81 = 71 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 95 := by
  rw [show 81 = 71 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 96 := by
  rw [show 81 = 71 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 97 := by
  rw [show 81 = 71 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 98 := by
  rw [show 81 = 71 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 99 := by
  rw [show 81 = 71 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 100 := by
  rw [show 81 = 71 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 101 := by
  rw [show 81 = 71 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 102 := by
  rw [show 81 = 71 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 103 := by
  rw [show 81 = 71 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 104 := by
  rw [show 81 = 71 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 105 := by
  rw [show 81 = 71 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 106 := by
  rw [show 81 = 71 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 107 := by
  rw [show 81 = 71 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 108 := by
  rw [show 81 = 71 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 109 := by
  rw [show 81 = 71 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 110 := by
  rw [show 81 = 71 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 111 := by
  rw [show 81 = 71 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 112 := by
  rw [show 81 = 71 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 113 := by
  rw [show 81 = 71 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 114 := by
  rw [show 81 = 71 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 115 := by
  rw [show 81 = 71 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 116 := by
  rw [show 81 = 71 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 117 := by
  rw [show 81 = 71 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 118 := by
  rw [show 81 = 71 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 119 := by
  rw [show 81 = 71 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 120 := by
  rw [show 81 = 71 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      71 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        81 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow81_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 81 j := by
  by_cases h15 : j < 15
  · exact divisionRow81_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow81_columns15To29 j (by omega) h30
  by_cases h44 : j < 44
  · exact divisionRow81_columns30To43 j (by omega) h44
  by_cases h45 : j < 45
  · have hj44 : j = 44 := by omega
    subst j
    exact divisionRow81_column44
  by_cases h46 : j < 46
  · have hj45 : j = 45 := by omega
    subst j
    exact divisionRow81_column45
  by_cases h47 : j < 47
  · have hj46 : j = 46 := by omega
    subst j
    exact divisionRow81_column46
  by_cases h48 : j < 48
  · have hj47 : j = 47 := by omega
    subst j
    exact divisionRow81_column47
  by_cases h49 : j < 49
  · have hj48 : j = 48 := by omega
    subst j
    exact divisionRow81_column48
  by_cases h50 : j < 50
  · have hj49 : j = 49 := by omega
    subst j
    exact divisionRow81_column49
  by_cases h51 : j < 51
  · have hj50 : j = 50 := by omega
    subst j
    exact divisionRow81_column50
  by_cases h52 : j < 52
  · have hj51 : j = 51 := by omega
    subst j
    exact divisionRow81_column51
  by_cases h53 : j < 53
  · have hj52 : j = 52 := by omega
    subst j
    exact divisionRow81_column52
  by_cases h54 : j < 54
  · have hj53 : j = 53 := by omega
    subst j
    exact divisionRow81_column53
  by_cases h55 : j < 55
  · have hj54 : j = 54 := by omega
    subst j
    exact divisionRow81_column54
  by_cases h56 : j < 56
  · have hj55 : j = 55 := by omega
    subst j
    exact divisionRow81_column55
  by_cases h57 : j < 57
  · have hj56 : j = 56 := by omega
    subst j
    exact divisionRow81_column56
  by_cases h58 : j < 58
  · have hj57 : j = 57 := by omega
    subst j
    exact divisionRow81_column57
  by_cases h59 : j < 59
  · have hj58 : j = 58 := by omega
    subst j
    exact divisionRow81_column58
  by_cases h60 : j < 60
  · have hj59 : j = 59 := by omega
    subst j
    exact divisionRow81_column59
  by_cases h61 : j < 61
  · have hj60 : j = 60 := by omega
    subst j
    exact divisionRow81_column60
  by_cases h62 : j < 62
  · have hj61 : j = 61 := by omega
    subst j
    exact divisionRow81_column61
  by_cases h63 : j < 63
  · have hj62 : j = 62 := by omega
    subst j
    exact divisionRow81_column62
  by_cases h64 : j < 64
  · have hj63 : j = 63 := by omega
    subst j
    exact divisionRow81_column63
  by_cases h65 : j < 65
  · have hj64 : j = 64 := by omega
    subst j
    exact divisionRow81_column64
  by_cases h66 : j < 66
  · have hj65 : j = 65 := by omega
    subst j
    exact divisionRow81_column65
  by_cases h67 : j < 67
  · have hj66 : j = 66 := by omega
    subst j
    exact divisionRow81_column66
  by_cases h68 : j < 68
  · have hj67 : j = 67 := by omega
    subst j
    exact divisionRow81_column67
  by_cases h69 : j < 69
  · have hj68 : j = 68 := by omega
    subst j
    exact divisionRow81_column68
  by_cases h70 : j < 70
  · have hj69 : j = 69 := by omega
    subst j
    exact divisionRow81_column69
  by_cases h71 : j < 71
  · have hj70 : j = 70 := by omega
    subst j
    exact divisionRow81_column70
  by_cases h72 : j < 72
  · have hj71 : j = 71 := by omega
    subst j
    exact divisionRow81_column71
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow81_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow81_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow81_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow81_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow81_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow81_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow81_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow81_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow81_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow81_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow81_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow81_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow81_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow81_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow81_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow81_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow81_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow81_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow81_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow81_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow81_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow81_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow81_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow81_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow81_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow81_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow81_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow81_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow81_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow81_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow81_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow81_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow81_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow81_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow81_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow81_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow81_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow81_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow81_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow81_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow81_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow81_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow81_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow81_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow81_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow81_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow81_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow81_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow81_column120

private theorem divisionRow81_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 81 j =
      ((rectangularize 83 121 divisionReducedData).getD 81 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow81_windowCoefficients j hj

private theorem divisionRow81_targetSupport :
    (divisionReducedData.getD 81 []).length ≤ 121 := by
  rw [show 81 = 63 + 18 by omega,
    ← getD_drop_window divisionReducedData 63 18 []]
  change (ReducedDataHigh.getD 18 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 18 0 []]
  decide

private theorem divisionRow81_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 81) =
      (rectangularize 83 121 divisionReducedData).getD 81 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 81
    ((rectangularize 83 121 divisionReducedData).getD 81 [])
  · rw [show 81 = 71 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        71 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 81 []).length ≤ 121 := by
      exact divisionRow81_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 81 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow81_coefficients

private theorem divisionRow82_columns0To14
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 15) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 j := by
  rw [show 82 = 72 + 10 by omega,
    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial
      divisionQuotientData 72 10 j
      (by rw [divisionSutherland_outerSupport])]
  interval_cases j <;> decide

private theorem divisionRow82_columns15To29
    (j : ℕ) (hLower : 15 ≤ j) (hUpper : j < 30) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 82 = 72 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow82_columns30To33
    (j : ℕ) (hLower : 30 ≤ j) (hUpper : j < 34) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 j := by
  have hSplit : j = (j - 15) + 15 := by omega
  rw [show 82 = 72 + 10 by omega, hSplit,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 (j - 15) 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  interval_cases j <;> decide

private theorem divisionRow82_column34 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 34 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 34 := by
  rw [show 82 = 72 + 10 by omega, show 34 = 19 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 19 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 34 = 0 := by
    rw [show 34 = 19 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 19 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column35 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 35 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 35 := by
  rw [show 82 = 72 + 10 by omega, show 35 = 20 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 20 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 35 = 0 := by
    rw [show 35 = 20 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 20 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column36 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 36 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 36 := by
  rw [show 82 = 72 + 10 by omega, show 36 = 21 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 21 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 36 = 0 := by
    rw [show 36 = 21 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 21 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column37 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 37 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 37 := by
  rw [show 82 = 72 + 10 by omega, show 37 = 22 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 22 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 37 = 0 := by
    rw [show 37 = 22 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 22 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column38 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 38 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 38 := by
  rw [show 82 = 72 + 10 by omega, show 38 = 23 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 23 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 38 = 0 := by
    rw [show 38 = 23 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 23 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column39 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 39 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 39 := by
  rw [show 82 = 72 + 10 by omega, show 39 = 24 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 24 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 39 = 0 := by
    rw [show 39 = 24 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 24 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column40 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 40 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 40 := by
  rw [show 82 = 72 + 10 by omega, show 40 = 25 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 25 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 40 = 0 := by
    rw [show 40 = 25 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 25 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column41 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 41 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 41 := by
  rw [show 82 = 72 + 10 by omega, show 41 = 26 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 26 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 41 = 0 := by
    rw [show 41 = 26 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 26 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column42 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 42 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 42 := by
  rw [show 82 = 72 + 10 by omega, show 42 = 27 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 27 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 42 = 0 := by
    rw [show 42 = 27 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 27 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column43 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 43 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 43 := by
  rw [show 82 = 72 + 10 by omega, show 43 = 28 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 28 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 43 = 0 := by
    rw [show 43 = 28 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 28 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column44 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 44 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 44 := by
  rw [show 82 = 72 + 10 by omega, show 44 = 29 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 29 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 44 = 0 := by
    rw [show 44 = 29 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 29 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column45 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 45 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 45 := by
  rw [show 82 = 72 + 10 by omega, show 45 = 30 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 30 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 45 = 0 := by
    rw [show 45 = 30 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 30 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column46 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 46 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 46 := by
  rw [show 82 = 72 + 10 by omega, show 46 = 31 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 31 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 46 = 0 := by
    rw [show 46 = 31 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 31 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column47 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 47 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 47 := by
  rw [show 82 = 72 + 10 by omega, show 47 = 32 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 32 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 47 = 0 := by
    rw [show 47 = 32 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 32 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column48 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 48 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 48 := by
  rw [show 82 = 72 + 10 by omega, show 48 = 33 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 33 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 48 = 0 := by
    rw [show 48 = 33 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 33 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column49 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 49 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 49 := by
  rw [show 82 = 72 + 10 by omega, show 49 = 34 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 34 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 49 = 0 := by
    rw [show 49 = 34 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 34 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column50 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 50 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 50 := by
  rw [show 82 = 72 + 10 by omega, show 50 = 35 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 35 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 50 = 0 := by
    rw [show 50 = 35 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 35 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column51 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 51 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 51 := by
  rw [show 82 = 72 + 10 by omega, show 51 = 36 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 36 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 51 = 0 := by
    rw [show 51 = 36 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 36 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column52 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 52 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 52 := by
  rw [show 82 = 72 + 10 by omega, show 52 = 37 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 37 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 52 = 0 := by
    rw [show 52 = 37 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 37 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column53 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 53 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 53 := by
  rw [show 82 = 72 + 10 by omega, show 53 = 38 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 38 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 53 = 0 := by
    rw [show 53 = 38 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 38 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column54 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 54 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 54 := by
  rw [show 82 = 72 + 10 by omega, show 54 = 39 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 39 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 54 = 0 := by
    rw [show 54 = 39 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 39 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column55 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 55 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 55 := by
  rw [show 82 = 72 + 10 by omega, show 55 = 40 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 40 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 55 = 0 := by
    rw [show 55 = 40 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 40 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column56 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 56 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 56 := by
  rw [show 82 = 72 + 10 by omega, show 56 = 41 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 41 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 56 = 0 := by
    rw [show 56 = 41 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 41 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column57 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 57 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 57 := by
  rw [show 82 = 72 + 10 by omega, show 57 = 42 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 42 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 57 = 0 := by
    rw [show 57 = 42 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 42 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column58 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 58 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 58 := by
  rw [show 82 = 72 + 10 by omega, show 58 = 43 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 43 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 58 = 0 := by
    rw [show 58 = 43 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 43 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column59 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 59 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 59 := by
  rw [show 82 = 72 + 10 by omega, show 59 = 44 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 44 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 59 = 0 := by
    rw [show 59 = 44 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 44 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column60 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 60 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 60 := by
  rw [show 82 = 72 + 10 by omega, show 60 = 45 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 45 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 60 = 0 := by
    rw [show 60 = 45 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 45 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column61 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 61 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 61 := by
  rw [show 82 = 72 + 10 by omega, show 61 = 46 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 46 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 61 = 0 := by
    rw [show 61 = 46 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 46 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column62 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 62 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 62 := by
  rw [show 82 = 72 + 10 by omega, show 62 = 47 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 47 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 62 = 0 := by
    rw [show 62 = 47 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 47 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column63 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 63 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 63 := by
  rw [show 82 = 72 + 10 by omega, show 63 = 48 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 48 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 63 = 0 := by
    rw [show 63 = 48 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 48 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column64 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 64 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 64 := by
  rw [show 82 = 72 + 10 by omega, show 64 = 49 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 49 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 64 = 0 := by
    rw [show 64 = 49 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 49 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column65 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 65 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 65 := by
  rw [show 82 = 72 + 10 by omega, show 65 = 50 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 50 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 65 = 0 := by
    rw [show 65 = 50 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 50 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column66 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 66 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 66 := by
  rw [show 82 = 72 + 10 by omega, show 66 = 51 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 51 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 66 = 0 := by
    rw [show 66 = 51 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 51 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column67 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 67 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 67 := by
  rw [show 82 = 72 + 10 by omega, show 67 = 52 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 52 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 67 = 0 := by
    rw [show 67 = 52 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 52 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column68 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 68 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 68 := by
  rw [show 82 = 72 + 10 by omega, show 68 = 53 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 53 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 68 = 0 := by
    rw [show 68 = 53 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 53 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column69 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 69 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 69 := by
  rw [show 82 = 72 + 10 by omega, show 69 = 54 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 54 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 69 = 0 := by
    rw [show 69 = 54 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 54 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column70 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 70 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 70 := by
  rw [show 82 = 72 + 10 by omega, show 70 = 55 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 55 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 70 = 0 := by
    rw [show 70 = 55 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 55 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column71 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 71 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 71 := by
  rw [show 82 = 72 + 10 by omega, show 71 = 56 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 56 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 71 = 0 := by
    rw [show 71 = 56 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 56 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column72 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 72 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 72 := by
  rw [show 82 = 72 + 10 by omega, show 72 = 57 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 57 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 72 = 0 := by
    rw [show 72 = 57 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 57 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column73 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 73 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 73 := by
  rw [show 82 = 72 + 10 by omega, show 73 = 58 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 58 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 73 = 0 := by
    rw [show 73 = 58 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 58 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column74 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 74 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 74 := by
  rw [show 82 = 72 + 10 by omega, show 74 = 59 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 59 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 74 = 0 := by
    rw [show 74 = 59 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 59 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column75 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 75 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 75 := by
  rw [show 82 = 72 + 10 by omega, show 75 = 60 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 60 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 75 = 0 := by
    rw [show 75 = 60 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 60 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column76 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 76 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 76 := by
  rw [show 82 = 72 + 10 by omega, show 76 = 61 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 61 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 76 = 0 := by
    rw [show 76 = 61 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 61 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column77 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 77 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 77 := by
  rw [show 82 = 72 + 10 by omega, show 77 = 62 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 62 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 77 = 0 := by
    rw [show 77 = 62 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 62 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column78 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 78 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 78 := by
  rw [show 82 = 72 + 10 by omega, show 78 = 63 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 63 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 78 = 0 := by
    rw [show 78 = 63 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 63 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column79 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 79 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 79 := by
  rw [show 82 = 72 + 10 by omega, show 79 = 64 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 64 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 79 = 0 := by
    rw [show 79 = 64 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 64 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column80 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 80 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 80 := by
  rw [show 82 = 72 + 10 by omega, show 80 = 65 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 65 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 80 = 0 := by
    rw [show 80 = 65 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 65 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column81 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 81 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 81 := by
  rw [show 82 = 72 + 10 by omega, show 81 = 66 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 66 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 81 = 0 := by
    rw [show 81 = 66 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 66 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column82 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 82 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 82 := by
  change
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData
        (72 + 10) (67 + 15) =
      windowCoeff (rectangularize 83 121 divisionReducedData)
        (72 + 10) (67 + 15)
  rw [mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 67 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 82 = 0 := by
    rw [show 82 = 67 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 67 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column83 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 83 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 83 := by
  rw [show 82 = 72 + 10 by omega, show 83 = 68 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 68 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 83 = 0 := by
    rw [show 83 = 68 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 68 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column84 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 84 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 84 := by
  rw [show 82 = 72 + 10 by omega, show 84 = 69 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 69 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 84 = 0 := by
    rw [show 84 = 69 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 69 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column85 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 85 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 85 := by
  rw [show 82 = 72 + 10 by omega, show 85 = 70 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 70 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 85 = 0 := by
    rw [show 85 = 70 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 70 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column86 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 86 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 86 := by
  rw [show 82 = 72 + 10 by omega, show 86 = 71 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 71 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 86 = 0 := by
    rw [show 86 = 71 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 71 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column87 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 87 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 87 := by
  rw [show 82 = 72 + 10 by omega, show 87 = 72 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 72 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 87 = 0 := by
    rw [show 87 = 72 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 72 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column88 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 88 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 88 := by
  rw [show 82 = 72 + 10 by omega, show 88 = 73 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 73 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 88 = 0 := by
    rw [show 88 = 73 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 73 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column89 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 89 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 89 := by
  rw [show 82 = 72 + 10 by omega, show 89 = 74 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 74 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 89 = 0 := by
    rw [show 89 = 74 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 74 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column90 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 90 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 90 := by
  rw [show 82 = 72 + 10 by omega, show 90 = 75 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 75 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 90 = 0 := by
    rw [show 90 = 75 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 75 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column91 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 91 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 91 := by
  rw [show 82 = 72 + 10 by omega, show 91 = 76 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 76 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 91 = 0 := by
    rw [show 91 = 76 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 76 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column92 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 92 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 92 := by
  rw [show 82 = 72 + 10 by omega, show 92 = 77 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 77 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 92 = 0 := by
    rw [show 92 = 77 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 77 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column93 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 93 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 93 := by
  rw [show 82 = 72 + 10 by omega, show 93 = 78 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 78 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 93 = 0 := by
    rw [show 93 = 78 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 78 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column94 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 94 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 94 := by
  rw [show 82 = 72 + 10 by omega, show 94 = 79 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 79 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 94 = 0 := by
    rw [show 94 = 79 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 79 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column95 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 95 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 95 := by
  rw [show 82 = 72 + 10 by omega, show 95 = 80 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 80 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 95 = 0 := by
    rw [show 95 = 80 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 80 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column96 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 96 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 96 := by
  rw [show 82 = 72 + 10 by omega, show 96 = 81 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 81 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 96 = 0 := by
    rw [show 96 = 81 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 81 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column97 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 97 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 97 := by
  rw [show 82 = 72 + 10 by omega, show 97 = 82 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 82 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 97 = 0 := by
    rw [show 97 = 82 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 82 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column98 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 98 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 98 := by
  rw [show 82 = 72 + 10 by omega, show 98 = 83 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 83 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 98 = 0 := by
    rw [show 98 = 83 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 83 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column99 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 99 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 99 := by
  rw [show 82 = 72 + 10 by omega, show 99 = 84 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 84 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 99 = 0 := by
    rw [show 99 = 84 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 84 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column100 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 100 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 100 := by
  rw [show 82 = 72 + 10 by omega, show 100 = 85 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 85 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 100 = 0 := by
    rw [show 100 = 85 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 85 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column101 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 101 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 101 := by
  rw [show 82 = 72 + 10 by omega, show 101 = 86 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 86 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 101 = 0 := by
    rw [show 101 = 86 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 86 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column102 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 102 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 102 := by
  rw [show 82 = 72 + 10 by omega, show 102 = 87 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 87 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 102 = 0 := by
    rw [show 102 = 87 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 87 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column103 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 103 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 103 := by
  rw [show 82 = 72 + 10 by omega, show 103 = 88 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 88 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 103 = 0 := by
    rw [show 103 = 88 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 88 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column104 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 104 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 104 := by
  rw [show 82 = 72 + 10 by omega, show 104 = 89 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 89 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 104 = 0 := by
    rw [show 104 = 89 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 89 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column105 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 105 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 105 := by
  rw [show 82 = 72 + 10 by omega, show 105 = 90 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 90 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 105 = 0 := by
    rw [show 105 = 90 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 90 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column106 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 106 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 106 := by
  rw [show 82 = 72 + 10 by omega, show 106 = 91 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 91 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 106 = 0 := by
    rw [show 106 = 91 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 91 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column107 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 107 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 107 := by
  rw [show 82 = 72 + 10 by omega, show 107 = 92 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 92 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 107 = 0 := by
    rw [show 107 = 92 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 92 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column108 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 108 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 108 := by
  rw [show 82 = 72 + 10 by omega, show 108 = 93 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 93 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 108 = 0 := by
    rw [show 108 = 93 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 93 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column109 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 109 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 109 := by
  rw [show 82 = 72 + 10 by omega, show 109 = 94 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 94 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 109 = 0 := by
    rw [show 109 = 94 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 94 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column110 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 110 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 110 := by
  rw [show 82 = 72 + 10 by omega, show 110 = 95 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 95 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 110 = 0 := by
    rw [show 110 = 95 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 95 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column111 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 111 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 111 := by
  rw [show 82 = 72 + 10 by omega, show 111 = 96 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 96 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 111 = 0 := by
    rw [show 111 = 96 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 96 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column112 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 112 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 112 := by
  rw [show 82 = 72 + 10 by omega, show 112 = 97 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 97 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 112 = 0 := by
    rw [show 112 = 97 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 97 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column113 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 113 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 113 := by
  rw [show 82 = 72 + 10 by omega, show 113 = 98 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 98 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 113 = 0 := by
    rw [show 113 = 98 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 98 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column114 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 114 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 114 := by
  rw [show 82 = 72 + 10 by omega, show 114 = 99 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 99 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 114 = 0 := by
    rw [show 114 = 99 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 99 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column115 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 115 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 115 := by
  rw [show 82 = 72 + 10 by omega, show 115 = 100 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 100 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 115 = 0 := by
    rw [show 115 = 100 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 100 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column116 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 116 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 116 := by
  rw [show 82 = 72 + 10 by omega, show 116 = 101 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 101 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 116 = 0 := by
    rw [show 116 = 101 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 101 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column117 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 117 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 117 := by
  rw [show 82 = 72 + 10 by omega, show 117 = 102 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 102 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 117 = 0 := by
    rw [show 117 = 102 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 102 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column118 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 118 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 118 := by
  rw [show 82 = 72 + 10 by omega, show 118 = 103 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 103 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 118 = 0 := by
    rw [show 118 = 103 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 103 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column119 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 119 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 119 := by
  rw [show 82 = 72 + 10 by omega, show 119 = 104 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 104 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 119 = 0 := by
    rw [show 119 = 104 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 104 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_column120 :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 120 =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 120 := by
  rw [show 82 = 72 + 10 by omega, show 120 = 105 + 15 by omega,
    mulCoeffTwo_window divisionSutherlandPolynomial divisionQuotientData
      72 10 105 15
      (by rw [divisionSutherland_outerSupport])
      divisionSutherland_innerSupport]
  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 (by decide) (by omega)]
  have hReduced :
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 120 = 0 := by
    rw [show 120 = 105 + 15 by omega,
      windowCoeff_rectangularize_window 83 121 divisionReducedData
        82 105 15 (by omega) (by omega)]
    decide
  rw [hReduced]
  decide

private theorem divisionRow82_windowCoefficients
    (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 j =
      windowCoeff (rectangularize 83 121 divisionReducedData) 82 j := by
  by_cases h15 : j < 15
  · exact divisionRow82_columns0To14 j (by omega) h15
  by_cases h30 : j < 30
  · exact divisionRow82_columns15To29 j (by omega) h30
  by_cases h34 : j < 34
  · exact divisionRow82_columns30To33 j (by omega) h34
  by_cases h35 : j < 35
  · have hj34 : j = 34 := by omega
    subst j
    exact divisionRow82_column34
  by_cases h36 : j < 36
  · have hj35 : j = 35 := by omega
    subst j
    exact divisionRow82_column35
  by_cases h37 : j < 37
  · have hj36 : j = 36 := by omega
    subst j
    exact divisionRow82_column36
  by_cases h38 : j < 38
  · have hj37 : j = 37 := by omega
    subst j
    exact divisionRow82_column37
  by_cases h39 : j < 39
  · have hj38 : j = 38 := by omega
    subst j
    exact divisionRow82_column38
  by_cases h40 : j < 40
  · have hj39 : j = 39 := by omega
    subst j
    exact divisionRow82_column39
  by_cases h41 : j < 41
  · have hj40 : j = 40 := by omega
    subst j
    exact divisionRow82_column40
  by_cases h42 : j < 42
  · have hj41 : j = 41 := by omega
    subst j
    exact divisionRow82_column41
  by_cases h43 : j < 43
  · have hj42 : j = 42 := by omega
    subst j
    exact divisionRow82_column42
  by_cases h44 : j < 44
  · have hj43 : j = 43 := by omega
    subst j
    exact divisionRow82_column43
  by_cases h45 : j < 45
  · have hj44 : j = 44 := by omega
    subst j
    exact divisionRow82_column44
  by_cases h46 : j < 46
  · have hj45 : j = 45 := by omega
    subst j
    exact divisionRow82_column45
  by_cases h47 : j < 47
  · have hj46 : j = 46 := by omega
    subst j
    exact divisionRow82_column46
  by_cases h48 : j < 48
  · have hj47 : j = 47 := by omega
    subst j
    exact divisionRow82_column47
  by_cases h49 : j < 49
  · have hj48 : j = 48 := by omega
    subst j
    exact divisionRow82_column48
  by_cases h50 : j < 50
  · have hj49 : j = 49 := by omega
    subst j
    exact divisionRow82_column49
  by_cases h51 : j < 51
  · have hj50 : j = 50 := by omega
    subst j
    exact divisionRow82_column50
  by_cases h52 : j < 52
  · have hj51 : j = 51 := by omega
    subst j
    exact divisionRow82_column51
  by_cases h53 : j < 53
  · have hj52 : j = 52 := by omega
    subst j
    exact divisionRow82_column52
  by_cases h54 : j < 54
  · have hj53 : j = 53 := by omega
    subst j
    exact divisionRow82_column53
  by_cases h55 : j < 55
  · have hj54 : j = 54 := by omega
    subst j
    exact divisionRow82_column54
  by_cases h56 : j < 56
  · have hj55 : j = 55 := by omega
    subst j
    exact divisionRow82_column55
  by_cases h57 : j < 57
  · have hj56 : j = 56 := by omega
    subst j
    exact divisionRow82_column56
  by_cases h58 : j < 58
  · have hj57 : j = 57 := by omega
    subst j
    exact divisionRow82_column57
  by_cases h59 : j < 59
  · have hj58 : j = 58 := by omega
    subst j
    exact divisionRow82_column58
  by_cases h60 : j < 60
  · have hj59 : j = 59 := by omega
    subst j
    exact divisionRow82_column59
  by_cases h61 : j < 61
  · have hj60 : j = 60 := by omega
    subst j
    exact divisionRow82_column60
  by_cases h62 : j < 62
  · have hj61 : j = 61 := by omega
    subst j
    exact divisionRow82_column61
  by_cases h63 : j < 63
  · have hj62 : j = 62 := by omega
    subst j
    exact divisionRow82_column62
  by_cases h64 : j < 64
  · have hj63 : j = 63 := by omega
    subst j
    exact divisionRow82_column63
  by_cases h65 : j < 65
  · have hj64 : j = 64 := by omega
    subst j
    exact divisionRow82_column64
  by_cases h66 : j < 66
  · have hj65 : j = 65 := by omega
    subst j
    exact divisionRow82_column65
  by_cases h67 : j < 67
  · have hj66 : j = 66 := by omega
    subst j
    exact divisionRow82_column66
  by_cases h68 : j < 68
  · have hj67 : j = 67 := by omega
    subst j
    exact divisionRow82_column67
  by_cases h69 : j < 69
  · have hj68 : j = 68 := by omega
    subst j
    exact divisionRow82_column68
  by_cases h70 : j < 70
  · have hj69 : j = 69 := by omega
    subst j
    exact divisionRow82_column69
  by_cases h71 : j < 71
  · have hj70 : j = 70 := by omega
    subst j
    exact divisionRow82_column70
  by_cases h72 : j < 72
  · have hj71 : j = 71 := by omega
    subst j
    exact divisionRow82_column71
  by_cases h73 : j < 73
  · have hj72 : j = 72 := by omega
    subst j
    exact divisionRow82_column72
  by_cases h74 : j < 74
  · have hj73 : j = 73 := by omega
    subst j
    exact divisionRow82_column73
  by_cases h75 : j < 75
  · have hj74 : j = 74 := by omega
    subst j
    exact divisionRow82_column74
  by_cases h76 : j < 76
  · have hj75 : j = 75 := by omega
    subst j
    exact divisionRow82_column75
  by_cases h77 : j < 77
  · have hj76 : j = 76 := by omega
    subst j
    exact divisionRow82_column76
  by_cases h78 : j < 78
  · have hj77 : j = 77 := by omega
    subst j
    exact divisionRow82_column77
  by_cases h79 : j < 79
  · have hj78 : j = 78 := by omega
    subst j
    exact divisionRow82_column78
  by_cases h80 : j < 80
  · have hj79 : j = 79 := by omega
    subst j
    exact divisionRow82_column79
  by_cases h81 : j < 81
  · have hj80 : j = 80 := by omega
    subst j
    exact divisionRow82_column80
  by_cases h82 : j < 82
  · have hj81 : j = 81 := by omega
    subst j
    exact divisionRow82_column81
  by_cases h83 : j < 83
  · have hj82 : j = 82 := by omega
    subst j
    exact divisionRow82_column82
  by_cases h84 : j < 84
  · have hj83 : j = 83 := by omega
    subst j
    exact divisionRow82_column83
  by_cases h85 : j < 85
  · have hj84 : j = 84 := by omega
    subst j
    exact divisionRow82_column84
  by_cases h86 : j < 86
  · have hj85 : j = 85 := by omega
    subst j
    exact divisionRow82_column85
  by_cases h87 : j < 87
  · have hj86 : j = 86 := by omega
    subst j
    exact divisionRow82_column86
  by_cases h88 : j < 88
  · have hj87 : j = 87 := by omega
    subst j
    exact divisionRow82_column87
  by_cases h89 : j < 89
  · have hj88 : j = 88 := by omega
    subst j
    exact divisionRow82_column88
  by_cases h90 : j < 90
  · have hj89 : j = 89 := by omega
    subst j
    exact divisionRow82_column89
  by_cases h91 : j < 91
  · have hj90 : j = 90 := by omega
    subst j
    exact divisionRow82_column90
  by_cases h92 : j < 92
  · have hj91 : j = 91 := by omega
    subst j
    exact divisionRow82_column91
  by_cases h93 : j < 93
  · have hj92 : j = 92 := by omega
    subst j
    exact divisionRow82_column92
  by_cases h94 : j < 94
  · have hj93 : j = 93 := by omega
    subst j
    exact divisionRow82_column93
  by_cases h95 : j < 95
  · have hj94 : j = 94 := by omega
    subst j
    exact divisionRow82_column94
  by_cases h96 : j < 96
  · have hj95 : j = 95 := by omega
    subst j
    exact divisionRow82_column95
  by_cases h97 : j < 97
  · have hj96 : j = 96 := by omega
    subst j
    exact divisionRow82_column96
  by_cases h98 : j < 98
  · have hj97 : j = 97 := by omega
    subst j
    exact divisionRow82_column97
  by_cases h99 : j < 99
  · have hj98 : j = 98 := by omega
    subst j
    exact divisionRow82_column98
  by_cases h100 : j < 100
  · have hj99 : j = 99 := by omega
    subst j
    exact divisionRow82_column99
  by_cases h101 : j < 101
  · have hj100 : j = 100 := by omega
    subst j
    exact divisionRow82_column100
  by_cases h102 : j < 102
  · have hj101 : j = 101 := by omega
    subst j
    exact divisionRow82_column101
  by_cases h103 : j < 103
  · have hj102 : j = 102 := by omega
    subst j
    exact divisionRow82_column102
  by_cases h104 : j < 104
  · have hj103 : j = 103 := by omega
    subst j
    exact divisionRow82_column103
  by_cases h105 : j < 105
  · have hj104 : j = 104 := by omega
    subst j
    exact divisionRow82_column104
  by_cases h106 : j < 106
  · have hj105 : j = 105 := by omega
    subst j
    exact divisionRow82_column105
  by_cases h107 : j < 107
  · have hj106 : j = 106 := by omega
    subst j
    exact divisionRow82_column106
  by_cases h108 : j < 108
  · have hj107 : j = 107 := by omega
    subst j
    exact divisionRow82_column107
  by_cases h109 : j < 109
  · have hj108 : j = 108 := by omega
    subst j
    exact divisionRow82_column108
  by_cases h110 : j < 110
  · have hj109 : j = 109 := by omega
    subst j
    exact divisionRow82_column109
  by_cases h111 : j < 111
  · have hj110 : j = 110 := by omega
    subst j
    exact divisionRow82_column110
  by_cases h112 : j < 112
  · have hj111 : j = 111 := by omega
    subst j
    exact divisionRow82_column111
  by_cases h113 : j < 113
  · have hj112 : j = 112 := by omega
    subst j
    exact divisionRow82_column112
  by_cases h114 : j < 114
  · have hj113 : j = 113 := by omega
    subst j
    exact divisionRow82_column113
  by_cases h115 : j < 115
  · have hj114 : j = 114 := by omega
    subst j
    exact divisionRow82_column114
  by_cases h116 : j < 116
  · have hj115 : j = 115 := by omega
    subst j
    exact divisionRow82_column115
  by_cases h117 : j < 117
  · have hj116 : j = 116 := by omega
    subst j
    exact divisionRow82_column116
  by_cases h118 : j < 118
  · have hj117 : j = 117 := by omega
    subst j
    exact divisionRow82_column117
  by_cases h119 : j < 119
  · have hj118 : j = 118 := by omega
    subst j
    exact divisionRow82_column118
  by_cases h120 : j < 120
  · have hj119 : j = 119 := by omega
    subst j
    exact divisionRow82_column119
  have hj120 : j = 120 := by omega
  subst j
  exact divisionRow82_column120

private theorem divisionRow82_coefficients (j : ℕ) (hj : j < 121) :
    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData 82 j =
      ((rectangularize 83 121 divisionReducedData).getD 82 []).getD j 0 := by
  rw [← windowCoeff_eq_getD]
  exact divisionRow82_windowCoefficients j hj

private theorem divisionRow82_targetSupport :
    (divisionReducedData.getD 82 []).length ≤ 121 := by
  rw [show 82 = 63 + 19 by omega,
    ← getD_drop_window divisionReducedData 63 19 []]
  change (ReducedDataHigh.getD 19 []).length ≤ 121
  rw [← getD_drop_window ReducedDataHigh 19 0 []]
  decide

private theorem divisionRow82_spec :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData 82) =
      (rectangularize 83 121 divisionReducedData).getD 82 [] := by
  apply padOne_mulRow_eq_of_coefficients 121 divisionSutherlandPolynomial
    divisionQuotientData 82
    ((rectangularize 83 121 divisionReducedData).getD 82 [])
  · rw [show 82 = 72 + 10 by omega,
      mulRow_drop_window divisionSutherlandPolynomial divisionQuotientData
        72 10 (by rw [divisionSutherland_outerSupport])]
    decide
  · have hTargetSupport :
        (divisionReducedData.getD 82 []).length ≤ 121 := by
      exact divisionRow82_targetSupport
    rw [getD_rectangularize 83 121 divisionReducedData 82 (by omega)]
    simp only [padOne, List.length_append, List.length_replicate]
    omega
  · exact divisionRow82_coefficients

/-- The complete exact-division certificates for rows 73 through 82. -/
theorem divisionRowsSeventyThreeToEightyTwo_spec (n : ℕ)
    (hLower : 73 ≤ n) (hUpper : n < 83) :
    padOne 121 (mulRow divisionSutherlandPolynomial divisionQuotientData n) =
      (rectangularize 83 121 divisionReducedData).getD n [] := by
  interval_cases n
  · exact divisionRow73_spec
  · exact divisionRow74_spec
  · exact divisionRow75_spec
  · exact divisionRow76_spec
  · exact divisionRow77_spec
  · exact divisionRow78_spec
  · exact divisionRow79_spec
  · exact divisionRow80_spec
  · exact divisionRow81_spec
  · exact divisionRow82_spec
end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
