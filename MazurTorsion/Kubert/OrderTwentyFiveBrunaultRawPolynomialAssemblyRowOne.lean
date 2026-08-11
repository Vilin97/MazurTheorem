/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSupport

/-!
# Row one of the raw numerator assembly certificate

This leaf checks one row of the rectangularized raw numerator identity.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomialRectangular

private theorem assemblyRow1_leftSupport :
    (assemblyData.getD 1 []).length ≤ 66 := by
  decide

private theorem assemblyRow1_rightSupport :
    (divisionReducedData.getD 1 []).length ≤ 66 := by
  decide

private theorem assemblyRow1_coefficients0To7
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 8) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients8To15
    (j : ℕ) (hLower : 8 ≤ j) (hUpper : j < 16) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients16To23
    (j : ℕ) (hLower : 16 ≤ j) (hUpper : j < 24) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients24To31
    (j : ℕ) (hLower : 24 ≤ j) (hUpper : j < 32) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients32To39
    (j : ℕ) (hLower : 32 ≤ j) (hUpper : j < 40) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients40To47
    (j : ℕ) (hLower : 40 ≤ j) (hUpper : j < 48) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients48To55
    (j : ℕ) (hLower : 48 ≤ j) (hUpper : j < 56) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients56To63
    (j : ℕ) (hLower : 56 ≤ j) (hUpper : j < 64) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients64To65
    (j : ℕ) (hLower : 64 ≤ j) (hUpper : j < 66) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  interval_cases j
  all_goals decide

private theorem assemblyRow1_coefficients (j : ℕ) (hj : j < 66) :
    (assemblyData.getD 1 []).getD j 0 =
      (divisionReducedData.getD 1 []).getD j 0 := by
  by_cases h0 : j < 8
  · exact assemblyRow1_coefficients0To7 j (by omega) h0
  by_cases h1 : j < 16
  · exact assemblyRow1_coefficients8To15 j (by omega) h1
  by_cases h2 : j < 24
  · exact assemblyRow1_coefficients16To23 j (by omega) h2
  by_cases h3 : j < 32
  · exact assemblyRow1_coefficients24To31 j (by omega) h3
  by_cases h4 : j < 40
  · exact assemblyRow1_coefficients32To39 j (by omega) h4
  by_cases h5 : j < 48
  · exact assemblyRow1_coefficients40To47 j (by omega) h5
  by_cases h6 : j < 56
  · exact assemblyRow1_coefficients48To55 j (by omega) h6
  by_cases h7 : j < 64
  · exact assemblyRow1_coefficients56To63 j (by omega) h7
  exact assemblyRow1_coefficients64To65 j (by omega) hj

theorem assemblyRow1 :
    (rectangularize 83 121 assemblyData).getD 1 [] =
      (rectangularize 83 121 divisionReducedData).getD 1 [] := by
  rw [getD_rectangularize 83 121 assemblyData 1 (by omega),
    getD_rectangularize 83 121 divisionReducedData 1 (by omega)]
  exact padOne_eq_of_bounded_coefficients 121 66
    (assemblyData.getD 1 []) (divisionReducedData.getD 1 [])
    assemblyRow1_leftSupport assemblyRow1_rightSupport (by omega)
    assemblyRow1_coefficients


end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

