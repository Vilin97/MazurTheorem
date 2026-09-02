/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSupport
import Mathlib.Tactic.IntervalCases

/-!
# Row 42 of the raw order-twenty-five numerator assembly

This leaf checks one complete structurally supported coefficient row against
the canonical reduced numerator.  Padding beyond that support is handled by
the shared bounded-coefficient lemma, without further computation.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular

private theorem assemblyRow42_leftSupport :
    (assemblyData.getD 42 []).length ≤ 121 := by
  decide

private theorem assemblyRow42_rightSupport :
    (divisionReducedData.getD 42 []).length ≤ 121 := by
  decide

private theorem assemblyRow42_coefficients0To3
    (j : ℕ) (hLower : 0 ≤ j) (hUpper : j < 4) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients4To7
    (j : ℕ) (hLower : 4 ≤ j) (hUpper : j < 8) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients8To11
    (j : ℕ) (hLower : 8 ≤ j) (hUpper : j < 12) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients12To15
    (j : ℕ) (hLower : 12 ≤ j) (hUpper : j < 16) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients16To19
    (j : ℕ) (hLower : 16 ≤ j) (hUpper : j < 20) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients20To23
    (j : ℕ) (hLower : 20 ≤ j) (hUpper : j < 24) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients24To27
    (j : ℕ) (hLower : 24 ≤ j) (hUpper : j < 28) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients28To31
    (j : ℕ) (hLower : 28 ≤ j) (hUpper : j < 32) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients32To35
    (j : ℕ) (hLower : 32 ≤ j) (hUpper : j < 36) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients36To39
    (j : ℕ) (hLower : 36 ≤ j) (hUpper : j < 40) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients40To43
    (j : ℕ) (hLower : 40 ≤ j) (hUpper : j < 44) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients44To47
    (j : ℕ) (hLower : 44 ≤ j) (hUpper : j < 48) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients48To51
    (j : ℕ) (hLower : 48 ≤ j) (hUpper : j < 52) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients52To55
    (j : ℕ) (hLower : 52 ≤ j) (hUpper : j < 56) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients56To59
    (j : ℕ) (hLower : 56 ≤ j) (hUpper : j < 60) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients60To63
    (j : ℕ) (hLower : 60 ≤ j) (hUpper : j < 64) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients64To67
    (j : ℕ) (hLower : 64 ≤ j) (hUpper : j < 68) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients68To71
    (j : ℕ) (hLower : 68 ≤ j) (hUpper : j < 72) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients72To75
    (j : ℕ) (hLower : 72 ≤ j) (hUpper : j < 76) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients76To79
    (j : ℕ) (hLower : 76 ≤ j) (hUpper : j < 80) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients80To83
    (j : ℕ) (hLower : 80 ≤ j) (hUpper : j < 84) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients84To87
    (j : ℕ) (hLower : 84 ≤ j) (hUpper : j < 88) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients88To91
    (j : ℕ) (hLower : 88 ≤ j) (hUpper : j < 92) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients92To95
    (j : ℕ) (hLower : 92 ≤ j) (hUpper : j < 96) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients96To99
    (j : ℕ) (hLower : 96 ≤ j) (hUpper : j < 100) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients100To103
    (j : ℕ) (hLower : 100 ≤ j) (hUpper : j < 104) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients104To107
    (j : ℕ) (hLower : 104 ≤ j) (hUpper : j < 108) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients108To111
    (j : ℕ) (hLower : 108 ≤ j) (hUpper : j < 112) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients112To115
    (j : ℕ) (hLower : 112 ≤ j) (hUpper : j < 116) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients116To119
    (j : ℕ) (hLower : 116 ≤ j) (hUpper : j < 120) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients120To120
    (j : ℕ) (hLower : 120 ≤ j) (hUpper : j < 121) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j <;> decide

private theorem assemblyRow42_coefficients (j : ℕ) (hj : j < 121) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  by_cases h4 : j < 4
  · exact assemblyRow42_coefficients0To3 j (by omega) h4
  by_cases h8 : j < 8
  · exact assemblyRow42_coefficients4To7 j (by omega) h8
  by_cases h12 : j < 12
  · exact assemblyRow42_coefficients8To11 j (by omega) h12
  by_cases h16 : j < 16
  · exact assemblyRow42_coefficients12To15 j (by omega) h16
  by_cases h20 : j < 20
  · exact assemblyRow42_coefficients16To19 j (by omega) h20
  by_cases h24 : j < 24
  · exact assemblyRow42_coefficients20To23 j (by omega) h24
  by_cases h28 : j < 28
  · exact assemblyRow42_coefficients24To27 j (by omega) h28
  by_cases h32 : j < 32
  · exact assemblyRow42_coefficients28To31 j (by omega) h32
  by_cases h36 : j < 36
  · exact assemblyRow42_coefficients32To35 j (by omega) h36
  by_cases h40 : j < 40
  · exact assemblyRow42_coefficients36To39 j (by omega) h40
  by_cases h44 : j < 44
  · exact assemblyRow42_coefficients40To43 j (by omega) h44
  by_cases h48 : j < 48
  · exact assemblyRow42_coefficients44To47 j (by omega) h48
  by_cases h52 : j < 52
  · exact assemblyRow42_coefficients48To51 j (by omega) h52
  by_cases h56 : j < 56
  · exact assemblyRow42_coefficients52To55 j (by omega) h56
  by_cases h60 : j < 60
  · exact assemblyRow42_coefficients56To59 j (by omega) h60
  by_cases h64 : j < 64
  · exact assemblyRow42_coefficients60To63 j (by omega) h64
  by_cases h68 : j < 68
  · exact assemblyRow42_coefficients64To67 j (by omega) h68
  by_cases h72 : j < 72
  · exact assemblyRow42_coefficients68To71 j (by omega) h72
  by_cases h76 : j < 76
  · exact assemblyRow42_coefficients72To75 j (by omega) h76
  by_cases h80 : j < 80
  · exact assemblyRow42_coefficients76To79 j (by omega) h80
  by_cases h84 : j < 84
  · exact assemblyRow42_coefficients80To83 j (by omega) h84
  by_cases h88 : j < 88
  · exact assemblyRow42_coefficients84To87 j (by omega) h88
  by_cases h92 : j < 92
  · exact assemblyRow42_coefficients88To91 j (by omega) h92
  by_cases h96 : j < 96
  · exact assemblyRow42_coefficients92To95 j (by omega) h96
  by_cases h100 : j < 100
  · exact assemblyRow42_coefficients96To99 j (by omega) h100
  by_cases h104 : j < 104
  · exact assemblyRow42_coefficients100To103 j (by omega) h104
  by_cases h108 : j < 108
  · exact assemblyRow42_coefficients104To107 j (by omega) h108
  by_cases h112 : j < 112
  · exact assemblyRow42_coefficients108To111 j (by omega) h112
  by_cases h116 : j < 116
  · exact assemblyRow42_coefficients112To115 j (by omega) h116
  by_cases h120 : j < 120
  · exact assemblyRow42_coefficients116To119 j (by omega) h120
  exact assemblyRow42_coefficients120To120 j (by omega) hj

/-- Complete checked equality for assembly row 42. -/
theorem assemblyRow42 :
    (rectangularize 83 121 assemblyData).getD 42 [] =
      (rectangularize 83 121 divisionReducedData).getD 42 [] := by
  rw [getD_rectangularize 83 121 assemblyData 42 (by omega),
    getD_rectangularize 83 121 divisionReducedData 42 (by omega)]
  exact padOne_eq_of_bounded_coefficients 121 121
    (assemblyData.getD 42 []) (divisionReducedData.getD 42 [])
    assemblyRow42_leftSupport assemblyRow42_rightSupport
    (by omega) assemblyRow42_coefficients

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
