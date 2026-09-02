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
the canonical reduced numerator.  Each scalar coefficient is isolated in its
own kernel check, and the shared support theorem handles the padded tail.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular

private theorem assemblyRow42_leftSupport :
    (assemblyData.getD 42 []).length ≤ 121 :=
  assemblyData_row_length_le 42

private theorem assemblyRow42_rightSupport :
    (divisionReducedData.getD 42 []).length ≤ 121 := by
  decide

private theorem assemblyRow42_coefficient0 :
    (assemblyData.getD 42 []).getD 0 0 =
      (divisionReducedData.getD 42 []).getD 0 0 := by
  decide

private theorem assemblyRow42_coefficient1 :
    (assemblyData.getD 42 []).getD 1 0 =
      (divisionReducedData.getD 42 []).getD 1 0 := by
  decide

private theorem assemblyRow42_coefficient2 :
    (assemblyData.getD 42 []).getD 2 0 =
      (divisionReducedData.getD 42 []).getD 2 0 := by
  decide

private theorem assemblyRow42_coefficient3 :
    (assemblyData.getD 42 []).getD 3 0 =
      (divisionReducedData.getD 42 []).getD 3 0 := by
  decide

private theorem assemblyRow42_coefficient4 :
    (assemblyData.getD 42 []).getD 4 0 =
      (divisionReducedData.getD 42 []).getD 4 0 := by
  decide

private theorem assemblyRow42_coefficient5 :
    (assemblyData.getD 42 []).getD 5 0 =
      (divisionReducedData.getD 42 []).getD 5 0 := by
  decide

private theorem assemblyRow42_coefficient6 :
    (assemblyData.getD 42 []).getD 6 0 =
      (divisionReducedData.getD 42 []).getD 6 0 := by
  decide

private theorem assemblyRow42_coefficient7 :
    (assemblyData.getD 42 []).getD 7 0 =
      (divisionReducedData.getD 42 []).getD 7 0 := by
  decide

private theorem assemblyRow42_coefficient8 :
    (assemblyData.getD 42 []).getD 8 0 =
      (divisionReducedData.getD 42 []).getD 8 0 := by
  decide

private theorem assemblyRow42_coefficient9 :
    (assemblyData.getD 42 []).getD 9 0 =
      (divisionReducedData.getD 42 []).getD 9 0 := by
  decide

private theorem assemblyRow42_coefficient10 :
    (assemblyData.getD 42 []).getD 10 0 =
      (divisionReducedData.getD 42 []).getD 10 0 := by
  decide

private theorem assemblyRow42_coefficient11 :
    (assemblyData.getD 42 []).getD 11 0 =
      (divisionReducedData.getD 42 []).getD 11 0 := by
  decide

private theorem assemblyRow42_coefficient12 :
    (assemblyData.getD 42 []).getD 12 0 =
      (divisionReducedData.getD 42 []).getD 12 0 := by
  decide

private theorem assemblyRow42_coefficient13 :
    (assemblyData.getD 42 []).getD 13 0 =
      (divisionReducedData.getD 42 []).getD 13 0 := by
  decide

private theorem assemblyRow42_coefficient14 :
    (assemblyData.getD 42 []).getD 14 0 =
      (divisionReducedData.getD 42 []).getD 14 0 := by
  decide

private theorem assemblyRow42_coefficient15 :
    (assemblyData.getD 42 []).getD 15 0 =
      (divisionReducedData.getD 42 []).getD 15 0 := by
  decide

private theorem assemblyRow42_coefficient16 :
    (assemblyData.getD 42 []).getD 16 0 =
      (divisionReducedData.getD 42 []).getD 16 0 := by
  decide

private theorem assemblyRow42_coefficient17 :
    (assemblyData.getD 42 []).getD 17 0 =
      (divisionReducedData.getD 42 []).getD 17 0 := by
  decide

private theorem assemblyRow42_coefficient18 :
    (assemblyData.getD 42 []).getD 18 0 =
      (divisionReducedData.getD 42 []).getD 18 0 := by
  decide

private theorem assemblyRow42_coefficient19 :
    (assemblyData.getD 42 []).getD 19 0 =
      (divisionReducedData.getD 42 []).getD 19 0 := by
  decide

private theorem assemblyRow42_coefficient20 :
    (assemblyData.getD 42 []).getD 20 0 =
      (divisionReducedData.getD 42 []).getD 20 0 := by
  decide

private theorem assemblyRow42_coefficient21 :
    (assemblyData.getD 42 []).getD 21 0 =
      (divisionReducedData.getD 42 []).getD 21 0 := by
  decide

private theorem assemblyRow42_coefficient22 :
    (assemblyData.getD 42 []).getD 22 0 =
      (divisionReducedData.getD 42 []).getD 22 0 := by
  decide

private theorem assemblyRow42_coefficient23 :
    (assemblyData.getD 42 []).getD 23 0 =
      (divisionReducedData.getD 42 []).getD 23 0 := by
  decide

private theorem assemblyRow42_coefficient24 :
    (assemblyData.getD 42 []).getD 24 0 =
      (divisionReducedData.getD 42 []).getD 24 0 := by
  decide

private theorem assemblyRow42_coefficient25 :
    (assemblyData.getD 42 []).getD 25 0 =
      (divisionReducedData.getD 42 []).getD 25 0 := by
  decide

private theorem assemblyRow42_coefficient26 :
    (assemblyData.getD 42 []).getD 26 0 =
      (divisionReducedData.getD 42 []).getD 26 0 := by
  decide

private theorem assemblyRow42_coefficient27 :
    (assemblyData.getD 42 []).getD 27 0 =
      (divisionReducedData.getD 42 []).getD 27 0 := by
  decide

private theorem assemblyRow42_coefficient28 :
    (assemblyData.getD 42 []).getD 28 0 =
      (divisionReducedData.getD 42 []).getD 28 0 := by
  decide

private theorem assemblyRow42_coefficient29 :
    (assemblyData.getD 42 []).getD 29 0 =
      (divisionReducedData.getD 42 []).getD 29 0 := by
  decide

private theorem assemblyRow42_coefficient30 :
    (assemblyData.getD 42 []).getD 30 0 =
      (divisionReducedData.getD 42 []).getD 30 0 := by
  decide

private theorem assemblyRow42_coefficient31 :
    (assemblyData.getD 42 []).getD 31 0 =
      (divisionReducedData.getD 42 []).getD 31 0 := by
  decide

private theorem assemblyRow42_coefficient32 :
    (assemblyData.getD 42 []).getD 32 0 =
      (divisionReducedData.getD 42 []).getD 32 0 := by
  decide

private theorem assemblyRow42_coefficient33 :
    (assemblyData.getD 42 []).getD 33 0 =
      (divisionReducedData.getD 42 []).getD 33 0 := by
  decide

private theorem assemblyRow42_coefficient34 :
    (assemblyData.getD 42 []).getD 34 0 =
      (divisionReducedData.getD 42 []).getD 34 0 := by
  decide

private theorem assemblyRow42_coefficient35 :
    (assemblyData.getD 42 []).getD 35 0 =
      (divisionReducedData.getD 42 []).getD 35 0 := by
  decide

private theorem assemblyRow42_coefficient36 :
    (assemblyData.getD 42 []).getD 36 0 =
      (divisionReducedData.getD 42 []).getD 36 0 := by
  decide

private theorem assemblyRow42_coefficient37 :
    (assemblyData.getD 42 []).getD 37 0 =
      (divisionReducedData.getD 42 []).getD 37 0 := by
  decide

private theorem assemblyRow42_coefficient38 :
    (assemblyData.getD 42 []).getD 38 0 =
      (divisionReducedData.getD 42 []).getD 38 0 := by
  decide

private theorem assemblyRow42_coefficient39 :
    (assemblyData.getD 42 []).getD 39 0 =
      (divisionReducedData.getD 42 []).getD 39 0 := by
  decide

private theorem assemblyRow42_coefficient40 :
    (assemblyData.getD 42 []).getD 40 0 =
      (divisionReducedData.getD 42 []).getD 40 0 := by
  decide

private theorem assemblyRow42_coefficient41 :
    (assemblyData.getD 42 []).getD 41 0 =
      (divisionReducedData.getD 42 []).getD 41 0 := by
  decide

private theorem assemblyRow42_coefficient42 :
    (assemblyData.getD 42 []).getD 42 0 =
      (divisionReducedData.getD 42 []).getD 42 0 := by
  decide

private theorem assemblyRow42_coefficient43 :
    (assemblyData.getD 42 []).getD 43 0 =
      (divisionReducedData.getD 42 []).getD 43 0 := by
  decide

private theorem assemblyRow42_coefficient44 :
    (assemblyData.getD 42 []).getD 44 0 =
      (divisionReducedData.getD 42 []).getD 44 0 := by
  decide

private theorem assemblyRow42_coefficient45 :
    (assemblyData.getD 42 []).getD 45 0 =
      (divisionReducedData.getD 42 []).getD 45 0 := by
  decide

private theorem assemblyRow42_coefficient46 :
    (assemblyData.getD 42 []).getD 46 0 =
      (divisionReducedData.getD 42 []).getD 46 0 := by
  decide

private theorem assemblyRow42_coefficient47 :
    (assemblyData.getD 42 []).getD 47 0 =
      (divisionReducedData.getD 42 []).getD 47 0 := by
  decide

private theorem assemblyRow42_coefficient48 :
    (assemblyData.getD 42 []).getD 48 0 =
      (divisionReducedData.getD 42 []).getD 48 0 := by
  decide

private theorem assemblyRow42_coefficient49 :
    (assemblyData.getD 42 []).getD 49 0 =
      (divisionReducedData.getD 42 []).getD 49 0 := by
  decide

private theorem assemblyRow42_coefficient50 :
    (assemblyData.getD 42 []).getD 50 0 =
      (divisionReducedData.getD 42 []).getD 50 0 := by
  decide

private theorem assemblyRow42_coefficient51 :
    (assemblyData.getD 42 []).getD 51 0 =
      (divisionReducedData.getD 42 []).getD 51 0 := by
  decide

private theorem assemblyRow42_coefficient52 :
    (assemblyData.getD 42 []).getD 52 0 =
      (divisionReducedData.getD 42 []).getD 52 0 := by
  decide

private theorem assemblyRow42_coefficient53 :
    (assemblyData.getD 42 []).getD 53 0 =
      (divisionReducedData.getD 42 []).getD 53 0 := by
  decide

private theorem assemblyRow42_coefficient54 :
    (assemblyData.getD 42 []).getD 54 0 =
      (divisionReducedData.getD 42 []).getD 54 0 := by
  decide

private theorem assemblyRow42_coefficient55 :
    (assemblyData.getD 42 []).getD 55 0 =
      (divisionReducedData.getD 42 []).getD 55 0 := by
  decide

private theorem assemblyRow42_coefficient56 :
    (assemblyData.getD 42 []).getD 56 0 =
      (divisionReducedData.getD 42 []).getD 56 0 := by
  decide

private theorem assemblyRow42_coefficient57 :
    (assemblyData.getD 42 []).getD 57 0 =
      (divisionReducedData.getD 42 []).getD 57 0 := by
  decide

private theorem assemblyRow42_coefficient58 :
    (assemblyData.getD 42 []).getD 58 0 =
      (divisionReducedData.getD 42 []).getD 58 0 := by
  decide

private theorem assemblyRow42_coefficient59 :
    (assemblyData.getD 42 []).getD 59 0 =
      (divisionReducedData.getD 42 []).getD 59 0 := by
  decide

private theorem assemblyRow42_coefficient60 :
    (assemblyData.getD 42 []).getD 60 0 =
      (divisionReducedData.getD 42 []).getD 60 0 := by
  decide

private theorem assemblyRow42_coefficient61 :
    (assemblyData.getD 42 []).getD 61 0 =
      (divisionReducedData.getD 42 []).getD 61 0 := by
  decide

private theorem assemblyRow42_coefficient62 :
    (assemblyData.getD 42 []).getD 62 0 =
      (divisionReducedData.getD 42 []).getD 62 0 := by
  decide

private theorem assemblyRow42_coefficient63 :
    (assemblyData.getD 42 []).getD 63 0 =
      (divisionReducedData.getD 42 []).getD 63 0 := by
  decide

private theorem assemblyRow42_coefficient64 :
    (assemblyData.getD 42 []).getD 64 0 =
      (divisionReducedData.getD 42 []).getD 64 0 := by
  decide

private theorem assemblyRow42_coefficient65 :
    (assemblyData.getD 42 []).getD 65 0 =
      (divisionReducedData.getD 42 []).getD 65 0 := by
  decide

private theorem assemblyRow42_coefficient66 :
    (assemblyData.getD 42 []).getD 66 0 =
      (divisionReducedData.getD 42 []).getD 66 0 := by
  decide

private theorem assemblyRow42_coefficient67 :
    (assemblyData.getD 42 []).getD 67 0 =
      (divisionReducedData.getD 42 []).getD 67 0 := by
  decide

private theorem assemblyRow42_coefficient68 :
    (assemblyData.getD 42 []).getD 68 0 =
      (divisionReducedData.getD 42 []).getD 68 0 := by
  decide

private theorem assemblyRow42_coefficient69 :
    (assemblyData.getD 42 []).getD 69 0 =
      (divisionReducedData.getD 42 []).getD 69 0 := by
  decide

private theorem assemblyRow42_coefficient70 :
    (assemblyData.getD 42 []).getD 70 0 =
      (divisionReducedData.getD 42 []).getD 70 0 := by
  decide

private theorem assemblyRow42_coefficient71 :
    (assemblyData.getD 42 []).getD 71 0 =
      (divisionReducedData.getD 42 []).getD 71 0 := by
  decide

private theorem assemblyRow42_coefficient72 :
    (assemblyData.getD 42 []).getD 72 0 =
      (divisionReducedData.getD 42 []).getD 72 0 := by
  decide

private theorem assemblyRow42_coefficient73 :
    (assemblyData.getD 42 []).getD 73 0 =
      (divisionReducedData.getD 42 []).getD 73 0 := by
  decide

private theorem assemblyRow42_coefficient74 :
    (assemblyData.getD 42 []).getD 74 0 =
      (divisionReducedData.getD 42 []).getD 74 0 := by
  decide

private theorem assemblyRow42_coefficient75 :
    (assemblyData.getD 42 []).getD 75 0 =
      (divisionReducedData.getD 42 []).getD 75 0 := by
  decide

private theorem assemblyRow42_coefficient76 :
    (assemblyData.getD 42 []).getD 76 0 =
      (divisionReducedData.getD 42 []).getD 76 0 := by
  decide

private theorem assemblyRow42_coefficient77 :
    (assemblyData.getD 42 []).getD 77 0 =
      (divisionReducedData.getD 42 []).getD 77 0 := by
  decide

private theorem assemblyRow42_coefficient78 :
    (assemblyData.getD 42 []).getD 78 0 =
      (divisionReducedData.getD 42 []).getD 78 0 := by
  decide

private theorem assemblyRow42_coefficient79 :
    (assemblyData.getD 42 []).getD 79 0 =
      (divisionReducedData.getD 42 []).getD 79 0 := by
  decide

private theorem assemblyRow42_coefficient80 :
    (assemblyData.getD 42 []).getD 80 0 =
      (divisionReducedData.getD 42 []).getD 80 0 := by
  decide

private theorem assemblyRow42_coefficient81 :
    (assemblyData.getD 42 []).getD 81 0 =
      (divisionReducedData.getD 42 []).getD 81 0 := by
  decide

private theorem assemblyRow42_coefficient82 :
    (assemblyData.getD 42 []).getD 82 0 =
      (divisionReducedData.getD 42 []).getD 82 0 := by
  decide

private theorem assemblyRow42_coefficient83 :
    (assemblyData.getD 42 []).getD 83 0 =
      (divisionReducedData.getD 42 []).getD 83 0 := by
  decide

private theorem assemblyRow42_coefficient84 :
    (assemblyData.getD 42 []).getD 84 0 =
      (divisionReducedData.getD 42 []).getD 84 0 := by
  decide

private theorem assemblyRow42_coefficient85 :
    (assemblyData.getD 42 []).getD 85 0 =
      (divisionReducedData.getD 42 []).getD 85 0 := by
  decide

private theorem assemblyRow42_coefficient86 :
    (assemblyData.getD 42 []).getD 86 0 =
      (divisionReducedData.getD 42 []).getD 86 0 := by
  decide

private theorem assemblyRow42_coefficient87 :
    (assemblyData.getD 42 []).getD 87 0 =
      (divisionReducedData.getD 42 []).getD 87 0 := by
  decide

private theorem assemblyRow42_coefficient88 :
    (assemblyData.getD 42 []).getD 88 0 =
      (divisionReducedData.getD 42 []).getD 88 0 := by
  decide

private theorem assemblyRow42_coefficient89 :
    (assemblyData.getD 42 []).getD 89 0 =
      (divisionReducedData.getD 42 []).getD 89 0 := by
  decide

private theorem assemblyRow42_coefficient90 :
    (assemblyData.getD 42 []).getD 90 0 =
      (divisionReducedData.getD 42 []).getD 90 0 := by
  decide

private theorem assemblyRow42_coefficient91 :
    (assemblyData.getD 42 []).getD 91 0 =
      (divisionReducedData.getD 42 []).getD 91 0 := by
  decide

private theorem assemblyRow42_coefficient92 :
    (assemblyData.getD 42 []).getD 92 0 =
      (divisionReducedData.getD 42 []).getD 92 0 := by
  decide

private theorem assemblyRow42_coefficient93 :
    (assemblyData.getD 42 []).getD 93 0 =
      (divisionReducedData.getD 42 []).getD 93 0 := by
  decide

private theorem assemblyRow42_coefficient94 :
    (assemblyData.getD 42 []).getD 94 0 =
      (divisionReducedData.getD 42 []).getD 94 0 := by
  decide

private theorem assemblyRow42_coefficient95 :
    (assemblyData.getD 42 []).getD 95 0 =
      (divisionReducedData.getD 42 []).getD 95 0 := by
  decide

private theorem assemblyRow42_coefficient96 :
    (assemblyData.getD 42 []).getD 96 0 =
      (divisionReducedData.getD 42 []).getD 96 0 := by
  decide

private theorem assemblyRow42_coefficient97 :
    (assemblyData.getD 42 []).getD 97 0 =
      (divisionReducedData.getD 42 []).getD 97 0 := by
  decide

private theorem assemblyRow42_coefficient98 :
    (assemblyData.getD 42 []).getD 98 0 =
      (divisionReducedData.getD 42 []).getD 98 0 := by
  decide

private theorem assemblyRow42_coefficient99 :
    (assemblyData.getD 42 []).getD 99 0 =
      (divisionReducedData.getD 42 []).getD 99 0 := by
  decide

private theorem assemblyRow42_coefficient100 :
    (assemblyData.getD 42 []).getD 100 0 =
      (divisionReducedData.getD 42 []).getD 100 0 := by
  decide

private theorem assemblyRow42_coefficient101 :
    (assemblyData.getD 42 []).getD 101 0 =
      (divisionReducedData.getD 42 []).getD 101 0 := by
  decide

private theorem assemblyRow42_coefficient102 :
    (assemblyData.getD 42 []).getD 102 0 =
      (divisionReducedData.getD 42 []).getD 102 0 := by
  decide

private theorem assemblyRow42_coefficient103 :
    (assemblyData.getD 42 []).getD 103 0 =
      (divisionReducedData.getD 42 []).getD 103 0 := by
  decide

private theorem assemblyRow42_coefficient104 :
    (assemblyData.getD 42 []).getD 104 0 =
      (divisionReducedData.getD 42 []).getD 104 0 := by
  decide

private theorem assemblyRow42_coefficient105 :
    (assemblyData.getD 42 []).getD 105 0 =
      (divisionReducedData.getD 42 []).getD 105 0 := by
  decide

private theorem assemblyRow42_coefficient106 :
    (assemblyData.getD 42 []).getD 106 0 =
      (divisionReducedData.getD 42 []).getD 106 0 := by
  decide

private theorem assemblyRow42_coefficient107 :
    (assemblyData.getD 42 []).getD 107 0 =
      (divisionReducedData.getD 42 []).getD 107 0 := by
  decide

private theorem assemblyRow42_coefficient108 :
    (assemblyData.getD 42 []).getD 108 0 =
      (divisionReducedData.getD 42 []).getD 108 0 := by
  decide

private theorem assemblyRow42_coefficient109 :
    (assemblyData.getD 42 []).getD 109 0 =
      (divisionReducedData.getD 42 []).getD 109 0 := by
  decide

private theorem assemblyRow42_coefficient110 :
    (assemblyData.getD 42 []).getD 110 0 =
      (divisionReducedData.getD 42 []).getD 110 0 := by
  decide

private theorem assemblyRow42_coefficient111 :
    (assemblyData.getD 42 []).getD 111 0 =
      (divisionReducedData.getD 42 []).getD 111 0 := by
  decide

private theorem assemblyRow42_coefficient112 :
    (assemblyData.getD 42 []).getD 112 0 =
      (divisionReducedData.getD 42 []).getD 112 0 := by
  decide

private theorem assemblyRow42_coefficient113 :
    (assemblyData.getD 42 []).getD 113 0 =
      (divisionReducedData.getD 42 []).getD 113 0 := by
  decide

private theorem assemblyRow42_coefficient114 :
    (assemblyData.getD 42 []).getD 114 0 =
      (divisionReducedData.getD 42 []).getD 114 0 := by
  decide

private theorem assemblyRow42_coefficient115 :
    (assemblyData.getD 42 []).getD 115 0 =
      (divisionReducedData.getD 42 []).getD 115 0 := by
  decide

private theorem assemblyRow42_coefficient116 :
    (assemblyData.getD 42 []).getD 116 0 =
      (divisionReducedData.getD 42 []).getD 116 0 := by
  decide

private theorem assemblyRow42_coefficient117 :
    (assemblyData.getD 42 []).getD 117 0 =
      (divisionReducedData.getD 42 []).getD 117 0 := by
  decide

private theorem assemblyRow42_coefficient118 :
    (assemblyData.getD 42 []).getD 118 0 =
      (divisionReducedData.getD 42 []).getD 118 0 := by
  decide

private theorem assemblyRow42_coefficient119 :
    (assemblyData.getD 42 []).getD 119 0 =
      (divisionReducedData.getD 42 []).getD 119 0 := by
  decide

private theorem assemblyRow42_coefficient120 :
    (assemblyData.getD 42 []).getD 120 0 =
      (divisionReducedData.getD 42 []).getD 120 0 := by
  decide

private theorem assemblyRow42_coefficients (j : ℕ) (hj : j < 121) :
    (assemblyData.getD 42 []).getD j 0 =
      (divisionReducedData.getD 42 []).getD j 0 := by
  interval_cases j
  · exact assemblyRow42_coefficient0
  · exact assemblyRow42_coefficient1
  · exact assemblyRow42_coefficient2
  · exact assemblyRow42_coefficient3
  · exact assemblyRow42_coefficient4
  · exact assemblyRow42_coefficient5
  · exact assemblyRow42_coefficient6
  · exact assemblyRow42_coefficient7
  · exact assemblyRow42_coefficient8
  · exact assemblyRow42_coefficient9
  · exact assemblyRow42_coefficient10
  · exact assemblyRow42_coefficient11
  · exact assemblyRow42_coefficient12
  · exact assemblyRow42_coefficient13
  · exact assemblyRow42_coefficient14
  · exact assemblyRow42_coefficient15
  · exact assemblyRow42_coefficient16
  · exact assemblyRow42_coefficient17
  · exact assemblyRow42_coefficient18
  · exact assemblyRow42_coefficient19
  · exact assemblyRow42_coefficient20
  · exact assemblyRow42_coefficient21
  · exact assemblyRow42_coefficient22
  · exact assemblyRow42_coefficient23
  · exact assemblyRow42_coefficient24
  · exact assemblyRow42_coefficient25
  · exact assemblyRow42_coefficient26
  · exact assemblyRow42_coefficient27
  · exact assemblyRow42_coefficient28
  · exact assemblyRow42_coefficient29
  · exact assemblyRow42_coefficient30
  · exact assemblyRow42_coefficient31
  · exact assemblyRow42_coefficient32
  · exact assemblyRow42_coefficient33
  · exact assemblyRow42_coefficient34
  · exact assemblyRow42_coefficient35
  · exact assemblyRow42_coefficient36
  · exact assemblyRow42_coefficient37
  · exact assemblyRow42_coefficient38
  · exact assemblyRow42_coefficient39
  · exact assemblyRow42_coefficient40
  · exact assemblyRow42_coefficient41
  · exact assemblyRow42_coefficient42
  · exact assemblyRow42_coefficient43
  · exact assemblyRow42_coefficient44
  · exact assemblyRow42_coefficient45
  · exact assemblyRow42_coefficient46
  · exact assemblyRow42_coefficient47
  · exact assemblyRow42_coefficient48
  · exact assemblyRow42_coefficient49
  · exact assemblyRow42_coefficient50
  · exact assemblyRow42_coefficient51
  · exact assemblyRow42_coefficient52
  · exact assemblyRow42_coefficient53
  · exact assemblyRow42_coefficient54
  · exact assemblyRow42_coefficient55
  · exact assemblyRow42_coefficient56
  · exact assemblyRow42_coefficient57
  · exact assemblyRow42_coefficient58
  · exact assemblyRow42_coefficient59
  · exact assemblyRow42_coefficient60
  · exact assemblyRow42_coefficient61
  · exact assemblyRow42_coefficient62
  · exact assemblyRow42_coefficient63
  · exact assemblyRow42_coefficient64
  · exact assemblyRow42_coefficient65
  · exact assemblyRow42_coefficient66
  · exact assemblyRow42_coefficient67
  · exact assemblyRow42_coefficient68
  · exact assemblyRow42_coefficient69
  · exact assemblyRow42_coefficient70
  · exact assemblyRow42_coefficient71
  · exact assemblyRow42_coefficient72
  · exact assemblyRow42_coefficient73
  · exact assemblyRow42_coefficient74
  · exact assemblyRow42_coefficient75
  · exact assemblyRow42_coefficient76
  · exact assemblyRow42_coefficient77
  · exact assemblyRow42_coefficient78
  · exact assemblyRow42_coefficient79
  · exact assemblyRow42_coefficient80
  · exact assemblyRow42_coefficient81
  · exact assemblyRow42_coefficient82
  · exact assemblyRow42_coefficient83
  · exact assemblyRow42_coefficient84
  · exact assemblyRow42_coefficient85
  · exact assemblyRow42_coefficient86
  · exact assemblyRow42_coefficient87
  · exact assemblyRow42_coefficient88
  · exact assemblyRow42_coefficient89
  · exact assemblyRow42_coefficient90
  · exact assemblyRow42_coefficient91
  · exact assemblyRow42_coefficient92
  · exact assemblyRow42_coefficient93
  · exact assemblyRow42_coefficient94
  · exact assemblyRow42_coefficient95
  · exact assemblyRow42_coefficient96
  · exact assemblyRow42_coefficient97
  · exact assemblyRow42_coefficient98
  · exact assemblyRow42_coefficient99
  · exact assemblyRow42_coefficient100
  · exact assemblyRow42_coefficient101
  · exact assemblyRow42_coefficient102
  · exact assemblyRow42_coefficient103
  · exact assemblyRow42_coefficient104
  · exact assemblyRow42_coefficient105
  · exact assemblyRow42_coefficient106
  · exact assemblyRow42_coefficient107
  · exact assemblyRow42_coefficient108
  · exact assemblyRow42_coefficient109
  · exact assemblyRow42_coefficient110
  · exact assemblyRow42_coefficient111
  · exact assemblyRow42_coefficient112
  · exact assemblyRow42_coefficient113
  · exact assemblyRow42_coefficient114
  · exact assemblyRow42_coefficient115
  · exact assemblyRow42_coefficient116
  · exact assemblyRow42_coefficient117
  · exact assemblyRow42_coefficient118
  · exact assemblyRow42_coefficient119
  · exact assemblyRow42_coefficient120

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
