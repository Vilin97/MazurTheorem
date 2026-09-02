/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSupport

/-!
# Row six of the raw numerator assembly certificate

This row has structural length 90 while the canonical reduced row has length
89.  The final supported coefficient is therefore the checked cancellation
of the assembly's explicit trailing-zero slot.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomialRectangular

private theorem assemblyRow6_leftSupport :
    (assemblyData.getD 6 []).length ≤ 121 := by
  exact assemblyData_row_length_le 6

private theorem assemblyRow6_rightSupport :
    (divisionReducedData.getD 6 []).length ≤ 121 := by
  decide

private theorem assemblyRow6_coefficient0 :
    (assemblyData.getD 6 []).getD 0 0 =
      (divisionReducedData.getD 6 []).getD 0 0 := by
  decide

private theorem assemblyRow6_coefficient1 :
    (assemblyData.getD 6 []).getD 1 0 =
      (divisionReducedData.getD 6 []).getD 1 0 := by
  decide

private theorem assemblyRow6_coefficient2 :
    (assemblyData.getD 6 []).getD 2 0 =
      (divisionReducedData.getD 6 []).getD 2 0 := by
  decide

private theorem assemblyRow6_coefficient3 :
    (assemblyData.getD 6 []).getD 3 0 =
      (divisionReducedData.getD 6 []).getD 3 0 := by
  decide

private theorem assemblyRow6_coefficient4 :
    (assemblyData.getD 6 []).getD 4 0 =
      (divisionReducedData.getD 6 []).getD 4 0 := by
  decide

private theorem assemblyRow6_coefficient5 :
    (assemblyData.getD 6 []).getD 5 0 =
      (divisionReducedData.getD 6 []).getD 5 0 := by
  decide

private theorem assemblyRow6_coefficient6 :
    (assemblyData.getD 6 []).getD 6 0 =
      (divisionReducedData.getD 6 []).getD 6 0 := by
  decide

private theorem assemblyRow6_coefficient7 :
    (assemblyData.getD 6 []).getD 7 0 =
      (divisionReducedData.getD 6 []).getD 7 0 := by
  decide

private theorem assemblyRow6_coefficient8 :
    (assemblyData.getD 6 []).getD 8 0 =
      (divisionReducedData.getD 6 []).getD 8 0 := by
  decide

private theorem assemblyRow6_coefficient9 :
    (assemblyData.getD 6 []).getD 9 0 =
      (divisionReducedData.getD 6 []).getD 9 0 := by
  decide

private theorem assemblyRow6_coefficient10 :
    (assemblyData.getD 6 []).getD 10 0 =
      (divisionReducedData.getD 6 []).getD 10 0 := by
  decide

private theorem assemblyRow6_coefficient11 :
    (assemblyData.getD 6 []).getD 11 0 =
      (divisionReducedData.getD 6 []).getD 11 0 := by
  decide

private theorem assemblyRow6_coefficient12 :
    (assemblyData.getD 6 []).getD 12 0 =
      (divisionReducedData.getD 6 []).getD 12 0 := by
  decide

private theorem assemblyRow6_coefficient13 :
    (assemblyData.getD 6 []).getD 13 0 =
      (divisionReducedData.getD 6 []).getD 13 0 := by
  decide

private theorem assemblyRow6_coefficient14 :
    (assemblyData.getD 6 []).getD 14 0 =
      (divisionReducedData.getD 6 []).getD 14 0 := by
  decide

private theorem assemblyRow6_coefficient15 :
    (assemblyData.getD 6 []).getD 15 0 =
      (divisionReducedData.getD 6 []).getD 15 0 := by
  decide

private theorem assemblyRow6_coefficient16 :
    (assemblyData.getD 6 []).getD 16 0 =
      (divisionReducedData.getD 6 []).getD 16 0 := by
  decide

private theorem assemblyRow6_coefficient17 :
    (assemblyData.getD 6 []).getD 17 0 =
      (divisionReducedData.getD 6 []).getD 17 0 := by
  decide

private theorem assemblyRow6_coefficient18 :
    (assemblyData.getD 6 []).getD 18 0 =
      (divisionReducedData.getD 6 []).getD 18 0 := by
  decide

private theorem assemblyRow6_coefficient19 :
    (assemblyData.getD 6 []).getD 19 0 =
      (divisionReducedData.getD 6 []).getD 19 0 := by
  decide

private theorem assemblyRow6_coefficient20 :
    (assemblyData.getD 6 []).getD 20 0 =
      (divisionReducedData.getD 6 []).getD 20 0 := by
  decide

private theorem assemblyRow6_coefficient21 :
    (assemblyData.getD 6 []).getD 21 0 =
      (divisionReducedData.getD 6 []).getD 21 0 := by
  decide

private theorem assemblyRow6_coefficient22 :
    (assemblyData.getD 6 []).getD 22 0 =
      (divisionReducedData.getD 6 []).getD 22 0 := by
  decide

private theorem assemblyRow6_coefficient23 :
    (assemblyData.getD 6 []).getD 23 0 =
      (divisionReducedData.getD 6 []).getD 23 0 := by
  decide

private theorem assemblyRow6_coefficient24 :
    (assemblyData.getD 6 []).getD 24 0 =
      (divisionReducedData.getD 6 []).getD 24 0 := by
  decide

private theorem assemblyRow6_coefficient25 :
    (assemblyData.getD 6 []).getD 25 0 =
      (divisionReducedData.getD 6 []).getD 25 0 := by
  decide

private theorem assemblyRow6_coefficient26 :
    (assemblyData.getD 6 []).getD 26 0 =
      (divisionReducedData.getD 6 []).getD 26 0 := by
  decide

private theorem assemblyRow6_coefficient27 :
    (assemblyData.getD 6 []).getD 27 0 =
      (divisionReducedData.getD 6 []).getD 27 0 := by
  decide

private theorem assemblyRow6_coefficient28 :
    (assemblyData.getD 6 []).getD 28 0 =
      (divisionReducedData.getD 6 []).getD 28 0 := by
  decide

private theorem assemblyRow6_coefficient29 :
    (assemblyData.getD 6 []).getD 29 0 =
      (divisionReducedData.getD 6 []).getD 29 0 := by
  decide

private theorem assemblyRow6_coefficient30 :
    (assemblyData.getD 6 []).getD 30 0 =
      (divisionReducedData.getD 6 []).getD 30 0 := by
  decide

private theorem assemblyRow6_coefficient31 :
    (assemblyData.getD 6 []).getD 31 0 =
      (divisionReducedData.getD 6 []).getD 31 0 := by
  decide

private theorem assemblyRow6_coefficient32 :
    (assemblyData.getD 6 []).getD 32 0 =
      (divisionReducedData.getD 6 []).getD 32 0 := by
  decide

private theorem assemblyRow6_coefficient33 :
    (assemblyData.getD 6 []).getD 33 0 =
      (divisionReducedData.getD 6 []).getD 33 0 := by
  decide

private theorem assemblyRow6_coefficient34 :
    (assemblyData.getD 6 []).getD 34 0 =
      (divisionReducedData.getD 6 []).getD 34 0 := by
  decide

private theorem assemblyRow6_coefficient35 :
    (assemblyData.getD 6 []).getD 35 0 =
      (divisionReducedData.getD 6 []).getD 35 0 := by
  decide

private theorem assemblyRow6_coefficient36 :
    (assemblyData.getD 6 []).getD 36 0 =
      (divisionReducedData.getD 6 []).getD 36 0 := by
  decide

private theorem assemblyRow6_coefficient37 :
    (assemblyData.getD 6 []).getD 37 0 =
      (divisionReducedData.getD 6 []).getD 37 0 := by
  decide

private theorem assemblyRow6_coefficient38 :
    (assemblyData.getD 6 []).getD 38 0 =
      (divisionReducedData.getD 6 []).getD 38 0 := by
  decide

private theorem assemblyRow6_coefficient39 :
    (assemblyData.getD 6 []).getD 39 0 =
      (divisionReducedData.getD 6 []).getD 39 0 := by
  decide

private theorem assemblyRow6_coefficient40 :
    (assemblyData.getD 6 []).getD 40 0 =
      (divisionReducedData.getD 6 []).getD 40 0 := by
  decide

private theorem assemblyRow6_coefficient41 :
    (assemblyData.getD 6 []).getD 41 0 =
      (divisionReducedData.getD 6 []).getD 41 0 := by
  decide

private theorem assemblyRow6_coefficient42 :
    (assemblyData.getD 6 []).getD 42 0 =
      (divisionReducedData.getD 6 []).getD 42 0 := by
  decide

private theorem assemblyRow6_coefficient43 :
    (assemblyData.getD 6 []).getD 43 0 =
      (divisionReducedData.getD 6 []).getD 43 0 := by
  decide

private theorem assemblyRow6_coefficient44 :
    (assemblyData.getD 6 []).getD 44 0 =
      (divisionReducedData.getD 6 []).getD 44 0 := by
  decide

private theorem assemblyRow6_coefficient45 :
    (assemblyData.getD 6 []).getD 45 0 =
      (divisionReducedData.getD 6 []).getD 45 0 := by
  decide

private theorem assemblyRow6_coefficient46 :
    (assemblyData.getD 6 []).getD 46 0 =
      (divisionReducedData.getD 6 []).getD 46 0 := by
  decide

private theorem assemblyRow6_coefficient47 :
    (assemblyData.getD 6 []).getD 47 0 =
      (divisionReducedData.getD 6 []).getD 47 0 := by
  decide

private theorem assemblyRow6_coefficient48 :
    (assemblyData.getD 6 []).getD 48 0 =
      (divisionReducedData.getD 6 []).getD 48 0 := by
  decide

private theorem assemblyRow6_coefficient49 :
    (assemblyData.getD 6 []).getD 49 0 =
      (divisionReducedData.getD 6 []).getD 49 0 := by
  decide

private theorem assemblyRow6_coefficient50 :
    (assemblyData.getD 6 []).getD 50 0 =
      (divisionReducedData.getD 6 []).getD 50 0 := by
  decide

private theorem assemblyRow6_coefficient51 :
    (assemblyData.getD 6 []).getD 51 0 =
      (divisionReducedData.getD 6 []).getD 51 0 := by
  decide

private theorem assemblyRow6_coefficient52 :
    (assemblyData.getD 6 []).getD 52 0 =
      (divisionReducedData.getD 6 []).getD 52 0 := by
  decide

private theorem assemblyRow6_coefficient53 :
    (assemblyData.getD 6 []).getD 53 0 =
      (divisionReducedData.getD 6 []).getD 53 0 := by
  decide

private theorem assemblyRow6_coefficient54 :
    (assemblyData.getD 6 []).getD 54 0 =
      (divisionReducedData.getD 6 []).getD 54 0 := by
  decide

private theorem assemblyRow6_coefficient55 :
    (assemblyData.getD 6 []).getD 55 0 =
      (divisionReducedData.getD 6 []).getD 55 0 := by
  decide

private theorem assemblyRow6_coefficient56 :
    (assemblyData.getD 6 []).getD 56 0 =
      (divisionReducedData.getD 6 []).getD 56 0 := by
  decide

private theorem assemblyRow6_coefficient57 :
    (assemblyData.getD 6 []).getD 57 0 =
      (divisionReducedData.getD 6 []).getD 57 0 := by
  decide

private theorem assemblyRow6_coefficient58 :
    (assemblyData.getD 6 []).getD 58 0 =
      (divisionReducedData.getD 6 []).getD 58 0 := by
  decide

private theorem assemblyRow6_coefficient59 :
    (assemblyData.getD 6 []).getD 59 0 =
      (divisionReducedData.getD 6 []).getD 59 0 := by
  decide

private theorem assemblyRow6_coefficient60 :
    (assemblyData.getD 6 []).getD 60 0 =
      (divisionReducedData.getD 6 []).getD 60 0 := by
  decide

private theorem assemblyRow6_coefficient61 :
    (assemblyData.getD 6 []).getD 61 0 =
      (divisionReducedData.getD 6 []).getD 61 0 := by
  decide

private theorem assemblyRow6_coefficient62 :
    (assemblyData.getD 6 []).getD 62 0 =
      (divisionReducedData.getD 6 []).getD 62 0 := by
  decide

private theorem assemblyRow6_coefficient63 :
    (assemblyData.getD 6 []).getD 63 0 =
      (divisionReducedData.getD 6 []).getD 63 0 := by
  decide

private theorem assemblyRow6_coefficient64 :
    (assemblyData.getD 6 []).getD 64 0 =
      (divisionReducedData.getD 6 []).getD 64 0 := by
  decide

private theorem assemblyRow6_coefficient65 :
    (assemblyData.getD 6 []).getD 65 0 =
      (divisionReducedData.getD 6 []).getD 65 0 := by
  decide

private theorem assemblyRow6_coefficient66 :
    (assemblyData.getD 6 []).getD 66 0 =
      (divisionReducedData.getD 6 []).getD 66 0 := by
  decide

private theorem assemblyRow6_coefficient67 :
    (assemblyData.getD 6 []).getD 67 0 =
      (divisionReducedData.getD 6 []).getD 67 0 := by
  decide

private theorem assemblyRow6_coefficient68 :
    (assemblyData.getD 6 []).getD 68 0 =
      (divisionReducedData.getD 6 []).getD 68 0 := by
  decide

private theorem assemblyRow6_coefficient69 :
    (assemblyData.getD 6 []).getD 69 0 =
      (divisionReducedData.getD 6 []).getD 69 0 := by
  decide

private theorem assemblyRow6_coefficient70 :
    (assemblyData.getD 6 []).getD 70 0 =
      (divisionReducedData.getD 6 []).getD 70 0 := by
  decide

private theorem assemblyRow6_coefficient71 :
    (assemblyData.getD 6 []).getD 71 0 =
      (divisionReducedData.getD 6 []).getD 71 0 := by
  decide

private theorem assemblyRow6_coefficient72 :
    (assemblyData.getD 6 []).getD 72 0 =
      (divisionReducedData.getD 6 []).getD 72 0 := by
  decide

private theorem assemblyRow6_coefficient73 :
    (assemblyData.getD 6 []).getD 73 0 =
      (divisionReducedData.getD 6 []).getD 73 0 := by
  decide

private theorem assemblyRow6_coefficient74 :
    (assemblyData.getD 6 []).getD 74 0 =
      (divisionReducedData.getD 6 []).getD 74 0 := by
  decide

private theorem assemblyRow6_coefficient75 :
    (assemblyData.getD 6 []).getD 75 0 =
      (divisionReducedData.getD 6 []).getD 75 0 := by
  decide

private theorem assemblyRow6_coefficient76 :
    (assemblyData.getD 6 []).getD 76 0 =
      (divisionReducedData.getD 6 []).getD 76 0 := by
  decide

private theorem assemblyRow6_coefficient77 :
    (assemblyData.getD 6 []).getD 77 0 =
      (divisionReducedData.getD 6 []).getD 77 0 := by
  decide

private theorem assemblyRow6_coefficient78 :
    (assemblyData.getD 6 []).getD 78 0 =
      (divisionReducedData.getD 6 []).getD 78 0 := by
  decide

private theorem assemblyRow6_coefficient79 :
    (assemblyData.getD 6 []).getD 79 0 =
      (divisionReducedData.getD 6 []).getD 79 0 := by
  decide

private theorem assemblyRow6_coefficient80 :
    (assemblyData.getD 6 []).getD 80 0 =
      (divisionReducedData.getD 6 []).getD 80 0 := by
  decide

private theorem assemblyRow6_coefficient81 :
    (assemblyData.getD 6 []).getD 81 0 =
      (divisionReducedData.getD 6 []).getD 81 0 := by
  decide

private theorem assemblyRow6_coefficient82 :
    (assemblyData.getD 6 []).getD 82 0 =
      (divisionReducedData.getD 6 []).getD 82 0 := by
  decide

private theorem assemblyRow6_coefficient83 :
    (assemblyData.getD 6 []).getD 83 0 =
      (divisionReducedData.getD 6 []).getD 83 0 := by
  decide

private theorem assemblyRow6_coefficient84 :
    (assemblyData.getD 6 []).getD 84 0 =
      (divisionReducedData.getD 6 []).getD 84 0 := by
  decide

private theorem assemblyRow6_coefficient85 :
    (assemblyData.getD 6 []).getD 85 0 =
      (divisionReducedData.getD 6 []).getD 85 0 := by
  decide

private theorem assemblyRow6_coefficient86 :
    (assemblyData.getD 6 []).getD 86 0 =
      (divisionReducedData.getD 6 []).getD 86 0 := by
  decide

private theorem assemblyRow6_coefficient87 :
    (assemblyData.getD 6 []).getD 87 0 =
      (divisionReducedData.getD 6 []).getD 87 0 := by
  decide

private theorem assemblyRow6_coefficient88 :
    (assemblyData.getD 6 []).getD 88 0 =
      (divisionReducedData.getD 6 []).getD 88 0 := by
  decide

private theorem assemblyRow6_coefficient89 :
    (assemblyData.getD 6 []).getD 89 0 =
      (divisionReducedData.getD 6 []).getD 89 0 := by
  decide

private theorem assemblyRow6_coefficient90 :
    (assemblyData.getD 6 []).getD 90 0 =
      (divisionReducedData.getD 6 []).getD 90 0 := by
  decide

private theorem assemblyRow6_coefficient91 :
    (assemblyData.getD 6 []).getD 91 0 =
      (divisionReducedData.getD 6 []).getD 91 0 := by
  decide

private theorem assemblyRow6_coefficient92 :
    (assemblyData.getD 6 []).getD 92 0 =
      (divisionReducedData.getD 6 []).getD 92 0 := by
  decide

private theorem assemblyRow6_coefficient93 :
    (assemblyData.getD 6 []).getD 93 0 =
      (divisionReducedData.getD 6 []).getD 93 0 := by
  decide

private theorem assemblyRow6_coefficient94 :
    (assemblyData.getD 6 []).getD 94 0 =
      (divisionReducedData.getD 6 []).getD 94 0 := by
  decide

private theorem assemblyRow6_coefficient95 :
    (assemblyData.getD 6 []).getD 95 0 =
      (divisionReducedData.getD 6 []).getD 95 0 := by
  decide

private theorem assemblyRow6_coefficient96 :
    (assemblyData.getD 6 []).getD 96 0 =
      (divisionReducedData.getD 6 []).getD 96 0 := by
  decide

private theorem assemblyRow6_coefficient97 :
    (assemblyData.getD 6 []).getD 97 0 =
      (divisionReducedData.getD 6 []).getD 97 0 := by
  decide

private theorem assemblyRow6_coefficient98 :
    (assemblyData.getD 6 []).getD 98 0 =
      (divisionReducedData.getD 6 []).getD 98 0 := by
  decide

private theorem assemblyRow6_coefficient99 :
    (assemblyData.getD 6 []).getD 99 0 =
      (divisionReducedData.getD 6 []).getD 99 0 := by
  decide

private theorem assemblyRow6_coefficient100 :
    (assemblyData.getD 6 []).getD 100 0 =
      (divisionReducedData.getD 6 []).getD 100 0 := by
  decide

private theorem assemblyRow6_coefficient101 :
    (assemblyData.getD 6 []).getD 101 0 =
      (divisionReducedData.getD 6 []).getD 101 0 := by
  decide

private theorem assemblyRow6_coefficient102 :
    (assemblyData.getD 6 []).getD 102 0 =
      (divisionReducedData.getD 6 []).getD 102 0 := by
  decide

private theorem assemblyRow6_coefficient103 :
    (assemblyData.getD 6 []).getD 103 0 =
      (divisionReducedData.getD 6 []).getD 103 0 := by
  decide

private theorem assemblyRow6_coefficient104 :
    (assemblyData.getD 6 []).getD 104 0 =
      (divisionReducedData.getD 6 []).getD 104 0 := by
  decide

private theorem assemblyRow6_coefficient105 :
    (assemblyData.getD 6 []).getD 105 0 =
      (divisionReducedData.getD 6 []).getD 105 0 := by
  decide

private theorem assemblyRow6_coefficient106 :
    (assemblyData.getD 6 []).getD 106 0 =
      (divisionReducedData.getD 6 []).getD 106 0 := by
  decide

private theorem assemblyRow6_coefficient107 :
    (assemblyData.getD 6 []).getD 107 0 =
      (divisionReducedData.getD 6 []).getD 107 0 := by
  decide

private theorem assemblyRow6_coefficient108 :
    (assemblyData.getD 6 []).getD 108 0 =
      (divisionReducedData.getD 6 []).getD 108 0 := by
  decide

private theorem assemblyRow6_coefficient109 :
    (assemblyData.getD 6 []).getD 109 0 =
      (divisionReducedData.getD 6 []).getD 109 0 := by
  decide

private theorem assemblyRow6_coefficient110 :
    (assemblyData.getD 6 []).getD 110 0 =
      (divisionReducedData.getD 6 []).getD 110 0 := by
  decide

private theorem assemblyRow6_coefficient111 :
    (assemblyData.getD 6 []).getD 111 0 =
      (divisionReducedData.getD 6 []).getD 111 0 := by
  decide

private theorem assemblyRow6_coefficient112 :
    (assemblyData.getD 6 []).getD 112 0 =
      (divisionReducedData.getD 6 []).getD 112 0 := by
  decide

private theorem assemblyRow6_coefficient113 :
    (assemblyData.getD 6 []).getD 113 0 =
      (divisionReducedData.getD 6 []).getD 113 0 := by
  decide

private theorem assemblyRow6_coefficient114 :
    (assemblyData.getD 6 []).getD 114 0 =
      (divisionReducedData.getD 6 []).getD 114 0 := by
  decide

private theorem assemblyRow6_coefficient115 :
    (assemblyData.getD 6 []).getD 115 0 =
      (divisionReducedData.getD 6 []).getD 115 0 := by
  decide

private theorem assemblyRow6_coefficient116 :
    (assemblyData.getD 6 []).getD 116 0 =
      (divisionReducedData.getD 6 []).getD 116 0 := by
  decide

private theorem assemblyRow6_coefficient117 :
    (assemblyData.getD 6 []).getD 117 0 =
      (divisionReducedData.getD 6 []).getD 117 0 := by
  decide

private theorem assemblyRow6_coefficient118 :
    (assemblyData.getD 6 []).getD 118 0 =
      (divisionReducedData.getD 6 []).getD 118 0 := by
  decide

private theorem assemblyRow6_coefficient119 :
    (assemblyData.getD 6 []).getD 119 0 =
      (divisionReducedData.getD 6 []).getD 119 0 := by
  decide

private theorem assemblyRow6_coefficient120 :
    (assemblyData.getD 6 []).getD 120 0 =
      (divisionReducedData.getD 6 []).getD 120 0 := by
  decide

private theorem assemblyRow6_coefficients (j : ℕ) (hj : j < 121) :
    (assemblyData.getD 6 []).getD j 0 =
      (divisionReducedData.getD 6 []).getD j 0 := by
  interval_cases j
  all_goals first
  | exact assemblyRow6_coefficient0
  | exact assemblyRow6_coefficient1
  | exact assemblyRow6_coefficient2
  | exact assemblyRow6_coefficient3
  | exact assemblyRow6_coefficient4
  | exact assemblyRow6_coefficient5
  | exact assemblyRow6_coefficient6
  | exact assemblyRow6_coefficient7
  | exact assemblyRow6_coefficient8
  | exact assemblyRow6_coefficient9
  | exact assemblyRow6_coefficient10
  | exact assemblyRow6_coefficient11
  | exact assemblyRow6_coefficient12
  | exact assemblyRow6_coefficient13
  | exact assemblyRow6_coefficient14
  | exact assemblyRow6_coefficient15
  | exact assemblyRow6_coefficient16
  | exact assemblyRow6_coefficient17
  | exact assemblyRow6_coefficient18
  | exact assemblyRow6_coefficient19
  | exact assemblyRow6_coefficient20
  | exact assemblyRow6_coefficient21
  | exact assemblyRow6_coefficient22
  | exact assemblyRow6_coefficient23
  | exact assemblyRow6_coefficient24
  | exact assemblyRow6_coefficient25
  | exact assemblyRow6_coefficient26
  | exact assemblyRow6_coefficient27
  | exact assemblyRow6_coefficient28
  | exact assemblyRow6_coefficient29
  | exact assemblyRow6_coefficient30
  | exact assemblyRow6_coefficient31
  | exact assemblyRow6_coefficient32
  | exact assemblyRow6_coefficient33
  | exact assemblyRow6_coefficient34
  | exact assemblyRow6_coefficient35
  | exact assemblyRow6_coefficient36
  | exact assemblyRow6_coefficient37
  | exact assemblyRow6_coefficient38
  | exact assemblyRow6_coefficient39
  | exact assemblyRow6_coefficient40
  | exact assemblyRow6_coefficient41
  | exact assemblyRow6_coefficient42
  | exact assemblyRow6_coefficient43
  | exact assemblyRow6_coefficient44
  | exact assemblyRow6_coefficient45
  | exact assemblyRow6_coefficient46
  | exact assemblyRow6_coefficient47
  | exact assemblyRow6_coefficient48
  | exact assemblyRow6_coefficient49
  | exact assemblyRow6_coefficient50
  | exact assemblyRow6_coefficient51
  | exact assemblyRow6_coefficient52
  | exact assemblyRow6_coefficient53
  | exact assemblyRow6_coefficient54
  | exact assemblyRow6_coefficient55
  | exact assemblyRow6_coefficient56
  | exact assemblyRow6_coefficient57
  | exact assemblyRow6_coefficient58
  | exact assemblyRow6_coefficient59
  | exact assemblyRow6_coefficient60
  | exact assemblyRow6_coefficient61
  | exact assemblyRow6_coefficient62
  | exact assemblyRow6_coefficient63
  | exact assemblyRow6_coefficient64
  | exact assemblyRow6_coefficient65
  | exact assemblyRow6_coefficient66
  | exact assemblyRow6_coefficient67
  | exact assemblyRow6_coefficient68
  | exact assemblyRow6_coefficient69
  | exact assemblyRow6_coefficient70
  | exact assemblyRow6_coefficient71
  | exact assemblyRow6_coefficient72
  | exact assemblyRow6_coefficient73
  | exact assemblyRow6_coefficient74
  | exact assemblyRow6_coefficient75
  | exact assemblyRow6_coefficient76
  | exact assemblyRow6_coefficient77
  | exact assemblyRow6_coefficient78
  | exact assemblyRow6_coefficient79
  | exact assemblyRow6_coefficient80
  | exact assemblyRow6_coefficient81
  | exact assemblyRow6_coefficient82
  | exact assemblyRow6_coefficient83
  | exact assemblyRow6_coefficient84
  | exact assemblyRow6_coefficient85
  | exact assemblyRow6_coefficient86
  | exact assemblyRow6_coefficient87
  | exact assemblyRow6_coefficient88
  | exact assemblyRow6_coefficient89
  | exact assemblyRow6_coefficient90
  | exact assemblyRow6_coefficient91
  | exact assemblyRow6_coefficient92
  | exact assemblyRow6_coefficient93
  | exact assemblyRow6_coefficient94
  | exact assemblyRow6_coefficient95
  | exact assemblyRow6_coefficient96
  | exact assemblyRow6_coefficient97
  | exact assemblyRow6_coefficient98
  | exact assemblyRow6_coefficient99
  | exact assemblyRow6_coefficient100
  | exact assemblyRow6_coefficient101
  | exact assemblyRow6_coefficient102
  | exact assemblyRow6_coefficient103
  | exact assemblyRow6_coefficient104
  | exact assemblyRow6_coefficient105
  | exact assemblyRow6_coefficient106
  | exact assemblyRow6_coefficient107
  | exact assemblyRow6_coefficient108
  | exact assemblyRow6_coefficient109
  | exact assemblyRow6_coefficient110
  | exact assemblyRow6_coefficient111
  | exact assemblyRow6_coefficient112
  | exact assemblyRow6_coefficient113
  | exact assemblyRow6_coefficient114
  | exact assemblyRow6_coefficient115
  | exact assemblyRow6_coefficient116
  | exact assemblyRow6_coefficient117
  | exact assemblyRow6_coefficient118
  | exact assemblyRow6_coefficient119
  | exact assemblyRow6_coefficient120

theorem assemblyRow6 :
    (rectangularize 83 121 assemblyData).getD 6 [] =
      (rectangularize 83 121 divisionReducedData).getD 6 [] := by
  rw [getD_rectangularize 83 121 assemblyData 6 (by omega),
    getD_rectangularize 83 121 divisionReducedData 6 (by omega)]
  exact padOne_eq_of_bounded_coefficients 121 121
    (assemblyData.getD 6 []) (divisionReducedData.getD 6 [])
    assemblyRow6_leftSupport assemblyRow6_rightSupport (by omega)
    assemblyRow6_coefficients

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
