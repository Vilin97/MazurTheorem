/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyRowSupport

/-!
# Row seven of the raw numerator assembly certificate

The complete structural support has width 93.  Coefficients beyond that
bound are discharged by the shared list-default lemma.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomialRectangular

private theorem assemblyRow7_leftSupport :
    (assemblyData.getD 7 []).length ≤ 121 := by
  exact assemblyData_row_length_le 7

private theorem assemblyRow7_rightSupport :
    (divisionReducedData.getD 7 []).length ≤ 121 := by
  decide

private theorem assemblyRow7_coefficient0 :
    (assemblyData.getD 7 []).getD 0 0 =
      (divisionReducedData.getD 7 []).getD 0 0 := by
  decide

private theorem assemblyRow7_coefficient1 :
    (assemblyData.getD 7 []).getD 1 0 =
      (divisionReducedData.getD 7 []).getD 1 0 := by
  decide

private theorem assemblyRow7_coefficient2 :
    (assemblyData.getD 7 []).getD 2 0 =
      (divisionReducedData.getD 7 []).getD 2 0 := by
  decide

private theorem assemblyRow7_coefficient3 :
    (assemblyData.getD 7 []).getD 3 0 =
      (divisionReducedData.getD 7 []).getD 3 0 := by
  decide

private theorem assemblyRow7_coefficient4 :
    (assemblyData.getD 7 []).getD 4 0 =
      (divisionReducedData.getD 7 []).getD 4 0 := by
  decide

private theorem assemblyRow7_coefficient5 :
    (assemblyData.getD 7 []).getD 5 0 =
      (divisionReducedData.getD 7 []).getD 5 0 := by
  decide

private theorem assemblyRow7_coefficient6 :
    (assemblyData.getD 7 []).getD 6 0 =
      (divisionReducedData.getD 7 []).getD 6 0 := by
  decide

private theorem assemblyRow7_coefficient7 :
    (assemblyData.getD 7 []).getD 7 0 =
      (divisionReducedData.getD 7 []).getD 7 0 := by
  decide

private theorem assemblyRow7_coefficient8 :
    (assemblyData.getD 7 []).getD 8 0 =
      (divisionReducedData.getD 7 []).getD 8 0 := by
  decide

private theorem assemblyRow7_coefficient9 :
    (assemblyData.getD 7 []).getD 9 0 =
      (divisionReducedData.getD 7 []).getD 9 0 := by
  decide

private theorem assemblyRow7_coefficient10 :
    (assemblyData.getD 7 []).getD 10 0 =
      (divisionReducedData.getD 7 []).getD 10 0 := by
  decide

private theorem assemblyRow7_coefficient11 :
    (assemblyData.getD 7 []).getD 11 0 =
      (divisionReducedData.getD 7 []).getD 11 0 := by
  decide

private theorem assemblyRow7_coefficient12 :
    (assemblyData.getD 7 []).getD 12 0 =
      (divisionReducedData.getD 7 []).getD 12 0 := by
  decide

private theorem assemblyRow7_coefficient13 :
    (assemblyData.getD 7 []).getD 13 0 =
      (divisionReducedData.getD 7 []).getD 13 0 := by
  decide

private theorem assemblyRow7_coefficient14 :
    (assemblyData.getD 7 []).getD 14 0 =
      (divisionReducedData.getD 7 []).getD 14 0 := by
  decide

private theorem assemblyRow7_coefficient15 :
    (assemblyData.getD 7 []).getD 15 0 =
      (divisionReducedData.getD 7 []).getD 15 0 := by
  decide

private theorem assemblyRow7_coefficient16 :
    (assemblyData.getD 7 []).getD 16 0 =
      (divisionReducedData.getD 7 []).getD 16 0 := by
  decide

private theorem assemblyRow7_coefficient17 :
    (assemblyData.getD 7 []).getD 17 0 =
      (divisionReducedData.getD 7 []).getD 17 0 := by
  decide

private theorem assemblyRow7_coefficient18 :
    (assemblyData.getD 7 []).getD 18 0 =
      (divisionReducedData.getD 7 []).getD 18 0 := by
  decide

private theorem assemblyRow7_coefficient19 :
    (assemblyData.getD 7 []).getD 19 0 =
      (divisionReducedData.getD 7 []).getD 19 0 := by
  decide

private theorem assemblyRow7_coefficient20 :
    (assemblyData.getD 7 []).getD 20 0 =
      (divisionReducedData.getD 7 []).getD 20 0 := by
  decide

private theorem assemblyRow7_coefficient21 :
    (assemblyData.getD 7 []).getD 21 0 =
      (divisionReducedData.getD 7 []).getD 21 0 := by
  decide

private theorem assemblyRow7_coefficient22 :
    (assemblyData.getD 7 []).getD 22 0 =
      (divisionReducedData.getD 7 []).getD 22 0 := by
  decide

private theorem assemblyRow7_coefficient23 :
    (assemblyData.getD 7 []).getD 23 0 =
      (divisionReducedData.getD 7 []).getD 23 0 := by
  decide

private theorem assemblyRow7_coefficient24 :
    (assemblyData.getD 7 []).getD 24 0 =
      (divisionReducedData.getD 7 []).getD 24 0 := by
  decide

private theorem assemblyRow7_coefficient25 :
    (assemblyData.getD 7 []).getD 25 0 =
      (divisionReducedData.getD 7 []).getD 25 0 := by
  decide

private theorem assemblyRow7_coefficient26 :
    (assemblyData.getD 7 []).getD 26 0 =
      (divisionReducedData.getD 7 []).getD 26 0 := by
  decide

private theorem assemblyRow7_coefficient27 :
    (assemblyData.getD 7 []).getD 27 0 =
      (divisionReducedData.getD 7 []).getD 27 0 := by
  decide

private theorem assemblyRow7_coefficient28 :
    (assemblyData.getD 7 []).getD 28 0 =
      (divisionReducedData.getD 7 []).getD 28 0 := by
  decide

private theorem assemblyRow7_coefficient29 :
    (assemblyData.getD 7 []).getD 29 0 =
      (divisionReducedData.getD 7 []).getD 29 0 := by
  decide

private theorem assemblyRow7_coefficient30 :
    (assemblyData.getD 7 []).getD 30 0 =
      (divisionReducedData.getD 7 []).getD 30 0 := by
  decide

private theorem assemblyRow7_coefficient31 :
    (assemblyData.getD 7 []).getD 31 0 =
      (divisionReducedData.getD 7 []).getD 31 0 := by
  decide

private theorem assemblyRow7_coefficient32 :
    (assemblyData.getD 7 []).getD 32 0 =
      (divisionReducedData.getD 7 []).getD 32 0 := by
  decide

private theorem assemblyRow7_coefficient33 :
    (assemblyData.getD 7 []).getD 33 0 =
      (divisionReducedData.getD 7 []).getD 33 0 := by
  decide

private theorem assemblyRow7_coefficient34 :
    (assemblyData.getD 7 []).getD 34 0 =
      (divisionReducedData.getD 7 []).getD 34 0 := by
  decide

private theorem assemblyRow7_coefficient35 :
    (assemblyData.getD 7 []).getD 35 0 =
      (divisionReducedData.getD 7 []).getD 35 0 := by
  decide

private theorem assemblyRow7_coefficient36 :
    (assemblyData.getD 7 []).getD 36 0 =
      (divisionReducedData.getD 7 []).getD 36 0 := by
  decide

private theorem assemblyRow7_coefficient37 :
    (assemblyData.getD 7 []).getD 37 0 =
      (divisionReducedData.getD 7 []).getD 37 0 := by
  decide

private theorem assemblyRow7_coefficient38 :
    (assemblyData.getD 7 []).getD 38 0 =
      (divisionReducedData.getD 7 []).getD 38 0 := by
  decide

private theorem assemblyRow7_coefficient39 :
    (assemblyData.getD 7 []).getD 39 0 =
      (divisionReducedData.getD 7 []).getD 39 0 := by
  decide

private theorem assemblyRow7_coefficient40 :
    (assemblyData.getD 7 []).getD 40 0 =
      (divisionReducedData.getD 7 []).getD 40 0 := by
  decide

private theorem assemblyRow7_coefficient41 :
    (assemblyData.getD 7 []).getD 41 0 =
      (divisionReducedData.getD 7 []).getD 41 0 := by
  decide

private theorem assemblyRow7_coefficient42 :
    (assemblyData.getD 7 []).getD 42 0 =
      (divisionReducedData.getD 7 []).getD 42 0 := by
  decide

private theorem assemblyRow7_coefficient43 :
    (assemblyData.getD 7 []).getD 43 0 =
      (divisionReducedData.getD 7 []).getD 43 0 := by
  decide

private theorem assemblyRow7_coefficient44 :
    (assemblyData.getD 7 []).getD 44 0 =
      (divisionReducedData.getD 7 []).getD 44 0 := by
  decide

private theorem assemblyRow7_coefficient45 :
    (assemblyData.getD 7 []).getD 45 0 =
      (divisionReducedData.getD 7 []).getD 45 0 := by
  decide

private theorem assemblyRow7_coefficient46 :
    (assemblyData.getD 7 []).getD 46 0 =
      (divisionReducedData.getD 7 []).getD 46 0 := by
  decide

private theorem assemblyRow7_coefficient47 :
    (assemblyData.getD 7 []).getD 47 0 =
      (divisionReducedData.getD 7 []).getD 47 0 := by
  decide

private theorem assemblyRow7_coefficient48 :
    (assemblyData.getD 7 []).getD 48 0 =
      (divisionReducedData.getD 7 []).getD 48 0 := by
  decide

private theorem assemblyRow7_coefficient49 :
    (assemblyData.getD 7 []).getD 49 0 =
      (divisionReducedData.getD 7 []).getD 49 0 := by
  decide

private theorem assemblyRow7_coefficient50 :
    (assemblyData.getD 7 []).getD 50 0 =
      (divisionReducedData.getD 7 []).getD 50 0 := by
  decide

private theorem assemblyRow7_coefficient51 :
    (assemblyData.getD 7 []).getD 51 0 =
      (divisionReducedData.getD 7 []).getD 51 0 := by
  decide

private theorem assemblyRow7_coefficient52 :
    (assemblyData.getD 7 []).getD 52 0 =
      (divisionReducedData.getD 7 []).getD 52 0 := by
  decide

private theorem assemblyRow7_coefficient53 :
    (assemblyData.getD 7 []).getD 53 0 =
      (divisionReducedData.getD 7 []).getD 53 0 := by
  decide

private theorem assemblyRow7_coefficient54 :
    (assemblyData.getD 7 []).getD 54 0 =
      (divisionReducedData.getD 7 []).getD 54 0 := by
  decide

private theorem assemblyRow7_coefficient55 :
    (assemblyData.getD 7 []).getD 55 0 =
      (divisionReducedData.getD 7 []).getD 55 0 := by
  decide

private theorem assemblyRow7_coefficient56 :
    (assemblyData.getD 7 []).getD 56 0 =
      (divisionReducedData.getD 7 []).getD 56 0 := by
  decide

private theorem assemblyRow7_coefficient57 :
    (assemblyData.getD 7 []).getD 57 0 =
      (divisionReducedData.getD 7 []).getD 57 0 := by
  decide

private theorem assemblyRow7_coefficient58 :
    (assemblyData.getD 7 []).getD 58 0 =
      (divisionReducedData.getD 7 []).getD 58 0 := by
  decide

private theorem assemblyRow7_coefficient59 :
    (assemblyData.getD 7 []).getD 59 0 =
      (divisionReducedData.getD 7 []).getD 59 0 := by
  decide

private theorem assemblyRow7_coefficient60 :
    (assemblyData.getD 7 []).getD 60 0 =
      (divisionReducedData.getD 7 []).getD 60 0 := by
  decide

private theorem assemblyRow7_coefficient61 :
    (assemblyData.getD 7 []).getD 61 0 =
      (divisionReducedData.getD 7 []).getD 61 0 := by
  decide

private theorem assemblyRow7_coefficient62 :
    (assemblyData.getD 7 []).getD 62 0 =
      (divisionReducedData.getD 7 []).getD 62 0 := by
  decide

private theorem assemblyRow7_coefficient63 :
    (assemblyData.getD 7 []).getD 63 0 =
      (divisionReducedData.getD 7 []).getD 63 0 := by
  decide

private theorem assemblyRow7_coefficient64 :
    (assemblyData.getD 7 []).getD 64 0 =
      (divisionReducedData.getD 7 []).getD 64 0 := by
  decide

private theorem assemblyRow7_coefficient65 :
    (assemblyData.getD 7 []).getD 65 0 =
      (divisionReducedData.getD 7 []).getD 65 0 := by
  decide

private theorem assemblyRow7_coefficient66 :
    (assemblyData.getD 7 []).getD 66 0 =
      (divisionReducedData.getD 7 []).getD 66 0 := by
  decide

private theorem assemblyRow7_coefficient67 :
    (assemblyData.getD 7 []).getD 67 0 =
      (divisionReducedData.getD 7 []).getD 67 0 := by
  decide

private theorem assemblyRow7_coefficient68 :
    (assemblyData.getD 7 []).getD 68 0 =
      (divisionReducedData.getD 7 []).getD 68 0 := by
  decide

private theorem assemblyRow7_coefficient69 :
    (assemblyData.getD 7 []).getD 69 0 =
      (divisionReducedData.getD 7 []).getD 69 0 := by
  decide

private theorem assemblyRow7_coefficient70 :
    (assemblyData.getD 7 []).getD 70 0 =
      (divisionReducedData.getD 7 []).getD 70 0 := by
  decide

private theorem assemblyRow7_coefficient71 :
    (assemblyData.getD 7 []).getD 71 0 =
      (divisionReducedData.getD 7 []).getD 71 0 := by
  decide

private theorem assemblyRow7_coefficient72 :
    (assemblyData.getD 7 []).getD 72 0 =
      (divisionReducedData.getD 7 []).getD 72 0 := by
  decide

private theorem assemblyRow7_coefficient73 :
    (assemblyData.getD 7 []).getD 73 0 =
      (divisionReducedData.getD 7 []).getD 73 0 := by
  decide

private theorem assemblyRow7_coefficient74 :
    (assemblyData.getD 7 []).getD 74 0 =
      (divisionReducedData.getD 7 []).getD 74 0 := by
  decide

private theorem assemblyRow7_coefficient75 :
    (assemblyData.getD 7 []).getD 75 0 =
      (divisionReducedData.getD 7 []).getD 75 0 := by
  decide

private theorem assemblyRow7_coefficient76 :
    (assemblyData.getD 7 []).getD 76 0 =
      (divisionReducedData.getD 7 []).getD 76 0 := by
  decide

private theorem assemblyRow7_coefficient77 :
    (assemblyData.getD 7 []).getD 77 0 =
      (divisionReducedData.getD 7 []).getD 77 0 := by
  decide

private theorem assemblyRow7_coefficient78 :
    (assemblyData.getD 7 []).getD 78 0 =
      (divisionReducedData.getD 7 []).getD 78 0 := by
  decide

private theorem assemblyRow7_coefficient79 :
    (assemblyData.getD 7 []).getD 79 0 =
      (divisionReducedData.getD 7 []).getD 79 0 := by
  decide

private theorem assemblyRow7_coefficient80 :
    (assemblyData.getD 7 []).getD 80 0 =
      (divisionReducedData.getD 7 []).getD 80 0 := by
  decide

private theorem assemblyRow7_coefficient81 :
    (assemblyData.getD 7 []).getD 81 0 =
      (divisionReducedData.getD 7 []).getD 81 0 := by
  decide

private theorem assemblyRow7_coefficient82 :
    (assemblyData.getD 7 []).getD 82 0 =
      (divisionReducedData.getD 7 []).getD 82 0 := by
  decide

private theorem assemblyRow7_coefficient83 :
    (assemblyData.getD 7 []).getD 83 0 =
      (divisionReducedData.getD 7 []).getD 83 0 := by
  decide

private theorem assemblyRow7_coefficient84 :
    (assemblyData.getD 7 []).getD 84 0 =
      (divisionReducedData.getD 7 []).getD 84 0 := by
  decide

private theorem assemblyRow7_coefficient85 :
    (assemblyData.getD 7 []).getD 85 0 =
      (divisionReducedData.getD 7 []).getD 85 0 := by
  decide

private theorem assemblyRow7_coefficient86 :
    (assemblyData.getD 7 []).getD 86 0 =
      (divisionReducedData.getD 7 []).getD 86 0 := by
  decide

private theorem assemblyRow7_coefficient87 :
    (assemblyData.getD 7 []).getD 87 0 =
      (divisionReducedData.getD 7 []).getD 87 0 := by
  decide

private theorem assemblyRow7_coefficient88 :
    (assemblyData.getD 7 []).getD 88 0 =
      (divisionReducedData.getD 7 []).getD 88 0 := by
  decide

private theorem assemblyRow7_coefficient89 :
    (assemblyData.getD 7 []).getD 89 0 =
      (divisionReducedData.getD 7 []).getD 89 0 := by
  decide

private theorem assemblyRow7_coefficient90 :
    (assemblyData.getD 7 []).getD 90 0 =
      (divisionReducedData.getD 7 []).getD 90 0 := by
  decide

private theorem assemblyRow7_coefficient91 :
    (assemblyData.getD 7 []).getD 91 0 =
      (divisionReducedData.getD 7 []).getD 91 0 := by
  decide

private theorem assemblyRow7_coefficient92 :
    (assemblyData.getD 7 []).getD 92 0 =
      (divisionReducedData.getD 7 []).getD 92 0 := by
  decide

private theorem assemblyRow7_coefficient93 :
    (assemblyData.getD 7 []).getD 93 0 =
      (divisionReducedData.getD 7 []).getD 93 0 := by
  decide

private theorem assemblyRow7_coefficient94 :
    (assemblyData.getD 7 []).getD 94 0 =
      (divisionReducedData.getD 7 []).getD 94 0 := by
  decide

private theorem assemblyRow7_coefficient95 :
    (assemblyData.getD 7 []).getD 95 0 =
      (divisionReducedData.getD 7 []).getD 95 0 := by
  decide

private theorem assemblyRow7_coefficient96 :
    (assemblyData.getD 7 []).getD 96 0 =
      (divisionReducedData.getD 7 []).getD 96 0 := by
  decide

private theorem assemblyRow7_coefficient97 :
    (assemblyData.getD 7 []).getD 97 0 =
      (divisionReducedData.getD 7 []).getD 97 0 := by
  decide

private theorem assemblyRow7_coefficient98 :
    (assemblyData.getD 7 []).getD 98 0 =
      (divisionReducedData.getD 7 []).getD 98 0 := by
  decide

private theorem assemblyRow7_coefficient99 :
    (assemblyData.getD 7 []).getD 99 0 =
      (divisionReducedData.getD 7 []).getD 99 0 := by
  decide

private theorem assemblyRow7_coefficient100 :
    (assemblyData.getD 7 []).getD 100 0 =
      (divisionReducedData.getD 7 []).getD 100 0 := by
  decide

private theorem assemblyRow7_coefficient101 :
    (assemblyData.getD 7 []).getD 101 0 =
      (divisionReducedData.getD 7 []).getD 101 0 := by
  decide

private theorem assemblyRow7_coefficient102 :
    (assemblyData.getD 7 []).getD 102 0 =
      (divisionReducedData.getD 7 []).getD 102 0 := by
  decide

private theorem assemblyRow7_coefficient103 :
    (assemblyData.getD 7 []).getD 103 0 =
      (divisionReducedData.getD 7 []).getD 103 0 := by
  decide

private theorem assemblyRow7_coefficient104 :
    (assemblyData.getD 7 []).getD 104 0 =
      (divisionReducedData.getD 7 []).getD 104 0 := by
  decide

private theorem assemblyRow7_coefficient105 :
    (assemblyData.getD 7 []).getD 105 0 =
      (divisionReducedData.getD 7 []).getD 105 0 := by
  decide

private theorem assemblyRow7_coefficient106 :
    (assemblyData.getD 7 []).getD 106 0 =
      (divisionReducedData.getD 7 []).getD 106 0 := by
  decide

private theorem assemblyRow7_coefficient107 :
    (assemblyData.getD 7 []).getD 107 0 =
      (divisionReducedData.getD 7 []).getD 107 0 := by
  decide

private theorem assemblyRow7_coefficient108 :
    (assemblyData.getD 7 []).getD 108 0 =
      (divisionReducedData.getD 7 []).getD 108 0 := by
  decide

private theorem assemblyRow7_coefficient109 :
    (assemblyData.getD 7 []).getD 109 0 =
      (divisionReducedData.getD 7 []).getD 109 0 := by
  decide

private theorem assemblyRow7_coefficient110 :
    (assemblyData.getD 7 []).getD 110 0 =
      (divisionReducedData.getD 7 []).getD 110 0 := by
  decide

private theorem assemblyRow7_coefficient111 :
    (assemblyData.getD 7 []).getD 111 0 =
      (divisionReducedData.getD 7 []).getD 111 0 := by
  decide

private theorem assemblyRow7_coefficient112 :
    (assemblyData.getD 7 []).getD 112 0 =
      (divisionReducedData.getD 7 []).getD 112 0 := by
  decide

private theorem assemblyRow7_coefficient113 :
    (assemblyData.getD 7 []).getD 113 0 =
      (divisionReducedData.getD 7 []).getD 113 0 := by
  decide

private theorem assemblyRow7_coefficient114 :
    (assemblyData.getD 7 []).getD 114 0 =
      (divisionReducedData.getD 7 []).getD 114 0 := by
  decide

private theorem assemblyRow7_coefficient115 :
    (assemblyData.getD 7 []).getD 115 0 =
      (divisionReducedData.getD 7 []).getD 115 0 := by
  decide

private theorem assemblyRow7_coefficient116 :
    (assemblyData.getD 7 []).getD 116 0 =
      (divisionReducedData.getD 7 []).getD 116 0 := by
  decide

private theorem assemblyRow7_coefficient117 :
    (assemblyData.getD 7 []).getD 117 0 =
      (divisionReducedData.getD 7 []).getD 117 0 := by
  decide

private theorem assemblyRow7_coefficient118 :
    (assemblyData.getD 7 []).getD 118 0 =
      (divisionReducedData.getD 7 []).getD 118 0 := by
  decide

private theorem assemblyRow7_coefficient119 :
    (assemblyData.getD 7 []).getD 119 0 =
      (divisionReducedData.getD 7 []).getD 119 0 := by
  decide

private theorem assemblyRow7_coefficient120 :
    (assemblyData.getD 7 []).getD 120 0 =
      (divisionReducedData.getD 7 []).getD 120 0 := by
  decide

private theorem assemblyRow7_coefficients (j : ℕ) (hj : j < 121) :
    (assemblyData.getD 7 []).getD j 0 =
      (divisionReducedData.getD 7 []).getD j 0 := by
  interval_cases j
  all_goals first
  | exact assemblyRow7_coefficient0
  | exact assemblyRow7_coefficient1
  | exact assemblyRow7_coefficient2
  | exact assemblyRow7_coefficient3
  | exact assemblyRow7_coefficient4
  | exact assemblyRow7_coefficient5
  | exact assemblyRow7_coefficient6
  | exact assemblyRow7_coefficient7
  | exact assemblyRow7_coefficient8
  | exact assemblyRow7_coefficient9
  | exact assemblyRow7_coefficient10
  | exact assemblyRow7_coefficient11
  | exact assemblyRow7_coefficient12
  | exact assemblyRow7_coefficient13
  | exact assemblyRow7_coefficient14
  | exact assemblyRow7_coefficient15
  | exact assemblyRow7_coefficient16
  | exact assemblyRow7_coefficient17
  | exact assemblyRow7_coefficient18
  | exact assemblyRow7_coefficient19
  | exact assemblyRow7_coefficient20
  | exact assemblyRow7_coefficient21
  | exact assemblyRow7_coefficient22
  | exact assemblyRow7_coefficient23
  | exact assemblyRow7_coefficient24
  | exact assemblyRow7_coefficient25
  | exact assemblyRow7_coefficient26
  | exact assemblyRow7_coefficient27
  | exact assemblyRow7_coefficient28
  | exact assemblyRow7_coefficient29
  | exact assemblyRow7_coefficient30
  | exact assemblyRow7_coefficient31
  | exact assemblyRow7_coefficient32
  | exact assemblyRow7_coefficient33
  | exact assemblyRow7_coefficient34
  | exact assemblyRow7_coefficient35
  | exact assemblyRow7_coefficient36
  | exact assemblyRow7_coefficient37
  | exact assemblyRow7_coefficient38
  | exact assemblyRow7_coefficient39
  | exact assemblyRow7_coefficient40
  | exact assemblyRow7_coefficient41
  | exact assemblyRow7_coefficient42
  | exact assemblyRow7_coefficient43
  | exact assemblyRow7_coefficient44
  | exact assemblyRow7_coefficient45
  | exact assemblyRow7_coefficient46
  | exact assemblyRow7_coefficient47
  | exact assemblyRow7_coefficient48
  | exact assemblyRow7_coefficient49
  | exact assemblyRow7_coefficient50
  | exact assemblyRow7_coefficient51
  | exact assemblyRow7_coefficient52
  | exact assemblyRow7_coefficient53
  | exact assemblyRow7_coefficient54
  | exact assemblyRow7_coefficient55
  | exact assemblyRow7_coefficient56
  | exact assemblyRow7_coefficient57
  | exact assemblyRow7_coefficient58
  | exact assemblyRow7_coefficient59
  | exact assemblyRow7_coefficient60
  | exact assemblyRow7_coefficient61
  | exact assemblyRow7_coefficient62
  | exact assemblyRow7_coefficient63
  | exact assemblyRow7_coefficient64
  | exact assemblyRow7_coefficient65
  | exact assemblyRow7_coefficient66
  | exact assemblyRow7_coefficient67
  | exact assemblyRow7_coefficient68
  | exact assemblyRow7_coefficient69
  | exact assemblyRow7_coefficient70
  | exact assemblyRow7_coefficient71
  | exact assemblyRow7_coefficient72
  | exact assemblyRow7_coefficient73
  | exact assemblyRow7_coefficient74
  | exact assemblyRow7_coefficient75
  | exact assemblyRow7_coefficient76
  | exact assemblyRow7_coefficient77
  | exact assemblyRow7_coefficient78
  | exact assemblyRow7_coefficient79
  | exact assemblyRow7_coefficient80
  | exact assemblyRow7_coefficient81
  | exact assemblyRow7_coefficient82
  | exact assemblyRow7_coefficient83
  | exact assemblyRow7_coefficient84
  | exact assemblyRow7_coefficient85
  | exact assemblyRow7_coefficient86
  | exact assemblyRow7_coefficient87
  | exact assemblyRow7_coefficient88
  | exact assemblyRow7_coefficient89
  | exact assemblyRow7_coefficient90
  | exact assemblyRow7_coefficient91
  | exact assemblyRow7_coefficient92
  | exact assemblyRow7_coefficient93
  | exact assemblyRow7_coefficient94
  | exact assemblyRow7_coefficient95
  | exact assemblyRow7_coefficient96
  | exact assemblyRow7_coefficient97
  | exact assemblyRow7_coefficient98
  | exact assemblyRow7_coefficient99
  | exact assemblyRow7_coefficient100
  | exact assemblyRow7_coefficient101
  | exact assemblyRow7_coefficient102
  | exact assemblyRow7_coefficient103
  | exact assemblyRow7_coefficient104
  | exact assemblyRow7_coefficient105
  | exact assemblyRow7_coefficient106
  | exact assemblyRow7_coefficient107
  | exact assemblyRow7_coefficient108
  | exact assemblyRow7_coefficient109
  | exact assemblyRow7_coefficient110
  | exact assemblyRow7_coefficient111
  | exact assemblyRow7_coefficient112
  | exact assemblyRow7_coefficient113
  | exact assemblyRow7_coefficient114
  | exact assemblyRow7_coefficient115
  | exact assemblyRow7_coefficient116
  | exact assemblyRow7_coefficient117
  | exact assemblyRow7_coefficient118
  | exact assemblyRow7_coefficient119
  | exact assemblyRow7_coefficient120

theorem assemblyRow7 :
    (rectangularize 83 121 assemblyData).getD 7 [] =
      (rectangularize 83 121 divisionReducedData).getD 7 [] := by
  rw [getD_rectangularize 83 121 assemblyData 7 (by omega),
    getD_rectangularize 83 121 divisionReducedData 7 (by omega)]
  exact padOne_eq_of_bounded_coefficients 121 121
    (assemblyData.getD 7 []) (divisionReducedData.getD 7 [])
    assemblyRow7_leftSupport assemblyRow7_rightSupport (by omega)
    assemblyRow7_coefficients

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
