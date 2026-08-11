/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial

/-! Generated U coefficient tables for the checked raw O25 certificate. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial

private def uRow0 : One :=
  [0, 0, 0, 0, 1]

private def uRow1 : One :=
  [0, -1, 3, -7, 1]

private def uRow2 : One :=
  [1, -1, 2, 8, -5, 1]

private def uRow3 : One :=
  [-2, 3, -9, 5, -1]

private def uRow4 : One :=
  [1]

def UData : Two :=
  [uRow0, uRow1, uRow2, uRow3, uRow4]

private def u2Row0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1]

private def u2Row1 : One :=
  [0, 0, 0, 0, 0, -2, 6, -14, 2]

private def u2Row2 : One :=
  [0, 0, 1, -6, 25, -46, 59, 2, -9, 2]

private def u2Row3 : One :=
  [0, -2, 8, -24, 8, 34, -158, 102, -26, 2]

private def u2Row4 : One :=
  [1, 2, -13, 76, -130, 208, -52, -52, 39, -10, 1]

private def u2Row5 : One :=
  [-4, 8, -26, -6, 22, -156, 172, -84, 20, -2]

private def u2Row6 : One :=
  [6, -14, 49, -58, 105, -94, 43, -10, 1]

private def u2Row7 : One :=
  [-4, 6, -18, 10, -2]

private def u2Row8 : One :=
  [1]

def U2Data : Two :=
  [u2Row0, u2Row1, u2Row2, u2Row3, u2Row4, u2Row5, u2Row6, u2Row7, u2Row8]

private def u3Row0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def u3Row1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 9, -21, 3]

private def u3Row2 : One :=
  [0, 0, 0, 0, 0, 0, 3, -18, 72, -135, 171, -18, -12, 3]

private def u3Row3 : One :=
  [0, 0, 0, -1, 9, -54, 180, -426, 540, -379, -291, 270, -74, 6]

private def u3Row4 : One :=
  [0, 0, 3, -21, 96, -207, 237, 402, -1437, 2586, -1443, 243, 60, -27, 3]

private def u3Row5 : One :=
  [0, -3, 9, -9, -177, 735, -2085, 2880, -2664, -681, 2235, -1377, 399, -57, 3]

private def u3Row6 : One :=
  [1, 9, -54, 263, -492, 681, 719, -2793, 6129, -5287, 1914, 9, -254, 93, -15, 1]

private def u3Row7 : One :=
  [-6, 3, 21, -357, 987, -2595, 3441, -4044, 1362, 1701, -2121, 1071, -297, 45, -3]

private def u3Row8 : One :=
  [15, -42, 156, -105, 96, 819, -1536, 3114, -3843, 2724, -1164, 303, -45, 3]

private def u3Row9 : One :=
  [-20, 63, -249, 414, -858, 972, -1308, 1410, -954, 398, -102, 15, -1]

private def u3Row10 : One :=
  [15, -39, 141, -198, 330, -285, 129, -30, 3]

private def u3Row11 : One :=
  [-6, 9, -27, 15, -3]

private def u3Row12 : One :=
  [1]

def U3Data : Two :=
  [u3Row0, u3Row1, u3Row2, u3Row3, u3Row4, u3Row5, u3Row6, u3Row7, u3Row8, u3Row9, u3Row10, u3Row11, u3Row12]

private def u4Row0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def u4Row1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 12, -28, 4]

private def u4Row2 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, -36, 142, -268, 338, -52, -14, 4]

private def u4Row3 : One :=
  [0, 0, 0, 0, 0, 0, 0, -4, 36, -204, 672, -1560, 2104, -1708, -252, 488, -144, 12]

private def u4Row4 : One :=
  [0, 0, 0, 0, 1, -12, 94, -448, 1545, -3552, 5662, -4344, -661, 7468, -5154, 1256, 7, -48, 6]

private def u4Row5 : One :=
  [0, 0, 0, -4, 40, -248, 892, -2152, 2300, 2120, -16232, 31096, -36172, 14512, 2236, -3928,
    1372, -212, 12]

private def u4Row6 : One :=
  [0, 0, 6, -40, 160, -84, -1400, 8316, -22656, 42200, -41470, 13152, 42650, -55392, 29262,
    -7264, 390, 228, -54, 4]

private def u4Row7 : One :=
  [0, -4, 0, 100, -940, 3504, -9212, 11592, -924, -46332, 104232, -145692, 95120, -13040,
    -21108, 15656, -5292, 996, -100, 4]

private def u4Row8 : One :=
  [1, 20, -106, 424, -61, -3100, 17820, -45156, 87294, -95628, 59304, 47628, -119716, 96556,
    -40004, 7524, 615, -696, 170, -20, 1]

private def u4Row9 : One :=
  [-8, -24, 228, -1580, 4428, -10380, 9480, 2428, -53856, 115800, -179444, 167280, -79372, 4368,
    17436, -11280, 3700, -720, 80, -4]

private def u4Row10 : One :=
  [28, -52, 72, 1336, -5210, 18000, -35014, 62448, -70386, 63128, -17132, -44532, 67172, -47796,
    20940, -5980, 1100, -120, 6]

private def u4Row11 : One :=
  [-56, 200, -820, 1040, -1412, -3788, 10824, -29664, 46452, -65092, 76804, -65000, 37788,
    -15096, 4116, -740, 80, -4]

private def u4Row12 : One :=
  [70, -276, 1206, -2548, 5889, -8160, 12642, -14004, 15945, -18412, 16014, -9492, 3819, -1040,
    186, -20, 1]

private def u4Row13 : One :=
  [-56, 200, -828, 1664, -3560, 4824, -6264, 6144, -3936, 1604, -408, 60, -4]

private def u4Row14 : One :=
  [28, -76, 278, -412, 670, -572, 258, -60, 6]

private def u4Row15 : One :=
  [-8, 12, -36, 20, -4]

private def u4Row16 : One :=
  [1]

def U4Data : Two :=
  [u4Row0, u4Row1, u4Row2, u4Row3, u4Row4, u4Row5, u4Row6, u4Row7, u4Row8, u4Row9, u4Row10, u4Row11, u4Row12, u4Row13, u4Row14, u4Row15, u4Row16]


end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
