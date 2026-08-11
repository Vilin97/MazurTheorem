/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial

/-! Generated factor powers coefficient tables for the checked raw O25 certificate. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial

private def b2Row0 : One :=
  [1, -2, 1]

def B2Data : Two :=
  [b2Row0]

private def b3Row0 : One :=
  [-1, 3, -3, 1]

def B3Data : Two :=
  [b3Row0]

private def b4Row0 : One :=
  [1, -4, 6, -4, 1]

def B4Data : Two :=
  [b4Row0]

private def b5Row0 : One :=
  [-1, 5, -10, 10, -5, 1]

def B5Data : Two :=
  [b5Row0]

private def d2Row0 : One :=
  [0, 0, 1]

private def d2Row1 : One :=
  [0, 0, -8, 6, -2]

private def d2Row2 : One :=
  [0, 2, 16, -24, 17, -6, 1]

private def d2Row3 : One :=
  [0, -8, 6, -2]

private def d2Row4 : One :=
  [1]

def D2Data : Two :=
  [d2Row0, d2Row1, d2Row2, d2Row3, d2Row4]

private def d3Row0 : One :=
  [0, 0, 0, 1]

private def d3Row1 : One :=
  [0, 0, 0, -12, 9, -3]

private def d3Row2 : One :=
  [0, 0, 3, 48, -72, 51, -18, 3]

private def d3Row3 : One :=
  [0, 0, -24, -46, 138, -156, 99, -39, 9, -1]

private def d3Row4 : One :=
  [0, 3, 48, -72, 51, -18, 3]

private def d3Row5 : One :=
  [0, -12, 9, -3]

private def d3Row6 : One :=
  [1]

def D3Data : Two :=
  [d3Row0, d3Row1, d3Row2, d3Row3, d3Row4, d3Row5, d3Row6]

private def d4Row0 : One :=
  [0, 0, 0, 0, 1]

private def d4Row1 : One :=
  [0, 0, 0, 0, -16, 12, -4]

private def d4Row2 : One :=
  [0, 0, 0, 4, 96, -144, 102, -36, 6]

private def d4Row3 : One :=
  [0, 0, 0, -48, -220, 564, -624, 396, -156, 36, -4]

private def d4Row4 : One :=
  [0, 0, 6, 192, -32, -564, 1048, -996, 609, -252, 70, -12, 1]

private def d4Row5 : One :=
  [0, 0, -48, -220, 564, -624, 396, -156, 36, -4]

private def d4Row6 : One :=
  [0, 4, 96, -144, 102, -36, 6]

private def d4Row7 : One :=
  [0, -16, 12, -4]

private def d4Row8 : One :=
  [1]

def D4Data : Two :=
  [d4Row0, d4Row1, d4Row2, d4Row3, d4Row4, d4Row5, d4Row6, d4Row7, d4Row8]

private def d5Row0 : One :=
  [0, 0, 0, 0, 0, 1]

private def d5Row1 : One :=
  [0, 0, 0, 0, 0, -20, 15, -5]

private def d5Row2 : One :=
  [0, 0, 0, 0, 5, 160, -240, 170, -60, 10]

private def d5Row3 : One :=
  [0, 0, 0, 0, -80, -580, 1420, -1560, 990, -390, 90, -10]

private def d5Row4 : One :=
  [0, 0, 0, 10, 480, 560, -3330, 5420, -5010, 3045, -1260, 350, -60, 5]

private def d5Row5 : One :=
  [0, 0, 0, -120, -1190, 1826, 720, -5060, 7380, -6400, 3823, -1645, 510, -110, 15, -1]

private def d5Row6 : One :=
  [0, 0, 10, 480, 560, -3330, 5420, -5010, 3045, -1260, 350, -60, 5]

private def d5Row7 : One :=
  [0, 0, -80, -580, 1420, -1560, 990, -390, 90, -10]

private def d5Row8 : One :=
  [0, 5, 160, -240, 170, -60, 10]

private def d5Row9 : One :=
  [0, -20, 15, -5]

private def d5Row10 : One :=
  [1]

def D5Data : Two :=
  [d5Row0, d5Row1, d5Row2, d5Row3, d5Row4, d5Row5, d5Row6, d5Row7, d5Row8, d5Row9, d5Row10]

private def d6Row0 : One :=
  [0, 0, 0, 0, 0, 0, 1]

private def d6Row1 : One :=
  [0, 0, 0, 0, 0, 0, -24, 18, -6]

private def d6Row2 : One :=
  [0, 0, 0, 0, 0, 6, 240, -360, 255, -90, 15]

private def d6Row3 : One :=
  [0, 0, 0, 0, 0, -120, -1190, 2850, -3120, 1980, -780, 180, -20]

private def d6Row4 : One :=
  [0, 0, 0, 0, 15, 960, 2400, -10500, 16440, -15060, 9135, -3780, 1050, -180, 15]

private def d6Row5 : One :=
  [0, 0, 0, 0, -240, -3660, 2436, 13680, -36300, 46620, -38940, 22998, -9870, 3060, -660, 90,
    -6]

private def d6Row6 : One :=
  [0, 0, 0, 20, 1440, 5520, -17414, 14628, 10554, -39330, 50280, -41172, 24329, -10788, 3615,
    -900, 159, -18, 1]

private def d6Row7 : One :=
  [0, 0, 0, -240, -3660, 2436, 13680, -36300, 46620, -38940, 22998, -9870, 3060, -660, 90, -6]

private def d6Row8 : One :=
  [0, 0, 15, 960, 2400, -10500, 16440, -15060, 9135, -3780, 1050, -180, 15]

private def d6Row9 : One :=
  [0, 0, -120, -1190, 2850, -3120, 1980, -780, 180, -20]

private def d6Row10 : One :=
  [0, 6, 240, -360, 255, -90, 15]

private def d6Row11 : One :=
  [0, -24, 18, -6]

private def d6Row12 : One :=
  [1]

def D6Data : Two :=
  [d6Row0, d6Row1, d6Row2, d6Row3, d6Row4, d6Row5, d6Row6, d6Row7, d6Row8, d6Row9, d6Row10, d6Row11, d6Row12]

private def d7Row0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 1]

private def d7Row1 : One :=
  [0, 0, 0, 0, 0, 0, 0, -28, 21, -7]

private def d7Row2 : One :=
  [0, 0, 0, 0, 0, 0, 7, 336, -504, 357, -126, 21]

private def d7Row3 : One :=
  [0, 0, 0, 0, 0, 0, -168, -2114, 4998, -5460, 3465, -1365, 315, -35]

private def d7Row4 : One :=
  [0, 0, 0, 0, 0, 21, 1680, 6440, -25095, 38570, -35175, 21315, -8820, 2450, -420, 35]

private def d7Row5 : One :=
  [0, 0, 0, 0, 0, -420, -8645, -1449, 58800, -133980, 165900, -136920, 80563, -34545, 10710,
    -2310, 315, -21]

private def d7Row6 : One :=
  [0, 0, 0, 0, 35, 3360, 21840, -48398, -12684, 179298, -339255, 378420, -295554, 171563,
    -75621, 25305, -6300, 1113, -126, 7]

private def d7Row7 : One :=
  [0, 0, 0, 0, -560, -13020, -12908, 112136, -188874, 112322, 96474, -283668, 335118, -264992,
    155991, -70973, 25221, -6951, 1449, -217, 21, -1]

private def d7Row8 : One :=
  [0, 0, 0, 35, 3360, 21840, -48398, -12684, 179298, -339255, 378420, -295554, 171563, -75621,
    25305, -6300, 1113, -126, 7]

private def d7Row9 : One :=
  [0, 0, 0, -420, -8645, -1449, 58800, -133980, 165900, -136920, 80563, -34545, 10710, -2310,
    315, -21]

private def d7Row10 : One :=
  [0, 0, 21, 1680, 6440, -25095, 38570, -35175, 21315, -8820, 2450, -420, 35]

private def d7Row11 : One :=
  [0, 0, -168, -2114, 4998, -5460, 3465, -1365, 315, -35]

private def d7Row12 : One :=
  [0, 7, 336, -504, 357, -126, 21]

private def d7Row13 : One :=
  [0, -28, 21, -7]

private def d7Row14 : One :=
  [1]

def D7Data : Two :=
  [d7Row0, d7Row1, d7Row2, d7Row3, d7Row4, d7Row5, d7Row6, d7Row7, d7Row8, d7Row9, d7Row10, d7Row11, d7Row12, d7Row13, d7Row14]

private def d8Row0 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, 1]

private def d8Row1 : One :=
  [0, 0, 0, 0, 0, 0, 0, 0, -32, 24, -8]

private def d8Row2 : One :=
  [0, 0, 0, 0, 0, 0, 0, 8, 448, -672, 476, -168, 28]

private def d8Row3 : One :=
  [0, 0, 0, 0, 0, 0, 0, -224, -3416, 8008, -8736, 5544, -2184, 504, -56]

private def d8Row4 : One :=
  [0, 0, 0, 0, 0, 0, 28, 2688, 13888, -50904, 77392, -70392, 42630, -17640, 4900, -840, 70]

private def d8Row5 : One :=
  [0, 0, 0, 0, 0, 0, -672, -17416, -17192, 171360, -366520, 446040, -365960, 214928, -92120,
    28560, -6160, 840, -56]

private def d8Row6 : One :=
  [0, 0, 0, 0, 0, 56, 6720, 61600, -93212, -205016, 857892, -1442280, 1548960, -1192016, 687932,
    -302624, 101220, -25200, 4452, -504, 28]

private def d8Row7 : One :=
  [0, 0, 0, 0, 0, -1120, -35000, -91672, 426688, -439152, -428624, 1867152, -2913848, 2957304,
    -2205616, 1266408, -570304, 201936, -55608, 11592, -1736, 168, -8]

private def d8Row8 : One :=
  [0, 0, 0, 0, 70, 8960, 94080, -83664, -499616, 1463408, -1806556, 896784, 720664, -1944824,
    2197748, -1703448, 1004257, -467568, 174188, -51856, 12166, -2184, 284, -24, 1]

private def d8Row9 : One :=
  [0, 0, 0, 0, -1120, -35000, -91672, 426688, -439152, -428624, 1867152, -2913848, 2957304,
    -2205616, 1266408, -570304, 201936, -55608, 11592, -1736, 168, -8]

private def d8Row10 : One :=
  [0, 0, 0, 56, 6720, 61600, -93212, -205016, 857892, -1442280, 1548960, -1192016, 687932,
    -302624, 101220, -25200, 4452, -504, 28]

private def d8Row11 : One :=
  [0, 0, 0, -672, -17416, -17192, 171360, -366520, 446040, -365960, 214928, -92120, 28560,
    -6160, 840, -56]

private def d8Row12 : One :=
  [0, 0, 28, 2688, 13888, -50904, 77392, -70392, 42630, -17640, 4900, -840, 70]

private def d8Row13 : One :=
  [0, 0, -224, -3416, 8008, -8736, 5544, -2184, 504, -56]

private def d8Row14 : One :=
  [0, 8, 448, -672, 476, -168, 28]

private def d8Row15 : One :=
  [0, -32, 24, -8]

private def d8Row16 : One :=
  [1]

def D8Data : Two :=
  [d8Row0, d8Row1, d8Row2, d8Row3, d8Row4, d8Row5, d8Row6, d8Row7, d8Row8, d8Row9, d8Row10, d8Row11, d8Row12, d8Row13, d8Row14, d8Row15, d8Row16]

private def e2Row0 : One :=
  [1, 0, 2, 0, 1]

private def e2Row1 : One :=
  [-6, -2, -6, -2]

private def e2Row2 : One :=
  [15, 4, 7, -2]

private def e2Row3 : One :=
  [-18, 0, 2]

private def e2Row4 : One :=
  [9, -6, 1]

def E2Data : Two :=
  [e2Row0, e2Row1, e2Row2, e2Row3, e2Row4]

private def e3Row0 : One :=
  [-1, 0, -3, 0, -3, 0, -1]

private def e3Row1 : One :=
  [9, 3, 18, 6, 9, 3]

private def e3Row2 : One :=
  [-36, -15, -48, -12, -12, 3]

private def e3Row3 : One :=
  [81, 27, 57, 1, -6]

private def e3Row4 : One :=
  [-108, -9, -21, 21, -3]

private def e3Row5 : One :=
  [81, -27, -9, 3]

private def e3Row6 : One :=
  [-27, 27, -9, 1]

def E3Data : Two :=
  [e3Row0, e3Row1, e3Row2, e3Row3, e3Row4, e3Row5, e3Row6]

private def e4Row0 : One :=
  [1, 0, 4, 0, 6, 0, 4, 0, 1]

private def e4Row1 : One :=
  [-12, -4, -36, -12, -36, -12, -12, -4]

private def e4Row2 : One :=
  [66, 32, 150, 60, 102, 24, 18, -4]

private def e4Row3 : One :=
  [-216, -108, -348, -112, -120, -4, 12]

private def e4Row4 : One :=
  [459, 180, 456, 36, 31, -48, 6]

private def e4Row5 : One :=
  [-648, -108, -288, 120, 40, -12]

private def e4Row6 : One :=
  [594, -108, 36, -112, 42, -4]

private def e4Row7 : One :=
  [-324, 216, 0, -24, 4]

private def e4Row8 : One :=
  [81, -108, 54, -12, 1]

def E4Data : Two :=
  [e4Row0, e4Row1, e4Row2, e4Row3, e4Row4, e4Row5, e4Row6, e4Row7, e4Row8]

private def e5Row0 : One :=
  [-1, 0, -5, 0, -10, 0, -10, 0, -5, 0, -1]

private def e5Row1 : One :=
  [15, 5, 60, 20, 90, 30, 60, 20, 15, 5]

private def e5Row2 : One :=
  [-105, -55, -340, -160, -390, -150, -180, -40, -25, 5]

private def e5Row3 : One :=
  [450, 270, 1150, 550, 930, 290, 210, 10, -20]

private def e5Row4 : One :=
  [-1305, -750, -2485, -930, -1205, -90, -35, 90, -10]

private def e5Row5 : One :=
  [2673, 1215, 3420, 540, 625, -329, -110, 30]

private def e5Row6 : One :=
  [-3915, -945, -2790, 640, 105, 295, -120, 10]

private def e5Row7 : One :=
  [4050, -270, 1080, -1140, 10, 130, -20]

private def e5Row8 : One :=
  [-2835, 1350, -135, 420, -305, 70, -5]

private def e5Row9 : One :=
  [1215, -1215, 270, 90, -45, 5]

private def e5Row10 : One :=
  [-243, 405, -270, 90, -15, 1]

def E5Data : Two :=
  [e5Row0, e5Row1, e5Row2, e5Row3, e5Row4, e5Row5, e5Row6, e5Row7, e5Row8, e5Row9, e5Row10]

private def t2Row0 : One :=
  [0, 0, 1]

private def t2Row1 : One :=
  [0, 2, -14, 12, -6, 2]

private def t2Row2 : One :=
  [1, -16, 73, -100, 82, -50, 21, -6, 1]

private def t2Row3 : One :=
  [-2, 26, -106, 150, -112, 54, -16, 2]

private def t2Row4 : One :=
  [1, -12, 46, -62, 37, -10, 1]

def T2Data : Two :=
  [t2Row0, t2Row1, t2Row2, t2Row3, t2Row4]

private def t3Row0 : One :=
  [0, 0, 0, 1]

private def t3Row1 : One :=
  [0, 0, 3, -21, 18, -9, 3]

private def t3Row2 : One :=
  [0, 3, -45, 201, -285, 243, -150, 63, -18, 3]

private def t3Row3 : One :=
  [1, -27, 243, -922, 1569, -1683, 1344, -831, 405, -156, 45, -9, 1]

private def t3Row4 : One :=
  [-3, 63, -486, 1719, -3003, 3234, -2463, 1389, -576, 171, -33, 3]

private def t3Row5 : One :=
  [3, -57, 408, -1377, 2352, -2373, 1575, -720, 219, -39, 3]

private def t3Row6 : One :=
  [-1, 18, -123, 399, -651, 588, -308, 93, -15, 1]

def T3Data : Two :=
  [t3Row0, t3Row1, t3Row2, t3Row3, t3Row4, t3Row5, t3Row6]

private def t4Row0 : One :=
  [0, 0, 0, 0, 1]

private def t4Row1 : One :=
  [0, 0, 0, 4, -28, 24, -12, 4]

private def t4Row2 : One :=
  [0, 0, 6, -88, 390, -560, 484, -300, 126, -36, 6]

private def t4Row3 : One :=
  [0, 4, -96, 816, -3052, 5376, -6060, 5052, -3228, 1608, -624, 180, -36, 4]

private def t4Row4 : One :=
  [1, -40, 564, -3760, 13001, -24960, 32016, -30892, 23682, -14844, 7746, -3372, 1213, -352, 78,
    -12, 1]

private def t4Row5 : One :=
  [-4, 120, -1412, 8432, -27864, 54392, -71344, 69216, -52296, 31464, -15192, 5844, -1744, 384,
    -56, 4]

private def t4Row6 : One :=
  [6, -160, 1722, -9660, 30822, -59364, 76026, -70064, 48732, -26040, 10654, -3264, 708, -96, 6]

private def t4Row7 : One :=
  [-4, 100, -1020, 5484, -16948, 31704, -38600, 32516, -19716, 8704, -2736, 576, -72, 4]

private def t4Row8 : One :=
  [1, -24, 236, -1228, 3678, -6612, 7490, -5532, 2701, -864, 174, -20, 1]

def T4Data : Two :=
  [t4Row0, t4Row1, t4Row2, t4Row3, t4Row4, t4Row5, t4Row6, t4Row7, t4Row8]

private def t5Row0 : One :=
  [0, 0, 0, 0, 0, 1]

private def t5Row1 : One :=
  [0, 0, 0, 0, 5, -35, 30, -15, 5]

private def t5Row2 : One :=
  [0, 0, 0, 10, -145, 640, -925, 805, -500, 210, -60, 10]

private def t5Row3 : One :=
  [0, 0, 10, -230, 1910, -7100, 12690, -14590, 12360, -7990, 4010, -1560, 450, -90, 10]

private def t5Row4 : One :=
  [0, 5, -170, 2200, -14060, 48275, -95390, 128110, -129930, 104530, -68460, 37020, -16530,
    6035, -1760, 390, -60, 5]

private def t5Row5 : One :=
  [1, -55, 1090, -10775, 59690, -195987, 405370, -590215, 658335, -591570, 441366, -278980,
    151195, -70645, 28450, -9793, 2830, -665, 120, -15, 1]

private def t5Row6 : One :=
  [-5, 200, -3245, 28115, -143805, 457540, -955885, 1423815, -1620050, 1473400, -1100360,
    685480, -358775, 157640, -57655, 17235, -4075, 720, -85, 5]

private def t5Row7 : One :=
  [10, -350, 5130, -41220, 200380, -620500, 1284360, -1896260, 2115470, -1857370, 1314920,
    -759690, 359140, -137970, 42300, -10010, 1720, -190, 10]

private def t5Row8 : One :=
  [-10, 325, -4480, 34270, -160540, 484400, -982280, 1410620, -1505130, 1236795, -799590,
    409910, -165970, 52195, -12310, 2040, -210, 10]

private def t5Row9 : One :=
  [5, -155, 2050, -15135, 68815, -202290, 398810, -549480, 549395, -410225, 232570, -100285,
    32390, -7565, 1200, -115, 5]

private def t5Row10 : One :=
  [-1, 30, -385, 2765, -12250, 35056, -66780, 87210, -79955, 52220, -24395, 8085, -1855, 280,
    -25, 1]

def T5Data : Two :=
  [t5Row0, t5Row1, t5Row2, t5Row3, t5Row4, t5Row5, t5Row6, t5Row7, t5Row8, t5Row9, t5Row10]


end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
