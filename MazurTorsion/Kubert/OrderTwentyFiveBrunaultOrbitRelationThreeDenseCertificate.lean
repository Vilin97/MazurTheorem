/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
import Mathlib.Tactic.NormNum

/-!
# Dense certificate for the fourth order-twenty-five orbit relation

The internal factor data in this leaf is also the checked input for the
adjacent fifth cyclic relation.  All generated quotient coefficients are
verified by ordinary kernel reduction after the factor-side expression is
cleared of denominators.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

open OrderTwentyFiveRawOrbitFactorCertificate
open OrderTwentyFiveDensePolynomial

namespace Internal

def neg (p : Two) : Two :=
  Two.mul [[-1]] p

def sub (p q : Two) : Two :=
  Two.add p (neg q)

def pow (p : Two) : ℕ → Two
  | 0 => [[1]]
  | n + 1 => Two.mul p (pow p n)

def product : List Two → Two
  | [] => [[1]]
  | p :: ps => Two.mul p (product ps)

theorem eval_neg (p : Two) (r s : ℚ) :
    Two.eval (neg p) r s = -Two.eval p r s := by
  rw [neg, Two.eval_mul]
  norm_num [Two.eval, One.eval, evalWith]

theorem eval_sub (p q : Two) (r s : ℚ) :
    Two.eval (sub p q) r s = Two.eval p r s - Two.eval q r s := by
  rw [sub, Two.eval_add, eval_neg]
  ring

theorem eval_pow (p : Two) (r s : ℚ) : ∀ n,
    Two.eval (pow p n) r s = Two.eval p r s ^ n := by
  intro n
  induction n with
  | zero => simp [pow, Two.eval, One.eval, evalWith]
  | succ n ih =>
      simp only [pow, Two.eval_mul, ih, pow_succ]
      ring

theorem eval_product (ps : List Two) (r s : ℚ) :
    Two.eval (product ps) r s = (ps.map (fun p => Two.eval p r s)).prod := by
  induction ps with
  | nil => simp [product, Two.eval, One.eval, evalWith]
  | cons p ps ih =>
      simp only [product, Two.eval_mul, List.map_cons, List.prod_cons, ih]

def rPolynomial : Two := [[], [1]]
def sPolynomial : Two := [[0, 1]]
def aPolynomial : Two := [[0, -1], [1]]
def bPolynomial : Two := [[-1, 1]]
def cPolynomial : Two := [[1], [-2, 1]]
def kPolynomial : Two := [[-1, 1, -1], [1]]
def dPolynomial : Two := [[0, 1], [0, -4, 3, -1], [1]]
def ePolynomial : Two := [[-1, 0, -1], [3, 1], [-3, 1]]
def gPolynomial : Two := [[0, 0, 1], [1, -3, 1]]
def lPolynomial : Two :=
  [[0, 0, 0, -1], [1, -3, 6, -1], [-2, 4, -9, 5, -1], [1]]
def jPolynomial : Two :=
  [[0, 0, 0, 0, 1],
    [1, -3, 6, -10, 4, -1],
    [-2, 2, 3],
    [2, -4, 1]]
def tPolynomial : Two :=
  [[0, 1], [1, -7, 6, -3, 1], [-1, 6, -5, 1]]
def mPolynomial : Two :=
  [[0, 0, 1, 1, 1], [0, 0, -8, -5, 1], [0, 0, 28, -11, 1],
    [1, -8, -19, 20, -7, 1], [-1, 9, -6, 1]]

def nPolynomial : Two :=
  sub (product [rPolynomial, aPolynomial, pow kPolynomial 3])
    (product [sPolynomial, pow cPolynomial 3, gPolynomial])

def p6Polynomial : Two :=
  sub (product [pow dPolynomial 2, aPolynomial, kPolynomial])
    (product
      [pow cPolynomial 2, sPolynomial, bPolynomial, gPolynomial,
        ePolynomial])

def p9Polynomial : Two :=
  sub (product [pow dPolynomial 3, lPolynomial])
    (product
      [rPolynomial, sPolynomial, pow bPolynomial 3, gPolynomial,
        pow ePolynomial 3])

def yOneNumeratorPolynomial : Two :=
  product [cPolynomial, lPolynomial, jPolynomial]
def yOneDenominatorPolynomial : Two :=
  product
    [rPolynomial, pow bPolynomial 2, pow kPolynomial 2, pow ePolynomial 2]
def yTwoNumeratorPolynomial : Two :=
  neg (product
    [rPolynomial, pow bPolynomial 3, cPolynomial, kPolynomial, mPolynomial])
def yTwoDenominatorPolynomial : Two :=
  product [pow aPolynomial 2, p6Polynomial]
def yFourNumeratorPolynomial : Two :=
  neg (product
    [rPolynomial, aPolynomial, bPolynomial, pow kPolynomial 2,
      ePolynomial, tPolynomial])
def yFourDenominatorPolynomial : Two :=
  product [cPolynomial, pow dPolynomial 2, jPolynomial]
def yEightNumeratorPolynomial : Two :=
  neg (product [aPolynomial, bPolynomial, ePolynomial])
def yEightDenominatorPolynomial : Two := lPolynomial
def yNineNumeratorPolynomial : Two :=
  neg (product [kPolynomial, dPolynomial, mPolynomial, nPolynomial])
def yNineDenominatorPolynomial : Two :=
  product [sPolynomial, aPolynomial, pow cPolynomial 2, p9Polynomial]

def yOneNumerator (r s : ℚ) : ℚ := C r s * L r s * J r s
def yOneDenominator (r s : ℚ) : ℚ :=
  r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2
def yTwoNumerator (r s : ℚ) : ℚ :=
  -(r * B r s ^ 3 * C r s * K r s * M r s)
def yTwoDenominator (r s : ℚ) : ℚ := A r s ^ 2 * P6 r s
def yFourNumerator (r s : ℚ) : ℚ :=
  -(r * A r s * B r s * K r s ^ 2 * E r s * T r s)
def yFourDenominator (r s : ℚ) : ℚ := C r s * D r s ^ 2 * J r s
def yEightNumerator (r s : ℚ) : ℚ := -(A r s * B r s * E r s)
def yEightDenominator (r s : ℚ) : ℚ := L r s
def yNineNumerator (r s : ℚ) : ℚ :=
  -(K r s * D r s * M r s * N r s)
def yNineDenominator (r s : ℚ) : ℚ := s * A r s * C r s ^ 2 * P9 r s

def relationThreePolynomial : Two :=
  sub
    (product
      [sub (Two.mul yEightNumeratorPolynomial yFourDenominatorPolynomial)
          (Two.mul yFourNumeratorPolynomial yEightDenominatorPolynomial),
        yEightDenominatorPolynomial, yTwoDenominatorPolynomial,
        yNineDenominatorPolynomial])
    (product
      [yEightNumeratorPolynomial, yTwoNumeratorPolynomial,
        sub (Two.mul yNineNumeratorPolynomial yEightDenominatorPolynomial)
          (Two.mul yEightNumeratorPolynomial yNineDenominatorPolynomial),
        yFourDenominatorPolynomial])

def clearedRelationThree (r s : ℚ) : ℚ :=
  (yEightNumerator r s * yFourDenominator r s -
      yFourNumerator r s * yEightDenominator r s) *
      yEightDenominator r s * yTwoDenominator r s * yNineDenominator r s -
    yEightNumerator r s * yTwoNumerator r s *
      (yNineNumerator r s * yEightDenominator r s -
        yEightNumerator r s * yNineDenominator r s) *
      yFourDenominator r s

def sutherlandPolynomial : Two :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, -1, 3, -6, 10, -15, 21, -28, 6],
    [0, 0, 0, 15, -45, 75, -91, 96, -126, 266, -231, 126, -56, 21, -6, 1],
    [0, 0, 0, -105, 340, -540, 470, 5, -705, 569, -181, 45, -35, 25, -9, 1],
    [0, 0, 0, 455, -1740, 3435, -4615, 4299, -1623, -433, 609, -165,
      -49, 48, -12, 1],
    [-1, 15, -120, -685, 3660, -8214, 12520, -15060, 12270, -6145,
      1587, 90, -245, 90, -15, 1],
    [5, -70, 555, -388, -2441, 7227, -11195, 14630, -15408, 11834,
      -6558, 2655, -770, 151, -18, 1],
    [-10, 126, -996, 2166, -1551, -789, 1289, -144, -351, 161, -21],
    [10, -105, 840, -2320, 3051, -1659, -185, 690, -345, 74, -6],
    [-5, 35, -294, 968, -1732, 1836, -1205, 494, -123, 17, -1],
    [1]]

def padOne (n : ℕ) (p : One) : One :=
  p ++ List.replicate (n - p.length) 0

def rectangularize (outer inner : ℕ) (p : Two) : Two :=
  p.map (padOne inner) ++
    List.replicate (outer - p.length) (List.replicate inner 0)

private theorem evalWith_replicate_zero (f : α → ℚ) (z : α)
    (hz : f z = 0) (x : ℚ) : ∀ n,
    evalWith f x (List.replicate n z) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change f z + x * evalWith f x (List.replicate n z) = 0
      rw [hz, ih, mul_zero, add_zero]

private theorem evalWith_append_replicate_zero (f : α → ℚ) (z : α)
    (hz : f z = 0) (x : ℚ) (n : ℕ) : ∀ p,
    evalWith f x (p ++ List.replicate n z) = evalWith f x p := by
  intro p
  induction p with
  | nil => exact evalWith_replicate_zero f z hz x n
  | cons a p ih => simp only [List.cons_append, evalWith, ih]

theorem eval_padOne (inner : ℕ) (p : One) (s : ℚ) :
    One.eval (padOne inner p) s = One.eval p s := by
  exact evalWith_append_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s (inner - p.length) p

private theorem eval_map_padOne (inner : ℕ) (p : Two) (r s : ℚ) :
    evalWith (fun q => One.eval q s) r (p.map (padOne inner)) =
      evalWith (fun q => One.eval q s) r p := by
  induction p with
  | nil => rfl
  | cons q p ih => simp only [List.map_cons, evalWith, eval_padOne, ih]

private theorem eval_zeroRow (inner : ℕ) (s : ℚ) :
    One.eval (List.replicate inner 0) s = 0 := by
  exact evalWith_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s inner

theorem eval_rectangularize (outer inner : ℕ) (p : Two) (r s : ℚ) :
    Two.eval (rectangularize outer inner p) r s = Two.eval p r s := by
  simp only [rectangularize, Two.eval]
  rw [evalWith_append_replicate_zero
    (fun q => One.eval q s) (List.replicate inner 0) (eval_zeroRow inner s) r]
  exact eval_map_padOne inner p r s

theorem eval_rPolynomial (r s : ℚ) : Two.eval rPolynomial r s = r := by
  simp [rPolynomial, Two.eval, One.eval, evalWith]
theorem eval_sPolynomial (r s : ℚ) : Two.eval sPolynomial r s = s := by
  simp [sPolynomial, Two.eval, One.eval, evalWith]
theorem eval_aPolynomial (r s : ℚ) : Two.eval aPolynomial r s = A r s := by
  simp [aPolynomial, Two.eval, One.eval, evalWith, A]
  ring
theorem eval_bPolynomial (r s : ℚ) : Two.eval bPolynomial r s = B r s := by
  simp [bPolynomial, Two.eval, One.eval, evalWith, B]
  ring
theorem eval_cPolynomial (r s : ℚ) : Two.eval cPolynomial r s = C r s := by
  simp [cPolynomial, Two.eval, One.eval, evalWith, C]
  ring
theorem eval_kPolynomial (r s : ℚ) : Two.eval kPolynomial r s = K r s := by
  simp [kPolynomial, Two.eval, One.eval, evalWith, K]
  ring
theorem eval_dPolynomial (r s : ℚ) : Two.eval dPolynomial r s = D r s := by
  simp [dPolynomial, Two.eval, One.eval, evalWith, D]
  ring
theorem eval_ePolynomial (r s : ℚ) : Two.eval ePolynomial r s = E r s := by
  simp [ePolynomial, Two.eval, One.eval, evalWith, E]
  ring
theorem eval_gPolynomial (r s : ℚ) : Two.eval gPolynomial r s = G r s := by
  simp [gPolynomial, Two.eval, One.eval, evalWith, G]
  ring
theorem eval_lPolynomial (r s : ℚ) : Two.eval lPolynomial r s = L r s := by
  simp [lPolynomial, Two.eval, One.eval, evalWith, L]
  ring
theorem eval_jPolynomial (r s : ℚ) : Two.eval jPolynomial r s = J r s := by
  simp [jPolynomial, Two.eval, One.eval, evalWith, J]
  ring
theorem eval_tPolynomial (r s : ℚ) : Two.eval tPolynomial r s = T r s := by
  simp [tPolynomial, Two.eval, One.eval, evalWith, T]
  ring
theorem eval_mPolynomial (r s : ℚ) : Two.eval mPolynomial r s = M r s := by
  simp [mPolynomial, Two.eval, One.eval, evalWith, M]
  ring
theorem eval_nPolynomial (r s : ℚ) : Two.eval nPolynomial r s = N r s := by
  simp [nPolynomial, eval_sub, eval_product, eval_pow, eval_rPolynomial,
    eval_sPolynomial, eval_aPolynomial, eval_cPolynomial, eval_gPolynomial,
    eval_kPolynomial, N]
  ring
theorem eval_p6Polynomial (r s : ℚ) : Two.eval p6Polynomial r s = P6 r s := by
  simp [p6Polynomial, eval_sub, eval_product, eval_pow, eval_sPolynomial,
    eval_aPolynomial, eval_bPolynomial, eval_cPolynomial, eval_dPolynomial,
    eval_ePolynomial, eval_gPolynomial, eval_kPolynomial, P6]
  ring
theorem eval_p9Polynomial (r s : ℚ) : Two.eval p9Polynomial r s = P9 r s := by
  simp [p9Polynomial, eval_sub, eval_product, eval_pow, eval_rPolynomial,
    eval_sPolynomial, eval_bPolynomial, eval_dPolynomial, eval_ePolynomial,
    eval_gPolynomial, eval_lPolynomial, P9]
  ring

theorem eval_yOneNumeratorPolynomial (r s : ℚ) :
    Two.eval yOneNumeratorPolynomial r s = yOneNumerator r s := by
  simp [yOneNumeratorPolynomial, yOneNumerator, eval_product,
    eval_cPolynomial, eval_lPolynomial, eval_jPolynomial]
  ring
theorem eval_yOneDenominatorPolynomial (r s : ℚ) :
    Two.eval yOneDenominatorPolynomial r s = yOneDenominator r s := by
  simp [yOneDenominatorPolynomial, yOneDenominator, eval_product, eval_pow,
    eval_rPolynomial, eval_bPolynomial, eval_kPolynomial, eval_ePolynomial]
  ring
theorem eval_yTwoNumeratorPolynomial (r s : ℚ) :
    Two.eval yTwoNumeratorPolynomial r s = yTwoNumerator r s := by
  simp [yTwoNumeratorPolynomial, yTwoNumerator, eval_neg, eval_product,
    eval_pow, eval_rPolynomial, eval_bPolynomial, eval_cPolynomial,
    eval_kPolynomial, eval_mPolynomial]
  ring
theorem eval_yTwoDenominatorPolynomial (r s : ℚ) :
    Two.eval yTwoDenominatorPolynomial r s = yTwoDenominator r s := by
  simp [yTwoDenominatorPolynomial, yTwoDenominator, eval_product, eval_pow,
    eval_aPolynomial, eval_p6Polynomial]
theorem eval_yFourNumeratorPolynomial (r s : ℚ) :
    Two.eval yFourNumeratorPolynomial r s = yFourNumerator r s := by
  simp [yFourNumeratorPolynomial, yFourNumerator, eval_neg, eval_product,
    eval_pow, eval_rPolynomial, eval_aPolynomial, eval_bPolynomial,
    eval_kPolynomial, eval_ePolynomial, eval_tPolynomial]
  ring
theorem eval_yFourDenominatorPolynomial (r s : ℚ) :
    Two.eval yFourDenominatorPolynomial r s = yFourDenominator r s := by
  simp [yFourDenominatorPolynomial, yFourDenominator, eval_product, eval_pow,
    eval_cPolynomial, eval_dPolynomial, eval_jPolynomial]
  ring
theorem eval_yEightNumeratorPolynomial (r s : ℚ) :
    Two.eval yEightNumeratorPolynomial r s = yEightNumerator r s := by
  simp [yEightNumeratorPolynomial, yEightNumerator, eval_neg, eval_product,
    eval_aPolynomial, eval_bPolynomial, eval_ePolynomial]
  ring
theorem eval_yEightDenominatorPolynomial (r s : ℚ) :
    Two.eval yEightDenominatorPolynomial r s = yEightDenominator r s := by
  exact eval_lPolynomial r s
theorem eval_yNineNumeratorPolynomial (r s : ℚ) :
    Two.eval yNineNumeratorPolynomial r s = yNineNumerator r s := by
  simp [yNineNumeratorPolynomial, yNineNumerator, eval_neg, eval_product,
    eval_kPolynomial, eval_dPolynomial, eval_mPolynomial, eval_nPolynomial]
  ring
theorem eval_yNineDenominatorPolynomial (r s : ℚ) :
    Two.eval yNineDenominatorPolynomial r s = yNineDenominator r s := by
  simp [yNineDenominatorPolynomial, yNineDenominator, eval_product, eval_pow,
    eval_sPolynomial, eval_aPolynomial, eval_cPolynomial, eval_p9Polynomial]
  ring

theorem eval_relationThreePolynomial (r s : ℚ) :
    Two.eval relationThreePolynomial r s = clearedRelationThree r s := by
  simp [relationThreePolynomial, clearedRelationThree, eval_sub, eval_product,
    Two.eval_mul, eval_yTwoNumeratorPolynomial,
    eval_yTwoDenominatorPolynomial, eval_yFourNumeratorPolynomial,
    eval_yFourDenominatorPolynomial, eval_yEightNumeratorPolynomial,
    eval_yEightDenominatorPolynomial, eval_yNineNumeratorPolynomial,
    eval_yNineDenominatorPolynomial]
  ring

theorem eval_sutherlandPolynomial (r s : ℚ) :
    Two.eval sutherlandPolynomial r s = orderTwentyFiveRawSutherlandF r s := by
  simp [sutherlandPolynomial, Two.eval, One.eval, evalWith,
    orderTwentyFiveRawSutherlandF]
  ring

end Internal

open Internal

private def quotientPolynomial : Two :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 15, 17, -44, 62,
      -86, 63, -38, 21, -10, 4, -1],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -7, 26, -69, 146, -251, 496, -1267,
      1572, -1497, 1316, -559, 79, 42, -45, 27, -22, 15, -3],
    [0, 0, 0, 0, 0, 0, 1, -12, 33, -4, -202, 681, -1274, 810, 576,
      5194, -12198, 16057, -19749, 16703, -9938, 4721, -1993, 949, -471,
      132, -20, 5, -1],
    [0, 0, 0, 0, 0, -2, -6, 223, -899, 1374, 635, -8045, 21004, -20001,
      -24204, 45071, -28928, 11423, 32982, -68867, 66266, -42038, 18406,
      -5941, 2305, -997, 296, -72, 17, -2],
    [0, 0, 0, 0, 2, 29, -49, -2435, 12980, -29970, 29495, 38916,
      -242760, 489204, -378232, 53723, 181803, -409082, 448103, -246899,
      19500, 91856, -87216, 40391, -11563, 2634, -452, 29, -14, 8, -1],
    [0, 0, 0, -1, -34, -230, 1470, 16414, -119835, 366283, -666098,
      661963, 471558, -3136819, 5075071, -4990572, 3947300, -2030311,
      -155311, 1362773, -1360046, 750117, -196604, -24500, 42143, -19590,
      5724, -865, -22, 24, -2],
    [0, 0, 0, 22, 254, 1618, -20289, -38418, 637888, -2512377, 5965697,
      -10095095, 10551400, -621339, -15028840, 25860128, -30380756,
      28766793, -21014130, 10942783, -3059802, -744760, 1325505, -735631,
      244137, -46730, -848, 3779, -1132, 151, -8],
    [0, 0, 0, -220, -1260, -8105, 163109, -302755, -1498804, 9487461,
      -27972991, 59148612, -92883935, 95000707, -52843909, -2319360,
      46461329, -73852707, 80386248, -67497751, 44467629, -22315265,
      8024177, -1781581, 37353, 162346, -77259, 19508, -2738, 155, 7, -1],
    [0, 0, -4, 1402, 5636, 9771, -767270, 3044203, -2380353, -15564075,
      69501618, -180609698, 351578013, -493297015, 495933249, -378204564,
      228048605, -96241627, 350642, 53477968, -68464234, 56196614,
      -33983559, 15764141, -5717888, 1612144, -337610, 47228, -3259, -114,
      38, -2],
    [0, 0, 85, -7037, -20420, 145132, 1998690, -12551473, 28606429,
      -19783539, -59145413, 268591621, -688702028, 1220602962, -1543098619,
      1485460374, -1175594565, 812331502, -505396327, 281208866, -130424136,
      41523113, -1990984, -7630773, 5896965, -2759747, 939109, -239392,
      45210, -6147, 575, -34, 1],
    [0, -3, -753, 31060, 25031, -974015, -1756330, 28749719, -96441631,
      164547588, -160099127, 4871997, 511432725, -1488457320, 2484070511,
      -2890905697, 2588087074, -1907287422, 1221821054, -717389447,
      399943480, -208550758, 96477176, -37684186, 11983829, -2959201,
      506674, -36056, -8900, 3443, -563, 50, -2],
    [0, 52, 3609, -115720, 203729, 2882940, -5955608, -32813923, 180688147,
      -412533593, 621874709, -783584732, 690780256, 126393446, -1605602796,
      2903550915, -3288232778, 2770926574, -1853904673, 1023921571,
      -489406074, 216163945, -92901506, 38625703, -14809332, 4987817,
      -1419103, 328515, -59345, 7949, -734, 41, -1],
    [-1, -381, -10014, 332716, -1357513, -3950309, 24305310, -8085995,
      -187759005, 599037557, -1042515115, 1507337468, -2077515076,
      2267322942, -1443214925, -141387693, 1535178678, -2081058110,
      1820065001, -1193333588, 613176390, -252008492, 84270874, -23417311,
      5590637, -1224730, 273234, -64792, 14569, -2639, 339, -27, 1],
    [13, 1580, 14534, -694149, 4287924, -1650267, -39027117, 94062029,
      38724916, -526543851, 1112341391, -1537553973, 2090851798,
      -2902302006, 3344764646, -2842375822, 1641329789, -442296361,
      -280048406, 484512373, -387008746, 217654245, -94148593, 32384448,
      -8960910, 1981010, -339489, 42127, -3200, 54, 14, -1],
    [-77, -4092, -833, 995950, -8539352, 18545950, 20180261, -153482007,
      203237829, 169895484, -844181016, 1224589438, -1212286160,
      1342044358, -1802581389, 2155897182, -2026006544, 1494417077,
      -871163445, 391698219, -123494668, 16906325, 8141700, -7148984,
      3107708, -958865, 225902, -41061, 5626, -549, 34, -1],
    [274, 6673, -40304, -874101, 11289890, -40026975, 42021213, 96524617,
      -334004500, 282060740, 297587134, -931354024, 999609084, -591274771,
      244451037, -196044337, 290346334, -339387689, 297678423, -206526696,
      115978471, -52936947, 19629969, -5916488, 1451087, -289141, 46330,
      -5810, 539, -33, 1],
    [-649, -5988, 80558, 245746, -9537638, 48637956, -106159597, 64139514,
      192926402, -467917849, 339016440, 229965662, -741516938, 793930431,
      -493958388, 168513617, 13622893, -68649025, 61980852, -38229818,
      17905221, -6441781, 1766637, -363578, 54681, -5727, 378, -12],
    [1069, 166, -69107, 398207, 4141869, -35022463, 113548886, -185045733,
      99331023, 189438345, -448687994, 401501937, -83073594, -223787218,
      332093370, -276855443, 174653365, -93336107, 44058351, -18116445,
      6238914, -1732786, 376895, -62566, 7690, -667, 37, -1],
    [-1239, 7134, 2185, -496533, 372164, 11934412, -62468600, 156736665,
      -224354393, 160175295, 34274085, -218746807, 267675816, -193563477,
      92336162, -28881271, 5843911, -1404734, 971373, -592291, 229993,
      -58864, 10052, -1107, 71, -2],
    [996, -9724, 56497, 143246, -1259341, 1190697, 11393476, -53062646,
      119308388, -168501639, 157339525, -90907142, 17195808, 23828622,
      -29278614, 18513177, -7889115, 2361297, -475189, 50894, 2400, -1916,
      330, -28, 1],
    [-530, 6538, -57717, 124181, 257407, -1876835, 3832373, -1168808,
      -11719743, 32560867, -49812058, 53062535, -42459587, 26427961,
      -13017023, 5107267, -1593849, 391941, -74517, 10594, -1062, 67, -2],
    [168, -2227, 25672, -110980, 220834, -43243, -957206, 2882829,
      -4840282, 5578800, -4733398, 3056290, -1526858, 593389, -178543,
      40911, -6910, 811, -59, 2],
    [-24, 236, -4276, 26018, -89038, 203881, -332705, 397992, -354616,
      237410, -119643, 45115, -12528, 2485, -333, 27, -1],
    [0, 36, -132, 193, -144, 58, -12, 1]]

def certificateProduct : Two :=
  Two.mul sutherlandPolynomial quotientPolynomial

def leftCertificate : Two :=
  rectangularize 35 48 relationThreePolynomial

def rightCertificate : Two :=
  rectangularize 35 48 certificateProduct

def leftTailOne : Two := leftCertificate.drop 5
def rightTailOne : Two := rightCertificate.drop 5
def leftTailTwo : Two := leftTailOne.drop 5
def rightTailTwo : Two := rightTailOne.drop 5
def leftTailThree : Two := leftTailTwo.drop 5
def rightTailThree : Two := rightTailTwo.drop 5
def leftTailFour : Two := leftTailThree.drop 5
def rightTailFour : Two := rightTailThree.drop 5
def leftTailFive : Two := leftTailFour.drop 5
def rightTailFive : Two := rightTailFour.drop 5
def leftTailSix : Two := leftTailFive.drop 5
def rightTailSix : Two := rightTailFive.drop 5

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
