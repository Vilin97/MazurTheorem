/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataMidLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataMidHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificateDataHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataMidLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataMidHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialReducedDataHigh
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Direct raw certificate for Brunault's order-twenty-five polynomial

This leaf checks an exact polynomial division after substituting the raw
Lécacheux coordinates `x₀` and `x₂` into Brunault's equation.  The generated
quotient is only data: the local dense-polynomial evaluator proves that list
arithmetic agrees with evaluation, and `closed_coefficient_certificate` asks
Lean to check every integer coefficient of the identity.

Factoring the visibly common factor `B²D²E²T` keeps the checked quotient to a
`73 × 106` matrix.  The public theorem retains every nonvanishing hypothesis
used to identify the raw cross-ratios with the simplified factor formulas.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRawOrbitFactorCertificate

private def neg (p : Two) : Two :=
  Two.mul [[-1]] p

private def sub (p q : Two) : Two :=
  Two.add p (neg q)

private def pow (p : Two) : ℕ → Two
  | 0 => [[1]]
  | n + 1 => Two.mul p (pow p n)

private def product : List Two → Two
  | [] => [[1]]
  | p :: ps => Two.mul p (product ps)

private def sum : List Two → Two
  | [] => []
  | p :: ps => Two.add p (sum ps)

private def scaledProduct (z : ℤ) (ps : List Two) : Two :=
  Two.mul [[z]] (product ps)

private theorem eval_neg (p : Two) (r s : ℚ) :
    Two.eval (neg p) r s = -Two.eval p r s := by
  rw [neg, Two.eval_mul]
  norm_num [Two.eval, One.eval, evalWith]

private theorem eval_sub (p q : Two) (r s : ℚ) :
    Two.eval (sub p q) r s = Two.eval p r s - Two.eval q r s := by
  rw [sub, Two.eval_add, eval_neg]
  ring

private theorem eval_pow (p : Two) (r s : ℚ) : ∀ n,
    Two.eval (pow p n) r s = Two.eval p r s ^ n := by
  intro n
  induction n with
  | zero => simp [pow, Two.eval, One.eval, evalWith]
  | succ n ih =>
      simp only [pow, Two.eval_mul, ih, pow_succ]
      ring

private theorem eval_product (ps : List Two) (r s : ℚ) :
    Two.eval (product ps) r s =
      (ps.map (fun p => Two.eval p r s)).prod := by
  induction ps with
  | nil => simp [product, Two.eval, One.eval, evalWith]
  | cons p ps ih =>
      simp only [product, Two.eval_mul, List.map_cons, List.prod_cons, ih]

private theorem eval_sum (ps : List Two) (r s : ℚ) :
    Two.eval (sum ps) r s =
      (ps.map (fun p => Two.eval p r s)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [sum, Two.eval_add, List.map_cons, List.sum_cons, ih]

private theorem eval_scaledProduct (z : ℤ) (ps : List Two) (r s : ℚ) :
    Two.eval (scaledProduct z ps) r s =
      (z : ℚ) * (ps.map (fun p => Two.eval p r s)).prod := by
  rw [scaledProduct, Two.eval_mul, eval_product]
  simp [Two.eval, One.eval, evalWith]

private def rPolynomial : Two :=
  [[], [1]]

private def sPolynomial : Two :=
  [[0, 1]]

private def aPolynomial : Two :=
  [[0, -1], [1]]

private def bPolynomial : Two :=
  [[-1, 1]]

private def cPolynomial : Two :=
  [[1], [-2, 1]]

private def kPolynomial : Two :=
  [[-1, 1, -1], [1]]

private def dPolynomial : Two :=
  [[0, 1], [0, -4, 3, -1], [1]]

private def ePolynomial : Two :=
  [[-1, 0, -1], [3, 1], [-3, 1]]

private def gPolynomial : Two :=
  [[0, 0, 1], [1, -3, 1]]

private def lPolynomial : Two :=
  [[0, 0, 0, -1], [1, -3, 6, -1], [-2, 4, -9, 5, -1], [1]]

private def jPolynomial : Two :=
  [[0, 0, 0, 0, 1], [1, -3, 6, -10, 4, -1], [-2, 2, 3],
    [2, -4, 1]]

private def tPolynomial : Two :=
  [[0, 1], [1, -7, 6, -3, 1], [-1, 6, -5, 1]]

private def mPolynomial : Two :=
  [[0, 0, 1, 1, 1], [0, 0, -8, -5, 1], [0, 0, 28, -11, 1],
    [1, -8, -19, 20, -7, 1], [-1, 9, -6, 1]]

private def nPolynomial : Two :=
  sub (product [rPolynomial, aPolynomial, pow kPolynomial 3])
    (product [sPolynomial, pow cPolynomial 3, gPolynomial])

private def p9Polynomial : Two :=
  sub (product [pow dPolynomial 3, lPolynomial])
    (product [rPolynomial, sPolynomial, pow bPolynomial 3, gPolynomial,
      pow ePolynomial 3])

private def sutherlandPolynomial : Two :=
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

private def quotientPolynomial : Two :=
  [quotientRow0, quotientRow1, quotientRow2, quotientRow3, quotientRow4,
    quotientRow5, quotientRow6, quotientRow7, quotientRow8, quotientRow9,
    quotientRow10, quotientRow11, quotientRow12, quotientRow13, quotientRow14,
    quotientRow15, quotientRow16, quotientRow17, quotientRow18, quotientRow19,
    quotientRow20, quotientRow21, quotientRow22, quotientRow23, quotientRow24,
    quotientRow25, quotientRow26, quotientRow27, quotientRow28, quotientRow29,
    quotientRow30, quotientRow31, quotientRow32, quotientRow33, quotientRow34,
    quotientRow35, quotientRow36, quotientRow37, quotientRow38, quotientRow39,
    quotientRow40, quotientRow41, quotientRow42, quotientRow43, quotientRow44,
    quotientRow45, quotientRow46, quotientRow47, quotientRow48, quotientRow49,
    quotientRow50, quotientRow51, quotientRow52, quotientRow53, quotientRow54,
    quotientRow55, quotientRow56, quotientRow57, quotientRow58, quotientRow59,
    quotientRow60, quotientRow61, quotientRow62, quotientRow63, quotientRow64,
    quotientRow65, quotientRow66, quotientRow67, quotientRow68, quotientRow69,
    quotientRow70, quotientRow71, quotientRow72]

/-- The cleared numerator after removing the common factor `B²D²E²T`. -/
def reducedNumerator (r s : ℚ) : ℚ :=
  A r s ^ 4 * L r s ^ 4 * T r s ^ 5 * r ^ 2 * K r s ^ 6 *
      M r s ^ 2 * N r s ^ 2 * s ^ 2 * C r s ^ 6 * J r s ^ 2 *
      P9 r s ^ 2 +
    r ^ 3 * K r s ^ 9 * M r s ^ 3 * N r s ^ 3 * A r s ^ 3 *
      L r s ^ 3 * s * C r s ^ 3 * J r s * P9 r s * B r s ^ 2 *
      D r s * E r s ^ 2 * T r s ^ 5 -
    r ^ 2 * K r s ^ 6 * M r s ^ 2 * N r s ^ 2 * A r s ^ 3 *
      L r s ^ 3 * s ^ 2 * C r s ^ 6 * J r s ^ 2 * P9 r s ^ 2 *
      B r s * D r s ^ 2 * E r s * T r s ^ 4 -
    3 * r ^ 3 * K r s ^ 9 * M r s ^ 3 * N r s ^ 3 * A r s ^ 2 *
      L r s ^ 2 * s * C r s ^ 3 * J r s * P9 r s * B r s ^ 3 *
      D r s ^ 3 * E r s ^ 3 * T r s ^ 4 -
    r ^ 2 * K r s ^ 6 * M r s ^ 2 * N r s ^ 2 * A r s ^ 2 *
      L r s ^ 2 * s ^ 2 * C r s ^ 6 * J r s ^ 2 * P9 r s ^ 2 *
      B r s ^ 2 * D r s ^ 4 * E r s ^ 2 * T r s ^ 3 +
    2 * r * K r s ^ 3 * M r s * N r s * A r s ^ 2 * L r s ^ 2 *
      s ^ 3 * C r s ^ 9 * J r s ^ 3 * P9 r s ^ 3 * B r s *
      D r s ^ 5 * E r s * T r s ^ 2 -
    r ^ 4 * K r s ^ 12 * M r s ^ 4 * N r s ^ 4 * A r s * L r s *
      B r s ^ 5 * D r s ^ 4 * E r s ^ 5 * T r s ^ 4 +
    4 * r ^ 2 * K r s ^ 6 * M r s ^ 2 * N r s ^ 2 * A r s * L r s *
      s ^ 2 * C r s ^ 6 * J r s ^ 2 * P9 r s ^ 2 * B r s ^ 3 *
      D r s ^ 6 * E r s ^ 3 * T r s ^ 2 +
    r * K r s ^ 3 * M r s * N r s * A r s * L r s * s ^ 3 *
      C r s ^ 9 * J r s ^ 3 * P9 r s ^ 3 * B r s ^ 2 * D r s ^ 7 *
      E r s ^ 2 * T r s +
    A r s * L r s * s ^ 4 * C r s ^ 12 * J r s ^ 4 * P9 r s ^ 4 *
      B r s * D r s ^ 8 * E r s +
    r ^ 3 * K r s ^ 9 * M r s ^ 3 * N r s ^ 3 * s * C r s ^ 3 *
      J r s * P9 r s * B r s ^ 5 * D r s ^ 7 * E r s ^ 5 * T r s ^ 2

private def termZeroPolynomial : Two :=
  scaledProduct 1 [pow aPolynomial 4, pow lPolynomial 4,
      pow tPolynomial 5, pow rPolynomial 2, pow kPolynomial 6,
      pow mPolynomial 2, pow nPolynomial 2, pow sPolynomial 2,
      pow cPolynomial 6, pow jPolynomial 2, pow p9Polynomial 2]

private def reducedPolynomial : Two :=
  sum [termZeroPolynomial,
    scaledProduct 1 [pow rPolynomial 3, pow kPolynomial 9,
      pow mPolynomial 3, pow nPolynomial 3, pow aPolynomial 3,
      pow lPolynomial 3, sPolynomial, pow cPolynomial 3, jPolynomial,
      p9Polynomial, pow bPolynomial 2, dPolynomial, pow ePolynomial 2,
      pow tPolynomial 5],
    scaledProduct (-1) [pow rPolynomial 2, pow kPolynomial 6,
      pow mPolynomial 2, pow nPolynomial 2, pow aPolynomial 3,
      pow lPolynomial 3, pow sPolynomial 2, pow cPolynomial 6,
      pow jPolynomial 2, pow p9Polynomial 2, bPolynomial,
      pow dPolynomial 2, ePolynomial, pow tPolynomial 4],
    scaledProduct (-3) [pow rPolynomial 3, pow kPolynomial 9,
      pow mPolynomial 3, pow nPolynomial 3, pow aPolynomial 2,
      pow lPolynomial 2, sPolynomial, pow cPolynomial 3, jPolynomial,
      p9Polynomial, pow bPolynomial 3, pow dPolynomial 3,
      pow ePolynomial 3, pow tPolynomial 4],
    scaledProduct (-1) [pow rPolynomial 2, pow kPolynomial 6,
      pow mPolynomial 2, pow nPolynomial 2, pow aPolynomial 2,
      pow lPolynomial 2, pow sPolynomial 2, pow cPolynomial 6,
      pow jPolynomial 2, pow p9Polynomial 2, pow bPolynomial 2,
      pow dPolynomial 4, pow ePolynomial 2, pow tPolynomial 3],
    scaledProduct 2 [rPolynomial, pow kPolynomial 3, mPolynomial,
      nPolynomial, pow aPolynomial 2, pow lPolynomial 2,
      pow sPolynomial 3, pow cPolynomial 9, pow jPolynomial 3,
      pow p9Polynomial 3, bPolynomial, pow dPolynomial 5, ePolynomial,
      pow tPolynomial 2],
    scaledProduct (-1) [pow rPolynomial 4, pow kPolynomial 12,
      pow mPolynomial 4, pow nPolynomial 4, aPolynomial, lPolynomial,
      pow bPolynomial 5, pow dPolynomial 4, pow ePolynomial 5,
      pow tPolynomial 4],
    scaledProduct 4 [pow rPolynomial 2, pow kPolynomial 6,
      pow mPolynomial 2, pow nPolynomial 2, aPolynomial, lPolynomial,
      pow sPolynomial 2, pow cPolynomial 6, pow jPolynomial 2,
      pow p9Polynomial 2, pow bPolynomial 3, pow dPolynomial 6,
      pow ePolynomial 3, pow tPolynomial 2],
    scaledProduct 1 [rPolynomial, pow kPolynomial 3, mPolynomial,
      nPolynomial, aPolynomial, lPolynomial, pow sPolynomial 3,
      pow cPolynomial 9, pow jPolynomial 3, pow p9Polynomial 3,
      pow bPolynomial 2, pow dPolynomial 7, pow ePolynomial 2,
      tPolynomial],
    scaledProduct 1 [aPolynomial, lPolynomial, pow sPolynomial 4,
      pow cPolynomial 12, pow jPolynomial 4, pow p9Polynomial 4,
      bPolynomial, pow dPolynomial 8, ePolynomial],
    scaledProduct 1 [pow rPolynomial 3, pow kPolynomial 9,
      pow mPolynomial 3, pow nPolynomial 3, sPolynomial,
      pow cPolynomial 3, jPolynomial, p9Polynomial, pow bPolynomial 5,
      pow dPolynomial 7, pow ePolynomial 5, pow tPolynomial 2]]

private def certificateProduct : Two :=
  Two.mul sutherlandPolynomial quotientPolynomial

private def reducedData : Two :=
  [
    reducedRow0, reducedRow1, reducedRow2, reducedRow3, reducedRow4, reducedRow5,
    reducedRow6, reducedRow7, reducedRow8, reducedRow9, reducedRow10, reducedRow11,
    reducedRow12, reducedRow13, reducedRow14, reducedRow15, reducedRow16, reducedRow17,
    reducedRow18, reducedRow19, reducedRow20, reducedRow21, reducedRow22, reducedRow23,
    reducedRow24, reducedRow25, reducedRow26, reducedRow27, reducedRow28, reducedRow29,
    reducedRow30, reducedRow31, reducedRow32, reducedRow33, reducedRow34, reducedRow35,
    reducedRow36, reducedRow37, reducedRow38, reducedRow39, reducedRow40, reducedRow41,
    reducedRow42, reducedRow43, reducedRow44, reducedRow45, reducedRow46, reducedRow47,
    reducedRow48, reducedRow49, reducedRow50, reducedRow51, reducedRow52, reducedRow53,
    reducedRow54, reducedRow55, reducedRow56, reducedRow57, reducedRow58, reducedRow59,
    reducedRow60, reducedRow61, reducedRow62, reducedRow63, reducedRow64, reducedRow65,
    reducedRow66, reducedRow67, reducedRow68, reducedRow69, reducedRow70, reducedRow71,
    reducedRow72, reducedRow73, reducedRow74, reducedRow75, reducedRow76, reducedRow77,
    reducedRow78, reducedRow79, reducedRow80, reducedRow81, reducedRow82
  ]

private theorem list_eq_of_length_eq_of_getD_eq (d : α)
    {xs ys : List α} (hlen : xs.length = ys.length)
    (hget : ∀ n, n < xs.length → xs.getD n d = ys.getD n d) :
    xs = ys := by
  apply List.ext_get hlen
  intro n hxs hys
  have h := hget n hxs
  rw [List.getD_eq_get xs d ⟨n, hxs⟩,
    List.getD_eq_get ys d ⟨n, hys⟩] at h
  exact h

private theorem certificateProduct_eq_reducedData :
    certificateProduct = reducedData := by
  apply list_eq_of_length_eq_of_getD_eq []
  · decide
  intro n hn
  interval_cases n <;> decide

private def padOne (n : ℕ) (p : One) : One :=
  p ++ List.replicate (n - p.length) 0

private def rectangularize (outer inner : ℕ) (p : Two) : Two :=
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

private theorem eval_padOne (p : One) (s : ℚ) :
    One.eval (padOne 121 p) s = One.eval p s := by
  exact evalWith_append_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s (121 - p.length) p

private theorem eval_map_padOne (p : Two) (r s : ℚ) :
    evalWith (fun q => One.eval q s) r (p.map (padOne 121)) =
      evalWith (fun q => One.eval q s) r p := by
  induction p with
  | nil => rfl
  | cons q p ih => simp only [List.map_cons, evalWith, eval_padOne, ih]

private theorem eval_zeroRow (s : ℚ) :
    One.eval (List.replicate 121 0) s = 0 := by
  exact evalWith_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s 121

private theorem eval_rectangularize (p : Two) (r s : ℚ) :
    Two.eval (rectangularize 83 121 p) r s = Two.eval p r s := by
  simp only [rectangularize, Two.eval]
  rw [evalWith_append_replicate_zero
    (fun q => One.eval q s) (List.replicate 121 0) (eval_zeroRow s) r]
  exact eval_map_padOne p r s

-- The exact coefficient certificate is inserted below after the two evaluator
-- identifications, which gives a direct normalization experiment a small
-- elaboration surface.

private theorem eval_rPolynomial (r s : ℚ) :
    Two.eval rPolynomial r s = r := by
  simp [rPolynomial, Two.eval, One.eval, evalWith]

private theorem eval_sPolynomial (r s : ℚ) :
    Two.eval sPolynomial r s = s := by
  simp [sPolynomial, Two.eval, One.eval, evalWith]

private theorem eval_aPolynomial (r s : ℚ) :
    Two.eval aPolynomial r s = A r s := by
  simp [aPolynomial, Two.eval, One.eval, evalWith, A]
  ring

private theorem eval_bPolynomial (r s : ℚ) :
    Two.eval bPolynomial r s = B r s := by
  simp [bPolynomial, Two.eval, One.eval, evalWith, B]
  ring

private theorem eval_cPolynomial (r s : ℚ) :
    Two.eval cPolynomial r s = C r s := by
  simp [cPolynomial, Two.eval, One.eval, evalWith, C]
  ring

private theorem eval_kPolynomial (r s : ℚ) :
    Two.eval kPolynomial r s = K r s := by
  simp [kPolynomial, Two.eval, One.eval, evalWith, K]
  ring

private theorem eval_dPolynomial (r s : ℚ) :
    Two.eval dPolynomial r s = D r s := by
  simp [dPolynomial, Two.eval, One.eval, evalWith, D]
  ring

private theorem eval_ePolynomial (r s : ℚ) :
    Two.eval ePolynomial r s = E r s := by
  simp [ePolynomial, Two.eval, One.eval, evalWith, E]
  ring

private theorem eval_gPolynomial (r s : ℚ) :
    Two.eval gPolynomial r s = G r s := by
  simp [gPolynomial, Two.eval, One.eval, evalWith, G]
  ring

private theorem eval_lPolynomial (r s : ℚ) :
    Two.eval lPolynomial r s = L r s := by
  simp [lPolynomial, Two.eval, One.eval, evalWith, L]
  ring

private theorem eval_jPolynomial (r s : ℚ) :
    Two.eval jPolynomial r s = J r s := by
  simp [jPolynomial, Two.eval, One.eval, evalWith, J]
  ring

private theorem eval_tPolynomial (r s : ℚ) :
    Two.eval tPolynomial r s = T r s := by
  simp [tPolynomial, Two.eval, One.eval, evalWith, T]
  ring

private theorem eval_mPolynomial (r s : ℚ) :
    Two.eval mPolynomial r s = M r s := by
  simp [mPolynomial, Two.eval, One.eval, evalWith, M]
  ring

private theorem eval_nPolynomial (r s : ℚ) :
    Two.eval nPolynomial r s = N r s := by
  simp [nPolynomial, eval_sub, eval_product, eval_pow, eval_rPolynomial,
    eval_sPolynomial, eval_aPolynomial, eval_cPolynomial, eval_gPolynomial,
    eval_kPolynomial, N]
  ring

private theorem eval_p9Polynomial (r s : ℚ) :
    Two.eval p9Polynomial r s = P9 r s := by
  simp [p9Polynomial, eval_sub, eval_product, eval_pow, eval_rPolynomial,
    eval_sPolynomial, eval_bPolynomial, eval_dPolynomial, eval_ePolynomial,
    eval_gPolynomial, eval_lPolynomial, P9]
  ring

private theorem eval_reducedPolynomial (r s : ℚ) :
    Two.eval reducedPolynomial r s = reducedNumerator r s := by
  simp [reducedPolynomial, termZeroPolynomial, eval_sum, eval_scaledProduct,
    eval_pow, eval_rPolynomial, eval_sPolynomial, eval_aPolynomial,
    eval_bPolynomial, eval_cPolynomial, eval_kPolynomial, eval_dPolynomial,
    eval_ePolynomial, eval_lPolynomial, eval_jPolynomial, eval_tPolynomial,
    eval_mPolynomial, eval_nPolynomial, eval_p9Polynomial,
    reducedNumerator]
  ring

private theorem eval_sutherlandPolynomial (r s : ℚ) :
    Two.eval sutherlandPolynomial r s =
      orderTwentyFiveRawSutherlandF r s := by
  simp [sutherlandPolynomial, Two.eval, One.eval, evalWith,
    orderTwentyFiveRawSutherlandF]
  ring

private theorem direct_normalization_probe (r s : ℚ) :
    reducedNumerator r s =
      orderTwentyFiveRawSutherlandF r s *
        Two.eval quotientPolynomial r s := by
  simp only [reducedNumerator, A, B, C, K, D, E, G, L, J, T, M, N, P9,
    orderTwentyFiveRawSutherlandF, quotientPolynomial,
+    quotientRow0,
    quotientRow1,
    quotientRow2,
    quotientRow3,
    quotientRow4,
    quotientRow5,
    quotientRow6,
    quotientRow7,
    quotientRow8,
    quotientRow9,
    quotientRow10,
    quotientRow11,
    quotientRow12,
    quotientRow13,
    quotientRow14,
    quotientRow15,
    quotientRow16,
    quotientRow17,
    quotientRow18,
    quotientRow19,
    quotientRow20,
    quotientRow21,
    quotientRow22,
    quotientRow23,
    quotientRow24,
    quotientRow25,
    quotientRow26,
    quotientRow27,
    quotientRow28,
    quotientRow29,
    quotientRow30,
    quotientRow31,
    quotientRow32,
    quotientRow33,
    quotientRow34,
    quotientRow35,
    quotientRow36,
    quotientRow37,
    quotientRow38,
    quotientRow39,
    quotientRow40,
    quotientRow41,
    quotientRow42,
    quotientRow43,
    quotientRow44,
    quotientRow45,
    quotientRow46,
    quotientRow47,
    quotientRow48,
    quotientRow49,
    quotientRow50,
    quotientRow51,
    quotientRow52,
    quotientRow53,
    quotientRow54,
    quotientRow55,
    quotientRow56,
    quotientRow57,
    quotientRow58,
    quotientRow59,
    quotientRow60,
    quotientRow61,
    quotientRow62,
    quotientRow63,
    quotientRow64,
    quotientRow65,
    quotientRow66,
    quotientRow67,
    quotientRow68,
    quotientRow69,
    quotientRow70,
    quotientRow71,
    quotientRow72,
    Two.eval, One.eval, evalWith]
  ring

/-- The reduced cleared numerator vanishes on Sutherland's raw curve. -/
theorem reducedNumerator_eq_zero_of_sutherland (r s : ℚ)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    reducedNumerator r s = 0 := by
  rw [direct_normalization_probe, hF, zero_mul]

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

namespace MazurTorsion.Kubert

open OrderTwentyFiveRawOrbitFactorCertificate

private def orderTwentyFiveRawBrunaultUNumerator (r s : ℚ) : ℚ :=
  -(A r s * L r s * T r s)

private def orderTwentyFiveRawBrunaultUDenominator (r s : ℚ) : ℚ :=
  B r s * D r s ^ 2 * E r s

private def orderTwentyFiveRawBrunaultXTwoNumerator (r s : ℚ) : ℚ :=
  r * B r s * K r s ^ 3 * E r s * T r s * M r s * N r s

private def orderTwentyFiveRawBrunaultXTwoDenominator (r s : ℚ) : ℚ :=
  s * C r s ^ 3 * D r s * J r s * P9 r s

private def orderTwentyFiveRawBrunaultCommonFactor (r s : ℚ) : ℚ :=
  B r s ^ 2 * D r s ^ 2 * E r s ^ 2 * T r s

private def orderTwentyFiveRawBrunaultClearedNumerator
    (uNum uDen vNum vDen : ℚ) : ℚ :=
  vNum ^ 2 * uNum ^ 4 * vDen ^ 2 +
    vNum ^ 3 * uNum ^ 3 * uDen * vDen +
    vNum ^ 2 * uNum ^ 3 * uDen * vDen ^ 2 +
    3 * vNum ^ 3 * uNum ^ 2 * uDen ^ 2 * vDen -
    vNum ^ 2 * uNum ^ 2 * uDen ^ 2 * vDen ^ 2 -
    2 * vNum * uNum ^ 2 * uDen ^ 2 * vDen ^ 3 +
    vNum ^ 4 * uNum * uDen ^ 3 -
    4 * vNum ^ 2 * uNum * uDen ^ 3 * vDen ^ 2 +
    vNum * uNum * uDen ^ 3 * vDen ^ 3 -
    uNum * uDen ^ 3 * vDen ^ 4 -
    vNum ^ 3 * uDen ^ 4 * vDen

private theorem orderTwentyFiveRawBrunault_cleared_identity
    (uNum uDen vNum vDen : ℚ) (huDen : uDen ≠ 0) (hvDen : vDen ≠ 0) :
    uDen ^ 4 * vDen ^ 4 *
        orderTwentyFiveBrunaultPolynomial
          (uNum / uDen) (vNum / vDen) =
      orderTwentyFiveRawBrunaultClearedNumerator
        uNum uDen vNum vDen := by
  simp only [orderTwentyFiveBrunaultPolynomial,
    orderTwentyFiveRawBrunaultClearedNumerator]
  field_simp [huDen, hvDen]
  ring

private theorem orderTwentyFiveRawBrunault_clearedNumerator_eq_factor
    (r s : ℚ) :
    orderTwentyFiveRawBrunaultClearedNumerator
        (orderTwentyFiveRawBrunaultUNumerator r s)
        (orderTwentyFiveRawBrunaultUDenominator r s)
        (-orderTwentyFiveRawBrunaultXTwoNumerator r s)
        (orderTwentyFiveRawBrunaultXTwoDenominator r s) =
      orderTwentyFiveRawBrunaultCommonFactor r s *
        OrderTwentyFiveRawPolynomialCertificate.Internal.reducedNumerator r s := by
  simp only [orderTwentyFiveRawBrunaultClearedNumerator,
    orderTwentyFiveRawBrunaultUNumerator,
    orderTwentyFiveRawBrunaultUDenominator,
    orderTwentyFiveRawBrunaultXTwoNumerator,
    orderTwentyFiveRawBrunaultXTwoDenominator,
    orderTwentyFiveRawBrunaultCommonFactor,
    OrderTwentyFiveRawPolynomialCertificate.Internal.reducedNumerator]
  ring

private theorem orderTwentyFiveRawOrbitXZero_eq_brunaultFraction
    (r s : ℚ) (hr : r ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (hK : K r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitXZero r s =
      orderTwentyFiveRawBrunaultUNumerator r s /
        orderTwentyFiveRawBrunaultUDenominator r s := by
  rw [orderTwentyFiveRawOrbitXZero,
    yOne_eq_factor r s hr hA hB hE hK hYOne,
    yFour_eq_factor r s hB hC hD hE hK hYFour]
  simp only [orderTwentyFiveRawBrunaultUNumerator,
    orderTwentyFiveRawBrunaultUDenominator]
  field_simp [hr, hA, hB, hC, hD, hE, hJ, hK]

private theorem orderTwentyFiveRawOrbitXTwo_eq_brunaultFraction
    (r s : ℚ) (hs : s ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (hK : K r s ≠ 0) (hP9 : P9 r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitXTwo r s =
      orderTwentyFiveRawBrunaultXTwoNumerator r s /
        orderTwentyFiveRawBrunaultXTwoDenominator r s := by
  rw [orderTwentyFiveRawOrbitXTwo,
    yFour_eq_factor r s hB hC hD hE hK hYFour,
    yNine_eq_factor r s hs hA hB hC hD hE hK hYNine]
  simp only [orderTwentyFiveRawBrunaultXTwoNumerator,
    orderTwentyFiveRawBrunaultXTwoDenominator]
  field_simp [hs, hA, hB, hC, hD, hE, hJ, hK, hP9]

/-- Sutherland's raw order-twenty-five equation forces Brunault's polynomial
at the first and third Lécacheux orbit units.  Every hypothesis is a genuine
denominator condition used in the checked cross-ratio simplification. -/
theorem orderTwentyFiveRawOrbit_brunaultPolynomial_eq_zero
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hK : K r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    orderTwentyFiveBrunaultPolynomial
        (orderTwentyFiveRawOrbitXZero r s)
        (-orderTwentyFiveRawOrbitXTwo r s) = 0 := by
  have hJ :=
    j_ne_zero_of_yFourDenominator_ne_zero r s hB hE hK hYFour
  have hP9 :=
    p9_ne_zero_of_yNineDenominator_ne_zero r s hB hD hE hK hYNine
  have huDen : orderTwentyFiveRawBrunaultUDenominator r s ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero hB (pow_ne_zero 2 hD)) hE
  have hxTwoDen : orderTwentyFiveRawBrunaultXTwoDenominator r s ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero hs (pow_ne_zero 3 hC)) hD) hJ) hP9
  rw [orderTwentyFiveRawOrbitXZero_eq_brunaultFraction
      r s hr hA hB hC hD hE hJ hK hYOne hYFour,
    orderTwentyFiveRawOrbitXTwo_eq_brunaultFraction
      r s hs hA hB hC hD hE hJ hK hP9 hYFour hYNine]
  have hreduced :=
    OrderTwentyFiveRawPolynomialCertificate.Internal.reducedNumerator_eq_zero_of_sutherland
      r s hF
  have hcleared :
      orderTwentyFiveRawBrunaultUDenominator r s ^ 4 *
          orderTwentyFiveRawBrunaultXTwoDenominator r s ^ 4 *
          orderTwentyFiveBrunaultPolynomial
            (orderTwentyFiveRawBrunaultUNumerator r s /
              orderTwentyFiveRawBrunaultUDenominator r s)
            (-orderTwentyFiveRawBrunaultXTwoNumerator r s /
              orderTwentyFiveRawBrunaultXTwoDenominator r s) = 0 := by
    rw [orderTwentyFiveRawBrunault_cleared_identity
      (orderTwentyFiveRawBrunaultUNumerator r s)
      (orderTwentyFiveRawBrunaultUDenominator r s)
      (-orderTwentyFiveRawBrunaultXTwoNumerator r s)
      (orderTwentyFiveRawBrunaultXTwoDenominator r s) huDen hxTwoDen]
    rw [orderTwentyFiveRawBrunault_clearedNumerator_eq_factor, hreduced,
      mul_zero]
  have hdenominator :
      orderTwentyFiveRawBrunaultUDenominator r s ^ 4 *
          orderTwentyFiveRawBrunaultXTwoDenominator r s ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 huDen) (pow_ne_zero 4 hxTwoDen)
  simpa only [neg_div] using
    (mul_eq_zero.mp hcleared).resolve_left hdenominator

end MazurTorsion.Kubert
