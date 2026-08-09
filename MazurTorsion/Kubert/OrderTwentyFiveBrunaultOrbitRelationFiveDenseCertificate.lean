/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomial
import Mathlib.Tactic.NormNum

/-!
# Dense certificate for the order-twenty-five norm relation

The factor-side numerator difference is compared with a multiple of
Sutherland's equation as a closed `20 × 29` matrix of integer coefficients.
The small dense evaluator is proved compatible with every arithmetic
operation used below, so the generated matrix equality is checked by Lean's
kernel rather than trusted as an external computation.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFiveDenseCertificate

open OrderTwentyFiveRawOrbitFactorCertificate
open OrderTwentyFiveDensePolynomial

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
    Two.eval (product ps) r s = (ps.map (fun p => Two.eval p r s)).prod := by
  induction ps with
  | nil => simp [product, Two.eval, One.eval, evalWith]
  | cons p ps ih =>
      simp only [product, Two.eval_mul, List.map_cons, List.prod_cons, ih]

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

private def tPolynomial : Two :=
  [[0, 1], [1, -7, 6, -3, 1], [-1, 6, -5, 1]]

private def mPolynomial : Two :=
  [[0, 0, 1, 1, 1], [0, 0, -8, -5, 1], [0, 0, 28, -11, 1],
    [1, -8, -19, 20, -7, 1], [-1, 9, -6, 1]]

private def nPolynomial : Two :=
  sub (product [rPolynomial, aPolynomial, pow kPolynomial 3])
    (product [sPolynomial, pow cPolynomial 3, gPolynomial])

private def p6Polynomial : Two :=
  sub (product [pow dPolynomial 2, aPolynomial, kPolynomial])
    (product
      [pow cPolynomial 2, sPolynomial, bPolynomial, gPolynomial,
        ePolynomial])

private def p9Polynomial : Two :=
  sub (product [pow dPolynomial 3, lPolynomial])
    (product
      [rPolynomial, sPolynomial, pow bPolynomial 3, gPolynomial,
        pow ePolynomial 3])

private def numeratorPolynomial : Two :=
  product
    [rPolynomial, pow bPolynomial 3, pow kPolynomial 2,
      pow mPolynomial 2, nPolynomial, tPolynomial]

private def denominatorPolynomial : Two :=
  product
    [sPolynomial, aPolynomial, cPolynomial, dPolynomial, p6Polynomial,
      p9Polynomial]

private def differencePolynomial : Two :=
  sub numeratorPolynomial denominatorPolynomial

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
  [[0, 0, 0, 0, 0, -1],
    [0, 0, 0, 0, -1, 20, -18, 11, -7, 5, -3, 1],
    [0, 0, -2, 12, -27, -83, 139, -93, 25, 8, -8, 1],
    [0, 0, 18, -111, 314, -78, -368, 547, -419, 201, -57, 10, -1],
    [0, -1, -60, 411, -1383, 1874, -1375, 584, -96, -52, 36, -9, 1],
    [-1, 20, -12, -284, 1532, -2795, 2833, -1909, 934, -332, 82,
      -13, 1],
    [2, -39, 143, -274, -85, 770, -1020, 711, -309, 86, -14, 1],
    [-1, 22, -88, 245, -341, 257, -107, 23, -2],
    [0, -2, 1]]

private def oneSubRPolynomial : Two :=
  [[1], [-1]]

private def certificateProduct : Two :=
  Two.mul sutherlandPolynomial (Two.mul oneSubRPolynomial quotientPolynomial)

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
    One.eval (padOne 29 p) s = One.eval p s := by
  exact evalWith_append_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s (29 - p.length) p

private theorem eval_map_padOne (p : Two) (r s : ℚ) :
    evalWith (fun q => One.eval q s) r (p.map (padOne 29)) =
      evalWith (fun q => One.eval q s) r p := by
  induction p with
  | nil => rfl
  | cons q p ih => simp only [List.map_cons, evalWith, eval_padOne, ih]

private theorem eval_zeroRow (s : ℚ) :
    One.eval (List.replicate 29 0) s = 0 := by
  exact evalWith_replicate_zero (fun z : ℤ => (z : ℚ)) 0
    (by norm_num) s 29

private theorem eval_rectangularize (p : Two) (r s : ℚ) :
    Two.eval (rectangularize 20 29 p) r s = Two.eval p r s := by
  simp only [rectangularize, Two.eval]
  rw [evalWith_append_replicate_zero
    (fun q => One.eval q s) (List.replicate 29 0) (eval_zeroRow s) r]
  exact eval_map_padOne p r s

private theorem closed_coefficient_certificate :
    rectangularize 20 29 differencePolynomial =
      rectangularize 20 29 certificateProduct := by
  decide

private theorem evaluated_coefficient_certificate (r s : ℚ) :
    Two.eval differencePolynomial r s = Two.eval certificateProduct r s := by
  have h := congrArg (fun p => Two.eval p r s) closed_coefficient_certificate
  simpa only [eval_rectangularize] using h

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

private theorem eval_p6Polynomial (r s : ℚ) :
    Two.eval p6Polynomial r s = P6 r s := by
  simp [p6Polynomial, eval_sub, eval_product, eval_pow, eval_sPolynomial,
    eval_aPolynomial, eval_bPolynomial, eval_cPolynomial, eval_dPolynomial,
    eval_ePolynomial, eval_gPolynomial, eval_kPolynomial, P6]
  ring

private theorem eval_p9Polynomial (r s : ℚ) :
    Two.eval p9Polynomial r s = P9 r s := by
  simp [p9Polynomial, eval_sub, eval_product, eval_pow, eval_rPolynomial,
    eval_sPolynomial, eval_bPolynomial, eval_dPolynomial, eval_ePolynomial,
    eval_gPolynomial, eval_lPolynomial, P9]
  ring

private theorem eval_differencePolynomial (r s : ℚ) :
    Two.eval differencePolynomial r s =
      r * B r s ^ 3 * K r s ^ 2 * M r s ^ 2 * N r s * T r s -
        s * A r s * C r s * D r s * P6 r s * P9 r s := by
  simp [differencePolynomial, numeratorPolynomial, denominatorPolynomial,
    eval_sub, eval_product, eval_pow, eval_rPolynomial, eval_sPolynomial,
    eval_aPolynomial, eval_bPolynomial, eval_cPolynomial, eval_dPolynomial,
    eval_kPolynomial, eval_mPolynomial, eval_nPolynomial, eval_p6Polynomial,
    eval_p9Polynomial, eval_tPolynomial]
  ring

private theorem eval_sutherlandPolynomial (r s : ℚ) :
    Two.eval sutherlandPolynomial r s =
      orderTwentyFiveRawSutherlandF r s := by
  simp [sutherlandPolynomial, Two.eval, One.eval, evalWith,
    orderTwentyFiveRawSutherlandF]
  ring

/-- The factor-side numerator difference vanishes on Sutherland's raw
order-twenty-five curve.  This is the checked polynomial step behind the
norm-one orbit relation. -/
theorem clearedProduct_eq_zero_of_sutherland (r s : ℚ)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    r * B r s ^ 3 * K r s ^ 2 * M r s ^ 2 * N r s * T r s -
        s * A r s * C r s * D r s * P6 r s * P9 r s = 0 := by
  have hcertificate := evaluated_coefficient_certificate r s
  rw [eval_differencePolynomial, certificateProduct, Two.eval_mul,
    eval_sutherlandPolynomial, hF, zero_mul] at hcertificate
  exact hcertificate

end MazurTorsion.Kubert.OrderTwentyFiveRelationFiveDenseCertificate
