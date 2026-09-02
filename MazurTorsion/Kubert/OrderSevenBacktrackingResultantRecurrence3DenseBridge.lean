/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseCertificate
import Mathlib.Data.List.GetD

/-!
# Polynomial interpretation of the recurrence 3 dense certificate

This module connects the fixed integer tables in the dense certificate to the
previously checked coefficient formulas.  The comparison is split into small
blocks so every proof stays within Lean's default kernel limits.  The third
recurrence module is the named downstream consumer.
-/

@[expose] public section

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate
namespace IntegerDenseCertificate

noncomputable section

/-- Interpret a little-endian dense integer coefficient list in the polynomial ring. -/
def toPolynomial : List ℤ → Coefficient
  | [] => 0
  | a :: as => C (a : ℚ) + X * toPolynomial as

/-- Dense-list addition is interpreted as polynomial addition. -/
theorem toPolynomial_add (xs ys : List ℤ) :
    toPolynomial (add xs ys) = toPolynomial xs + toPolynomial ys := by
  induction xs generalizing ys with
  | nil => simp [add, toPolynomial]
  | cons x xs ih =>
      cases ys with
      | nil => simp [add, toPolynomial]
      | cons y ys =>
          simp only [add, toPolynomial, ih, Int.cast_add, map_add]
          ring

/-- Dense-list scaling is interpreted as polynomial scaling. -/
theorem toPolynomial_scale (a : ℤ) (xs : List ℤ) :
    toPolynomial (scale a xs) = C (a : ℚ) * toPolynomial xs := by
  induction xs with
  | nil => simp [scale, toPolynomial]
  | cons x xs ih =>
      simp only [scale, toPolynomial, ih, Int.cast_mul, map_mul]
      ring

/-- Dense convolution is interpreted as polynomial multiplication. -/
theorem toPolynomial_mul (xs ys : List ℤ) :
    toPolynomial (mul xs ys) = toPolynomial xs * toPolynomial ys := by
  induction xs with
  | nil => simp [mul, toPolynomial]
  | cons x xs ih =>
      simp only [mul, toPolynomial, toPolynomial_add,
        toPolynomial_scale, ih, Int.cast_zero, map_zero]
      ring

/-- Dense-list negation is interpreted as polynomial negation. -/
theorem toPolynomial_neg (xs : List ℤ) :
    toPolynomial (neg xs) = -toPolynomial xs := by
  simp [neg, toPolynomial_scale]

/-- Dense-list subtraction is interpreted as polynomial subtraction. -/
theorem toPolynomial_sub (xs ys : List ℤ) :
    toPolynomial (sub xs ys) = toPolynomial xs - toPolynomial ys := by
  simp [sub, toPolynomial_add, toPolynomial_neg, sub_eq_add_neg]

/-- Coefficient lookup commutes with dense-list interpretation. -/
theorem coeff_toPolynomial (xs : List ℤ) (n : ℕ) :
    (toPolynomial xs).coeff n = (xs.getD n 0 : ℤ) := by
  induction xs generalizing n with
  | nil => simp [toPolynomial]
  | cons x xs ih =>
      cases n with
      | zero => simp [toPolynomial]
      | succ n =>
          rw [toPolynomial, Polynomial.coeff_add,
            Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, ih]
          simp

attribute [local orderSevenCoefficient]
  recurrence4A0_coeff_0
  recurrence4A1_coeff_0
  recurrence4B0_coeff_0
  recurrence4B1_coeff_0

private theorem a0_prefix0_length :
    (Data.a0Chunk0).length = 16 := by
  rfl

private theorem a0_prefix1_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1).length = 32 := by
  rfl

private theorem a0_prefix2_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2).length = 48 := by
  rfl

private theorem a0_prefix3_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3).length = 64 := by
  rfl

private theorem a0_prefix4_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3
       ++ Data.a0Chunk4).length = 80 := by
  rfl

private theorem a0_prefix5_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3
       ++ Data.a0Chunk4 ++ Data.a0Chunk5).length = 96 := by
  rfl

private theorem a0_prefix6_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3
       ++ Data.a0Chunk4 ++ Data.a0Chunk5
       ++ Data.a0Chunk6).length = 112 := by
  rfl

private theorem a0_prefix7_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3
       ++ Data.a0Chunk4 ++ Data.a0Chunk5
       ++ Data.a0Chunk6 ++ Data.a0Chunk7).length = 128 := by
  rfl

private theorem a0_prefix8_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3
       ++ Data.a0Chunk4 ++ Data.a0Chunk5
       ++ Data.a0Chunk6 ++ Data.a0Chunk7
       ++ Data.a0Chunk8).length = 144 := by
  rfl

private theorem a0_prefix9_length :
    (Data.a0Chunk0 ++ Data.a0Chunk1
       ++ Data.a0Chunk2 ++ Data.a0Chunk3
       ++ Data.a0Chunk4 ++ Data.a0Chunk5
       ++ Data.a0Chunk6 ++ Data.a0Chunk7
       ++ Data.a0Chunk8 ++ Data.a0Chunk9).length = 155 := by
  rfl

private theorem a0_length : Data.a0.length = 155 := by
  unfold Data.a0
  exact a0_prefix9_length

private theorem a0_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.a0Chunk0, orderSevenCoefficient]

private theorem a0_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix0_length]
    omega)]
  rw [a0_prefix0_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk1, orderSevenCoefficient]

private theorem a0_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix1_length]
    omega)]
  rw [a0_prefix1_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk2, orderSevenCoefficient]

private theorem a0_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix2_length]
    omega)]
  rw [a0_prefix2_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk3, orderSevenCoefficient]

private theorem a0_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix3_length]
    omega)]
  rw [a0_prefix3_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk4, orderSevenCoefficient]

private theorem a0_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix4_length]
    omega)]
  rw [a0_prefix4_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk5, orderSevenCoefficient]

private theorem a0_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix5_length]
    omega)]
  rw [a0_prefix5_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk6, orderSevenCoefficient]

private theorem a0_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix6_length]
    omega)]
  rw [a0_prefix6_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk7, orderSevenCoefficient]

private theorem a0_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix7_length]
    omega)]
  rw [a0_prefix7_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk8, orderSevenCoefficient]

private theorem a0_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 155) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  unfold Data.a0
  rw [List.getD_append_right _ _ _ _ (by
    rw [a0_prefix8_length]
    omega)]
  rw [a0_prefix8_length]
  interval_cases n <;>
    norm_num [Data.a0Chunk9, orderSevenCoefficient]

private theorem a0_coeff (n : ℕ) (h : n < 155) :
    ((Data.a0.getD n 0 : ℤ) : ℚ) = remainder3Coefficient0.coeff n := by
  by_cases h0 : n < 16
  · exact a0_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact a0_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact a0_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact a0_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact a0_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact a0_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact a0_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact a0_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact a0_range8 n (by omega) h8
  exact a0_range9 n (by omega) (by omega)

/-- The dense table for the first third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a0 : toPolynomial a0 = remainder3Coefficient0 := by
  ext n
  rw [coeff_toPolynomial]
  unfold a0
  by_cases hn : n < 155
  · exact a0_coeff n hn
  · rw [List.getD_eq_default (l := Data.a0) (d := (0 : ℤ)) (by
      rw [a0_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence2B0_natDegree_le)
      n (by omega)).symm

private theorem a1_prefix0_length :
    (Data.a1Chunk0).length = 16 := by
  rfl

private theorem a1_prefix1_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1).length = 32 := by
  rfl

private theorem a1_prefix2_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2).length = 48 := by
  rfl

private theorem a1_prefix3_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3).length = 64 := by
  rfl

private theorem a1_prefix4_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3
       ++ Data.a1Chunk4).length = 80 := by
  rfl

private theorem a1_prefix5_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3
       ++ Data.a1Chunk4 ++ Data.a1Chunk5).length = 96 := by
  rfl

private theorem a1_prefix6_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3
       ++ Data.a1Chunk4 ++ Data.a1Chunk5
       ++ Data.a1Chunk6).length = 112 := by
  rfl

private theorem a1_prefix7_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3
       ++ Data.a1Chunk4 ++ Data.a1Chunk5
       ++ Data.a1Chunk6 ++ Data.a1Chunk7).length = 128 := by
  rfl

private theorem a1_prefix8_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3
       ++ Data.a1Chunk4 ++ Data.a1Chunk5
       ++ Data.a1Chunk6 ++ Data.a1Chunk7
       ++ Data.a1Chunk8).length = 144 := by
  rfl

private theorem a1_prefix9_length :
    (Data.a1Chunk0 ++ Data.a1Chunk1
       ++ Data.a1Chunk2 ++ Data.a1Chunk3
       ++ Data.a1Chunk4 ++ Data.a1Chunk5
       ++ Data.a1Chunk6 ++ Data.a1Chunk7
       ++ Data.a1Chunk8 ++ Data.a1Chunk9).length = 151 := by
  rfl

private theorem a1_length : Data.a1.length = 151 := by
  unfold Data.a1
  exact a1_prefix9_length

private theorem a1_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.a1Chunk0, orderSevenCoefficient]

private theorem a1_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix0_length]
    omega)]
  rw [a1_prefix0_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk1, orderSevenCoefficient]

private theorem a1_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix1_length]
    omega)]
  rw [a1_prefix1_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk2, orderSevenCoefficient]

private theorem a1_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix2_length]
    omega)]
  rw [a1_prefix2_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk3, orderSevenCoefficient]

private theorem a1_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix3_length]
    omega)]
  rw [a1_prefix3_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk4, orderSevenCoefficient]

private theorem a1_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix4_length]
    omega)]
  rw [a1_prefix4_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk5, orderSevenCoefficient]

private theorem a1_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix5_length]
    omega)]
  rw [a1_prefix5_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk6, orderSevenCoefficient]

private theorem a1_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix6_length]
    omega)]
  rw [a1_prefix6_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk7, orderSevenCoefficient]

private theorem a1_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix7_length]
    omega)]
  rw [a1_prefix7_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk8, orderSevenCoefficient]

private theorem a1_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 151) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  unfold Data.a1
  rw [List.getD_append_right _ _ _ _ (by
    rw [a1_prefix8_length]
    omega)]
  rw [a1_prefix8_length]
  interval_cases n <;>
    norm_num [Data.a1Chunk9, orderSevenCoefficient]

private theorem a1_coeff (n : ℕ) (h : n < 151) :
    ((Data.a1.getD n 0 : ℤ) : ℚ) = remainder3Coefficient1.coeff n := by
  by_cases h0 : n < 16
  · exact a1_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact a1_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact a1_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact a1_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact a1_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact a1_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact a1_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact a1_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact a1_range8 n (by omega) h8
  exact a1_range9 n (by omega) (by omega)

/-- The dense table for the second third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a1 : toPolynomial a1 = remainder3Coefficient1 := by
  ext n
  rw [coeff_toPolynomial]
  unfold a1
  by_cases hn : n < 151
  · exact a1_coeff n hn
  · rw [List.getD_eq_default (l := Data.a1) (d := (0 : ℤ)) (by
      rw [a1_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence2B1_natDegree_le)
      n (by omega)).symm

private theorem a2_prefix0_length :
    (Data.a2Chunk0).length = 16 := by
  rfl

private theorem a2_prefix1_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1).length = 32 := by
  rfl

private theorem a2_prefix2_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2).length = 48 := by
  rfl

private theorem a2_prefix3_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3).length = 64 := by
  rfl

private theorem a2_prefix4_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3
       ++ Data.a2Chunk4).length = 80 := by
  rfl

private theorem a2_prefix5_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3
       ++ Data.a2Chunk4 ++ Data.a2Chunk5).length = 96 := by
  rfl

private theorem a2_prefix6_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3
       ++ Data.a2Chunk4 ++ Data.a2Chunk5
       ++ Data.a2Chunk6).length = 112 := by
  rfl

private theorem a2_prefix7_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3
       ++ Data.a2Chunk4 ++ Data.a2Chunk5
       ++ Data.a2Chunk6 ++ Data.a2Chunk7).length = 128 := by
  rfl

private theorem a2_prefix8_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3
       ++ Data.a2Chunk4 ++ Data.a2Chunk5
       ++ Data.a2Chunk6 ++ Data.a2Chunk7
       ++ Data.a2Chunk8).length = 144 := by
  rfl

private theorem a2_prefix9_length :
    (Data.a2Chunk0 ++ Data.a2Chunk1
       ++ Data.a2Chunk2 ++ Data.a2Chunk3
       ++ Data.a2Chunk4 ++ Data.a2Chunk5
       ++ Data.a2Chunk6 ++ Data.a2Chunk7
       ++ Data.a2Chunk8 ++ Data.a2Chunk9).length = 147 := by
  rfl

private theorem a2_length : Data.a2.length = 147 := by
  unfold Data.a2
  exact a2_prefix9_length

private theorem a2_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.a2Chunk0, orderSevenCoefficient]

private theorem a2_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix0_length]
    omega)]
  rw [a2_prefix0_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk1, orderSevenCoefficient]

private theorem a2_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix1_length]
    omega)]
  rw [a2_prefix1_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk2, orderSevenCoefficient]

private theorem a2_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix2_length]
    omega)]
  rw [a2_prefix2_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk3, orderSevenCoefficient]

private theorem a2_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix3_length]
    omega)]
  rw [a2_prefix3_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk4, orderSevenCoefficient]

private theorem a2_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix4_length]
    omega)]
  rw [a2_prefix4_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk5, orderSevenCoefficient]

private theorem a2_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix5_length]
    omega)]
  rw [a2_prefix5_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk6, orderSevenCoefficient]

private theorem a2_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix6_length]
    omega)]
  rw [a2_prefix6_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk7, orderSevenCoefficient]

private theorem a2_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix7_length]
    omega)]
  rw [a2_prefix7_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk8, orderSevenCoefficient]

private theorem a2_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 147) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  unfold Data.a2
  rw [List.getD_append_right _ _ _ _ (by
    rw [a2_prefix8_length]
    omega)]
  rw [a2_prefix8_length]
  interval_cases n <;>
    norm_num [Data.a2Chunk9, orderSevenCoefficient]

private theorem a2_coeff (n : ℕ) (h : n < 147) :
    ((Data.a2.getD n 0 : ℤ) : ℚ) = remainder3Coefficient2.coeff n := by
  by_cases h0 : n < 16
  · exact a2_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact a2_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact a2_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact a2_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact a2_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact a2_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact a2_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact a2_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact a2_range8 n (by omega) h8
  exact a2_range9 n (by omega) (by omega)

/-- The dense table for the third third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a2 : toPolynomial a2 = remainder3Coefficient2 := by
  ext n
  rw [coeff_toPolynomial]
  unfold a2
  by_cases hn : n < 147
  · exact a2_coeff n hn
  · rw [List.getD_eq_default (l := Data.a2) (d := (0 : ℤ)) (by
      rw [a2_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence2B2_natDegree_le)
      n (by omega)).symm

private theorem a3_prefix0_length :
    (Data.a3Chunk0).length = 16 := by
  rfl

private theorem a3_prefix1_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1).length = 32 := by
  rfl

private theorem a3_prefix2_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2).length = 48 := by
  rfl

private theorem a3_prefix3_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2 ++ Data.a3Chunk3).length = 64 := by
  rfl

private theorem a3_prefix4_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2 ++ Data.a3Chunk3
       ++ Data.a3Chunk4).length = 80 := by
  rfl

private theorem a3_prefix5_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2 ++ Data.a3Chunk3
       ++ Data.a3Chunk4 ++ Data.a3Chunk5).length = 96 := by
  rfl

private theorem a3_prefix6_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2 ++ Data.a3Chunk3
       ++ Data.a3Chunk4 ++ Data.a3Chunk5
       ++ Data.a3Chunk6).length = 112 := by
  rfl

private theorem a3_prefix7_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2 ++ Data.a3Chunk3
       ++ Data.a3Chunk4 ++ Data.a3Chunk5
       ++ Data.a3Chunk6 ++ Data.a3Chunk7).length = 128 := by
  rfl

private theorem a3_prefix8_length :
    (Data.a3Chunk0 ++ Data.a3Chunk1
       ++ Data.a3Chunk2 ++ Data.a3Chunk3
       ++ Data.a3Chunk4 ++ Data.a3Chunk5
       ++ Data.a3Chunk6 ++ Data.a3Chunk7
       ++ Data.a3Chunk8).length = 143 := by
  rfl

private theorem a3_length : Data.a3.length = 143 := by
  unfold Data.a3
  exact a3_prefix8_length

private theorem a3_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.a3Chunk0, orderSevenCoefficient]

private theorem a3_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix0_length]
    omega)]
  rw [a3_prefix0_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk1, orderSevenCoefficient]

private theorem a3_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix1_length]
    omega)]
  rw [a3_prefix1_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk2, orderSevenCoefficient]

private theorem a3_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix2_length]
    omega)]
  rw [a3_prefix2_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk3, orderSevenCoefficient]

private theorem a3_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix3_length]
    omega)]
  rw [a3_prefix3_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk4, orderSevenCoefficient]

private theorem a3_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix4_length]
    omega)]
  rw [a3_prefix4_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk5, orderSevenCoefficient]

private theorem a3_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix5_length]
    omega)]
  rw [a3_prefix5_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk6, orderSevenCoefficient]

private theorem a3_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix6_length]
    omega)]
  rw [a3_prefix6_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk7, orderSevenCoefficient]

private theorem a3_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 143) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  unfold Data.a3
  rw [List.getD_append_right _ _ _ _ (by
    rw [a3_prefix7_length]
    omega)]
  rw [a3_prefix7_length]
  interval_cases n <;>
    norm_num [Data.a3Chunk8, orderSevenCoefficient]

private theorem a3_coeff (n : ℕ) (h : n < 143) :
    ((Data.a3.getD n 0 : ℤ) : ℚ) = remainder3Coefficient3.coeff n := by
  by_cases h0 : n < 16
  · exact a3_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact a3_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact a3_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact a3_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact a3_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact a3_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact a3_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact a3_range7 n (by omega) h7
  exact a3_range8 n (by omega) (by omega)

/-- The dense table for the fourth third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a3 : toPolynomial a3 = remainder3Coefficient3 := by
  ext n
  rw [coeff_toPolynomial]
  unfold a3
  by_cases hn : n < 143
  · exact a3_coeff n hn
  · rw [List.getD_eq_default (l := Data.a3) (d := (0 : ℤ)) (by
      rw [a3_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence2B3_natDegree_le)
      n (by omega)).symm

private theorem a4_prefix0_length :
    (Data.a4Chunk0).length = 16 := by
  rfl

private theorem a4_prefix1_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1).length = 32 := by
  rfl

private theorem a4_prefix2_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2).length = 48 := by
  rfl

private theorem a4_prefix3_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2 ++ Data.a4Chunk3).length = 64 := by
  rfl

private theorem a4_prefix4_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2 ++ Data.a4Chunk3
       ++ Data.a4Chunk4).length = 80 := by
  rfl

private theorem a4_prefix5_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2 ++ Data.a4Chunk3
       ++ Data.a4Chunk4 ++ Data.a4Chunk5).length = 96 := by
  rfl

private theorem a4_prefix6_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2 ++ Data.a4Chunk3
       ++ Data.a4Chunk4 ++ Data.a4Chunk5
       ++ Data.a4Chunk6).length = 112 := by
  rfl

private theorem a4_prefix7_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2 ++ Data.a4Chunk3
       ++ Data.a4Chunk4 ++ Data.a4Chunk5
       ++ Data.a4Chunk6 ++ Data.a4Chunk7).length = 128 := by
  rfl

private theorem a4_prefix8_length :
    (Data.a4Chunk0 ++ Data.a4Chunk1
       ++ Data.a4Chunk2 ++ Data.a4Chunk3
       ++ Data.a4Chunk4 ++ Data.a4Chunk5
       ++ Data.a4Chunk6 ++ Data.a4Chunk7
       ++ Data.a4Chunk8).length = 139 := by
  rfl

private theorem a4_length : Data.a4.length = 139 := by
  unfold Data.a4
  exact a4_prefix8_length

private theorem a4_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.a4Chunk0, orderSevenCoefficient]

private theorem a4_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix0_length]
    omega)]
  rw [a4_prefix0_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk1, orderSevenCoefficient]

private theorem a4_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix1_length]
    omega)]
  rw [a4_prefix1_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk2, orderSevenCoefficient]

private theorem a4_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix2_length]
    omega)]
  rw [a4_prefix2_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk3, orderSevenCoefficient]

private theorem a4_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix3_length]
    omega)]
  rw [a4_prefix3_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk4, orderSevenCoefficient]

private theorem a4_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix4_length]
    omega)]
  rw [a4_prefix4_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk5, orderSevenCoefficient]

private theorem a4_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix5_length]
    omega)]
  rw [a4_prefix5_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk6, orderSevenCoefficient]

private theorem a4_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix6_length]
    omega)]
  rw [a4_prefix6_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk7, orderSevenCoefficient]

private theorem a4_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 139) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  unfold Data.a4
  rw [List.getD_append_right _ _ _ _ (by
    rw [a4_prefix7_length]
    omega)]
  rw [a4_prefix7_length]
  interval_cases n <;>
    norm_num [Data.a4Chunk8, orderSevenCoefficient]

private theorem a4_coeff (n : ℕ) (h : n < 139) :
    ((Data.a4.getD n 0 : ℤ) : ℚ) = remainder3Coefficient4.coeff n := by
  by_cases h0 : n < 16
  · exact a4_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact a4_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact a4_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact a4_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact a4_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact a4_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact a4_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact a4_range7 n (by omega) h7
  exact a4_range8 n (by omega) (by omega)

/-- The dense table for the fifth third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a4 : toPolynomial a4 = remainder3Coefficient4 := by
  ext n
  rw [coeff_toPolynomial]
  unfold a4
  by_cases hn : n < 139
  · exact a4_coeff n hn
  · rw [List.getD_eq_default (l := Data.a4) (d := (0 : ℤ)) (by
      rw [a4_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence2B4_natDegree_le)
      n (by omega)).symm

private theorem a5_prefix0_length :
    (Data.a5Chunk0).length = 16 := by
  rfl

private theorem a5_prefix1_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1).length = 32 := by
  rfl

private theorem a5_prefix2_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2).length = 48 := by
  rfl

private theorem a5_prefix3_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2 ++ Data.a5Chunk3).length = 64 := by
  rfl

private theorem a5_prefix4_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2 ++ Data.a5Chunk3
       ++ Data.a5Chunk4).length = 80 := by
  rfl

private theorem a5_prefix5_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2 ++ Data.a5Chunk3
       ++ Data.a5Chunk4 ++ Data.a5Chunk5).length = 96 := by
  rfl

private theorem a5_prefix6_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2 ++ Data.a5Chunk3
       ++ Data.a5Chunk4 ++ Data.a5Chunk5
       ++ Data.a5Chunk6).length = 112 := by
  rfl

private theorem a5_prefix7_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2 ++ Data.a5Chunk3
       ++ Data.a5Chunk4 ++ Data.a5Chunk5
       ++ Data.a5Chunk6 ++ Data.a5Chunk7).length = 128 := by
  rfl

private theorem a5_prefix8_length :
    (Data.a5Chunk0 ++ Data.a5Chunk1
       ++ Data.a5Chunk2 ++ Data.a5Chunk3
       ++ Data.a5Chunk4 ++ Data.a5Chunk5
       ++ Data.a5Chunk6 ++ Data.a5Chunk7
       ++ Data.a5Chunk8).length = 135 := by
  rfl

private theorem a5_length : Data.a5.length = 135 := by
  unfold Data.a5
  exact a5_prefix8_length

private theorem a5_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.a5Chunk0, orderSevenCoefficient]

private theorem a5_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix0_length]
    omega)]
  rw [a5_prefix0_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk1, orderSevenCoefficient]

private theorem a5_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix1_length]
    omega)]
  rw [a5_prefix1_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk2, orderSevenCoefficient]

private theorem a5_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix2_length]
    omega)]
  rw [a5_prefix2_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk3, orderSevenCoefficient]

private theorem a5_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix3_length]
    omega)]
  rw [a5_prefix3_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk4, orderSevenCoefficient]

private theorem a5_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix4_length]
    omega)]
  rw [a5_prefix4_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk5, orderSevenCoefficient]

private theorem a5_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix5_length]
    omega)]
  rw [a5_prefix5_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk6, orderSevenCoefficient]

private theorem a5_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix6_length]
    omega)]
  rw [a5_prefix6_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk7, orderSevenCoefficient]

private theorem a5_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 135) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  unfold Data.a5
  rw [List.getD_append_right _ _ _ _ (by
    rw [a5_prefix7_length]
    omega)]
  rw [a5_prefix7_length]
  interval_cases n <;>
    norm_num [Data.a5Chunk8, orderSevenCoefficient]

private theorem a5_coeff (n : ℕ) (h : n < 135) :
    ((Data.a5.getD n 0 : ℤ) : ℚ) = remainder3Coefficient5.coeff n := by
  by_cases h0 : n < 16
  · exact a5_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact a5_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact a5_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact a5_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact a5_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact a5_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact a5_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact a5_range7 n (by omega) h7
  exact a5_range8 n (by omega) (by omega)

/-- The dense table for the sixth third-remainder coefficient has its intended meaning. -/
theorem toPolynomial_a5 : toPolynomial a5 = remainder3Coefficient5 := by
  ext n
  rw [coeff_toPolynomial]
  unfold a5
  by_cases hn : n < 135
  · exact a5_coeff n hn
  · rw [List.getD_eq_default (l := Data.a5) (d := (0 : ℤ)) (by
      rw [a5_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence2B5_natDegree_le)
      n (by omega)).symm

private theorem b0_prefix0_length :
    (Data.b0Chunk0).length = 16 := by
  rfl

private theorem b0_prefix1_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1).length = 32 := by
  rfl

private theorem b0_prefix2_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2).length = 48 := by
  rfl

private theorem b0_prefix3_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3).length = 64 := by
  rfl

private theorem b0_prefix4_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4).length = 80 := by
  rfl

private theorem b0_prefix5_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5).length = 96 := by
  rfl

private theorem b0_prefix6_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6).length = 112 := by
  rfl

private theorem b0_prefix7_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6 ++ Data.b0Chunk7).length = 128 := by
  rfl

private theorem b0_prefix8_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6 ++ Data.b0Chunk7
       ++ Data.b0Chunk8).length = 144 := by
  rfl

private theorem b0_prefix9_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6 ++ Data.b0Chunk7
       ++ Data.b0Chunk8 ++ Data.b0Chunk9).length = 160 := by
  rfl

private theorem b0_prefix10_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6 ++ Data.b0Chunk7
       ++ Data.b0Chunk8 ++ Data.b0Chunk9
       ++ Data.b0Chunk10).length = 176 := by
  rfl

private theorem b0_prefix11_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6 ++ Data.b0Chunk7
       ++ Data.b0Chunk8 ++ Data.b0Chunk9
       ++ Data.b0Chunk10 ++ Data.b0Chunk11).length = 192 := by
  rfl

private theorem b0_prefix12_length :
    (Data.b0Chunk0 ++ Data.b0Chunk1
       ++ Data.b0Chunk2 ++ Data.b0Chunk3
       ++ Data.b0Chunk4 ++ Data.b0Chunk5
       ++ Data.b0Chunk6 ++ Data.b0Chunk7
       ++ Data.b0Chunk8 ++ Data.b0Chunk9
       ++ Data.b0Chunk10 ++ Data.b0Chunk11
       ++ Data.b0Chunk12).length = 195 := by
  rfl

private theorem b0_length : Data.b0.length = 195 := by
  unfold Data.b0
  exact b0_prefix12_length

private theorem b0_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.b0Chunk0, orderSevenCoefficient]

private theorem b0_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix0_length]
    omega)]
  rw [b0_prefix0_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk1, orderSevenCoefficient]

private theorem b0_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix1_length]
    omega)]
  rw [b0_prefix1_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk2, orderSevenCoefficient]

private theorem b0_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix2_length]
    omega)]
  rw [b0_prefix2_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk3, orderSevenCoefficient]

private theorem b0_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix3_length]
    omega)]
  rw [b0_prefix3_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk4, orderSevenCoefficient]

private theorem b0_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix4_length]
    omega)]
  rw [b0_prefix4_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk5, orderSevenCoefficient]

private theorem b0_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix5_length]
    omega)]
  rw [b0_prefix5_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk6, orderSevenCoefficient]

private theorem b0_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix6_length]
    omega)]
  rw [b0_prefix6_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk7, orderSevenCoefficient]

private theorem b0_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix7_length]
    omega)]
  rw [b0_prefix7_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk8, orderSevenCoefficient]

private theorem b0_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix8_length]
    omega)]
  rw [b0_prefix8_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk9, orderSevenCoefficient]

private theorem b0_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 176) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix9_length]
    omega)]
  rw [b0_prefix9_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk10, orderSevenCoefficient]

private theorem b0_range11 (n : ℕ) (hlo : 176 ≤ n) (hhi : n < 192) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix10_length]
    omega)]
  rw [b0_prefix10_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk11, orderSevenCoefficient]

private theorem b0_range12 (n : ℕ) (hlo : 192 ≤ n) (hhi : n < 195) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  unfold Data.b0
  rw [List.getD_append_right _ _ _ _ (by
    rw [b0_prefix11_length]
    omega)]
  rw [b0_prefix11_length]
  interval_cases n <;>
    norm_num [Data.b0Chunk12, orderSevenCoefficient]

private theorem b0_coeff (n : ℕ) (h : n < 195) :
    ((Data.b0.getD n 0 : ℤ) : ℚ) = remainder4Coefficient0.coeff n := by
  by_cases h0 : n < 16
  · exact b0_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact b0_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact b0_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact b0_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact b0_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact b0_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact b0_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact b0_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact b0_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact b0_range9 n (by omega) h9
  by_cases h10 : n < 176
  · exact b0_range10 n (by omega) h10
  by_cases h11 : n < 192
  · exact b0_range11 n (by omega) h11
  exact b0_range12 n (by omega) (by omega)

/-- The dense table for the first fourth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_b0 : toPolynomial b0 = remainder4Coefficient0 := by
  ext n
  rw [coeff_toPolynomial]
  unfold b0
  by_cases hn : n < 195
  · exact b0_coeff n hn
  · rw [List.getD_eq_default (l := Data.b0) (d := (0 : ℤ)) (by
      rw [b0_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4A0_natDegree_le)
      n (by omega)).symm

private theorem b1_prefix0_length :
    (Data.b1Chunk0).length = 16 := by
  rfl

private theorem b1_prefix1_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1).length = 32 := by
  rfl

private theorem b1_prefix2_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2).length = 48 := by
  rfl

private theorem b1_prefix3_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3).length = 64 := by
  rfl

private theorem b1_prefix4_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4).length = 80 := by
  rfl

private theorem b1_prefix5_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5).length = 96 := by
  rfl

private theorem b1_prefix6_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5
       ++ Data.b1Chunk6).length = 112 := by
  rfl

private theorem b1_prefix7_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5
       ++ Data.b1Chunk6 ++ Data.b1Chunk7).length = 128 := by
  rfl

private theorem b1_prefix8_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5
       ++ Data.b1Chunk6 ++ Data.b1Chunk7
       ++ Data.b1Chunk8).length = 144 := by
  rfl

private theorem b1_prefix9_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5
       ++ Data.b1Chunk6 ++ Data.b1Chunk7
       ++ Data.b1Chunk8 ++ Data.b1Chunk9).length = 160 := by
  rfl

private theorem b1_prefix10_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5
       ++ Data.b1Chunk6 ++ Data.b1Chunk7
       ++ Data.b1Chunk8 ++ Data.b1Chunk9
       ++ Data.b1Chunk10).length = 176 := by
  rfl

private theorem b1_prefix11_length :
    (Data.b1Chunk0 ++ Data.b1Chunk1
       ++ Data.b1Chunk2 ++ Data.b1Chunk3
       ++ Data.b1Chunk4 ++ Data.b1Chunk5
       ++ Data.b1Chunk6 ++ Data.b1Chunk7
       ++ Data.b1Chunk8 ++ Data.b1Chunk9
       ++ Data.b1Chunk10 ++ Data.b1Chunk11).length = 191 := by
  rfl

private theorem b1_length : Data.b1.length = 191 := by
  unfold Data.b1
  exact b1_prefix11_length

private theorem b1_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.b1Chunk0, orderSevenCoefficient]

private theorem b1_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix0_length]
    omega)]
  rw [b1_prefix0_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk1, orderSevenCoefficient]

private theorem b1_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix1_length]
    omega)]
  rw [b1_prefix1_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk2, orderSevenCoefficient]

private theorem b1_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix2_length]
    omega)]
  rw [b1_prefix2_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk3, orderSevenCoefficient]

private theorem b1_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix3_length]
    omega)]
  rw [b1_prefix3_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk4, orderSevenCoefficient]

private theorem b1_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix4_length]
    omega)]
  rw [b1_prefix4_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk5, orderSevenCoefficient]

private theorem b1_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix5_length]
    omega)]
  rw [b1_prefix5_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk6, orderSevenCoefficient]

private theorem b1_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix6_length]
    omega)]
  rw [b1_prefix6_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk7, orderSevenCoefficient]

private theorem b1_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix7_length]
    omega)]
  rw [b1_prefix7_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk8, orderSevenCoefficient]

private theorem b1_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix8_length]
    omega)]
  rw [b1_prefix8_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk9, orderSevenCoefficient]

private theorem b1_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 176) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix9_length]
    omega)]
  rw [b1_prefix9_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk10, orderSevenCoefficient]

private theorem b1_range11 (n : ℕ) (hlo : 176 ≤ n) (hhi : n < 191) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  unfold Data.b1
  rw [List.getD_append_right _ _ _ _ (by
    rw [b1_prefix10_length]
    omega)]
  rw [b1_prefix10_length]
  interval_cases n <;>
    norm_num [Data.b1Chunk11, orderSevenCoefficient]

private theorem b1_coeff (n : ℕ) (h : n < 191) :
    ((Data.b1.getD n 0 : ℤ) : ℚ) = remainder4Coefficient1.coeff n := by
  by_cases h0 : n < 16
  · exact b1_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact b1_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact b1_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact b1_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact b1_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact b1_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact b1_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact b1_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact b1_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact b1_range9 n (by omega) h9
  by_cases h10 : n < 176
  · exact b1_range10 n (by omega) h10
  exact b1_range11 n (by omega) (by omega)

/-- The dense table for the second fourth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_b1 : toPolynomial b1 = remainder4Coefficient1 := by
  ext n
  rw [coeff_toPolynomial]
  unfold b1
  by_cases hn : n < 191
  · exact b1_coeff n hn
  · rw [List.getD_eq_default (l := Data.b1) (d := (0 : ℤ)) (by
      rw [b1_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4A1_natDegree_le)
      n (by omega)).symm

private theorem b2_prefix0_length :
    (Data.b2Chunk0).length = 16 := by
  rfl

private theorem b2_prefix1_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1).length = 32 := by
  rfl

private theorem b2_prefix2_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2).length = 48 := by
  rfl

private theorem b2_prefix3_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3).length = 64 := by
  rfl

private theorem b2_prefix4_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4).length = 80 := by
  rfl

private theorem b2_prefix5_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5).length = 96 := by
  rfl

private theorem b2_prefix6_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5
       ++ Data.b2Chunk6).length = 112 := by
  rfl

private theorem b2_prefix7_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5
       ++ Data.b2Chunk6 ++ Data.b2Chunk7).length = 128 := by
  rfl

private theorem b2_prefix8_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5
       ++ Data.b2Chunk6 ++ Data.b2Chunk7
       ++ Data.b2Chunk8).length = 144 := by
  rfl

private theorem b2_prefix9_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5
       ++ Data.b2Chunk6 ++ Data.b2Chunk7
       ++ Data.b2Chunk8 ++ Data.b2Chunk9).length = 160 := by
  rfl

private theorem b2_prefix10_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5
       ++ Data.b2Chunk6 ++ Data.b2Chunk7
       ++ Data.b2Chunk8 ++ Data.b2Chunk9
       ++ Data.b2Chunk10).length = 176 := by
  rfl

private theorem b2_prefix11_length :
    (Data.b2Chunk0 ++ Data.b2Chunk1
       ++ Data.b2Chunk2 ++ Data.b2Chunk3
       ++ Data.b2Chunk4 ++ Data.b2Chunk5
       ++ Data.b2Chunk6 ++ Data.b2Chunk7
       ++ Data.b2Chunk8 ++ Data.b2Chunk9
       ++ Data.b2Chunk10 ++ Data.b2Chunk11).length = 187 := by
  rfl

private theorem b2_length : Data.b2.length = 187 := by
  unfold Data.b2
  exact b2_prefix11_length

private theorem b2_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.b2Chunk0, orderSevenCoefficient]

private theorem b2_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix0_length]
    omega)]
  rw [b2_prefix0_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk1, orderSevenCoefficient]

private theorem b2_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix1_length]
    omega)]
  rw [b2_prefix1_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk2, orderSevenCoefficient]

private theorem b2_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix2_length]
    omega)]
  rw [b2_prefix2_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk3, orderSevenCoefficient]

private theorem b2_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix3_length]
    omega)]
  rw [b2_prefix3_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk4, orderSevenCoefficient]

private theorem b2_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix4_length]
    omega)]
  rw [b2_prefix4_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk5, orderSevenCoefficient]

private theorem b2_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix5_length]
    omega)]
  rw [b2_prefix5_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk6, orderSevenCoefficient]

private theorem b2_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix6_length]
    omega)]
  rw [b2_prefix6_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk7, orderSevenCoefficient]

private theorem b2_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix7_length]
    omega)]
  rw [b2_prefix7_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk8, orderSevenCoefficient]

private theorem b2_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix8_length]
    omega)]
  rw [b2_prefix8_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk9, orderSevenCoefficient]

private theorem b2_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 176) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix9_length]
    omega)]
  rw [b2_prefix9_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk10, orderSevenCoefficient]

private theorem b2_range11 (n : ℕ) (hlo : 176 ≤ n) (hhi : n < 187) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  unfold Data.b2
  rw [List.getD_append_right _ _ _ _ (by
    rw [b2_prefix10_length]
    omega)]
  rw [b2_prefix10_length]
  interval_cases n <;>
    norm_num [Data.b2Chunk11, orderSevenCoefficient]

private theorem b2_coeff (n : ℕ) (h : n < 187) :
    ((Data.b2.getD n 0 : ℤ) : ℚ) = remainder4Coefficient2.coeff n := by
  by_cases h0 : n < 16
  · exact b2_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact b2_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact b2_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact b2_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact b2_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact b2_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact b2_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact b2_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact b2_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact b2_range9 n (by omega) h9
  by_cases h10 : n < 176
  · exact b2_range10 n (by omega) h10
  exact b2_range11 n (by omega) (by omega)

/-- The dense table for the third fourth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_b2 : toPolynomial b2 = remainder4Coefficient2 := by
  ext n
  rw [coeff_toPolynomial]
  unfold b2
  by_cases hn : n < 187
  · exact b2_coeff n hn
  · rw [List.getD_eq_default (l := Data.b2) (d := (0 : ℤ)) (by
      rw [b2_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4A2_natDegree_le)
      n (by omega)).symm

private theorem b3_prefix0_length :
    (Data.b3Chunk0).length = 16 := by
  rfl

private theorem b3_prefix1_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1).length = 32 := by
  rfl

private theorem b3_prefix2_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2).length = 48 := by
  rfl

private theorem b3_prefix3_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3).length = 64 := by
  rfl

private theorem b3_prefix4_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4).length = 80 := by
  rfl

private theorem b3_prefix5_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5).length = 96 := by
  rfl

private theorem b3_prefix6_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5
       ++ Data.b3Chunk6).length = 112 := by
  rfl

private theorem b3_prefix7_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5
       ++ Data.b3Chunk6 ++ Data.b3Chunk7).length = 128 := by
  rfl

private theorem b3_prefix8_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5
       ++ Data.b3Chunk6 ++ Data.b3Chunk7
       ++ Data.b3Chunk8).length = 144 := by
  rfl

private theorem b3_prefix9_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5
       ++ Data.b3Chunk6 ++ Data.b3Chunk7
       ++ Data.b3Chunk8 ++ Data.b3Chunk9).length = 160 := by
  rfl

private theorem b3_prefix10_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5
       ++ Data.b3Chunk6 ++ Data.b3Chunk7
       ++ Data.b3Chunk8 ++ Data.b3Chunk9
       ++ Data.b3Chunk10).length = 176 := by
  rfl

private theorem b3_prefix11_length :
    (Data.b3Chunk0 ++ Data.b3Chunk1
       ++ Data.b3Chunk2 ++ Data.b3Chunk3
       ++ Data.b3Chunk4 ++ Data.b3Chunk5
       ++ Data.b3Chunk6 ++ Data.b3Chunk7
       ++ Data.b3Chunk8 ++ Data.b3Chunk9
       ++ Data.b3Chunk10 ++ Data.b3Chunk11).length = 183 := by
  rfl

private theorem b3_length : Data.b3.length = 183 := by
  unfold Data.b3
  exact b3_prefix11_length

private theorem b3_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.b3Chunk0, orderSevenCoefficient]

private theorem b3_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix0_length]
    omega)]
  rw [b3_prefix0_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk1, orderSevenCoefficient]

private theorem b3_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix1_length]
    omega)]
  rw [b3_prefix1_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk2, orderSevenCoefficient]

private theorem b3_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix2_length]
    omega)]
  rw [b3_prefix2_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk3, orderSevenCoefficient]

private theorem b3_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix3_length]
    omega)]
  rw [b3_prefix3_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk4, orderSevenCoefficient]

private theorem b3_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix4_length]
    omega)]
  rw [b3_prefix4_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk5, orderSevenCoefficient]

private theorem b3_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix5_length]
    omega)]
  rw [b3_prefix5_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk6, orderSevenCoefficient]

private theorem b3_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix6_length]
    omega)]
  rw [b3_prefix6_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk7, orderSevenCoefficient]

private theorem b3_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix7_length]
    omega)]
  rw [b3_prefix7_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk8, orderSevenCoefficient]

private theorem b3_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix8_length]
    omega)]
  rw [b3_prefix8_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk9, orderSevenCoefficient]

private theorem b3_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 176) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix9_length]
    omega)]
  rw [b3_prefix9_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk10, orderSevenCoefficient]

private theorem b3_range11 (n : ℕ) (hlo : 176 ≤ n) (hhi : n < 183) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  unfold Data.b3
  rw [List.getD_append_right _ _ _ _ (by
    rw [b3_prefix10_length]
    omega)]
  rw [b3_prefix10_length]
  interval_cases n <;>
    norm_num [Data.b3Chunk11, orderSevenCoefficient]

private theorem b3_coeff (n : ℕ) (h : n < 183) :
    ((Data.b3.getD n 0 : ℤ) : ℚ) = remainder4Coefficient3.coeff n := by
  by_cases h0 : n < 16
  · exact b3_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact b3_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact b3_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact b3_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact b3_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact b3_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact b3_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact b3_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact b3_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact b3_range9 n (by omega) h9
  by_cases h10 : n < 176
  · exact b3_range10 n (by omega) h10
  exact b3_range11 n (by omega) (by omega)

/-- The dense table for the fourth fourth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_b3 : toPolynomial b3 = remainder4Coefficient3 := by
  ext n
  rw [coeff_toPolynomial]
  unfold b3
  by_cases hn : n < 183
  · exact b3_coeff n hn
  · rw [List.getD_eq_default (l := Data.b3) (d := (0 : ℤ)) (by
      rw [b3_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4A3_natDegree_le)
      n (by omega)).symm

private theorem b4_prefix0_length :
    (Data.b4Chunk0).length = 16 := by
  rfl

private theorem b4_prefix1_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1).length = 32 := by
  rfl

private theorem b4_prefix2_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2).length = 48 := by
  rfl

private theorem b4_prefix3_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3).length = 64 := by
  rfl

private theorem b4_prefix4_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4).length = 80 := by
  rfl

private theorem b4_prefix5_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5).length = 96 := by
  rfl

private theorem b4_prefix6_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5
       ++ Data.b4Chunk6).length = 112 := by
  rfl

private theorem b4_prefix7_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5
       ++ Data.b4Chunk6 ++ Data.b4Chunk7).length = 128 := by
  rfl

private theorem b4_prefix8_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5
       ++ Data.b4Chunk6 ++ Data.b4Chunk7
       ++ Data.b4Chunk8).length = 144 := by
  rfl

private theorem b4_prefix9_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5
       ++ Data.b4Chunk6 ++ Data.b4Chunk7
       ++ Data.b4Chunk8 ++ Data.b4Chunk9).length = 160 := by
  rfl

private theorem b4_prefix10_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5
       ++ Data.b4Chunk6 ++ Data.b4Chunk7
       ++ Data.b4Chunk8 ++ Data.b4Chunk9
       ++ Data.b4Chunk10).length = 176 := by
  rfl

private theorem b4_prefix11_length :
    (Data.b4Chunk0 ++ Data.b4Chunk1
       ++ Data.b4Chunk2 ++ Data.b4Chunk3
       ++ Data.b4Chunk4 ++ Data.b4Chunk5
       ++ Data.b4Chunk6 ++ Data.b4Chunk7
       ++ Data.b4Chunk8 ++ Data.b4Chunk9
       ++ Data.b4Chunk10 ++ Data.b4Chunk11).length = 179 := by
  rfl

private theorem b4_length : Data.b4.length = 179 := by
  unfold Data.b4
  exact b4_prefix11_length

private theorem b4_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.b4Chunk0, orderSevenCoefficient]

private theorem b4_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix0_length]
    omega)]
  rw [b4_prefix0_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk1, orderSevenCoefficient]

private theorem b4_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix1_length]
    omega)]
  rw [b4_prefix1_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk2, orderSevenCoefficient]

private theorem b4_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix2_length]
    omega)]
  rw [b4_prefix2_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk3, orderSevenCoefficient]

private theorem b4_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix3_length]
    omega)]
  rw [b4_prefix3_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk4, orderSevenCoefficient]

private theorem b4_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix4_length]
    omega)]
  rw [b4_prefix4_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk5, orderSevenCoefficient]

private theorem b4_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix5_length]
    omega)]
  rw [b4_prefix5_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk6, orderSevenCoefficient]

private theorem b4_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix6_length]
    omega)]
  rw [b4_prefix6_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk7, orderSevenCoefficient]

private theorem b4_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix7_length]
    omega)]
  rw [b4_prefix7_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk8, orderSevenCoefficient]

private theorem b4_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix8_length]
    omega)]
  rw [b4_prefix8_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk9, orderSevenCoefficient]

private theorem b4_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 176) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix9_length]
    omega)]
  rw [b4_prefix9_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk10, orderSevenCoefficient]

private theorem b4_range11 (n : ℕ) (hlo : 176 ≤ n) (hhi : n < 179) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  unfold Data.b4
  rw [List.getD_append_right _ _ _ _ (by
    rw [b4_prefix10_length]
    omega)]
  rw [b4_prefix10_length]
  interval_cases n <;>
    norm_num [Data.b4Chunk11, orderSevenCoefficient]

private theorem b4_coeff (n : ℕ) (h : n < 179) :
    ((Data.b4.getD n 0 : ℤ) : ℚ) = remainder4Coefficient4.coeff n := by
  by_cases h0 : n < 16
  · exact b4_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact b4_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact b4_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact b4_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact b4_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact b4_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact b4_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact b4_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact b4_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact b4_range9 n (by omega) h9
  by_cases h10 : n < 176
  · exact b4_range10 n (by omega) h10
  exact b4_range11 n (by omega) (by omega)

/-- The dense table for the fifth fourth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_b4 : toPolynomial b4 = remainder4Coefficient4 := by
  ext n
  rw [coeff_toPolynomial]
  unfold b4
  by_cases hn : n < 179
  · exact b4_coeff n hn
  · rw [List.getD_eq_default (l := Data.b4) (d := (0 : ℤ)) (by
      rw [b4_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4A4_natDegree_le)
      n (by omega)).symm

private theorem c0_prefix0_length :
    (Data.c0Chunk0).length = 16 := by
  rfl

private theorem c0_prefix1_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1).length = 32 := by
  rfl

private theorem c0_prefix2_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2).length = 48 := by
  rfl

private theorem c0_prefix3_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3).length = 64 := by
  rfl

private theorem c0_prefix4_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4).length = 80 := by
  rfl

private theorem c0_prefix5_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5).length = 96 := by
  rfl

private theorem c0_prefix6_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5
       ++ Data.c0Chunk6).length = 112 := by
  rfl

private theorem c0_prefix7_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5
       ++ Data.c0Chunk6 ++ Data.c0Chunk7).length = 128 := by
  rfl

private theorem c0_prefix8_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5
       ++ Data.c0Chunk6 ++ Data.c0Chunk7
       ++ Data.c0Chunk8).length = 144 := by
  rfl

private theorem c0_prefix9_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5
       ++ Data.c0Chunk6 ++ Data.c0Chunk7
       ++ Data.c0Chunk8 ++ Data.c0Chunk9).length = 160 := by
  rfl

private theorem c0_prefix10_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5
       ++ Data.c0Chunk6 ++ Data.c0Chunk7
       ++ Data.c0Chunk8 ++ Data.c0Chunk9
       ++ Data.c0Chunk10).length = 176 := by
  rfl

private theorem c0_prefix11_length :
    (Data.c0Chunk0 ++ Data.c0Chunk1
       ++ Data.c0Chunk2 ++ Data.c0Chunk3
       ++ Data.c0Chunk4 ++ Data.c0Chunk5
       ++ Data.c0Chunk6 ++ Data.c0Chunk7
       ++ Data.c0Chunk8 ++ Data.c0Chunk9
       ++ Data.c0Chunk10 ++ Data.c0Chunk11).length = 177 := by
  rfl

private theorem c0_length : Data.c0.length = 177 := by
  unfold Data.c0
  exact c0_prefix11_length

private theorem c0_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.c0Chunk0, orderSevenCoefficient]

private theorem c0_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix0_length]
    omega)]
  rw [c0_prefix0_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk1, orderSevenCoefficient]

private theorem c0_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix1_length]
    omega)]
  rw [c0_prefix1_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk2, orderSevenCoefficient]

private theorem c0_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix2_length]
    omega)]
  rw [c0_prefix2_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk3, orderSevenCoefficient]

private theorem c0_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix3_length]
    omega)]
  rw [c0_prefix3_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk4, orderSevenCoefficient]

private theorem c0_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix4_length]
    omega)]
  rw [c0_prefix4_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk5, orderSevenCoefficient]

private theorem c0_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix5_length]
    omega)]
  rw [c0_prefix5_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk6, orderSevenCoefficient]

private theorem c0_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix6_length]
    omega)]
  rw [c0_prefix6_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk7, orderSevenCoefficient]

private theorem c0_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix7_length]
    omega)]
  rw [c0_prefix7_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk8, orderSevenCoefficient]

private theorem c0_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix8_length]
    omega)]
  rw [c0_prefix8_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk9, orderSevenCoefficient]

private theorem c0_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 176) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix9_length]
    omega)]
  rw [c0_prefix9_length]
  interval_cases n <;>
    norm_num [Data.c0Chunk10, orderSevenCoefficient]

private theorem c0_range11 (n : ℕ) (hlo : 176 ≤ n) (hhi : n < 177) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  unfold Data.c0
  rw [List.getD_append_right _ _ _ _ (by
    rw [c0_prefix10_length]
    omega)]
  rw [c0_prefix10_length]
  interval_cases n
  norm_num [Data.c0Chunk11, orderSevenCoefficient]

private theorem c0_coeff (n : ℕ) (h : n < 177) :
    ((Data.c0.getD n 0 : ℤ) : ℚ) = remainder5Coefficient0.coeff n := by
  by_cases h0 : n < 16
  · exact c0_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact c0_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact c0_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact c0_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact c0_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact c0_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact c0_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact c0_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact c0_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact c0_range9 n (by omega) h9
  by_cases h10 : n < 176
  · exact c0_range10 n (by omega) h10
  exact c0_range11 n (by omega) (by omega)

/-- The dense table for the first fifth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_c0 : toPolynomial c0 = remainder5Coefficient0 := by
  ext n
  rw [coeff_toPolynomial]
  unfold c0
  by_cases hn : n < 177
  · exact c0_coeff n hn
  · rw [List.getD_eq_default (l := Data.c0) (d := (0 : ℤ)) (by
      rw [c0_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4B0_natDegree_le)
      n (by omega)).symm

private theorem c1_prefix0_length :
    (Data.c1Chunk0).length = 16 := by
  rfl

private theorem c1_prefix1_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1).length = 32 := by
  rfl

private theorem c1_prefix2_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2).length = 48 := by
  rfl

private theorem c1_prefix3_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3).length = 64 := by
  rfl

private theorem c1_prefix4_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4).length = 80 := by
  rfl

private theorem c1_prefix5_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4 ++ Data.c1Chunk5).length = 96 := by
  rfl

private theorem c1_prefix6_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4 ++ Data.c1Chunk5
       ++ Data.c1Chunk6).length = 112 := by
  rfl

private theorem c1_prefix7_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4 ++ Data.c1Chunk5
       ++ Data.c1Chunk6 ++ Data.c1Chunk7).length = 128 := by
  rfl

private theorem c1_prefix8_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4 ++ Data.c1Chunk5
       ++ Data.c1Chunk6 ++ Data.c1Chunk7
       ++ Data.c1Chunk8).length = 144 := by
  rfl

private theorem c1_prefix9_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4 ++ Data.c1Chunk5
       ++ Data.c1Chunk6 ++ Data.c1Chunk7
       ++ Data.c1Chunk8 ++ Data.c1Chunk9).length = 160 := by
  rfl

private theorem c1_prefix10_length :
    (Data.c1Chunk0 ++ Data.c1Chunk1
       ++ Data.c1Chunk2 ++ Data.c1Chunk3
       ++ Data.c1Chunk4 ++ Data.c1Chunk5
       ++ Data.c1Chunk6 ++ Data.c1Chunk7
       ++ Data.c1Chunk8 ++ Data.c1Chunk9
       ++ Data.c1Chunk10).length = 173 := by
  rfl

private theorem c1_length : Data.c1.length = 173 := by
  unfold Data.c1
  exact c1_prefix10_length

private theorem c1_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.c1Chunk0, orderSevenCoefficient]

private theorem c1_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix0_length]
    omega)]
  rw [c1_prefix0_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk1, orderSevenCoefficient]

private theorem c1_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix1_length]
    omega)]
  rw [c1_prefix1_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk2, orderSevenCoefficient]

private theorem c1_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix2_length]
    omega)]
  rw [c1_prefix2_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk3, orderSevenCoefficient]

private theorem c1_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix3_length]
    omega)]
  rw [c1_prefix3_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk4, orderSevenCoefficient]

private theorem c1_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix4_length]
    omega)]
  rw [c1_prefix4_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk5, orderSevenCoefficient]

private theorem c1_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix5_length]
    omega)]
  rw [c1_prefix5_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk6, orderSevenCoefficient]

private theorem c1_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix6_length]
    omega)]
  rw [c1_prefix6_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk7, orderSevenCoefficient]

private theorem c1_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix7_length]
    omega)]
  rw [c1_prefix7_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk8, orderSevenCoefficient]

private theorem c1_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix8_length]
    omega)]
  rw [c1_prefix8_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk9, orderSevenCoefficient]

private theorem c1_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 173) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  unfold Data.c1
  rw [List.getD_append_right _ _ _ _ (by
    rw [c1_prefix9_length]
    omega)]
  rw [c1_prefix9_length]
  interval_cases n <;>
    norm_num [Data.c1Chunk10, orderSevenCoefficient]

private theorem c1_coeff (n : ℕ) (h : n < 173) :
    ((Data.c1.getD n 0 : ℤ) : ℚ) = remainder5Coefficient1.coeff n := by
  by_cases h0 : n < 16
  · exact c1_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact c1_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact c1_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact c1_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact c1_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact c1_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact c1_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact c1_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact c1_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact c1_range9 n (by omega) h9
  exact c1_range10 n (by omega) (by omega)

/-- The dense table for the second fifth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_c1 : toPolynomial c1 = remainder5Coefficient1 := by
  ext n
  rw [coeff_toPolynomial]
  unfold c1
  by_cases hn : n < 173
  · exact c1_coeff n hn
  · rw [List.getD_eq_default (l := Data.c1) (d := (0 : ℤ)) (by
      rw [c1_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4B1_natDegree_le)
      n (by omega)).symm

private theorem c2_prefix0_length :
    (Data.c2Chunk0).length = 16 := by
  rfl

private theorem c2_prefix1_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1).length = 32 := by
  rfl

private theorem c2_prefix2_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2).length = 48 := by
  rfl

private theorem c2_prefix3_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3).length = 64 := by
  rfl

private theorem c2_prefix4_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4).length = 80 := by
  rfl

private theorem c2_prefix5_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4 ++ Data.c2Chunk5).length = 96 := by
  rfl

private theorem c2_prefix6_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4 ++ Data.c2Chunk5
       ++ Data.c2Chunk6).length = 112 := by
  rfl

private theorem c2_prefix7_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4 ++ Data.c2Chunk5
       ++ Data.c2Chunk6 ++ Data.c2Chunk7).length = 128 := by
  rfl

private theorem c2_prefix8_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4 ++ Data.c2Chunk5
       ++ Data.c2Chunk6 ++ Data.c2Chunk7
       ++ Data.c2Chunk8).length = 144 := by
  rfl

private theorem c2_prefix9_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4 ++ Data.c2Chunk5
       ++ Data.c2Chunk6 ++ Data.c2Chunk7
       ++ Data.c2Chunk8 ++ Data.c2Chunk9).length = 160 := by
  rfl

private theorem c2_prefix10_length :
    (Data.c2Chunk0 ++ Data.c2Chunk1
       ++ Data.c2Chunk2 ++ Data.c2Chunk3
       ++ Data.c2Chunk4 ++ Data.c2Chunk5
       ++ Data.c2Chunk6 ++ Data.c2Chunk7
       ++ Data.c2Chunk8 ++ Data.c2Chunk9
       ++ Data.c2Chunk10).length = 169 := by
  rfl

private theorem c2_length : Data.c2.length = 169 := by
  unfold Data.c2
  exact c2_prefix10_length

private theorem c2_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.c2Chunk0, orderSevenCoefficient]

private theorem c2_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix0_length]
    omega)]
  rw [c2_prefix0_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk1, orderSevenCoefficient]

private theorem c2_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix1_length]
    omega)]
  rw [c2_prefix1_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk2, orderSevenCoefficient]

private theorem c2_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix2_length]
    omega)]
  rw [c2_prefix2_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk3, orderSevenCoefficient]

private theorem c2_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix3_length]
    omega)]
  rw [c2_prefix3_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk4, orderSevenCoefficient]

private theorem c2_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix4_length]
    omega)]
  rw [c2_prefix4_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk5, orderSevenCoefficient]

private theorem c2_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix5_length]
    omega)]
  rw [c2_prefix5_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk6, orderSevenCoefficient]

private theorem c2_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix6_length]
    omega)]
  rw [c2_prefix6_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk7, orderSevenCoefficient]

private theorem c2_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix7_length]
    omega)]
  rw [c2_prefix7_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk8, orderSevenCoefficient]

private theorem c2_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix8_length]
    omega)]
  rw [c2_prefix8_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk9, orderSevenCoefficient]

private theorem c2_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 169) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  unfold Data.c2
  rw [List.getD_append_right _ _ _ _ (by
    rw [c2_prefix9_length]
    omega)]
  rw [c2_prefix9_length]
  interval_cases n <;>
    norm_num [Data.c2Chunk10, orderSevenCoefficient]

private theorem c2_coeff (n : ℕ) (h : n < 169) :
    ((Data.c2.getD n 0 : ℤ) : ℚ) = remainder5Coefficient2.coeff n := by
  by_cases h0 : n < 16
  · exact c2_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact c2_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact c2_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact c2_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact c2_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact c2_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact c2_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact c2_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact c2_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact c2_range9 n (by omega) h9
  exact c2_range10 n (by omega) (by omega)

/-- The dense table for the third fifth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_c2 : toPolynomial c2 = remainder5Coefficient2 := by
  ext n
  rw [coeff_toPolynomial]
  unfold c2
  by_cases hn : n < 169
  · exact c2_coeff n hn
  · rw [List.getD_eq_default (l := Data.c2) (d := (0 : ℤ)) (by
      rw [c2_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4B2_natDegree_le)
      n (by omega)).symm

private theorem c3_prefix0_length :
    (Data.c3Chunk0).length = 16 := by
  rfl

private theorem c3_prefix1_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1).length = 32 := by
  rfl

private theorem c3_prefix2_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2).length = 48 := by
  rfl

private theorem c3_prefix3_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3).length = 64 := by
  rfl

private theorem c3_prefix4_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4).length = 80 := by
  rfl

private theorem c3_prefix5_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4 ++ Data.c3Chunk5).length = 96 := by
  rfl

private theorem c3_prefix6_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4 ++ Data.c3Chunk5
       ++ Data.c3Chunk6).length = 112 := by
  rfl

private theorem c3_prefix7_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4 ++ Data.c3Chunk5
       ++ Data.c3Chunk6 ++ Data.c3Chunk7).length = 128 := by
  rfl

private theorem c3_prefix8_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4 ++ Data.c3Chunk5
       ++ Data.c3Chunk6 ++ Data.c3Chunk7
       ++ Data.c3Chunk8).length = 144 := by
  rfl

private theorem c3_prefix9_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4 ++ Data.c3Chunk5
       ++ Data.c3Chunk6 ++ Data.c3Chunk7
       ++ Data.c3Chunk8 ++ Data.c3Chunk9).length = 160 := by
  rfl

private theorem c3_prefix10_length :
    (Data.c3Chunk0 ++ Data.c3Chunk1
       ++ Data.c3Chunk2 ++ Data.c3Chunk3
       ++ Data.c3Chunk4 ++ Data.c3Chunk5
       ++ Data.c3Chunk6 ++ Data.c3Chunk7
       ++ Data.c3Chunk8 ++ Data.c3Chunk9
       ++ Data.c3Chunk10).length = 165 := by
  rfl

private theorem c3_length : Data.c3.length = 165 := by
  unfold Data.c3
  exact c3_prefix10_length

private theorem c3_range0 (n : ℕ) (hlo : 0 ≤ n) (hhi : n < 16) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix1_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix0_length]
    omega)]
  interval_cases n <;>
    norm_num [Data.c3Chunk0, orderSevenCoefficient]

private theorem c3_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix2_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix1_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix0_length]
    omega)]
  rw [c3_prefix0_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk1, orderSevenCoefficient]

private theorem c3_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix3_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix2_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix1_length]
    omega)]
  rw [c3_prefix1_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk2, orderSevenCoefficient]

private theorem c3_range3 (n : ℕ) (hlo : 48 ≤ n) (hhi : n < 64) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix4_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix3_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix2_length]
    omega)]
  rw [c3_prefix2_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk3, orderSevenCoefficient]

private theorem c3_range4 (n : ℕ) (hlo : 64 ≤ n) (hhi : n < 80) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix4_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix3_length]
    omega)]
  rw [c3_prefix3_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk4, orderSevenCoefficient]

private theorem c3_range5 (n : ℕ) (hlo : 80 ≤ n) (hhi : n < 96) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix4_length]
    omega)]
  rw [c3_prefix4_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk5, orderSevenCoefficient]

private theorem c3_range6 (n : ℕ) (hlo : 96 ≤ n) (hhi : n < 112) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix5_length]
    omega)]
  rw [c3_prefix5_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk6, orderSevenCoefficient]

private theorem c3_range7 (n : ℕ) (hlo : 112 ≤ n) (hhi : n < 128) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix6_length]
    omega)]
  rw [c3_prefix6_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk7, orderSevenCoefficient]

private theorem c3_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix7_length]
    omega)]
  rw [c3_prefix7_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk8, orderSevenCoefficient]

private theorem c3_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 160) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix8_length]
    omega)]
  rw [c3_prefix8_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk9, orderSevenCoefficient]

private theorem c3_range10 (n : ℕ) (hlo : 160 ≤ n) (hhi : n < 165) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  unfold Data.c3
  rw [List.getD_append_right _ _ _ _ (by
    rw [c3_prefix9_length]
    omega)]
  rw [c3_prefix9_length]
  interval_cases n <;>
    norm_num [Data.c3Chunk10, orderSevenCoefficient]

private theorem c3_coeff (n : ℕ) (h : n < 165) :
    ((Data.c3.getD n 0 : ℤ) : ℚ) = remainder5Coefficient3.coeff n := by
  by_cases h0 : n < 16
  · exact c3_range0 n (by omega) h0
  by_cases h1 : n < 32
  · exact c3_range1 n (by omega) h1
  by_cases h2 : n < 48
  · exact c3_range2 n (by omega) h2
  by_cases h3 : n < 64
  · exact c3_range3 n (by omega) h3
  by_cases h4 : n < 80
  · exact c3_range4 n (by omega) h4
  by_cases h5 : n < 96
  · exact c3_range5 n (by omega) h5
  by_cases h6 : n < 112
  · exact c3_range6 n (by omega) h6
  by_cases h7 : n < 128
  · exact c3_range7 n (by omega) h7
  by_cases h8 : n < 144
  · exact c3_range8 n (by omega) h8
  by_cases h9 : n < 160
  · exact c3_range9 n (by omega) h9
  exact c3_range10 n (by omega) (by omega)

/-- The dense table for the fourth fifth-remainder coefficient has its intended meaning. -/
theorem toPolynomial_c3 : toPolynomial c3 = remainder5Coefficient3 := by
  ext n
  rw [coeff_toPolynomial]
  unfold c3
  by_cases hn : n < 165
  · exact c3_coeff n hn
  · rw [List.getD_eq_default (l := Data.c3) (d := (0 : ℤ)) (by
      rw [c3_length]
      omega)]
    simp only [Int.cast_zero]
    exact ((Polynomial.natDegree_le_iff_coeff_eq_zero.mp recurrence4B3_natDegree_le)
      n (by omega)).symm

/-- The dense discriminant table represents the discriminant factor. -/
theorem toPolynomial_discriminant :
    toPolynomial discriminant = discriminantFactor := by
  simp [discriminant, Data.discriminant, Data.discriminantChunk0,
    toPolynomial, discriminantFactor, parameter]
  simp only [map_ofNat]
  ring

/-- The certified quartic-leading square has its intended meaning. -/
theorem toPolynomial_b4Square :
    toPolynomial b4Square = remainder4Coefficient4 ^ 2 := by
  rw [← b4Square_checked, toPolynomial_mul, toPolynomial_b4]
  ring

/-- The certified quintic-leading square has its intended meaning. -/
theorem toPolynomial_a5Square :
    toPolynomial a5Square = remainder3Coefficient5 ^ 2 := by
  rw [← a5Square_checked, toPolynomial_mul, toPolynomial_a5]
  ring

/-- The certified discriminant square has its intended meaning. -/
theorem toPolynomial_discriminantSquare :
    toPolynomial discriminantSquare = discriminantFactor ^ 2 := by
  rw [← discriminantSquare_checked, toPolynomial_mul,
    toPolynomial_discriminant]
  ring

/-- The certified fourth discriminant power has its intended meaning. -/
theorem toPolynomial_discriminantPower4 :
    toPolynomial discriminantPower4 = discriminantFactor ^ 4 := by
  rw [← discriminantPower4_checked, toPolynomial_mul,
    toPolynomial_discriminantSquare]
  ring

/-- The certified eighth discriminant power has its intended meaning. -/
theorem toPolynomial_discriminantPower8 :
    toPolynomial discriminantPower8 = discriminantFactor ^ 8 := by
  rw [← discriminantPower8_checked, toPolynomial_mul,
    toPolynomial_discriminantPower4]
  ring

/-- The certified sixteenth discriminant power has its intended meaning. -/
theorem toPolynomial_discriminantPower16 :
    toPolynomial discriminantPower16 = discriminantFactor ^ 16 := by
  rw [← discriminantPower16_checked, toPolynomial_mul,
    toPolynomial_discriminantPower8]
  ring

/-- The certified twentieth discriminant power has its intended meaning. -/
theorem toPolynomial_discriminantPower20 :
    toPolynomial discriminantPower20 = discriminantFactor ^ 20 := by
  rw [← discriminantPower20_checked, toPolynomial_mul,
    toPolynomial_discriminantPower16, toPolynomial_discriminantPower4]
  ring

/-- The certified twenty-second discriminant power has its intended meaning. -/
theorem toPolynomial_discriminantPower22 :
    toPolynomial discriminantPower22 = discriminantFactor ^ 22 := by
  rw [← discriminantPower22_checked, toPolynomial_mul,
    toPolynomial_discriminantPower20, toPolynomial_discriminantSquare]
  ring

/-- The certified linear pseudo-quotient coefficient has its intended meaning. -/
theorem toPolynomial_quotientLinear :
    toPolynomial quotientLinear =
      remainder4Coefficient4 * remainder3Coefficient5 := by
  rw [← quotientLinear_checked, toPolynomial_mul,
    toPolynomial_b4, toPolynomial_a5]

/-- The certified constant pseudo-quotient coefficient has its intended meaning. -/
theorem toPolynomial_quotientConstant :
    toPolynomial quotientConstant =
      remainder4Coefficient4 * remainder3Coefficient4 -
        remainder4Coefficient3 * remainder3Coefficient5 := by
  rw [← quotientConstant_checked, toPolynomial_sub, toPolynomial_mul,
    toPolynomial_b4, toPolynomial_a4]
  rw [toPolynomial_mul, toPolynomial_b3, toPolynomial_a5]

/-- The certified cleared exceptional product has its intended meaning. -/
theorem toPolynomial_exceptionalProductNumerator :
    toPolynomial exceptionalProductNumerator =
      remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 := by
  rw [← exceptionalProductNumerator_checked, toPolynomial_mul,
    toPolynomial_a5Square, toPolynomial_discriminantPower22]

end
end IntegerDenseCertificate
end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
