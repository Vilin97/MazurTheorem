/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA6High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: A6 source bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence2A6_remainder2Coefficient6Chunk0_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk0.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk1_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk1.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk2_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk2.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk3_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk3.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk4_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk4.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk5_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk5.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk6_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk6.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk7_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk7.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk8_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk8.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk9_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk9.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk10_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk10.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A6_remainder2Coefficient6Chunk11_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6Chunk11.coeff n = 0 := by
  unfold remainder2Coefficient6Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence2A6_coeff_high (n : ℕ) (h : 95 < n) :
    remainder2Coefficient6.coeff n = 0 := by
  unfold
    remainder2Coefficient6
    remainder2Coefficient6Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence2A6_remainder2Coefficient6Chunk0_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk1_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk2_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk3_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk4_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk5_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk6_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk7_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk8_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk9_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk10_coeff_high n h]
  rw [recurrence2A6_remainder2Coefficient6Chunk11_coeff_high n h]
  norm_num

theorem recurrence2A6_natDegree_le :
    remainder2Coefficient6.natDegree ≤ 95 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence2A6_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
