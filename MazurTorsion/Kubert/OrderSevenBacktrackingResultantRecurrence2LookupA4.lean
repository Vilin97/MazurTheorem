/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA4Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA4High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: A4 source bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence2A4_remainder2Coefficient4Chunk0_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk0.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk1_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk1.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk2_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk2.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk3_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk3.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk4_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk4.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk5_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk5.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk6_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk6.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk7_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk7.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk8_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk8.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk9_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk9.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk10_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk10.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk11_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk11.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A4_remainder2Coefficient4Chunk12_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4Chunk12.coeff n = 0 := by
  unfold remainder2Coefficient4Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence2A4_coeff_high (n : ℕ) (h : 102 < n) :
    remainder2Coefficient4.coeff n = 0 := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence2A4_remainder2Coefficient4Chunk0_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk1_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk2_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk3_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk4_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk5_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk6_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk7_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk8_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk9_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk10_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk11_coeff_high n h]
  rw [recurrence2A4_remainder2Coefficient4Chunk12_coeff_high n h]
  norm_num

theorem recurrence2A4_natDegree_le :
    remainder2Coefficient4.natDegree ≤ 102 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence2A4_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
