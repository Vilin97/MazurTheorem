/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupC1High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: C1 source bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence5C1_remainder7Coefficient1Chunk0_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk0.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk1_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk1.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk2_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk2.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk3_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk3.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk4_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk4.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk5_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk5.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk6_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk6.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk7_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk7.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk8_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk8.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk9_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk9.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5C1_remainder7Coefficient1Chunk10_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1Chunk10.coeff n = 0 := by
  unfold remainder7Coefficient1Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence5C1_coeff_high (n : ℕ) (h : 84 < n) :
    remainder7Coefficient1.coeff n = 0 := by
  unfold remainder7Coefficient1 remainder7Coefficient1Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence5C1_remainder7Coefficient1Chunk0_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk1_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk2_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk3_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk4_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk5_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk6_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk7_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk8_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk9_coeff_high n h]
  rw [recurrence5C1_remainder7Coefficient1Chunk10_coeff_high n h]
  norm_num

theorem recurrence5C1_natDegree_le :
    remainder7Coefficient1.natDegree ≤ 84 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence5C1_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
