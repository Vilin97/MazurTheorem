/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA3Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA3High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: A3 source bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence2A3_remainder2Coefficient3Chunk0_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk0.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk1_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk1.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk2_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk2.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk3_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk3.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk4_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk4.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk5_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk5.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk6_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk6.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk7_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk7.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk8_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk8.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk9_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk9.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk10_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk10.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk11_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk11.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk12_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk12.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2A3_remainder2Coefficient3Chunk13_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3Chunk13.coeff n = 0 := by
  unfold remainder2Coefficient3Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence2A3_coeff_high (n : ℕ) (h : 106 < n) :
    remainder2Coefficient3.coeff n = 0 := by
  unfold
    remainder2Coefficient3
    remainder2Coefficient3Block1
    remainder2Coefficient3Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence2A3_remainder2Coefficient3Chunk0_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk1_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk2_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk3_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk4_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk5_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk6_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk7_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk8_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk9_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk10_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk11_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk12_coeff_high n h]
  rw [recurrence2A3_remainder2Coefficient3Chunk13_coeff_high n h]
  norm_num

theorem recurrence2A3_natDegree_le :
    remainder2Coefficient3.natDegree ≤ 106 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence2A3_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
