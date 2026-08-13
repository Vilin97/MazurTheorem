/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: B5 source bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence2B5_remainder3Coefficient5Chunk0_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk0.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk1_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk1.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk2_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk2.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk3_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk3.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk4_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk4.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk5_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk5.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk6_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk6.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk7_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk7.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk8_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk8.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk9_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk9.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk10_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk10.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk11_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk11.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk12_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk12.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk13_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk13.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk14_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk14.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk15_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk15.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B5_remainder3Coefficient5Chunk16_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5Chunk16.coeff n = 0 := by
  unfold remainder3Coefficient5Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence2B5_coeff_high (n : ℕ) (h : 134 < n) :
    remainder3Coefficient5.coeff n = 0 := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence2B5_remainder3Coefficient5Chunk0_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk1_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk2_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk3_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk4_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk5_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk6_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk7_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk8_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk9_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk10_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk11_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk12_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk13_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk14_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk15_coeff_high n h]
  rw [recurrence2B5_remainder3Coefficient5Chunk16_coeff_high n h]
  norm_num

theorem recurrence2B5_natDegree_le :
    remainder3Coefficient5.natDegree ≤ 134 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence2B5_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
