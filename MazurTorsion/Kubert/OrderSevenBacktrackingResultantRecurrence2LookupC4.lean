/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC4High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: C4 source bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence2C4_remainder4Coefficient4Chunk0_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk0.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk1_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk1.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk2_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk2.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk3_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk3.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk4_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk4.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk5_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk5.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk6_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk6.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk7_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk7.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk8_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk8.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk9_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk9.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk10_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk10.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk11_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk11.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk12_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk12.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk13_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk13.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk14_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk14.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk15_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk15.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk16_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk16.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk17_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk17.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk18_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk18.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk19_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk19.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk19 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk20_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk20.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk20 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk21_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk21.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk21 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2C4_remainder4Coefficient4Chunk22_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4Chunk22.coeff n = 0 := by
  unfold remainder4Coefficient4Chunk22 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence2C4_coeff_high (n : ℕ) (h : 178 < n) :
    remainder4Coefficient4.coeff n = 0 := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence2C4_remainder4Coefficient4Chunk0_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk1_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk2_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk3_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk4_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk5_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk6_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk7_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk8_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk9_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk10_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk11_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk12_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk13_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk14_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk15_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk16_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk17_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk18_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk19_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk20_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk21_coeff_high n h]
  rw [recurrence2C4_remainder4Coefficient4Chunk22_coeff_high n h]
  norm_num

theorem recurrence2C4_natDegree_le :
    remainder4Coefficient4.natDegree ≤ 178 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence2C4_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
