/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A2 source bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence4A2_remainder4Coefficient2Chunk0_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk0.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk1_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk1.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk2_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk2.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk3_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk3.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk4_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk4.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk5_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk5.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk6_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk6.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk7_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk7.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk8_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk8.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk9_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk9.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk10_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk10.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk11_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk11.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk12_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk12.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk13_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk13.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk14_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk14.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk15_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk15.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk16_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk16.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk17_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk17.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk18_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk18.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk19_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk19.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk19 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk20_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk20.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk20 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk21_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk21.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk21 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk22_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk22.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk22 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A2_remainder4Coefficient2Chunk23_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2Chunk23.coeff n = 0 := by
  unfold remainder4Coefficient2Chunk23 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

theorem recurrence4A2_coeff_high (n : ℕ) (h : 186 < n) :
    remainder4Coefficient2.coeff n = 0 := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence4A2_remainder4Coefficient2Chunk0_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk1_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk2_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk3_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk4_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk5_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk6_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk7_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk8_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk9_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk10_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk11_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk12_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk13_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk14_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk15_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk16_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk17_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk18_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk19_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk20_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk21_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk22_coeff_high n h]
  rw [recurrence4A2_remainder4Coefficient2Chunk23_coeff_high n h]
  norm_num

theorem recurrence4A2_natDegree_le :
    remainder4Coefficient2.natDegree ≤ 186 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence4A2_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
