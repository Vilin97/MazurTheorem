/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: A0 source bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence4A0_remainder4Coefficient0Chunk0_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk0.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk1_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk1.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk2_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk2.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk3_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk3.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk4_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk4.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk5_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk5.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk6_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk6.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk7_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk7.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk8_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk8.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk9_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk9.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk10_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk10.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk11_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk11.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk12_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk12.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk13_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk13.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk14_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk14.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk15_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk15.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk16_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk16.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk17_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk17.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk18_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk18.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk19_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk19.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk19 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk20_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk20.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk20 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk21_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk21.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk21 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk22_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk22.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk22 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk23_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk23.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk23 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4A0_remainder4Coefficient0Chunk24_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0Chunk24.coeff n = 0 := by
  unfold remainder4Coefficient0Chunk24 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

theorem recurrence4A0_coeff_high (n : ℕ) (h : 194 < n) :
    remainder4Coefficient0.coeff n = 0 := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence4A0_remainder4Coefficient0Chunk0_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk1_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk2_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk3_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk4_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk5_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk6_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk7_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk8_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk9_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk10_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk11_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk12_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk13_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk14_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk15_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk16_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk17_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk18_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk19_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk20_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk21_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk22_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk23_coeff_high n h]
  rw [recurrence4A0_remainder4Coefficient0Chunk24_coeff_high n h]
  norm_num

theorem recurrence4A0_natDegree_le :
    remainder4Coefficient0.natDegree ≤ 194 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence4A0_coeff_high

theorem recurrence4A0_coeff_low (n : ℕ) (h : n < 1) :
    remainder4Coefficient0.coeff n = 0 := by
  have hn : n = 0 := by omega
  subst n
  simpa only using recurrence4A0_coeff_0

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
