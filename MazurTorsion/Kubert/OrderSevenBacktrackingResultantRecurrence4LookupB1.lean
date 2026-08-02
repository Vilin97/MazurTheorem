/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B1 source bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence4B1_remainder5Coefficient1Chunk0_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk0.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk1_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk1.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk2_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk2.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk3_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk3.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk4_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk4.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk5_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk5.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk6_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk6.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk7_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk7.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk8_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk8.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk9_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk9.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk10_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk10.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk11_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk11.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk12_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk12.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk13_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk13.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk14_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk14.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk15_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk15.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk16_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk16.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk17_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk17.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk18_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk18.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk19_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk19.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk19 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk20_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk20.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk20 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B1_remainder5Coefficient1Chunk21_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1Chunk21.coeff n = 0 := by
  unfold remainder5Coefficient1Chunk21 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

theorem recurrence4B1_coeff_high (n : ℕ) (h : 172 < n) :
    remainder5Coefficient1.coeff n = 0 := by
  unfold
    remainder5Coefficient1
    remainder5Coefficient1Block1
    remainder5Coefficient1Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence4B1_remainder5Coefficient1Chunk0_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk1_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk2_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk3_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk4_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk5_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk6_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk7_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk8_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk9_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk10_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk11_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk12_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk13_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk14_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk15_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk16_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk17_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk18_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk19_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk20_coeff_high n h]
  rw [recurrence4B1_remainder5Coefficient1Chunk21_coeff_high n h]
  norm_num

theorem recurrence4B1_natDegree_le :
    remainder5Coefficient1.natDegree ≤ 172 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence4B1_coeff_high

theorem recurrence4B1_coeff_low (n : ℕ) (h : n < 1) :
    remainder5Coefficient1.coeff n = 0 := by
  have hn : n = 0 := by omega
  subst n
  simpa only using recurrence4B1_coeff_0

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
