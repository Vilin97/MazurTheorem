/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B3 source bound

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence4B3_remainder5Coefficient3Chunk0_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk0.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk1_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk1.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk2_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk2.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk3_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk3.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk4_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk4.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk5_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk5.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk6_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk6.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk7_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk7.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk8_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk8.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk9_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk9.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk10_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk10.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk11_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk11.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk12_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk12.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk13_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk13.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk14_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk14.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk15_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk15.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk16_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk16.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk17_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk17.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk18_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk18.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk19_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk19.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk19 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

private theorem recurrence4B3_remainder5Coefficient3Chunk20_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3Chunk20.coeff n = 0 := by
  unfold remainder5Coefficient3Chunk20 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs
  all_goals norm_num
  all_goals omega

theorem recurrence4B3_coeff_high (n : ℕ) (h : 164 < n) :
    remainder5Coefficient3.coeff n = 0 := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence4B3_remainder5Coefficient3Chunk0_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk1_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk2_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk3_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk4_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk5_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk6_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk7_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk8_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk9_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk10_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk11_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk12_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk13_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk14_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk15_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk16_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk17_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk18_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk19_coeff_high n h]
  rw [recurrence4B3_remainder5Coefficient3Chunk20_coeff_high n h]
  norm_num

theorem recurrence4B3_natDegree_le :
    remainder5Coefficient3.natDegree ≤ 164 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence4B3_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
