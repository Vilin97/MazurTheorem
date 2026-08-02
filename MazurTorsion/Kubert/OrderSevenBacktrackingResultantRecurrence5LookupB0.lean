/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B0 source bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence5B0_remainder6Coefficient0Chunk0_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk0.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk1_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk1.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk2_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk2.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk3_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk3.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk4_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk4.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk5_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk5.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk6_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk6.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk7_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk7.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk8_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk8.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk9_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk9.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk10_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk10.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk11_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk11.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk12_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk12.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk13_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk13.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk14_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk14.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk15_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk15.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk16_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk16.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk17_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk17.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk18_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk18.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B0_remainder6Coefficient0Chunk19_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0Chunk19.coeff n = 0 := by
  unfold remainder6Coefficient0Chunk19 coefficientTerm
  simp only [Polynomial.coeff_monomial]
  split_ifs <;> norm_num
  omega

theorem recurrence5B0_coeff_high (n : ℕ) (h : 153 < n) :
    remainder6Coefficient0.coeff n = 0 := by
  unfold remainder6Coefficient0 remainder6Coefficient0Block1 remainder6Coefficient0Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence5B0_remainder6Coefficient0Chunk0_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk1_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk2_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk3_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk4_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk5_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk6_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk7_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk8_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk9_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk10_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk11_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk12_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk13_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk14_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk15_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk16_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk17_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk18_coeff_high n h]
  rw [recurrence5B0_remainder6Coefficient0Chunk19_coeff_high n h]
  norm_num

theorem recurrence5B0_natDegree_le :
    remainder6Coefficient0.natDegree ≤ 153 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence5B0_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
