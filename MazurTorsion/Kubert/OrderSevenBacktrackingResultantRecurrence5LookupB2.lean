/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2 source bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence5B2_remainder6Coefficient2Chunk0_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk0.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk1_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk1.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk2_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk2.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk3_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk3.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk4_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk4.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk5_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk5.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk6_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk6.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk7_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk7.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk8_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk8.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk9_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk9.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk10_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk10.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk11_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk11.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk12_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk12.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk13_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk13.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk14_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk14.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk15_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk15.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk16_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk16.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk17_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk17.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B2_remainder6Coefficient2Chunk18_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2Chunk18.coeff n = 0 := by
  unfold remainder6Coefficient2Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence5B2_coeff_high (n : ℕ) (h : 145 < n) :
    remainder6Coefficient2.coeff n = 0 := by
  unfold remainder6Coefficient2 remainder6Coefficient2Block1 remainder6Coefficient2Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence5B2_remainder6Coefficient2Chunk0_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk1_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk2_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk3_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk4_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk5_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk6_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk7_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk8_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk9_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk10_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk11_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk12_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk13_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk14_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk15_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk16_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk17_coeff_high n h]
  rw [recurrence5B2_remainder6Coefficient2Chunk18_coeff_high n h]
  norm_num

theorem recurrence5B2_natDegree_le :
    remainder6Coefficient2.natDegree ≤ 145 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence5B2_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
