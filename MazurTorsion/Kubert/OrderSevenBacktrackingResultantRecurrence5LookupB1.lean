/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1Low
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B1 source bound

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence5B1_remainder6Coefficient1Chunk0_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk0.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk1_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk1.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk2_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk2.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk3_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk3.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk4_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk4.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk5_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk5.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk6_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk6.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk7_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk7.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk8_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk8.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk9_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk9.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk10_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk10.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk11_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk11.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk12_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk12.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk13_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk13.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk14_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk14.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk15_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk15.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk16_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk16.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk17_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk17.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5B1_remainder6Coefficient1Chunk18_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1Chunk18.coeff n = 0 := by
  unfold remainder6Coefficient1Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence5B1_coeff_high (n : ℕ) (h : 149 < n) :
    remainder6Coefficient1.coeff n = 0 := by
  unfold remainder6Coefficient1 remainder6Coefficient1Block1 remainder6Coefficient1Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence5B1_remainder6Coefficient1Chunk0_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk1_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk2_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk3_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk4_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk5_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk6_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk7_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk8_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk9_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk10_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk11_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk12_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk13_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk14_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk15_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk16_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk17_coeff_high n h]
  rw [recurrence5B1_remainder6Coefficient1Chunk18_coeff_high n h]
  norm_num

theorem recurrence5B1_natDegree_le :
    remainder6Coefficient1.natDegree ≤ 149 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence5B1_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
