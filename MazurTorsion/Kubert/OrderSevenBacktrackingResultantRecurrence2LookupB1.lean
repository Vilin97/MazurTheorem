/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1Low
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1High
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: B1 source bound

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem recurrence2B1_remainder3Coefficient1Chunk0_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk0.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk1_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk1.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk2_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk2.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk3_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk3.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk4_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk4.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk5_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk5.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk6_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk6.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk6 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk7_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk7.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk7 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk8_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk8.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk8 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk9_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk9.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk9 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk10_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk10.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk10 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk11_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk11.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk11 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk12_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk12.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk12 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk13_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk13.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk13 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk14_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk14.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk14 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk15_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk15.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk15 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk16_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk16.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk16 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk17_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk17.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk17 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence2B1_remainder3Coefficient1Chunk18_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1Chunk18.coeff n = 0 := by
  unfold remainder3Coefficient1Chunk18 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

theorem recurrence2B1_coeff_high (n : ℕ) (h : 150 < n) :
    remainder3Coefficient1.coeff n = 0 := by
  unfold
    remainder3Coefficient1
    remainder3Coefficient1Block1
    remainder3Coefficient1Block0
  simp only [Polynomial.coeff_add]
  rw [recurrence2B1_remainder3Coefficient1Chunk0_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk1_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk2_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk3_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk4_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk5_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk6_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk7_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk8_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk9_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk10_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk11_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk12_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk13_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk14_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk15_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk16_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk17_coeff_high n h]
  rw [recurrence2B1_remainder3Coefficient1Chunk18_coeff_high n h]
  norm_num

theorem recurrence2B1_natDegree_le :
    remainder3Coefficient1.natDegree ≤ 150 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence2B1_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
