/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentMagmaBridge
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.FinCases

/-!
# Concrete `Q_2` point inputs for the `X_1(13)` two-descent

This file checks the two elementary local-point inputs used by the planned
`XOneThirteenTwoDescentLocalIntersection` consumer.  The right-hand side of
the genus-two model takes the values `313 / 64` and `193` at `1 / 2` and
`2`, respectively.  Both odd numerators are `1` modulo `8`; the resulting
square roots in `Q_2` are constructed using Mathlib's checked Hensel lemma.

The final declaration records only the elementary arithmetic common to the
two possible factor patterns of the sextic over `Q_2`.  It does not assert
Stoll's Jacobian-dimension formula or any local Kummer-image theorem.

The repeated-factor input itself is also checked here: the alternate sextic
used for the descent is the square of the irreducible cubic
`X^3 + X^2 + 1` modulo `2`.
-/

namespace MazurTorsion.XOneThirteenTwoDescentLocalPointInputs

open Polynomial
open XOneThirteenTwoDescentMagmaBridge

noncomputable section

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The right-hand side of the fixed genus-two model, evaluated in `Q`. -/
def curveRhs (x : ℚ) : ℚ :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- Exact value at the point whose descent image is represented by
`qB = 1 - 2 * a^2`. -/
theorem curveRhs_oneHalf : curveRhs (1 / 2) = 313 / 64 := by
  norm_num [curveRhs]

/-- Exact value at the point whose descent image is represented by
`qC = 2 - a^2`. -/
theorem curveRhs_two : curveRhs 2 = 193 := by
  norm_num [curveRhs]

theorem threeHundredThirteen_mod_eight : 313 % 8 = 1 := by
  norm_num

theorem oneHundredNinetyThree_mod_eight : 193 % 8 = 1 := by
  norm_num

/-! ## The repeated cubic factor modulo two -/

/-- The sole distinct factor of the alternate sextic modulo `2`. -/
def phi : (ZMod 2)[X] := X ^ 3 + X ^ 2 + 1

theorem phi_natDegree : phi.natDegree = 3 := by
  simp only [phi]
  compute_degree!

theorem phi_monic : phi.Monic := by
  simp only [phi]
  monicity!

/-- The cubic has no root in `ZMod 2`, so it is irreducible. -/
theorem phi_irreducible : Irreducible phi := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [phi_natDegree]
    norm_num
  · intro x
    unfold Polynomial.IsRoot
    simp only [phi, eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide

/-- Exact repeated-factor identity for the alternate descent polynomial. -/
theorem magmaSexticModTwo_eq_phi_sq : magmaSexticModTwo = phi ^ 2 := by
  rw [magmaSexticModTwo_eq]
  simp only [phi]
  ring_nf
  reduce_mod_char

/-- The complete polynomial input behind the local factor pattern: there is
one displayed irreducible monic factor, of degree three, and the sextic is
its square.  No Jacobian-dimension formula is included. -/
theorem magmaSexticModTwo_singleFactorData :
    phi.Monic ∧ Irreducible phi ∧ phi.natDegree = 3 ∧
      magmaSexticModTwo = phi ^ 2 := by
  exact ⟨phi_monic, phi_irreducible, phi_natDegree,
    magmaSexticModTwo_eq_phi_sq⟩

/-- The concrete `1 mod 8` Hensel step.  It is kept private because the
downstream descent only needs the two displayed instances below. -/
private theorem exists_padicInt_sq_eq_of_eight_dvd_one_sub
    (n : ℤ) (hdiv : (8 : ℤ) ∣ 1 - n) :
    ∃ z : ℤ_[2], z ^ 2 = n := by
  let F : ℤ[X] := X ^ 2 - C n
  let a : ℤ_[2] := 1
  have hEval : F.aeval a = ((1 - n : ℤ) : ℤ_[2]) := by
    simp [F, a]
  have hDerivative : F.derivative.aeval a = (2 : ℤ_[2]) := by
    norm_num [F, a, aeval_def]
  have hNormBound :
      ‖((1 - n : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    exact (PadicInt.norm_int_le_pow_iff_dvd
      (p := 2) (k := 1 - n) (n := 3)).2 (by
        norm_num
        exact hdiv)
  have hHensel : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hEval, hDerivative]
    calc
      ‖((1 - n : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := hNormBound
      _ < ((2 : ℝ)⁻¹) ^ 2 := by norm_num
      _ = ‖(2 : ℤ_[2])‖ ^ 2 := by
        exact congrArg (fun x : ℝ ↦ x ^ 2) (PadicInt.norm_p (p := 2)).symm
  obtain ⟨z, hz, -⟩ := hensels_lemma hHensel
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 - (n : ℤ_[2]) = 0 := by
    simpa [F] using hz
  exact sub_eq_zero.mp hz'

/-- The odd unit `193` is a square in `Q_2`. -/
theorem exists_padic_sq_eq_oneHundredNinetyThree :
    ∃ y : ℚ_[2], y ^ 2 = (193 : ℚ_[2]) := by
  obtain ⟨z, hz⟩ := exists_padicInt_sq_eq_of_eight_dvd_one_sub
    193 (by norm_num)
  refine ⟨z, ?_⟩
  calc
    (z : ℚ_[2]) ^ 2 = (((193 : ℤ) : ℤ_[2]) : ℚ_[2]) := by
      simpa only [PadicInt.coe_pow] using
        congrArg (fun w : ℤ_[2] ↦ (w : ℚ_[2])) hz
    _ = ((193 : ℤ) : ℚ_[2]) := PadicInt.coe_intCast 193
    _ = 193 := Int.cast_ofNat 193

/-- The value `313 / 64` is a square in `Q_2`. -/
theorem exists_padic_sq_eq_threeHundredThirteen_div_sixtyFour :
    ∃ y : ℚ_[2], y ^ 2 = ((313 / 64 : ℚ) : ℚ_[2]) := by
  obtain ⟨z, hz⟩ := exists_padicInt_sq_eq_of_eight_dvd_one_sub
    313 (by norm_num)
  refine ⟨(z : ℚ_[2]) / 8, ?_⟩
  have hzQ : ((z : ℚ_[2]) ^ 2) = 313 := by
    calc
      (z : ℚ_[2]) ^ 2 = (((313 : ℤ) : ℤ_[2]) : ℚ_[2]) := by
        simpa only [PadicInt.coe_pow] using
          congrArg (fun w : ℤ_[2] ↦ (w : ℚ_[2])) hz
      _ = ((313 : ℤ) : ℚ_[2]) := PadicInt.coe_intCast 313
      _ = 313 := Int.cast_ofNat 313
  rw [div_pow, hzQ]
  norm_num

/-- The two possible local factor-count/parity pairs give the same numeric
expression.  This is only the arithmetic substitution into
`m_2 - 1 - t_2 + 2`; no Jacobian formula is asserted here. -/
theorem localFactorPattern_numericExpression
    (m₂ t₂ : ℕ)
    (hpattern : (m₂ = 1 ∧ t₂ = 0) ∨ (m₂ = 2 ∧ t₂ = 1)) :
    m₂ - 1 - t₂ + 2 = 2 := by
  rcases hpattern with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

end

end MazurTorsion.XOneThirteenTwoDescentLocalPointInputs
