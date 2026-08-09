/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic

/-!
# Concrete norm certificates for the `X₁(18)` two-division algebra

This file evaluates the relative norms of the explicit squareclass
representatives used in the two-descent.  The proofs use only the determinant
formula from `XOneEighteenTwoDivisionArithmetic` and the defining cubic
relation for the coefficient generator.  In particular, no field structure on
the relative cubic algebra is used.
-/

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

private theorem tau_pow_four : Q.tau ^ 4 = 3 * Q.tau ^ 2 + Q.tau := by
  calc
    Q.tau ^ 4 = Q.tau * Q.tau ^ 3 := by ring
    _ = Q.tau * (3 * Q.tau + 1) := by rw [Q.tau_cubic]
    _ = 3 * Q.tau ^ 2 + Q.tau := by ring

private theorem tau_pow_five :
    Q.tau ^ 5 = Q.tau ^ 2 + 9 * Q.tau + 3 := by
  calc
    Q.tau ^ 5 = Q.tau * Q.tau ^ 4 := by ring
    _ = Q.tau * (3 * Q.tau ^ 2 + Q.tau) := by rw [tau_pow_four]
    _ = 3 * Q.tau ^ 3 + Q.tau ^ 2 := by ring
    _ = Q.tau ^ 2 + 9 * Q.tau + 3 := by rw [Q.tau_cubic]; ring

private theorem tau_pow_six :
    Q.tau ^ 6 = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by
  calc
    Q.tau ^ 6 = (Q.tau ^ 3) ^ 2 := by ring
    _ = (3 * Q.tau + 1) ^ 2 := by rw [Q.tau_cubic]
    _ = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by ring

/-- The first explicit dyadic generator has relative norm `2`. -/
theorem norm_alpha : Algebra.norm Q.K alpha = 2 := by
  rw [alpha, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The second explicit dyadic generator has relative norm `2(τ+1)`. -/
theorem norm_beta : Algebra.norm Q.K beta = 2 * Q.tau + 2 := by
  rw [beta, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The explicit generator above `3` has relative norm `-3`. -/
theorem norm_rho : Algebra.norm Q.K rho = -3 := by
  rw [rho, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four, Q.tau_cubic]
  ring

/-- The first kernel representative has relative norm one. -/
theorem norm_h1 : Algebra.norm Q.K h1 = 1 := by
  rw [h1, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The second kernel representative has relative norm one. -/
theorem norm_h2 : Algebra.norm Q.K h2 = 1 := by
  rw [h2, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The third kernel representative has relative norm four. -/
theorem norm_h3 : Algebra.norm Q.K h3 = 4 := by
  rw [h3, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four, Q.tau_cubic]
  ring

/-- The fourth kernel representative has the displayed quadratic norm. -/
theorem norm_h4 :
    Algebra.norm Q.K h4 = 4 * (-Q.tau ^ 2 + Q.tau + 4) := by
  rw [h4, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four]
  ring

/-- The coefficient occurring in `norm_h4` is the advertised square after
using the coefficient cubic relation. -/
theorem four_mul_neg_tau_sq_add_tau_add_four_eq_square :
    4 * (-Q.tau ^ 2 + Q.tau + 4) = (2 * (Q.tau ^ 2 - 2)) ^ 2 := by
  rw [show (2 * (Q.tau ^ 2 - 2)) ^ 2 =
    4 * Q.tau ^ 4 - 16 * Q.tau ^ 2 + 16 by ring, tau_pow_four]
  ring

/-- The norm of `h4`, in a form immediately usable by squareclass code. -/
theorem norm_h4_eq_square :
    Algebra.norm Q.K h4 = (2 * (Q.tau ^ 2 - 2)) ^ 2 := by
  rw [norm_h4, four_mul_neg_tau_sq_add_tau_add_four_eq_square]

/-- All four explicit kernel representatives have square relative norm. -/
theorem kernel_generators_have_square_norm :
    (∃ z : Q.K, Algebra.norm Q.K h1 = z ^ 2) ∧
      (∃ z : Q.K, Algebra.norm Q.K h2 = z ^ 2) ∧
      (∃ z : Q.K, Algebra.norm Q.K h3 = z ^ 2) ∧
      (∃ z : Q.K, Algebra.norm Q.K h4 = z ^ 2) := by
  refine ⟨⟨1, by simpa using norm_h1⟩, ?_⟩
  refine ⟨⟨1, by simpa using norm_h2⟩, ?_⟩
  refine ⟨⟨2, ?_⟩, ⟨2 * (Q.tau ^ 2 - 2), norm_h4_eq_square⟩⟩
  rw [norm_h3]
  norm_num

end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic
