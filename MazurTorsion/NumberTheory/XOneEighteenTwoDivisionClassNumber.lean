/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Integral arithmetic for the `X₁(18)` two-division compositum

This file begins the independently checked class-number certificate for the
degree-nine two-division compositum.  The first essential step is to prove
that the relative cubic algebra from
`XOneEighteenTwoDivisionArithmetic` really is a field.  We do this without a
computer algebra oracle: if the two rational cubic fields met, their power
bases would be related by a rational change-of-basis matrix.  Their exact
discriminants have opposite signs, which is impossible because a basis
discriminant changes by the square of a determinant.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic

private theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

private def coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic

private theorem twoDivisionPolynomial_monic : twoDivisionPolynomial.Monic := by
  simp only [twoDivisionPolynomial]
  monicity <;> norm_num

private def twoDivisionPowerBasis : PowerBasis ℚ F :=
  AdjoinRoot.powerBasis' twoDivisionPolynomial_monic

private theorem coefficientPowerBasis_minpolyGen :
    coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm

private theorem twoDivisionPowerBasis_minpolyGen :
    twoDivisionPowerBasis.minpolyGen = twoDivisionPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval sigma twoDivisionPolynomial = 0 := by
    simp only [twoDivisionPolynomial, map_sub, map_pow, aeval_X,
      map_mul, map_ofNat]
    linear_combination sigma_cubic
  exact (minpoly.eq_of_irreducible_of_monic twoDivisionPolynomial_irreducible
    hroot twoDivisionPolynomial_monic).symm

private theorem coefficientPowerBasis_dim : coefficientPowerBasis.dim = 3 := by
  rw [coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!

private theorem twoDivisionPowerBasis_dim : twoDivisionPowerBasis.dim = 3 := by
  rw [twoDivisionPowerBasis, AdjoinRoot.powerBasis'_dim]
  exact twoDivisionPolynomial_natDegree

/-! ## The two incompatible cubic discriminants -/

/-- Determinant certificate for the derivative norm of a depressed cubic
`X³ - 3X - d`.  This is deliberately proved at the level of an arbitrary
power basis, so the certificate does not depend on an external polynomial
discriminant computation. -/
private theorem norm_cubic_derivative
    {L : Type*} [CommRing L] [Algebra ℚ L]
    (pb : PowerBasis ℚ L) (hdim : pb.dim = 3) (d : ℚ)
    (hmin : pb.minpolyGen = X ^ 3 - 3 * X - C d) :
    Algebra.norm ℚ (3 * pb.gen ^ 2 - 3) = 27 * (d ^ 2 - 4) := by
  rw [Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [pb.leftMulMatrix, hmin]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) ℚ :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -(X ^ 3 - 3 * X - C d).coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3 *
        companion ^ 2 -
      algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3) = _
  have hcompanion :
      Matrix.reindexAlgEquiv ℚ ℚ e companion =
        !![0, 0, d; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, coeff_sub, coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv ℚ (R := ℚ) e]
  rw [map_sub, map_mul, map_pow]
  rw [(Matrix.reindexAlgEquiv ℚ ℚ e).commutes 3, hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring

private theorem coefficientPowerBasis_discriminant :
    Algebra.discr ℚ coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative coefficientPowerBasis
    coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using coefficientPowerBasis_minpolyGen)
  rw [show coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]
  norm_num

private theorem twoDivisionPowerBasis_discriminant :
    Algebra.discr ℚ twoDivisionPowerBasis.basis = -2592 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [twoDivisionPowerBasis.finrank, twoDivisionPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, twoDivisionPowerBasis_minpolyGen]
  simp only [twoDivisionPolynomial, derivative_sub, derivative_pow,
    derivative_X, derivative_mul, derivative_ofNat, mul_one,
    Nat.cast_ofNat, zero_mul, sub_zero]
  rw [show twoDivisionPowerBasis.gen = sigma by rfl]
  have hnorm := norm_cubic_derivative twoDivisionPowerBasis
    twoDivisionPowerBasis_dim 10 (by
      simpa only [twoDivisionPolynomial, Polynomial.C_ofNat] using
        twoDivisionPowerBasis_minpolyGen)
  rw [show twoDivisionPowerBasis.gen = sigma by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]

/-! ## Linear disjointness of the two rational cubic fields -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim]

private theorem relativePolynomial_eq_map :
    twoDivisionPolynomial.map (algebraMap ℚ Q.K) = relativePolynomial := by
  norm_num [twoDivisionPolynomial, relativePolynomial]

/-- The two-division cubic stays irreducible after extending scalars from
`ℚ` to the real cubic coefficient field.  The proof uses only the two exact
power-basis discriminants above, not the ring of integers of either field. -/
theorem relativePolynomial_irreducible : Irreducible relativePolynomial := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [relativePolynomial_natDegree]
    norm_num
  · intro x hx
    have hxroot : Polynomial.aeval x twoDivisionPolynomial = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, relativePolynomial_eq_map]
      exact hx
    have hxroot' :
        Polynomial.aeval x (minpoly ℚ twoDivisionPowerBasis.gen) = 0 := by
      rw [← PowerBasis.minpolyGen_eq,
        twoDivisionPowerBasis_minpolyGen]
      exact hxroot
    let φ : F →ₐ[ℚ] Q.K := twoDivisionPowerBasis.lift x hxroot'
    have hφinj : Function.Injective φ := φ.toRingHom.injective
    have hfinrank : Module.finrank ℚ F = Module.finrank ℚ Q.K := by
      rw [finrank_F_over_rat, coefficientField_finrank]
    have hφsurj : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hfinrank).mp hφinj
    let e : F ≃ₐ[ℚ] Q.K := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
    let mappedBasis : Basis (Fin twoDivisionPowerBasis.dim) ℚ Q.K :=
      twoDivisionPowerBasis.basis.map e.toLinearEquiv
    have hmapped_discriminant :
        Algebra.discr ℚ mappedBasis = -2592 := by
      rw [← twoDivisionPowerBasis_discriminant]
      calc
        Algebra.discr ℚ mappedBasis = Algebra.discr ℚ
            (e ∘ twoDivisionPowerBasis.basis) := by
          congr 1
        _ = Algebra.discr ℚ twoDivisionPowerBasis.basis :=
          (Algebra.discr_eq_discr_of_algEquiv
            twoDivisionPowerBasis.basis e).symm
    let coefficientBasis' : Basis (Fin twoDivisionPowerBasis.dim) ℚ Q.K :=
      coefficientPowerBasis.basis.reindex
        (coefficientPowerBasis.basis.indexEquiv mappedBasis)
    have hcoefficient_discriminant :
        Algebra.discr ℚ coefficientBasis' = 81 := by
      dsimp [coefficientBasis']
      rw [Basis.coe_reindex,
        Algebra.discr_reindex, coefficientPowerBasis_discriminant]
    have hchange :
        Algebra.discr ℚ mappedBasis =
          (coefficientBasis'.toMatrix mappedBasis).det ^ 2 *
            Algebra.discr ℚ coefficientBasis' := by
      convert! Algebra.discr_of_matrix_vecMul coefficientBasis'
        (coefficientBasis'.toMatrix mappedBasis) using 1
      rw [Basis.toMatrix_map_vecMul]
    rw [hmapped_discriminant, hcoefficient_discriminant] at hchange
    have hsquare :
        0 ≤ (coefficientBasis'.toMatrix mappedBasis).det ^ 2 := sq_nonneg _
    nlinarith

instance relativePolynomial_irreducibleFact :
    Fact (Irreducible relativePolynomial) :=
  ⟨relativePolynomial_irreducible⟩

/-- The now-field-valued relative algebra is a number field. -/
instance compositumNumberField : NumberField M :=
  letI : Module.Finite Q.K M :=
    (AdjoinRoot.powerBasis' relativePolynomial_monic).finite
  NumberField.of_module_finite Q.K M

/-- The compositum has degree nine over `ℚ`. -/
theorem finrank_M_over_rat : Module.finrank ℚ M = 9 := by
  rw [← Module.finrank_mul_finrank ℚ Q.K M, finrank_M_over_K,
    coefficientField_finrank]

end

end MazurTorsion.XOneEighteenTwoDivisionClassNumber
