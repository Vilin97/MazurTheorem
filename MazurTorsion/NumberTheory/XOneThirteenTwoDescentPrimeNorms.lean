/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentPrimeSupport
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentDiscriminant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Norm certificates for the prime-supported `X₁(13)` descent generators

This file connects the three explicit elements used by
`XOneThirteenTwoDescentPrimeSupport` to actual finite-index principal ideals
in the integral Magma order.  The retained certificates are the three
six-by-six multiplication matrices.  Their determinants give quotient
cardinalities `8`, `13`, and `2197`; short Bezout identities additionally
place the ideals over the rational primes `2` and `13`.

No maximal-order identification is used in these computations.  A later
section gives the explicit injection into the ring of integers and extends
the ideals, without claiming unproved maximal-order quotient cardinalities.
-/

namespace MazurTorsion.XOneThirteenTwoDescentPrimeNorms

open Module Polynomial
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentMagmaBridge
open XOneThirteenTwoDescentPrimeSupport
open XOneThirteenTwoDescentDiscriminant

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

private local instance : IsDomain MagmaAlgebra :=
  oldToMagmaEquiv.symm.toMulEquiv.isDomain

/-- The alternate rational sextic is irreducible. -/
theorem magmaRationalSextic_irreducible :
    Irreducible magmaRationalSextic := by
  rw [← magmaQuotientPowerBasis_minpolyGen,
    PowerBasis.minpolyGen_eq]
  exact minpoly.irreducible magmaQuotientPowerBasis.isIntegral_gen

/-- The integral alternate sextic is irreducible, by Gauss's lemma. -/
theorem magmaSextic_irreducible : Irreducible magmaSextic := by
  rw [magmaSextic_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)]
  simpa only [← magmaRationalSextic_eq_map] using
    magmaRationalSextic_irreducible

private theorem magmaSextic_prime : Prime magmaSextic :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp magmaSextic_irreducible

private local instance : IsDomain MagmaOrder :=
  AdjoinRoot.isDomain_of_prime magmaSextic_prime

private local instance : IsTorsionFree ℤ MagmaOrder :=
  AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
    magmaSextic_prime (by
      rw [show magmaSextic.degree = 6 by
        simp only [magmaSextic]
        compute_degree!]
      norm_num)

/-- The canonical integral power basis `1,a,…,a⁵`. -/
def magmaIntegralPowerBasis : PowerBasis ℤ MagmaOrder :=
  AdjoinRoot.powerBasis' magmaSextic_monic

private local instance : Module.Free ℤ MagmaOrder :=
  Module.Free.of_basis magmaIntegralPowerBasis.basis

private local instance : Module.Finite ℤ MagmaOrder :=
  Module.Finite.of_basis magmaIntegralPowerBasis.basis

/-! ## The monogenic order inside the number field -/

private def magmaIntegralEmbeddingIndexEquiv :
    Fin magmaIntegralPowerBasis.dim ≃ Fin 6 :=
  finCongr (by
    change magmaSextic.natDegree = 6
    simp only [magmaSextic]
    compute_degree!)

private def magmaRationalIndexEquiv :
    Fin magmaQuotientPowerBasis.dim ≃ Fin 6 :=
  finCongr magmaQuotientPowerBasis_dim

private def magmaIntegralFixedBasis : Basis (Fin 6) ℤ MagmaOrder :=
  magmaIntegralPowerBasis.basis.reindex magmaIntegralEmbeddingIndexEquiv

private def magmaRationalFixedBasis : Basis (Fin 6) ℚ MagmaAlgebra :=
  magmaQuotientPowerBasis.basis.reindex magmaRationalIndexEquiv

@[simp]
private theorem magmaOrderToAlgebra_fixedBasis (i : Fin 6) :
    magmaOrderToAlgebra (magmaIntegralFixedBasis i) =
      magmaRationalFixedBasis i := by
  rw [magmaIntegralFixedBasis, magmaRationalFixedBasis,
    Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    PowerBasis.basis_eq_pow, PowerBasis.basis_eq_pow]
  change magmaOrderToAlgebra (integralA ^ _) = a ^ _
  rw [map_pow, magmaOrderToAlgebra_integralA]
  congr 1

/-- Base change from the integral Magma order to its rational quotient is
injective.  The proof checks this on the two matching six-term power bases;
it does not assume that the monogenic order is the full ring of integers. -/
theorem magmaOrderToAlgebra_injective :
    Function.Injective magmaOrderToAlgebra := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hs :
      ∑ i : Fin 6,
          ((magmaIntegralFixedBasis.repr x i : ℤ) : ℚ) •
            magmaRationalFixedBasis i = 0 := by
    simp_rw [← magmaOrderToAlgebra_fixedBasis]
    simp only [Int.cast_smul_eq_zsmul]
    simp_rw [← map_zsmul magmaOrderToAlgebra]
    rw [← map_sum, magmaIntegralFixedBasis.sum_repr, hx]
  have hc : ∀ i : Fin 6,
      ((magmaIntegralFixedBasis.repr x i : ℤ) : ℚ) = 0 :=
    Fintype.linearIndependent_iff.mp
      magmaRationalFixedBasis.linearIndependent _ hs
  apply magmaIntegralFixedBasis.ext_elem
  intro i
  simpa using (Int.cast_injective (hc i))

/-- The explicit inclusion of the Magma order into the original sextic
number field. -/
noncomputable def magmaOrderToField : MagmaOrder →ₐ[ℤ] SexticField :=
  (oldToMagmaEquiv.symm.toRingEquiv.toRingHom.comp
    magmaOrderToAlgebra).toIntAlgHom

@[simp]
theorem magmaOrderToField_apply (x : MagmaOrder) :
    magmaOrderToField x =
      oldToMagmaEquiv.symm (magmaOrderToAlgebra x) :=
  rfl

/-- The explicit inclusion into the sextic field is injective. -/
theorem magmaOrderToField_injective :
    Function.Injective magmaOrderToField :=
  oldToMagmaEquiv.symm.injective.comp magmaOrderToAlgebra_injective

private theorem magmaOrderToField_isIntegral (x : MagmaOrder) :
    IsIntegral ℤ (magmaOrderToField x) := by
  exact (IsIntegral.of_finite ℤ x).map magmaOrderToField

/-- The inclusion of the monogenic order into the maximal order of the
sextic number field. -/
noncomputable def magmaOrderToIntegers :
    MagmaOrder →+* NumberField.RingOfIntegers SexticField where
  toFun x := IsIntegralClosure.mk'
    (NumberField.RingOfIntegers SexticField)
    (magmaOrderToField x) (magmaOrderToField_isIntegral x)
  map_zero' := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [IsIntegralClosure.algebraMap_mk', map_zero]
  map_one' := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [IsIntegralClosure.algebraMap_mk', map_one]
  map_add' x y := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [IsIntegralClosure.algebraMap_mk', map_add]
  map_mul' x y := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [IsIntegralClosure.algebraMap_mk', map_mul]

@[simp]
theorem algebraMap_magmaOrderToIntegers (x : MagmaOrder) :
    algebraMap (NumberField.RingOfIntegers SexticField) SexticField
        (magmaOrderToIntegers x) =
      magmaOrderToField x := by
  change algebraMap (NumberField.RingOfIntegers SexticField) SexticField
    (IsIntegralClosure.mk' (NumberField.RingOfIntegers SexticField)
      (magmaOrderToField x)
      (magmaOrderToField_isIntegral x)) = _
  exact IsIntegralClosure.algebraMap_mk' (R := ℤ)
    (NumberField.RingOfIntegers SexticField) (magmaOrderToField x)
    (magmaOrderToField_isIntegral x)

/-- The lift of the monogenic order to the maximal order remains injective. -/
theorem magmaOrderToIntegers_injective :
    Function.Injective magmaOrderToIntegers := by
  intro x y h
  apply magmaOrderToField_injective
  rw [← algebraMap_magmaOrderToIntegers x,
    ← algebraMap_magmaOrderToIntegers y, h]

@[simp]
theorem magmaIntegralPowerBasis_dim : magmaIntegralPowerBasis.dim = 6 := by
  change magmaSextic.natDegree = 6
  simp only [magmaSextic]
  compute_degree!

theorem magmaIntegralPowerBasis_minpolyGen :
    magmaIntegralPowerBasis.minpolyGen = magmaSextic := by
  rw [PowerBasis.minpolyGen_eq]
  exact
    (AdjoinRoot.isAdjoinRootMonic magmaSextic magmaSextic_monic).minpoly_eq
      magmaSextic_irreducible

private def magmaIntegralIndexEquiv :
    Fin magmaIntegralPowerBasis.dim ≃ Fin 6 :=
  finCongr magmaIntegralPowerBasis_dim

/-- Multiplication in the integral order, reindexed to a fixed six-element
coordinate type. -/
def magmaMultiplicationMatrix :
    MagmaOrder →ₐ[ℤ] Matrix (Fin 6) (Fin 6) ℤ :=
  (Matrix.reindexAlgEquiv ℤ ℤ magmaIntegralIndexEquiv).toAlgHom.comp
    (Algebra.leftMulMatrix magmaIntegralPowerBasis.basis)

/-- Multiplication by `a`, in the fixed power basis. -/
def magmaIntegralCompanionMatrix : Matrix (Fin 6) (Fin 6) ℤ :=
  magmaMultiplicationMatrix magmaIntegralPowerBasis.gen

theorem magmaIntegralCompanionMatrix_eq :
    magmaIntegralCompanionMatrix =
      !![0, 0, 0, 0, 0, -1;
         1, 0, 0, 0, 0,  2;
         0, 1, 0, 0, 0, -4;
         0, 0, 1, 0, 0,  4;
         0, 0, 0, 1, 0, -3;
         0, 0, 0, 0, 1,  2] := by
  rw [magmaIntegralCompanionMatrix, magmaMultiplicationMatrix]
  change Matrix.reindexAlgEquiv ℤ ℤ magmaIntegralIndexEquiv
      (Algebra.leftMulMatrix magmaIntegralPowerBasis.basis
        magmaIntegralPowerBasis.gen) = _
  rw [magmaIntegralPowerBasis.leftMulMatrix,
    magmaIntegralPowerBasis_minpolyGen]
  simp only [magmaIntegralPowerBasis_dim]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindexAlgEquiv, Matrix.reindexLinearEquiv,
      Matrix.reindex, magmaIntegralIndexEquiv, magmaIntegralPowerBasis,
      magmaSextic, Polynomial.coeff_one, Polynomial.coeff_X]

@[simp]
theorem magmaMultiplicationMatrix_integralA :
    magmaMultiplicationMatrix integralA = magmaIntegralCompanionMatrix := by
  rfl

theorem primeTwoFactor_multiplicationMatrix :
    magmaMultiplicationMatrix primeTwoFactor =
      !![-1, 0, -1, -2, -2, -1;
         -1, -1, 2, 3, 2, 0;
          1, -1, -5, -6, -5, -2;
          0, 1, 3, 3, 2, -1;
         1, 0, -2, -3, -3, -1;
         0, 1, 2, 2, 1, -1] := by
  calc
    magmaMultiplicationMatrix primeTwoFactor =
        -(1 : Matrix (Fin 6) (Fin 6) ℤ) - magmaIntegralCompanionMatrix +
          magmaIntegralCompanionMatrix ^ 2 + magmaIntegralCompanionMatrix ^ 4 := by
      rw [primeTwoFactor, map_add, map_add, map_sub, map_pow,
        map_pow, map_neg, map_one, magmaMultiplicationMatrix_integralA]
    _ = _ := by
      rw [magmaIntegralCompanionMatrix_eq]
      decide

theorem primeThirteenLinearFactor_multiplicationMatrix :
    magmaMultiplicationMatrix primeThirteenLinearFactor =
      !![-1, 0, 0, 0, 1, 3;
         -1, -1, 0, 0, -2, -5;
         -1, -1, -1, 0, 4, 10;
          0, -1, -1, -1, -4, -8;
          0, 0, -1, -1, 2, 5;
          0, 0, 0, -1, -3, -4] := by
  calc
    magmaMultiplicationMatrix primeThirteenLinearFactor =
        -(1 : Matrix (Fin 6) (Fin 6) ℤ) - magmaIntegralCompanionMatrix -
          magmaIntegralCompanionMatrix ^ 2 := by
      rw [primeThirteenLinearFactor, map_sub, map_sub, map_neg, map_one,
        map_pow, magmaMultiplicationMatrix_integralA]
    _ = _ := by
      rw [magmaIntegralCompanionMatrix_eq]
      decide

theorem primeThirteenCubicFactorRaw_multiplicationMatrix :
    magmaMultiplicationMatrix primeThirteenCubicFactorRaw =
      !![-2, 0, 0, -2, -2, 3;
         -1, -2, 0, 4, 2, -8;
         -2, -1, -2, -8, -4, 14;
          2, -2, -1, 6, 0, -16;
          0, 2, -2, -7, 0, 9;
          0, 0, 2, 2, -3, -6] := by
  calc
    magmaMultiplicationMatrix primeThirteenCubicFactorRaw =
        -(2 : Matrix (Fin 6) (Fin 6) ℤ) - magmaIntegralCompanionMatrix -
          2 * magmaIntegralCompanionMatrix ^ 2 +
          2 * magmaIntegralCompanionMatrix ^ 3 := by
      rw [primeThirteenCubicFactorRaw, map_add, map_sub, map_sub,
        map_mul, map_mul, map_pow, map_pow, map_neg, map_ofNat,
        magmaMultiplicationMatrix_integralA]
    _ = _ := by
      rw [magmaIntegralCompanionMatrix_eq]
      decide

/-! ## Small determinant certificates -/

private def primeTwoMatrixQ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-1, 0, -1, -2, -2, -1;
     -1, -1, 2, 3, 2, 0;
      1, -1, -5, -6, -5, -2;
      0, 1, 3, 3, 2, -1;
      1, 0, -2, -3, -3, -1;
      0, 1, 2, 2, 1, -1]

private def primeTwoLower : Matrix (Fin 6) (Fin 6) ℚ :=
  !![ 1,  0,    0,   0, 0, 0;
      1,  1,    0,   0, 0, 0;
     -1,  1,    1,   0, 0, 0;
      0, -1, -2/3,   1, 0, 0;
      0, -1, -5/9, 1/3, 1, 0;
     -1,  0,  1/3,   1, 0, 1]

private def primeTwoUpper : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-1, 0, -1,   -2,   -2,   -1;
      0, -1, 3,     5,     4,    1;
      0,  0, -9,  -13,   -11,   -4;
      0,  0,  0, -2/3,  -4/3, -8/3;
      0,  0,  0,    0,  -2/3, -4/3;
      0,  0,  0,    0,     0,    2]

private theorem primeTwo_permuted_eq_mul :
    primeTwoMatrixQ.submatrix (Equiv.swap (4 : Fin 6) 5) id =
      primeTwoLower * primeTwoUpper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeTwoMatrixQ, primeTwoLower, primeTwoUpper,
      Matrix.mul_apply, Fin.sum_univ_succ, Equiv.swap_apply_def] <;>
    norm_num

private theorem primeTwoLower_det : Matrix.det primeTwoLower = 1 := by
  rw [← Matrix.det_transpose primeTwoLower,
    Matrix.det_of_upperTriangular]
  · norm_num [primeTwoLower, Matrix.transpose_apply, Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [primeTwoLower, Matrix.transpose_apply]

private theorem primeTwoUpper_det : Matrix.det primeTwoUpper = -8 := by
  rw [Matrix.det_of_upperTriangular]
  · norm_num [primeTwoUpper, Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [primeTwoUpper]

private theorem primeTwoMatrixQ_det : Matrix.det primeTwoMatrixQ = 8 := by
  have h := Matrix.det_permute (Equiv.swap (4 : Fin 6) 5) primeTwoMatrixQ
  rw [primeTwo_permuted_eq_mul, Matrix.det_mul, primeTwoLower_det,
    primeTwoUpper_det, one_mul,
    Equiv.Perm.sign_swap (by decide : (4 : Fin 6) ≠ 5)] at h
  norm_num at h
  linarith

private def primeThirteenLinearMatrixQ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-1, 0, 0, 0, 1, 3;
     -1, -1, 0, 0, -2, -5;
     -1, -1, -1, 0, 4, 10;
      0, -1, -1, -1, -4, -8;
      0, 0, -1, -1, 2, 5;
      0, 0, 0, -1, -3, -4]

private def primeThirteenLinearLower : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0,   0, 0;
     1, 1, 0, 0,   0, 0;
     1, 1, 1, 0,   0, 0;
     0, 1, 1, 1,   0, 0;
     0, 0, 1, 1,   1, 0;
     0, 0, 0, 1, 4/3, 1]

private def primeThirteenLinearUpper : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-1, 0, 0, 0,  1,    3;
      0, -1, 0, 0, -3,   -8;
      0, 0, -1, 0,  6,   15;
      0, 0, 0, -1, -7,  -15;
      0, 0, 0, 0,   3,    5;
      0, 0, 0, 0,   0, 13/3]

private theorem primeThirteenLinearMatrixQ_eq_mul :
    primeThirteenLinearMatrixQ =
      primeThirteenLinearLower * primeThirteenLinearUpper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeThirteenLinearMatrixQ, primeThirteenLinearLower,
      primeThirteenLinearUpper, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem primeThirteenLinearLower_det :
    Matrix.det primeThirteenLinearLower = 1 := by
  rw [← Matrix.det_transpose primeThirteenLinearLower,
    Matrix.det_of_upperTriangular]
  · norm_num [primeThirteenLinearLower, Matrix.transpose_apply,
      Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [primeThirteenLinearLower, Matrix.transpose_apply]

private theorem primeThirteenLinearUpper_det :
    Matrix.det primeThirteenLinearUpper = 13 := by
  rw [Matrix.det_of_upperTriangular]
  · norm_num [primeThirteenLinearUpper, Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [primeThirteenLinearUpper]

private theorem primeThirteenLinearMatrixQ_det :
    Matrix.det primeThirteenLinearMatrixQ = 13 := by
  rw [primeThirteenLinearMatrixQ_eq_mul, Matrix.det_mul,
    primeThirteenLinearLower_det, primeThirteenLinearUpper_det, one_mul]

private def primeThirteenCubicMatrixQ : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-2, 0, 0, -2, -2, 3;
     -1, -2, 0, 4, 2, -8;
     -2, -1, -2, -8, -4, 14;
      2, -2, -1, 6, 0, -16;
      0, 2, -2, -7, 0, 9;
      0, 0, 2, 2, -3, -6]

private def primeThirteenCubicLower : Matrix (Fin 6) (Fin 6) ℚ :=
  !![   1,  0,  0,  0,  0, 0;
      1/2,  1,  0,  0,  0, 0;
        1, 1/2,  1,  0,  0, 0;
       -1,  1, 1/2,  1,  0, 0;
        0, -1,  1,  2,  1, 0;
        0,  0, -1, -2, -1, 1]

private def primeThirteenCubicUpper : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-2, 0, 0,    -2,    -2,      3;
      0, -2, 0,     5,     3,  -19/2;
      0, 0, -2, -17/2,  -7/2,   63/4;
      0, 0, 0,    13/4, -13/4,  -91/8;
      0, 0, 0,       0,    13,   13/2;
      0, 0, 0,       0,     0,  -13/2]

private theorem primeThirteenCubicMatrixQ_eq_mul :
    primeThirteenCubicMatrixQ =
      primeThirteenCubicLower * primeThirteenCubicUpper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeThirteenCubicMatrixQ, primeThirteenCubicLower,
      primeThirteenCubicUpper, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem primeThirteenCubicLower_det :
    Matrix.det primeThirteenCubicLower = 1 := by
  rw [← Matrix.det_transpose primeThirteenCubicLower,
    Matrix.det_of_upperTriangular]
  · norm_num [primeThirteenCubicLower, Matrix.transpose_apply,
      Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [primeThirteenCubicLower, Matrix.transpose_apply]

private theorem primeThirteenCubicUpper_det :
    Matrix.det primeThirteenCubicUpper = 2197 := by
  rw [Matrix.det_of_upperTriangular]
  · norm_num [primeThirteenCubicUpper, Fin.prod_univ_succ]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [primeThirteenCubicUpper]

private theorem primeThirteenCubicMatrixQ_det :
    Matrix.det primeThirteenCubicMatrixQ = 2197 := by
  rw [primeThirteenCubicMatrixQ_eq_mul, Matrix.det_mul,
    primeThirteenCubicLower_det, primeThirteenCubicUpper_det, one_mul]

private def primeTwoMatrixZ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-1, 0, -1, -2, -2, -1;
     -1, -1, 2, 3, 2, 0;
      1, -1, -5, -6, -5, -2;
      0, 1, 3, 3, 2, -1;
      1, 0, -2, -3, -3, -1;
      0, 1, 2, 2, 1, -1]

private def primeThirteenLinearMatrixZ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-1, 0, 0, 0, 1, 3;
     -1, -1, 0, 0, -2, -5;
     -1, -1, -1, 0, 4, 10;
      0, -1, -1, -1, -4, -8;
      0, 0, -1, -1, 2, 5;
      0, 0, 0, -1, -3, -4]

private def primeThirteenCubicMatrixZ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-2, 0, 0, -2, -2, 3;
     -1, -2, 0, 4, 2, -8;
     -2, -1, -2, -8, -4, 14;
      2, -2, -1, 6, 0, -16;
      0, 2, -2, -7, 0, 9;
      0, 0, 2, 2, -3, -6]

private theorem primeTwoMatrixZ_map :
    (Int.castRingHom ℚ).mapMatrix primeTwoMatrixZ = primeTwoMatrixQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeTwoMatrixZ, primeTwoMatrixQ]

private theorem primeThirteenLinearMatrixZ_map :
    (Int.castRingHom ℚ).mapMatrix primeThirteenLinearMatrixZ =
      primeThirteenLinearMatrixQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeThirteenLinearMatrixZ, primeThirteenLinearMatrixQ]

private theorem primeThirteenCubicMatrixZ_map :
    (Int.castRingHom ℚ).mapMatrix primeThirteenCubicMatrixZ =
      primeThirteenCubicMatrixQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeThirteenCubicMatrixZ, primeThirteenCubicMatrixQ]

private theorem primeTwoCertificateMatrix_det :
    Matrix.det
      (!![-1, 0, -1, -2, -2, -1;
          -1, -1, 2, 3, 2, 0;
           1, -1, -5, -6, -5, -2;
           0, 1, 3, 3, 2, -1;
           1, 0, -2, -3, -3, -1;
           0, 1, 2, 2, 1, -1] : Matrix (Fin 6) (Fin 6) ℤ) = 8 := by
  change Matrix.det primeTwoMatrixZ = 8
  apply (Int.castRingHom ℚ).injective_int
  rw [RingHom.map_det, primeTwoMatrixZ_map, primeTwoMatrixQ_det]
  norm_num

private theorem primeThirteenLinearCertificateMatrix_det :
    Matrix.det
      (!![-1, 0, 0, 0, 1, 3;
          -1, -1, 0, 0, -2, -5;
          -1, -1, -1, 0, 4, 10;
           0, -1, -1, -1, -4, -8;
           0, 0, -1, -1, 2, 5;
           0, 0, 0, -1, -3, -4] : Matrix (Fin 6) (Fin 6) ℤ) = 13 := by
  change Matrix.det primeThirteenLinearMatrixZ = 13
  apply (Int.castRingHom ℚ).injective_int
  rw [RingHom.map_det, primeThirteenLinearMatrixZ_map,
    primeThirteenLinearMatrixQ_det]
  norm_num

private theorem primeThirteenCubicCertificateMatrix_det :
    Matrix.det
      (!![-2, 0, 0, -2, -2, 3;
          -1, -2, 0, 4, 2, -8;
          -2, -1, -2, -8, -4, 14;
           2, -2, -1, 6, 0, -16;
           0, 2, -2, -7, 0, 9;
           0, 0, 2, 2, -3, -6] : Matrix (Fin 6) (Fin 6) ℤ) = 2197 := by
  change Matrix.det primeThirteenCubicMatrixZ = 2197
  apply (Int.castRingHom ℚ).injective_int
  rw [RingHom.map_det, primeThirteenCubicMatrixZ_map,
    primeThirteenCubicMatrixQ_det]
  norm_num

/-- The determinant of the fixed multiplication matrix is the integral
algebra norm. -/
theorem norm_eq_det_magmaMultiplicationMatrix (x : MagmaOrder) :
    Algebra.norm ℤ x = Matrix.det (magmaMultiplicationMatrix x) := by
  rw [Algebra.norm_eq_matrix_det magmaIntegralPowerBasis.basis,
    magmaMultiplicationMatrix]
  change Matrix.det (Algebra.leftMulMatrix magmaIntegralPowerBasis.basis x) =
    Matrix.det (Matrix.reindexAlgEquiv ℤ ℤ magmaIntegralIndexEquiv
      (Algebra.leftMulMatrix magmaIntegralPowerBasis.basis x))
  symm
  apply Matrix.det_reindexAlgEquiv

theorem primeTwoFactor_norm :
    Algebra.norm ℤ primeTwoFactor = 8 := by
  rw [norm_eq_det_magmaMultiplicationMatrix,
    primeTwoFactor_multiplicationMatrix]
  exact primeTwoCertificateMatrix_det

theorem primeThirteenLinearFactor_norm :
    Algebra.norm ℤ primeThirteenLinearFactor = 13 := by
  rw [norm_eq_det_magmaMultiplicationMatrix,
    primeThirteenLinearFactor_multiplicationMatrix]
  exact primeThirteenLinearCertificateMatrix_det

theorem primeThirteenCubicFactorRaw_norm :
    Algebra.norm ℤ primeThirteenCubicFactorRaw = 2197 := by
  rw [norm_eq_det_magmaMultiplicationMatrix,
    primeThirteenCubicFactorRaw_multiplicationMatrix]
  exact primeThirteenCubicCertificateMatrix_det

/-! ## Principal ideals and rational-prime support -/

/-- A short Bezout certificate placing the first principal ideal over `2`. -/
theorem primeTwoFactor_bezout :
    (-integralA ^ 3 + integralA ^ 2 - 1) * primeTwoFactor = 2 := by
  have h := integralA_spec
  simp only [primeTwoFactor]
  linear_combination -(integralA + 1) * h

/-- A short Bezout certificate placing the linear principal ideal over `13`. -/
theorem primeThirteenLinearFactor_bezout :
    (integralA ^ 5 - 6 * integralA ^ 4 + 14 * integralA ^ 3 -
        21 * integralA ^ 2 + 23 * integralA - 16) *
      primeThirteenLinearFactor = 13 := by
  have h := integralA_spec
  simp only [primeThirteenLinearFactor]
  linear_combination (3 - integralA) * h

/-- A short Bezout certificate placing the cubic principal ideal over `13`. -/
theorem primeThirteenCubicFactorRaw_bezout :
    (integralA ^ 5 - 4 * integralA ^ 4 + 7 * integralA ^ 3 -
        10 * integralA ^ 2 + 10 * integralA - 8) *
      primeThirteenCubicFactorRaw = 13 := by
  have h := integralA_spec
  simp only [primeThirteenCubicFactorRaw]
  linear_combination (2 * integralA ^ 2 - 6 * integralA + 3) * h

theorem primeTwoFactor_ne_zero : primeTwoFactor ≠ 0 := by
  intro h
  have hb := primeTwoFactor_bezout
  rw [h, mul_zero] at hb
  apply (show (0 : ℤ) ≠ 2 by norm_num)
  apply (isTorsionFree_iff_algebraMap_injective.mp
    (inferInstance : IsTorsionFree ℤ MagmaOrder))
  simpa using hb

theorem primeThirteenLinearFactor_ne_zero :
    primeThirteenLinearFactor ≠ 0 := by
  intro h
  have hb := primeThirteenLinearFactor_bezout
  rw [h, mul_zero] at hb
  apply (show (0 : ℤ) ≠ 13 by norm_num)
  apply (isTorsionFree_iff_algebraMap_injective.mp
    (inferInstance : IsTorsionFree ℤ MagmaOrder))
  simpa using hb

theorem primeThirteenCubicFactorRaw_ne_zero :
    primeThirteenCubicFactorRaw ≠ 0 := by
  intro h
  have hb := primeThirteenCubicFactorRaw_bezout
  rw [h, mul_zero] at hb
  apply (show (0 : ℤ) ≠ 13 by norm_num)
  apply (isTorsionFree_iff_algebraMap_injective.mp
    (inferInstance : IsTorsionFree ℤ MagmaOrder))
  simpa using hb

/-- The principal ideal generated by the explicit factor above `2`. -/
def primeTwoIdeal : Ideal MagmaOrder :=
  Ideal.span ({primeTwoFactor} : Set MagmaOrder)

/-- The principal ideal generated by the explicit linear factor above `13`. -/
def primeThirteenLinearIdeal : Ideal MagmaOrder :=
  Ideal.span ({primeThirteenLinearFactor} : Set MagmaOrder)

/-- The principal ideal generated by the explicit cubic factor above `13`. -/
def primeThirteenCubicIdeal : Ideal MagmaOrder :=
  Ideal.span ({primeThirteenCubicFactorRaw} : Set MagmaOrder)

theorem two_mem_primeTwoIdeal : (2 : MagmaOrder) ∈ primeTwoIdeal := by
  apply Ideal.mem_span_singleton'.mpr
  exact ⟨-integralA ^ 3 + integralA ^ 2 - 1, primeTwoFactor_bezout⟩

theorem thirteen_mem_primeThirteenLinearIdeal :
    (13 : MagmaOrder) ∈ primeThirteenLinearIdeal := by
  apply Ideal.mem_span_singleton'.mpr
  exact ⟨integralA ^ 5 - 6 * integralA ^ 4 + 14 * integralA ^ 3 -
      21 * integralA ^ 2 + 23 * integralA - 16,
    primeThirteenLinearFactor_bezout⟩

theorem thirteen_mem_primeThirteenCubicIdeal :
    (13 : MagmaOrder) ∈ primeThirteenCubicIdeal := by
  apply Ideal.mem_span_singleton'.mpr
  exact ⟨integralA ^ 5 - 4 * integralA ^ 4 + 7 * integralA ^ 3 -
      10 * integralA ^ 2 + 10 * integralA - 8,
    primeThirteenCubicFactorRaw_bezout⟩

private theorem card_quotient_span_singleton (x : MagmaOrder) (hx : x ≠ 0) :
    Nat.card (MagmaOrder ⧸ (Ideal.span ({x} : Set MagmaOrder) : Ideal MagmaOrder)) =
      (Algebra.norm ℤ x).natAbs := by
  let I : Ideal MagmaOrder := Ideal.span ({x} : Set MagmaOrder)
  let bI : Basis (Fin magmaIntegralPowerBasis.dim) ℤ I :=
    Ideal.basisSpanSingleton magmaIntegralPowerBasis.basis hx
  have hcard := Submodule.natAbs_det_basis_change
    magmaIntegralPowerBasis.basis
    (I.restrictScalars ℤ) bI
  have hdet :
      magmaIntegralPowerBasis.basis.det
          (((↑) : I → MagmaOrder) ∘ bI) = Algebra.norm ℤ x := by
    rw [Basis.det_apply, Basis.toMatrix_eq_toMatrix_constr]
    have hconstr :
        (magmaIntegralPowerBasis.basis.constr ℕ).toFun
            (((↑) : I → MagmaOrder) ∘ bI) =
          Algebra.lmul ℤ MagmaOrder x := by
      simpa only [bI, I] using
        (Ideal.constr_basisSpanSingleton
          (N := ℕ) magmaIntegralPowerBasis.basis hx)
    change Matrix.det (LinearMap.toMatrix magmaIntegralPowerBasis.basis
      magmaIntegralPowerBasis.basis
      ((magmaIntegralPowerBasis.basis.constr ℕ).toFun
        (((↑) : I → MagmaOrder) ∘ bI))) = Algebra.norm ℤ x
    rw [hconstr]
    rw [Algebra.norm_eq_matrix_det magmaIntegralPowerBasis.basis]
    rfl
  calc
    Nat.card (MagmaOrder ⧸ (Ideal.span ({x} : Set MagmaOrder) : Ideal MagmaOrder)) =
        Nat.card (MagmaOrder ⧸ I.restrictScalars ℤ) := by
      rw [show Ideal.span ({x} : Set MagmaOrder) = I by rfl]
      exact (Nat.card_congr
        (Submodule.Quotient.restrictScalarsEquiv ℤ
          (I : Submodule MagmaOrder MagmaOrder)).toEquiv).symm
    _ = (Algebra.norm ℤ x).natAbs := by
      rw [← hdet]
      exact hcard.symm

/-- The quotient by the displayed factor above `2` has eight elements. -/
theorem primeTwoIdeal_quotient_card :
    Nat.card (MagmaOrder ⧸ primeTwoIdeal) = 8 := by
  rw [primeTwoIdeal, card_quotient_span_singleton primeTwoFactor
    primeTwoFactor_ne_zero, primeTwoFactor_norm]
  norm_num

/-- The quotient by the displayed linear factor above `13` has thirteen
elements. -/
theorem primeThirteenLinearIdeal_quotient_card :
    Nat.card (MagmaOrder ⧸ primeThirteenLinearIdeal) = 13 := by
  rw [primeThirteenLinearIdeal,
    card_quotient_span_singleton primeThirteenLinearFactor
      primeThirteenLinearFactor_ne_zero,
    primeThirteenLinearFactor_norm]
  norm_num

/-- The quotient by the displayed cubic factor above `13` has `13³`
elements. -/
theorem primeThirteenCubicIdeal_quotient_card :
    Nat.card (MagmaOrder ⧸ primeThirteenCubicIdeal) = 2197 := by
  rw [primeThirteenCubicIdeal,
    card_quotient_span_singleton primeThirteenCubicFactorRaw
      primeThirteenCubicFactorRaw_ne_zero,
    primeThirteenCubicFactorRaw_norm]
  norm_num

/-- The displayed linear factor defines a maximal ideal in the monogenic
order.  Its quotient is a ring with the prime cardinality `13`, hence is
isomorphic to `ZMod 13`. -/
theorem primeThirteenLinearIdeal_isMaximal :
    primeThirteenLinearIdeal.IsMaximal := by
  let Q := MagmaOrder ⧸ primeThirteenLinearIdeal
  letI : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [primeThirteenLinearIdeal_quotient_card]
    norm_num)
  letI : Fintype Q := Fintype.ofFinite Q
  have hcard : Fintype.card Q = 13 := by
    rw [Fintype.card_eq_nat_card]
    exact primeThirteenLinearIdeal_quotient_card
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  let e : ZMod 13 ≃+* Q :=
    ZMod.ringEquivOfPrime Q Fact.out hcard
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField (ZMod 13)) e.symm.toMulEquiv

/-! ## Extension to the maximal order

These are ideal extensions along the checked inclusion above.  Their exact
quotient cardinalities in the maximal order are deliberately not asserted:
that would additionally require a checked index/maximality calculation for
the monogenic order.
-/

/-- Extension of the displayed ideal above `2` to the maximal order. -/
noncomputable def primeTwoIdealExtension :
    Ideal (NumberField.RingOfIntegers SexticField) :=
  primeTwoIdeal.map magmaOrderToIntegers

/-- Extension of the displayed linear ideal above `13` to the maximal
order. -/
noncomputable def primeThirteenLinearIdealExtension :
    Ideal (NumberField.RingOfIntegers SexticField) :=
  primeThirteenLinearIdeal.map magmaOrderToIntegers

/-- Extension of the displayed cubic ideal above `13` to the maximal
order. -/
noncomputable def primeThirteenCubicIdealExtension :
    Ideal (NumberField.RingOfIntegers SexticField) :=
  primeThirteenCubicIdeal.map magmaOrderToIntegers

theorem primeTwoIdeal_le_extension_comap :
    primeTwoIdeal ≤ primeTwoIdealExtension.comap magmaOrderToIntegers :=
  Ideal.le_comap_map

theorem primeThirteenLinearIdeal_le_extension_comap :
    primeThirteenLinearIdeal ≤
      primeThirteenLinearIdealExtension.comap magmaOrderToIntegers :=
  Ideal.le_comap_map

theorem primeThirteenCubicIdeal_le_extension_comap :
    primeThirteenCubicIdeal ≤
      primeThirteenCubicIdealExtension.comap magmaOrderToIntegers :=
  Ideal.le_comap_map

theorem two_mem_primeTwoIdealExtension :
    (2 : NumberField.RingOfIntegers SexticField) ∈
      primeTwoIdealExtension := by
  have h := Ideal.mem_map_of_mem magmaOrderToIntegers
    two_mem_primeTwoIdeal
  simpa only [primeTwoIdealExtension, map_ofNat] using h

theorem thirteen_mem_primeThirteenLinearIdealExtension :
    (13 : NumberField.RingOfIntegers SexticField) ∈
      primeThirteenLinearIdealExtension := by
  have h := Ideal.mem_map_of_mem magmaOrderToIntegers
    thirteen_mem_primeThirteenLinearIdeal
  simpa only [primeThirteenLinearIdealExtension, map_ofNat] using h

theorem thirteen_mem_primeThirteenCubicIdealExtension :
    (13 : NumberField.RingOfIntegers SexticField) ∈
      primeThirteenCubicIdealExtension := by
  have h := Ideal.mem_map_of_mem magmaOrderToIntegers
    thirteen_mem_primeThirteenCubicIdeal
  simpa only [primeThirteenCubicIdealExtension, map_ofNat] using h

/-- The checked extension/contraction and rational-prime support bridge from
the monogenic Magma order to the maximal order. -/
theorem maximalOrderExtension_certificates :
    Function.Injective magmaOrderToIntegers ∧
      primeTwoIdeal ≤
        primeTwoIdealExtension.comap magmaOrderToIntegers ∧
      primeThirteenLinearIdeal ≤
        primeThirteenLinearIdealExtension.comap magmaOrderToIntegers ∧
      primeThirteenCubicIdeal ≤
        primeThirteenCubicIdealExtension.comap magmaOrderToIntegers ∧
      (2 : NumberField.RingOfIntegers SexticField) ∈
        primeTwoIdealExtension ∧
      (13 : NumberField.RingOfIntegers SexticField) ∈
        primeThirteenLinearIdealExtension ∧
      (13 : NumberField.RingOfIntegers SexticField) ∈
        primeThirteenCubicIdealExtension :=
  ⟨magmaOrderToIntegers_injective,
    primeTwoIdeal_le_extension_comap,
    primeThirteenLinearIdeal_le_extension_comap,
    primeThirteenCubicIdeal_le_extension_comap,
    two_mem_primeTwoIdealExtension,
    thirteen_mem_primeThirteenLinearIdealExtension,
    thirteen_mem_primeThirteenCubicIdealExtension⟩

/-- The exact norm, quotient-cardinality, and rational-prime support data
needed by the finite squareclass computation. -/
theorem rawPrimeSupport_certificates :
    Algebra.norm ℤ primeTwoFactor = 8 ∧
      Nat.card (MagmaOrder ⧸ primeTwoIdeal) = 8 ∧
      (2 : MagmaOrder) ∈ primeTwoIdeal ∧
      Algebra.norm ℤ primeThirteenLinearFactor = 13 ∧
      Nat.card (MagmaOrder ⧸ primeThirteenLinearIdeal) = 13 ∧
      (13 : MagmaOrder) ∈ primeThirteenLinearIdeal ∧
      Algebra.norm ℤ primeThirteenCubicFactorRaw = 2197 ∧
      Nat.card (MagmaOrder ⧸ primeThirteenCubicIdeal) = 2197 ∧
      (13 : MagmaOrder) ∈ primeThirteenCubicIdeal :=
  ⟨primeTwoFactor_norm, primeTwoIdeal_quotient_card,
    two_mem_primeTwoIdeal, primeThirteenLinearFactor_norm,
    primeThirteenLinearIdeal_quotient_card,
    thirteen_mem_primeThirteenLinearIdeal,
    primeThirteenCubicFactorRaw_norm,
    primeThirteenCubicIdeal_quotient_card,
    thirteen_mem_primeThirteenCubicIdeal⟩

end

end MazurTorsion.XOneThirteenTwoDescentPrimeNorms
