/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTensorAdd

/-!
# Base-change naturality of affine divisor tensor addition

Multiplication of extended inverse ideals commutes with a further flat epimorphic scalar
extension.  The comparison is expressed using the canonical equivalence distributing scalar
extension over tensor product.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors TensorProduct

universe u

/-- Two linear equivalences out of a scalar extension of a tensor product agree when they agree
on scalar multiples of nested pure tensors. -/
private theorem nestedTensorLinearEquiv_ext
    {R A M N P : Type*}
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module A P]
    (e f : A ⊗[R] (M ⊗[R] N) ≃ₗ[A] P)
    (h : ∀ (a : A) (m : M) (n : N),
      e (a ⊗ₜ[R] (m ⊗ₜ[R] n)) = f (a ⊗ₜ[R] (m ⊗ₜ[R] n))) :
    e = f := by
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul m n => exact h a m n
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Scalar extension of inverse-ideal multiplication sends a scalar multiple of a pure tensor
to the corresponding scalar multiple of the product in the common fraction field. -/
@[simp]
theorem extendedInverseIdealTensorAddEquiv_baseChange_tmul
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D E : WeilDivisor (HeightOneSpectrum R)) (c : C)
    (x : extendedInverseIdeal R B K D)
    (y : extendedInverseIdeal R B K E) :
    ((((extendedInverseIdealTensorAddEquiv R B K D E).baseChange B C).trans
        (extendedInverseIdealBaseChangeEquiv R B C K (D + E)))
        (c ⊗ₜ[B] (x ⊗ₜ[B] y)) : K) =
      c • ((x : K) * (y : K)) := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    extendedInverseIdealBaseChangeEquiv_apply_tmul,
    extendedInverseIdealTensorAddEquiv_tmul]

/-- The path that first distributes scalar extension and then multiplies the two extended
ideals has the same expected value on nested pure tensors. -/
private theorem extendedInverseIdealTensorAddEquiv_baseChange_rhs_tmul
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D E : WeilDivisor (HeightOneSpectrum R)) (c : C)
    (x : extendedInverseIdeal R B K D)
    (y : extendedInverseIdeal R B K E) :
    (((TensorProduct.AlgebraTensorModule.distribBaseChange B C
          (extendedInverseIdeal R B K D)
          (extendedInverseIdeal R B K E)).trans
        ((TensorProduct.congr
            (extendedInverseIdealBaseChangeEquiv R B C K D)
            (extendedInverseIdealBaseChangeEquiv R B C K E)).trans
          (extendedInverseIdealTensorAddEquiv R C K D E)))
        (c ⊗ₜ[B] (x ⊗ₜ[B] y)) : K) =
      c • ((x : K) * (y : K)) := by
  simp only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul, extendedInverseIdealBaseChangeEquiv_apply_tmul,
    extendedInverseIdealTensorAddEquiv_tmul, one_smul, Algebra.smul_mul_assoc]

/-- Multiplication of extended inverse ideals is natural under a further flat epimorphic base
change. The comparison uses the canonical distributivity equivalence from scalar extension of a
tensor product to the tensor product of the two scalar extensions. -/
theorem extendedInverseIdealTensorAddEquiv_baseChange
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((extendedInverseIdealTensorAddEquiv R B K D E).baseChange B C).trans
        (extendedInverseIdealBaseChangeEquiv R B C K (D + E)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange B C
          (extendedInverseIdeal R B K D)
          (extendedInverseIdeal R B K E)).trans
        ((TensorProduct.congr
            (extendedInverseIdealBaseChangeEquiv R B C K D)
            (extendedInverseIdealBaseChangeEquiv R B C K E)).trans
          (extendedInverseIdealTensorAddEquiv R C K D E)) := by
  apply nestedTensorLinearEquiv_ext
  intro c x y
  apply Subtype.ext
  exact (extendedInverseIdealTensorAddEquiv_baseChange_tmul
    R B C K D E c x y).trans
      (extendedInverseIdealTensorAddEquiv_baseChange_rhs_tmul
        R B C K D E c x y).symm

/-- The path that first multiplies the fixed chosen line-bundle modules and then compares with
the extended inverse ideal has the expected value on nested pure tensors. -/
private theorem lineBundleModuleTensorAddEquiv_baseChange_lhs_tmul
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) (b : B)
    (x : AffineDedekind.lineBundleModule R K D)
    (y : AffineDedekind.lineBundleModule R K E) :
    (((ExplicitIdeal.lineBundleModuleTensorAddEquiv R K D E).baseChange R B |>.trans
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E)))
        (b ⊗ₜ[R] (x ⊗ₜ[R] y)) : K) =
      b • ((FractionRing.algEquiv R K)
          ((ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K D x :
            ExplicitIdeal.inverseIdeal R K D) : FractionRing R) *
        (FractionRing.algEquiv R K)
          ((ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K E y :
            ExplicitIdeal.inverseIdeal R K E) : FractionRing R)) := by
  simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    lineBundleModuleBaseChangeEquivExtendedInverseIdeal_tmul,
    ExplicitIdeal.lineBundleModuleTensorAddEquiv_tmul, map_mul]

/-- The path that first distributes scalar extension, compares each chosen module with its
extended inverse ideal, and then multiplies has the same value on nested pure tensors. -/
private theorem lineBundleModuleTensorAddEquiv_baseChange_rhs_tmul
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) (b : B)
    (x : AffineDedekind.lineBundleModule R K D)
    (y : AffineDedekind.lineBundleModule R K E) :
    (((TensorProduct.AlgebraTensorModule.distribBaseChange R B
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).trans
        ((TensorProduct.congr
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)).trans
          (extendedInverseIdealTensorAddEquiv R B K D E)))
        (b ⊗ₜ[R] (x ⊗ₜ[R] y)) : K) =
      b • ((FractionRing.algEquiv R K)
          ((ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K D x :
            ExplicitIdeal.inverseIdeal R K D) : FractionRing R) *
        (FractionRing.algEquiv R K)
          ((ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K E y :
            ExplicitIdeal.inverseIdeal R K E) : FractionRing R)) := by
  simp only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul,
    lineBundleModuleBaseChangeEquivExtendedInverseIdeal_tmul,
    extendedInverseIdealTensorAddEquiv_tmul, one_smul,
    Algebra.smul_mul_assoc]

/-- The deterministic tensor-to-sum equivalence for the fixed affine line-bundle modules is
natural under flat epimorphic scalar extension.  The lower path distributes scalar extension,
compares both factors with their extended inverse ideals, and multiplies there. -/
theorem lineBundleModuleTensorAddEquiv_baseChange
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((ExplicitIdeal.lineBundleModuleTensorAddEquiv R K D E).baseChange R B).trans
        (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K (D + E)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R B
          (AffineDedekind.lineBundleModule R K D)
          (AffineDedekind.lineBundleModule R K E)).trans
        ((TensorProduct.congr
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K D)
            (lineBundleModuleBaseChangeEquivExtendedInverseIdeal R B K E)).trans
          (extendedInverseIdealTensorAddEquiv R B K D E)) := by
  apply nestedTensorLinearEquiv_ext
  intro b x y
  apply Subtype.ext
  exact (lineBundleModuleTensorAddEquiv_baseChange_lhs_tmul
    R B K D E b x y).trans
      (lineBundleModuleTensorAddEquiv_baseChange_rhs_tmul
        R B K D E b x y).symm

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension
