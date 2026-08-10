/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorLocalization

/-!
# Tensor addition for extended affine divisor ideals

This module equips the extended inverse ideal of an affine divisor with its canonical
tensor/addition equivalence.  The construction is multiplication inside the specified common
fraction field, and its pure-tensor formula is recorded explicitly for base-change consumers.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors TensorProduct

universe u

/-- The extended inverse divisor ideal as an invertible `B`-submodule of the common fraction
field `K`. -/
noncomputable abbrev extendedInverseIdealUnit
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D : WeilDivisor (HeightOneSpectrum R)) : (Submodule B K)ˣ :=
  FractionalIdeal.unitsMulEquivSubmodule
    (Units.map (FractionalIdeal.extendedHom K B).toMonoidHom
      (ExplicitIdeal.divisorFractionalIdeal R K D)⁻¹)

/-- The carrier of the invertible extended inverse ideal is the existing extended-ideal
submodule. -/
@[simp]
lemma coe_extendedInverseIdealUnit
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (extendedInverseIdealUnit R B K D : Submodule B K) =
      extendedInverseIdeal R B K D :=
  rfl

/-- Extension to a common fraction field carries divisor addition to multiplication of the
corresponding invertible inverse-ideal submodules. -/
@[simp]
lemma extendedInverseIdealUnit_add
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    extendedInverseIdealUnit R B K (D + E) =
      extendedInverseIdealUnit R B K D * extendedInverseIdealUnit R B K E := by
  simp only [extendedInverseIdealUnit, ExplicitIdeal.divisorFractionalIdeal_add,
    mul_inv_rev, map_mul]
  exact mul_comm _ _

/-- The extended inverse ideal of a sum is the product of the two extended inverse ideals. -/
@[simp]
lemma extendedInverseIdeal_add
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    extendedInverseIdeal R B K (D + E) =
      extendedInverseIdeal R B K D * extendedInverseIdeal R B K E := by
  simpa only [coe_extendedInverseIdealUnit, Units.val_mul] using
    congrArg Units.val (extendedInverseIdealUnit_add R B K D E)

/-- Multiplication inside the common fraction field identifies the tensor product of two
extended inverse ideals with the extended inverse ideal of the divisor sum. -/
noncomputable def extendedInverseIdealTensorAddEquiv
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (extendedInverseIdeal R B K D ⊗[B] extendedInverseIdeal R B K E) ≃ₗ[B]
      extendedInverseIdeal R B K (D + E) :=
  (Submodule.tensorEquivMul
      (extendedInverseIdealUnit R B K D)
      (extendedInverseIdealUnit R B K E)).trans
    (LinearEquiv.ofEq _ _ (extendedInverseIdeal_add R B K D E).symm)

/-- The extended-ideal tensor/addition equivalence sends pure tensors to multiplication in the
common fraction field. -/
@[simp]
theorem extendedInverseIdealTensorAddEquiv_tmul
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D E : WeilDivisor (HeightOneSpectrum R))
    (x : extendedInverseIdeal R B K D)
    (y : extendedInverseIdeal R B K E) :
    ((extendedInverseIdealTensorAddEquiv R B K D E (x ⊗ₜ[B] y)) : K) =
      (x : K) * (y : K) := by
  simp only [extendedInverseIdealTensorAddEquiv]
  exact Submodule.val_mulMap'_tmul _ _

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension
